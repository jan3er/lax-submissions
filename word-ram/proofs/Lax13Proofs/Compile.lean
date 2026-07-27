import Lax13.Ram
import Lax13Proofs.Bounds

/-!
The compiler from IMP+ to word-machine programs.

Its whole content is the memory layout, because the machine has no
structure at all: one accumulator, cells addressed by number, absolute
jumps. Three regions, all at statically known addresses since the
machine's memory starts empty (`Lax13.Ram.initState`):

* cells `0 … temps-1` hold temporaries, one per nesting depth of the
  expression being evaluated;
* cell `temps + i` holds the `i`-th scalar variable;
* cell `temps + p + j + q * i` holds entry `i` of the `j`-th array,
  where `p` is the number of scalars and `q` the number of arrays.

The arrays are *interleaved* rather than laid out in blocks. Their
lengths are not known to the compiler, so blocks would start at
addresses known only at run time, and a machine with one accumulator
cannot usefully compute with such addresses; striding by the number of
arrays keeps every address a static affine function of the index, at
the price of `q` additions per access and a factor `q` of address
space. Address space is nearly free: there is no space measure, and the
only cost is that the word length has to be large enough to address the
last cell, which is what `Layout.span` measures.

Jump targets are absolute, so the compiler takes the address at which
the block it emits will be placed, and the length of a block has to be
known before it is emitted. `size` computes it, and `compile_length`
says the two agree.

Expressions are compiled at a depth `d`: the code may use temporaries
`d, d+1, …`, and leaves its value in the accumulator. Both operands of
a binary operator are compiled at consecutive depths, the second
operand first, so that the non-commutative operators need no swap. All
nine operators compile to the same three-block shape, which is what
`binInstr` is for.

Conditions leave the accumulator *zero exactly when they hold*, so both
are followed by the same `jzero`; truncated subtraction is what makes
this possible without a comparison instruction, and it is the reason
the model keeps monus.
-/

namespace Lax13Proofs.Compile

open Lax13.Ram Lax13Proofs.Imp

/-! ### Layouts -/

/-- A memory layout: the scalar names and the array names it can
address, and the number of temporary cells reserved below them. -/
structure Layout where
  /-- The scalar variables, in the order of their cells. -/
  scalars : List String
  /-- The arrays, in the order of their cells. -/
  arrays : List String
  /-- The number of temporary cells, which are the lowest ones. -/
  temps : ℕ

/-- The cell holding the scalar variable `x`. -/
def Layout.varAddr (L : Layout) (x : String) : ℕ :=
  L.temps + L.scalars.idxOf x

/-- The cell holding entry `0` of the array `a`. -/
def Layout.arrBase (L : Layout) (a : String) : ℕ :=
  L.temps + L.scalars.length + L.arrays.idxOf a

/-- The cell holding entry `i` of the array `a`. -/
def Layout.arrAddr (L : Layout) (a : String) (i : ℕ) : ℕ :=
  L.arrBase a + L.arrays.length * i

/-- One past every cell the layout addresses, when every index stays
below `B`. -/
def Layout.span (L : Layout) (B : ℕ) : ℕ :=
  L.temps + L.scalars.length + L.arrays.length * B

/-- The layout runs on words of length `w` when values stay below `B`:
the values fit into a word, and so does every cell the layout
addresses. This is the whole of the word-length hypothesis of the
simulation theorem; it is where the model's `% 2 ^ w` is paid for, and
it is stated as an explicit inequality against `2 ^ w`, as everything
about word lengths in this development is. -/
structure Layout.FitsWords (L : Layout) (B w : ℕ) : Prop where
  /-- The bound admits at least the values `0` and `1`, which the
  compiled comparisons need. -/
  one_lt : 1 < B
  /-- Every value the run produces is a word. -/
  bound : B ≤ 2 ^ w
  /-- Every cell the layout addresses is a word. -/
  span : L.span B ≤ 2 ^ w

theorem Layout.lt_two_pow_of_lt_temps {L : Layout} {B w d : ℕ} (h : L.FitsWords B w)
    (hd : d < L.temps) : d < 2 ^ w := by
  have hs := h.span
  simp only [Layout.span] at hs
  omega

theorem Layout.varAddr_lt_two_pow {L : Layout} {B w : ℕ} (h : L.FitsWords B w) {x : String}
    (hx : x ∈ L.scalars) : L.varAddr x < 2 ^ w := by
  have hidx : L.scalars.idxOf x < L.scalars.length := List.idxOf_lt_length_of_mem hx
  have hs := h.span
  simp only [Layout.span] at hs
  simp only [Layout.varAddr]
  omega

theorem Layout.arrAddr_lt_two_pow {L : Layout} {B w : ℕ} (h : L.FitsWords B w) {a : String}
    (ha : a ∈ L.arrays) {k : ℕ} (hk : k < B) : L.arrAddr a k < 2 ^ w := by
  have hidx : L.arrays.idxOf a < L.arrays.length := List.idxOf_lt_length_of_mem ha
  have hmul : L.arrays.length * (k + 1) ≤ L.arrays.length * B := Nat.mul_le_mul_left _ hk
  have hexp : L.arrays.length * (k + 1) = L.arrays.length * k + L.arrays.length := by ring
  have hs := h.span
  simp only [Layout.span] at hs
  simp only [Layout.arrAddr, Layout.arrBase]
  omega

theorem Layout.mul_le_arrAddr (L : Layout) (a : String) (k : ℕ) :
    L.arrays.length * k ≤ L.arrAddr a k := by
  simp only [Layout.arrAddr]; omega

/-! ### The instruction of a binary operator -/

/-- The machine instruction computing the operator `op` against the
operand `o`. -/
def binInstr : Bop → Op → Instr
  | .add, o => .add o
  | .sub, o => .sub o
  | .mul, o => .mul o
  | .div, o => .div o
  | .and, o => .and o
  | .or, o => .or o
  | .xor, o => .xor o
  | .shiftl, o => .shiftl o
  | .shiftr, o => .shiftr o

/-- Every operator's instruction has the same effect: the operator
applied to the accumulator and the operand, reduced modulo `2 ^ w`.
This one equation is what lets the nine operators be compiled and
proved correct once. -/
theorem effect_binInstr (op : Bop) (w : ℕ) (o : Op) (s : State) :
    (binInstr op o).effect w s =
      some { s with pc := s.pc + 1, acc := op.apply s.acc (o.value w s.mem) % 2 ^ w } := by
  cases op <;> rfl

/-! ### Code -/

/-- The code turning the index of an entry of `a`, held in the
accumulator, into the address of that entry, left both in the
accumulator and in the temporary `d`. -/
def Layout.idxCode (L : Layout) (a : String) (d : ℕ) : Program :=
  Instr.store d :: (List.replicate (L.arrays.length - 1) (Instr.add (.mem d)) ++
    [.add (.lit (L.arrBase a)), .store d])

/-- The length of `Layout.idxCode`. -/
def Layout.idxLen (L : Layout) : ℕ := L.arrays.length - 1 + 3

/-- The constant of the simulation theorem: the compiled program takes
at most this many machine steps per unit of IMP+ cost. It depends on
the layout only through the cost of one array access, which is where
the number of arrays enters, and not on the program, the input or the
word length. Nothing about it is tight. -/
def Layout.const (L : Layout) : ℕ := 3 * L.idxLen + 13

/-- The code evaluating `e` into the accumulator, using the temporaries
from `d` upwards. -/
def compileExpr (L : Layout) : Expr → ℕ → Program
  | .lit n, _ => [.load (.lit n)]
  | .var x, _ => [.load (.mem (L.varAddr x))]
  | .get a i, d => compileExpr L i d ++ L.idxCode a d ++ [.load (.ind d)]
  | .bin op e f, d =>
      compileExpr L f d ++ [.store d] ++ compileExpr L e (d + 1) ++ [binInstr op (.mem d)]

/-- The number of instructions of `compileExpr`. -/
def esize (L : Layout) : Expr → ℕ
  | .lit _ => 1
  | .var _ => 1
  | .get _ i => esize L i + L.idxLen + 1
  | .bin _ e f => esize L f + 1 + esize L e + 1

/-- The arithmetic expression that is zero exactly when the condition
holds. Truncated subtraction is what makes both conditions expressible,
and it is why the machine needs no comparison instruction; compiling a
condition is then compiling this expression, and the `jzero` that
follows needs to know nothing else. -/
def condExpr : Cond → Expr
  | .eq e f => .bin .add (.bin .sub e f) (.bin .sub f e)
  | .lt e f => .bin .sub (.lit 1) (.bin .sub f e)

/-- The code leaving the accumulator zero exactly when `b` holds. -/
def compileCond (L : Layout) (b : Cond) (d : ℕ) : Program :=
  compileExpr L (condExpr b) d

/-- The number of instructions of `compileCond`. -/
def bsize (L : Layout) (b : Cond) : ℕ := esize L (condExpr b)

/-- The number of instructions of `compile`. -/
def size (L : Layout) : Com → ℕ
  | .skip => 0
  | .assign _ e => esize L e + 1
  | .store _ i e => esize L i + L.idxLen + esize L e + 1
  | .seq c d => size L c + size L d
  | .ite b c d => bsize L b + 1 + size L d + 1 + size L c
  | .while b c => bsize L b + 2 + size L c + 1
  | .read _ => 1
  | .write e => esize L e + 2

/-- The code running `c`, laid out at address `a`. -/
def compile (L : Layout) : Com → ℕ → Program
  | .skip, _ => []
  | .assign x e, _ => compileExpr L e 0 ++ [.store (L.varAddr x)]
  | .store a i e, _ =>
      compileExpr L i 0 ++ L.idxCode a 0 ++ compileExpr L e 1 ++ [.storeInd 0]
  | .seq c d, a => compile L c a ++ compile L d (a + size L c)
  | .ite b c d, a =>
      compileCond L b 0 ++ [.jzero (a + bsize L b + 1 + size L d + 1)] ++
        compile L d (a + bsize L b + 1) ++
        [.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
        compile L c (a + bsize L b + 1 + size L d + 1)
  | .while b c, a =>
      compileCond L b 0 ++
        [.jzero (a + bsize L b + 2), .jump (a + bsize L b + 2 + size L c + 1)] ++
        compile L c (a + bsize L b + 2) ++ [.jump a]
  | .read x, _ => [.read (L.varAddr x)]
  | .write e, _ => compileExpr L e 0 ++ [.store 0, .write (.mem 0)]

/-- The whole machine program for `c`: its code, then a halt. -/
def compileProgram (L : Layout) (c : Com) : Program :=
  compile L c 0 ++ [.halt]

/-! ### Compilability -/

/-- `e` can be compiled by `L` at depth `d`: every name it mentions is
in the layout, and the temporaries it uses are there. -/
def Expr.Ok (L : Layout) : Expr → ℕ → Prop
  | .lit _, _ => True
  | .var x, _ => x ∈ L.scalars
  | .get a i, d => a ∈ L.arrays ∧ Expr.Ok L i d ∧ d < L.temps
  | .bin _ e f, d => Expr.Ok L f d ∧ Expr.Ok L e (d + 1) ∧ d < L.temps

/-- `b` can be compiled by `L` at depth `d`. -/
def Cond.Ok (L : Layout) (b : Cond) (d : ℕ) : Prop := Expr.Ok L (condExpr b) d

/-- `c` can be compiled by `L`. -/
def Com.Ok (L : Layout) : Com → Prop
  | .skip => True
  | .assign x e => x ∈ L.scalars ∧ Expr.Ok L e 0
  | .store a i e => a ∈ L.arrays ∧ Expr.Ok L i 0 ∧ Expr.Ok L e 1 ∧ 0 < L.temps
  | .seq c d => Com.Ok L c ∧ Com.Ok L d
  | .ite b c d => Cond.Ok L b 0 ∧ Com.Ok L c ∧ Com.Ok L d
  | .while b c => Cond.Ok L b 0 ∧ Com.Ok L c
  | .read x => x ∈ L.scalars
  | .write e => Expr.Ok L e 0 ∧ 0 < L.temps

/-! ### Code lengths

Block lengths are what the absolute jump targets are computed from, so
the emitted code has to have the length `size` predicted, whatever
address it is emitted at. -/

@[simp] theorem idxCode_length (L : Layout) (a : String) (d : ℕ) :
    (L.idxCode a d).length = L.idxLen := by
  simp [Layout.idxCode, Layout.idxLen]

@[simp] theorem compileExpr_length (L : Layout) (e : Expr) (d : ℕ) :
    (compileExpr L e d).length = esize L e := by
  induction e generalizing d with
  | lit n => simp [compileExpr, esize]
  | var x => simp [compileExpr, esize]
  | get a i ih => simp [compileExpr, esize, ih]; omega
  | bin op e f ihe ihf => simp [compileExpr, esize, ihe, ihf]; omega

@[simp] theorem compileCond_length (L : Layout) (b : Cond) (d : ℕ) :
    (compileCond L b d).length = bsize L b := by
  simp [compileCond, bsize]

@[simp] theorem compile_length (L : Layout) (c : Com) (a : ℕ) :
    (compile L c a).length = size L c := by
  induction c generalizing a with
  | skip => simp [compile, size]
  | assign x e => simp [compile, size]
  | store x i e => simp [compile, size]; omega
  | seq c d ihc ihd => simp [compile, size, ihc, ihd]
  | ite b c d ihc ihd => simp [compile, size, ihc, ihd]; omega
  | «while» b c ih => simp [compile, size, ih]; omega
  | read x => simp [compile, size]
  | write e => simp [compile, size]

/-! ### The layout is injective

Distinct names, and distinct entries of an array, get distinct cells;
temporaries are below everything else. This is the only place where the
interleaving of the arrays has to be argued: the entry `i` of the `j`-th
array sits at `j + q * i`, and `j < q` recovers both `j` and `i` from
that number as its remainder and quotient. -/

theorem index_inj {q ja jb i j : ℕ} (hja : ja < q) (hjb : jb < q)
    (h : ja + q * i = jb + q * j) : ja = jb ∧ i = j := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hja
  refine ⟨?_, ?_⟩
  · have := congrArg (· % q) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hja, Nat.mod_eq_of_lt hjb] using this
  · have := congrArg (· / q) h
    simpa [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hja, Nat.div_eq_of_lt hjb] using this

theorem temps_le_varAddr (L : Layout) (x : String) : L.temps ≤ L.varAddr x :=
  Nat.le_add_right _ _

theorem varAddr_lt (L : Layout) {x : String} (h : x ∈ L.scalars) :
    L.varAddr x < L.temps + L.scalars.length :=
  Nat.add_lt_add_left (List.idxOf_lt_length_of_mem h) _

theorem le_arrAddr (L : Layout) (a : String) (i : ℕ) :
    L.temps + L.scalars.length ≤ L.arrAddr a i :=
  Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem varAddr_inj (L : Layout) {x y : String} (hx : x ∈ L.scalars) (hy : y ∈ L.scalars)
    (h : L.varAddr x = L.varAddr y) : x = y := by
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  have : L.scalars.idxOf x = L.scalars.idxOf y := by
    simp only [Layout.varAddr] at h; omega
  calc x = L.scalars[L.scalars.idxOf x] := (List.getElem_idxOf hx').symm
    _ = L.scalars[L.scalars.idxOf y]'(by omega) := by simp [this]
    _ = y := List.getElem_idxOf hy'

theorem arrAddr_inj (L : Layout) {a b : String} {i j : ℕ} (ha : a ∈ L.arrays)
    (hb : b ∈ L.arrays) (h : L.arrAddr a i = L.arrAddr b j) : a = b ∧ i = j := by
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have h' : L.arrays.idxOf a + L.arrays.length * i = L.arrays.idxOf b + L.arrays.length * j := by
    simp only [Layout.arrAddr, Layout.arrBase] at h; omega
  obtain ⟨hidx, hij⟩ := index_inj ha' hb' h'
  refine ⟨?_, hij⟩
  calc a = L.arrays[L.arrays.idxOf a] := (List.getElem_idxOf ha').symm
    _ = L.arrays[L.arrays.idxOf b]'(by omega) := by simp [hidx]
    _ = b := List.getElem_idxOf hb'

theorem varAddr_ne_arrAddr (L : Layout) {x a : String} (hx : x ∈ L.scalars) (i : ℕ) :
    L.varAddr x ≠ L.arrAddr a i := by
  have := varAddr_lt L hx
  have := le_arrAddr L a i
  omega

/-! ### Conditions under the bound

`condExpr` computes with differences of the two operands only, so it
stays below the bound as soon as the operands do — with the single
exception of the literal `1` of `lt`, which is why `FitsWords` asks for
`1 < B`. -/

theorem condExpr_evalB {B : ℕ} {b : Cond} {σ : Env} {r : Bool} (hB : 1 < B)
    (h : b.evalB B σ = some r) :
    ∃ v, (condExpr b).evalB B σ = some v ∧ (v = 0 ↔ r = true) := by
  cases b with
  | eq e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      have hmB := Expr.lt_of_evalB hm
      have hnB := Expr.lt_of_evalB hn
      have h1 : (Expr.bin Bop.sub e f).evalB B σ = some (m - n) := by
        show ((e.evalB B σ).bind fun p => (f.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
          = some (m - n)
        rw [hm, hn]
        exact fit_self (show m - n < B by omega)
      have h2 : (Expr.bin Bop.sub f e).evalB B σ = some (n - m) := by
        show ((f.evalB B σ).bind fun p => (e.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
          = some (n - m)
        rw [hm, hn]
        exact fit_self (show n - m < B by omega)
      refine ⟨(m - n) + (n - m), ?_, by simp only [beq_iff_eq]; omega⟩
      show ((Expr.bin Bop.sub e f).evalB B σ).bind
          (fun p => ((Expr.bin Bop.sub f e).evalB B σ).bind fun q => fit B (Bop.add.apply p q))
        = some ((m - n) + (n - m))
      rw [h1, h2]
      exact fit_self (show (m - n) + (n - m) < B by omega)
  | lt e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      have hmB := Expr.lt_of_evalB hm
      have hnB := Expr.lt_of_evalB hn
      have h2 : (Expr.bin Bop.sub f e).evalB B σ = some (n - m) := by
        show ((f.evalB B σ).bind fun p => (e.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
          = some (n - m)
        rw [hm, hn]
        exact fit_self (show n - m < B by omega)
      refine ⟨1 - (n - m), ?_, by simp only [decide_eq_true_eq]; omega⟩
      show (fit B 1).bind
          (fun p => ((Expr.bin Bop.sub f e).evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
        = some (1 - (n - m))
      rw [fit_self hB, h2]
      exact fit_self (show 1 - (n - m) < B by omega)

end Lax13Proofs.Compile
