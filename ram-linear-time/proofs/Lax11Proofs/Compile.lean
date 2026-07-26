import Lax11.Ram
import Lax11Proofs.Imp

/-!
The compiler from IMP+ to machine programs.

Its whole content is the memory layout, because the machine has no
structure at all: one accumulator, cells addressed by number, absolute
jumps. Three regions, all at statically known addresses since the
machine's memory starts empty (`Lax11.Ram.initState`):

* cells `0 … temps-1` hold temporaries, one per nesting depth of the
  expression being evaluated;
* cell `temps + i` holds the `i`-th scalar variable;
* cell `temps + p + j + q * i` holds entry `i` of the `j`-th array,
  where `p` is the number of scalars and `q` the number of arrays.

The arrays are *interleaved* rather than laid out in blocks. Their
lengths are unbounded, so blocks would start at addresses that are
known only at run time, and a machine with one accumulator cannot
usefully compute with such addresses; striding by the number of arrays
keeps every address a static affine function of the index, at the price
of `q` additions per access and a factor `q` of address space. Address
space is free: there is no space measure.

Jump targets are absolute, so the compiler takes the address at which
the block it emits will be placed, and the length of a block has to be
known before it is emitted. `size` computes it, and
`compile_length` says the two agree.

Expressions are compiled at a depth `d`: the code may use temporaries
`d, d+1, …`, and leaves its value in the accumulator. Both branches of
a binary operator are compiled at consecutive depths, the second
operand first, so that the non-commutative `sub` needs no swap.
Conditions leave the accumulator *zero exactly when they hold*, so both
are followed by the same `jzero`; truncated subtraction is what makes
this possible without a comparison instruction.
-/

namespace Lax11Proofs.Compile

open Lax11.Ram Lax11Proofs.Imp

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
the number of arrays enters, and not on the program or the input.
Nothing about it is tight. -/
def Layout.const (L : Layout) : ℕ := 3 * L.idxLen + 13

/-- The code evaluating `e` into the accumulator, using the temporaries
from `d` upwards. -/
def compileExpr (L : Layout) : Expr → ℕ → Program
  | .lit n, _ => [.load (.lit n)]
  | .var x, _ => [.load (.mem (L.varAddr x))]
  | .get a i, d => compileExpr L i d ++ L.idxCode a d ++ [.load (.ind d)]
  | .add e f, d =>
      compileExpr L f d ++ [.store d] ++ compileExpr L e (d + 1) ++ [.add (.mem d)]
  | .sub e f, d =>
      compileExpr L f d ++ [.store d] ++ compileExpr L e (d + 1) ++ [.sub (.mem d)]

/-- The number of instructions of `compileExpr`. -/
def esize (L : Layout) : Expr → ℕ
  | .lit _ => 1
  | .var _ => 1
  | .get _ i => esize L i + L.idxLen + 1
  | .add e f => esize L f + 1 + esize L e + 1
  | .sub e f => esize L f + 1 + esize L e + 1

/-- The arithmetic expression that is zero exactly when the condition
holds. Truncated subtraction is what makes both conditions expressible,
and it is why the machine needs no comparison instruction; compiling a
condition is then compiling this expression, and the `jzero` that
follows needs to know nothing else. -/
def condExpr : Cond → Expr
  | .eq e f => .add (.sub e f) (.sub f e)
  | .lt e f => .sub (.lit 1) (.sub f e)

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

/-- `e` can be compiled by `L` at depth `d`: every name it mentions is
in the layout, and the temporaries it uses are there. -/
def Expr.Ok (L : Layout) : Expr → ℕ → Prop
  | .lit _, _ => True
  | .var x, _ => x ∈ L.scalars
  | .get a i, d => a ∈ L.arrays ∧ Expr.Ok L i d ∧ d < L.temps
  | .add e f, d => Expr.Ok L f d ∧ Expr.Ok L e (d + 1) ∧ d < L.temps
  | .sub e f, d => Expr.Ok L f d ∧ Expr.Ok L e (d + 1) ∧ d < L.temps

/-- `b` can be compiled by `L` at depth `d`. -/
def Cond.Ok (L : Layout) (b : Cond) (d : ℕ) : Prop := Expr.Ok L (condExpr b) d

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
  | add e f ihe ihf => simp [compileExpr, esize, ihe, ihf]; omega
  | sub e f ihe ihf => simp [compileExpr, esize, ihe, ihf]; omega

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

end Lax11Proofs.Compile
