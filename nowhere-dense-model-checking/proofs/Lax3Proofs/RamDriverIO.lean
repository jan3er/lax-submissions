import Lax3Proofs.RamDriver

/-!
The driver's two ends: the tape decode that opens the root arena, and
the sentence readback that writes the one bit.

These are the first and the last phase of `Lax3Proofs.RamDriver`'s
program — the two that touch the tapes — and they are the two whose
obligations (`RamDriver.DecodeImplements`, `RamDriver.SentenceImplements`)
this file answers.

# Two clauses those obligations were missing

Both obligations used to be stated with a precondition that pinned no
array and named no value bound, and as stated **both were false**. They
now carry the two missing conjuncts, and this file discharges them as
they stand.

*The memory clause.* IMP+ arrays have lengths, an out-of-range store is
*stuck* rather than defaulted, and the decode's first act is a store
into `off`; so the state whose arrays are all empty satisfied the
decode's old precondition and no run of the phase starts in it. Since a
run cannot lengthen an array either, the postcondition's `off` of
`n + 1` cells refuted the old obligation outright. The house form of
the clause is `RamCover.CoverPre`, which does pin every array its pass
touches; `RamDriver.DecodeMem` is that clause for the decode.
`RootMem` is it for the readback — the scratch arrays of the scatter
pass must hold *words* (`RamScatter.scatter_spec` asks for
`RamScatter.Words`), and so must the table arrays, since the readback's
copy reads their cells and a cell at or above the value bound makes the
read stuck — and `rootMem_of_levelPre` is why the sentence obligation
needs no memory conjunct beyond `RamDriver.LevelPre`'s own
`RamDriver.LevelMem` and `RamDriver.TableInv`'s own bit clause.

*The value bounds.* Nothing in either obligation used to say that the
carrier, the slot count, or the constants of the sentence are words.
They have to be: at `B = 0` no expression evaluates at all, so the
sentence's own final write has no derivation. `RamDriver.WordBound` is
the one bound every phase of a level is stated over, and every bound
this file asks for is one of its four readings.

# The walks

*The decode* is `Lax11Proofs.CC`'s reading phase: two `Spec.read`s, two
counter assignments, two read loops, and two constant fills.
`readLoop_spec` is the read loop, proved once against the kit's
`Fill.Below`; `RamBfs.csrGraph_of_encodesGraph` turns what the loops
leave into the block structure every pass below reads; and
`Fill.loop_spec` at the constant one is the all-alive mask, of which
`RamElim.masked_of_all_alive` (used by the caller, not here) says that
the arena it opens is the input graph.

*The sentence readback* is one `RamScatter.scatter_spec` per scatter
atom of the top sentence — each preceded by the two copies the calling
convention asks for, each followed by the assignment of the atom's flag
— and then a single `Spec.write` of `RamDriver.bcExpr` over the flags
and the construction-time constants `Evaluator.localSentenceEval`
decides. `evalB_bcExpr` is the arithmetic of the bits: a boolean
combination of expressions valued in `{0, 1}` evaluates to `1` exactly
when the combination holds.

# Names

The driver generates its array and scalar names by string
interpolation, and a walk over its program text has to know that the
generated names are distinct from the fixed names its sub-programs
address, and from each other. `ne_of_append` is the whole of it: a name
built from a literal prefix differs from any literal that the prefix is
not an initial segment of, which on concrete strings is `decide`.
Injectivity of the flag names is `Nat.toNat?_repr`, the round trip
through the decimal reading.

# Two additions to the kit

`Run` preserves the length of every array (`RamDriver.run_length_arrs`)
and, being bounded, preserves "every cell of this array is a word"
(`RamDriver.run_mem_arrs_lt`). Neither is a frame condition — both hold
of arrays the command *does* write — and the scatter pass, which writes
its three scratch arrays and says nothing about them afterwards, cannot
be called twice without them. Both live in `Lax3Proofs.RamDriver`, since
the memory clauses of every phase are carried across runs by them.
-/

namespace Lax3Proofs.RamDriverIO

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph csrGraph_of_encodesGraph)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (run_length_arrs run_mem_arrs_lt exists_arrOf words_of_length
  DecodeMem)

/-! ### Generated names

Every per-depth name of `Lax3Proofs.RamDriver` is a literal prefix
followed by a decimal numeral. Two facts about such names are needed and
no more: one differs from a literal that does not extend its prefix, and
two of them with the same prefix differ as soon as their numerals do. -/

/-- **A prefixed name differs from a literal it does not begin.** The
hypothesis is about two closed strings, so every use of this is
`decide`. -/
theorem ne_of_append (p s q : String) (h : q.toList.take p.toList.length ≠ p.toList) :
    p ++ s ≠ q := by
  intro he
  exact h (by rw [← he, String.toList_append, List.take_left])

/-- The decimal numeral determines the number: the round trip through
`String.toNat?`. -/
theorem toString_inj {a b : ℕ} (h : toString a = toString b) : a = b := by
  have h' : (Nat.repr a).toNat? = (Nat.repr b).toNat? := by
    simp only [← Nat.toString_eq_repr]; rw [h]
  rw [Nat.toNat?_repr, Nat.toNat?_repr] at h'
  exact Option.some.inj h'

/-- **The root's flag names are pairwise distinct**, which is why the
flag a scatter call leaves survives every later call. -/
theorem rootFlgName_inj {a b : ℕ} (h : RamDriver.rootFlgName a = RamDriver.rootFlgName b) :
    a = b := by
  have h₁ : (toString a).toList = (toString b).toList := by
    have h₂ := congrArg String.toList h
    rw [RamDriver.rootFlgName, RamDriver.rootFlgName, String.toList_append,
      String.toList_append] at h₂
    exact List.append_cancel_left h₂
  exact toString_inj (String.toList_inj.mp h₁)

/-- The depth-zero table names, as a prefixed name. -/
theorem tabName_zero_eq (i : ℕ) : RamDriver.tabName 0 i = "ta0_" ++ toString i := by
  rw [RamDriver.tabName]; rfl

/-- **A prefixed name is none of a list of literals it does not begin.**
On concrete program text the hypothesis is `decide`, since `Com.wvars`
and `Com.warrs` reduce to closed lists of literals. -/
theorem notMem_of_append {p s : String} {l : List String}
    (h : ∀ q ∈ l, q.toList.take p.toList.length ≠ p.toList) : p ++ s ∉ l :=
  fun hm => ne_of_append p s _ (h _ hm) rfl

/-! The radius and the threshold of a scatter call occur only inside
expressions, which neither `Com.wvars` nor `Com.warrs` looks at, so the
frame of the pass is one closed list and every question about it is
`decide`. -/

/-- The scalars the scatter pass may assign to do not depend on its two
parameters. -/
theorem wvars_scatterCom (r t : ℕ) :
    (RamScatter.scatterCom r t).wvars = (RamScatter.scatterCom 0 0).wvars := rfl

/-- Nor do the arrays it may store into. -/
theorem warrs_scatterCom (r t : ℕ) :
    (RamScatter.scatterCom r t).warrs = (RamScatter.scatterCom 0 0).warrs := rfl

/-- The root's flag names are none of the scatter pass's scalars. -/
theorem rootFlg_notMem_scatter_wvars (r t k : ℕ) :
    RamDriver.rootFlgName k ∉ (RamScatter.scatterCom r t).wvars := by
  rw [wvars_scatterCom]
  exact notMem_of_append (p := "rf") (s := toString k) (by decide)

/-- The depth-zero table arrays are none of the scatter pass's. -/
theorem tab_notMem_scatter_warrs (r t i : ℕ) :
    RamDriver.tabName 0 i ∉ (RamScatter.scatterCom r t).warrs := by
  rw [tabName_zero_eq, warrs_scatterCom]
  exact notMem_of_append (p := "ta0_") (s := toString i) (by decide)

/-- The scatter pass writes no output. -/
theorem noWrite_scatterCom (r t : ℕ) : (RamScatter.scatterCom r t).NoWrite := by
  have h : (RamScatter.scatterCom 0 0).NoWrite := by decide
  exact h

/-- A root flag name differs from every literal that does not begin
`"rf"`. -/
theorem rootFlgName_ne (k : ℕ) (q : String)
    (h : q.toList.take ("rf" : String).toList.length ≠ ("rf" : String).toList) :
    RamDriver.rootFlgName k ≠ q := ne_of_append _ _ _ h

/-- Nor is a depth-zero table array either of the two the calling
convention copies into. -/
theorem tabName_zero_ne (i : ℕ) (q : String)
    (h : q.toList.take ("ta0_" : String).toList.length ≠ ("ta0_" : String).toList) :
    RamDriver.tabName 0 i ≠ q := by
  rw [tabName_zero_eq]; exact ne_of_append _ _ _ h

/-! ### Reading a word by position

Three `List` facts about `getD`, and the four fields of
`Lax11.GraphEncoding` restated as readings of the word. The restatements
are `rfl`, which is how a concept-side definition is taken apart here:
the definitions themselves are never handed to a tactic. -/

theorem getD_take {l : List ℕ} {k i : ℕ} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_drop {l : List ℕ} {k i : ℕ} : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_cons_cons {a b i : ℕ} {l : List ℕ} : (a :: b :: l).getD (2 + i) 0 = l.getD i 0 := by
  rw [show 2 + i = i + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]

/-- The declared number of vertices is the word's first entry. -/
theorem vertexCount_eq (x : List ℕ) : vertexCount x = x.getD 0 0 := rfl

/-- The declared number of edges is the word's second entry. -/
theorem edgeCount_eq (x : List ℕ) : edgeCount x = x.getD 1 0 := rfl

/-- The offsets follow the two header entries. -/
theorem offset_eq (x : List ℕ) (i : ℕ) : offset x i = x.getD (2 + i) 0 := rfl

/-- The target array follows the header and the offsets. -/
theorem target_eq (x : List ℕ) (j : ℕ) : target x j = x.getD (3 + vertexCount x + j) 0 := rfl

/-! ### The read loop

`RamDriver.readLoop a lim` moves the first `lim` numbers of the tape
into `a`. It is `Spec.forRangeZero` over the kit's fill, with the tape's
own bookkeeping — how much of the block is still to come — as the extra
clause of the invariant. -/

/-- The invariant of a read loop: `i` numbers have been moved from the
tape into the array, and what is left of the tape starts at `i`.

**The array is the allocation width, the block is a prefix of it**
(rebase F-c-4). The loop reads `k` numbers into an array of `W ≥ k`
cells, so the fill's physical length is `W` while the counter stops at
`k`; the last two conjuncts are the difference. `τ.vars "i" ≤ k` is
what `Fill.Below.le` used to give for free and no longer does, since
`Below` now bounds the counter by `W`. The tail clause is the one the
flip is for: the `W - k` cells above the block hold zero, and the loop's
`k` stores — every one of them at an index below the counter, hence
below `k` — leave them alone. -/
def ReadInv (a lim : String) (k W : ℕ) (ys rest : List ℕ) (τ : Env) : Prop :=
  τ.vars lim = k ∧ τ.inp = ys.drop (τ.vars "i") ++ rest ∧
    Fill.Below a "i" W (fun i => ys.getD i 0) τ ∧ τ.vars "i" ≤ k ∧
    ∀ j, k ≤ j → j < W → (τ.arrs a).getD j 0 = 0

/-- **Reading a block of the tape into a wider array.** The array has
`W` cells with the `W - k` above the block zeroed; what comes back is
that every cell of the block holds the number the tape had at that
position, that the zeroed tail is still zeroed, and what is left of the
tape.

`readLoop_spec` is the case `W = k`, where the tail is empty and both
extra clauses are vacuous. -/
theorem readLoop_specW {B : ℕ} {a lim : String} (hi : lim ≠ "i") (ht : lim ≠ "t")
    {k W : ℕ} {ys rest : List ℕ} (hys : ys.length = k) (hkB : k < B) (hkW : k ≤ W)
    (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => (σ.arrs a).length = W ∧ (∀ j, k ≤ j → j < W → (σ.arrs a).getD j 0 = 0) ∧
        σ.vars lim = k ∧ σ.inp = ys ++ rest)
      (RamDriver.readLoop a lim)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf W g ∧ (∀ i < k, g i = ys.getD i 0) ∧
          ∀ j, k ≤ j → j < W → g j = 0) ∧ σ'.inp = rest)
      (12 * k + 6) := by
  have hbody : Spec B (fun τ => ReadInv a lim k W ys rest τ ∧ τ.vars "i" < k)
      (.seq (.read "t") (Fill.put a "i" (.var "t")))
      (fun τ τ' => ReadInv a lim k W ys rest τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 8 := by
    rintro τ ⟨⟨hl, hinp, hbel, -, htail⟩, hlt⟩
    have hylen : τ.vars "i" < ys.length := by omega
    have hhead : τ.inp = ys.getD (τ.vars "i") 0 :: (ys.drop (τ.vars "i" + 1) ++ rest) := by
      rw [hinp, List.drop_eq_getElem_cons hylen, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hylen]; rfl
    have hvB : ys.getD (τ.vars "i") 0 < B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hylen]
      exact hyB _ (List.getElem_mem hylen)
    -- the read
    obtain ⟨τ₁, hτ₁⟩ : ∃ τ' : Env, τ' = { τ.setVar "t" (ys.getD (τ.vars "i") 0) with
      inp := ys.drop (τ.vars "i" + 1) ++ rest } := ⟨_, rfl⟩
    have r₁ : Run B (.read "t") τ τ₁ 1 := hτ₁ ▸ Run.read hhead
    have hv₁ : τ₁.vars "i" = τ.vars "i" := by rw [hτ₁]; simp
    have ha₁ : τ₁.arrs = τ.arrs := by rw [hτ₁]; simp
    have ht₁ : τ₁.vars "t" = ys.getD (τ.vars "i") 0 := by rw [hτ₁]; simp
    have hbel₁ : Fill.Below a "i" W (fun i => ys.getD i 0) τ₁ := hbel.of_eq (by rw [ha₁]) hv₁
    -- the store and the bump
    have hlen₁ : τ₁.vars "i" < (τ₁.arrs a).length := by
      rw [hbel₁.length, hv₁]; omega
    obtain ⟨τ₂, hτ₂⟩ : ∃ τ' : Env, τ' = τ₁.setArr a (τ₁.vars "i") (τ₁.vars "t") := ⟨_, rfl⟩
    have r₂ : Run B (.store a (.var "i") (.var "t")) τ₁ τ₂ 3 :=
      hτ₂ ▸ (Run.store (evalB_var (by rw [hv₁]; omega)) (evalB_var (by rw [ht₁]; exact hvB))
        hlen₁).mono (by simp)
    have r₃ : Run B (.assign "i" (.add (.var "i") (.lit 1))) τ₂ (τ₂.setVar "i" (τ₁.vars "i" + 1))
        4 :=
      (Run.assign (v := τ₁.vars "i" + 1)
        (by
          have hvi : τ₂.vars "i" = τ.vars "i" := by
            rw [hτ₂]; simp only [vars_setArr]; exact hv₁
          rw [evalB_bin (evalB_var (σ := τ₂) (x := "i") (by rw [hvi]; omega))
            (evalB_lit (by omega)) (by simp only [Bop.apply_add]; rw [hvi]; omega)]
          simp only [Bop.apply_add]
          rw [hvi, hv₁])).mono (by simp)
    refine ⟨τ₂.setVar "i" (τ₁.vars "i" + 1), (r₁.seq (r₂.seq r₃)).mono (by norm_num),
      ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [hτ₂]; simp [hv₁]⟩
    · rw [hτ₂, hτ₁]; simp [hi, ht, hl]
    · rw [show (τ₂.setVar "i" (τ₁.vars "i" + 1)).vars "i" = τ₁.vars "i" + 1 by simp]
      rw [hv₁]
      simp only [inp_setVar]
      rw [hτ₂]
      simp only [inp_setArr]
      rw [hτ₁]
    · rw [hτ₂]
      exact Fill.Below.step (v := τ₁.vars "t") hbel₁ (by rw [hv₁]; omega)
        (by rw [ht₁, hv₁])
    · rw [show (τ₂.setVar "i" (τ₁.vars "i" + 1)).vars "i" = τ₁.vars "i" + 1 by simp, hv₁]
      omega
    -- the tail: the store is at the counter, which is below `k`, so no
    -- padding slot is the cell it writes
    · intro j hjk hjW
      rw [arrs_setVar, hτ₂, arrs_setArr, if_pos rfl, ha₁,
        List.getD_eq_getElem?_getD, List.getElem?_set_ne (by rw [hv₁]; omega),
        ← List.getD_eq_getElem?_getD]
      exact htail j hjk hjW
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨harr, htail, hlim, hinp⟩ := hσ
  obtain ⟨g, hg⟩ := exists_arrOf harr
  obtain ⟨σ', hrun, ⟨-, hinp', hbel, -, htail'⟩, hik⟩ :=
    (Spec.forRangeZero "i" lim (ReadInv a lim k W ys rest) k 8 hkB
      (fun _ h => h.2.2.2.1) (fun _ h => h.1) hbody).run (σ := σ)
      ⟨by simp [hi, hlim], by simp [hinp],
        Fill.below_zero (g := g) (by simp [hg]) (by simp), by simp, by simpa using htail⟩
  obtain ⟨g', hfill⟩ := hbel
  refine ⟨σ', _, hrun, by omega, ⟨g', hfill.arr, fun i hi' => hfill.cell (by omega), ?_⟩, by
    rw [hik] at hinp'; rw [hinp', List.drop_eq_nil_of_le (by omega)]; rfl⟩
  intro j hjk hjW
  rw [← hfill.getD hjW]
  exact htail' j hjk hjW

/-- **Reading a block of the tape into an array of its own length.** The
case `W = k` of `readLoop_specW`, where the padding is empty. -/
theorem readLoop_spec {B : ℕ} {a lim : String} (hi : lim ≠ "i") (ht : lim ≠ "t")
    {k : ℕ} {ys rest : List ℕ} (hys : ys.length = k) (hkB : k < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => (σ.arrs a).length = k ∧ σ.vars lim = k ∧ σ.inp = ys ++ rest)
      (RamDriver.readLoop a lim)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf k g ∧ ∀ i < k, g i = ys.getD i 0) ∧ σ'.inp = rest)
      (12 * k + 6) :=
  ((readLoop_specW (W := k) hi ht hys hkB le_rfl hyB).pre
      (fun _ hσ => ⟨hσ.1, fun _ h₁ h₂ => absurd h₁ (by omega), hσ.2.1, hσ.2.2⟩)).post
    (fun _ _ _ hq => ⟨⟨hq.1.choose, hq.1.choose_spec.1, hq.1.choose_spec.2.1⟩, hq.2⟩)

/-! ### The two flat passes the driver writes itself

`RamDriver.copyCom` and `RamDriver.fillCom` are the kit's array pass at
two cell expressions. The fill is `Fill.loop_spec` and nothing else; the
copy needs an invariant of its own, since the cell it writes is read out
of another array and `Fill.loop_spec` holds nothing about that array
across the loop. -/

/-- The invariant of a copy: the carrier and the source frozen, the
destination the kit's fill at the source's cell function. -/
def CopyInv (src dst : String) (n : ℕ) (F : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs src = arrOf n F ∧ Fill.Below dst "i" n F σ

/-- **Copying one array of the carrier's length into another**: the
whole of the driver's calling convention. -/
theorem copy_spec {B n : ℕ} {src dst : String} (hsd : src ≠ dst) (F : ℕ → ℕ)
    (hnB : n < B) (hF : ∀ i < n, F i < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs src = arrOf n F ∧ (σ.arrs dst).length = n)
      (RamDriver.copyCom src dst)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs src = arrOf n F ∧ σ'.arrs dst = arrOf n F)
      (12 * n + 6) := by
  have hbody : Spec B (fun σ => CopyInv src dst n F σ ∧ σ.vars "i" < n)
      (Fill.put dst "i" (.get src (.var "i")))
      (fun σ σ' => CopyInv src dst n F σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 8 := by
    have hput := (Fill.put_spec B n dst "i" (.get src (.var "i")) F
      (fun σ => CopyInv src dst n F σ ∧ σ.vars "i" < n)
      (fun _ hσ => ⟨hσ.1.2.2, hσ.2⟩) hnB
      (fun σ hσ => evalB_get (evalB_var (by omega)) (by rw [hσ.1.2.1]; exact getElem?_arrOf F hσ.2)
        (hF _ hσ.2))).frame
    exact hput.post fun σ σ' hσ hq =>
      ⟨⟨by rw [hq.2.1 "n" (by simp), hσ.1.1],
        by rw [hq.2.2.1 src (by simp [hsd]), hσ.1.2.1], hq.1.1⟩, hq.1.2⟩
  refine ((Spec.forRangeZero "i" "n" (CopyInv src dst n F) n 8 hnB
    (fun _ h => h.2.2.le) (fun _ h => h.1) hbody).pre ?_).post ?_ |>.mono (by omega)
  · rintro σ ⟨hn, hsrc, hdst⟩
    obtain ⟨g, hg⟩ := exists_arrOf hdst
    exact ⟨by simp [hn], by simp [hsrc], Fill.below_zero (g := g) (by simp [hg]) (by simp)⟩
  · rintro σ σ' - ⟨⟨hn, hsrc, hbel⟩, hik⟩
    obtain ⟨g, hg, hgF⟩ := hbel.done hik
    exact ⟨hn, hsrc, by rw [hg]; exact arrOf_congr hgF⟩

/-- **Filling an array of the carrier's length with a constant.** -/
theorem fill_spec {B n c : ℕ} {a : String} (hnB : n < B) (hcB : c < B) :
    Spec B (fun σ => (σ.arrs a).length = n ∧ σ.vars "n" = n)
      (RamDriver.fillCom a (.lit c))
      (fun _ σ' => ∃ g, σ'.arrs a = arrOf n g ∧ ∀ j < n, g j = c)
      ((10 + 1) * n + 6) :=
  ((Fill.loop_spec B n a "i" "n" (.lit c) (fun _ => c) (by decide) hnB
    (fun _ _ _ _ => evalB_lit hcB)).pre
      (fun _ hσ => ⟨exists_arrOf hσ.1, hσ.2⟩)).post (fun _ _ _ hq => hq.1)

/-! The frames of the three passes, read off their syntax. -/

theorem wvars_readLoop (a lim : String) : (RamDriver.readLoop a lim).wvars = ["i", "t", "i"] := by
  simp [RamDriver.readLoop, Com.wvars]

theorem warrs_readLoop (a lim : String) : (RamDriver.readLoop a lim).warrs = [a] := by
  simp [RamDriver.readLoop, Com.warrs]

theorem noWrite_readLoop (a lim : String) : (RamDriver.readLoop a lim).NoWrite := by
  simp [RamDriver.readLoop, Com.NoWrite]

theorem wvars_fillCom (a : String) (e : Expr) : (RamDriver.fillCom a e).wvars = ["i", "i"] := by
  simp [RamDriver.fillCom, RamDriver.fillUpto, Fill.put, Com.wvars]

theorem warrs_fillCom (a : String) (e : Expr) : (RamDriver.fillCom a e).warrs = [a] := by
  simp [RamDriver.fillCom, RamDriver.fillUpto, Fill.put, Com.warrs]

theorem noWrite_fillCom (a : String) (e : Expr) : (RamDriver.fillCom a e).NoWrite := by
  simp [RamDriver.fillCom, RamDriver.fillUpto, Fill.put, Com.NoWrite]

/-- A copy is a fill whose cell expression reads the source. -/
theorem copyCom_eq (src dst : String) :
    RamDriver.copyCom src dst = RamDriver.fillCom dst (.get src (.var "i")) := rfl

/-- The root's flag names are none of a copy's scalars. -/
theorem rootFlg_notMem_copy_wvars (src dst : String) (k : ℕ) :
    RamDriver.rootFlgName k ∉ (RamDriver.copyCom src dst).wvars := by
  refine notMem_of_append (p := "rf") (s := toString k) ?_
  rw [copyCom_eq, wvars_fillCom]
  decide

/-! ### The decode

`RamDriver.decodeCom` reads the two counts and the two arrays of the
encoding off the tape and opens the root arena with everything alive.
This is `Lax11Proofs.CC`'s reading phase, at the driver's names. -/

/-- What the decode costs: the two reads, the two counter assignments,
the two read loops and the two fills. -/
def decodeCost (n ns : ℕ) : ℕ := 12 * (n + 1) + 12 * ns + 22 * n + 34

/-- **The decode obligation, discharged.** This is
`RamDriver.DecodeImplements B x G ns O T K` in its repaired form: the
memory clause and the three value bounds are conjuncts and hypotheses
of the obligation itself, so the theorem closes it as it stands.

The block structure the two loops leave is the encoding's own, by
`RamBfs.csrGraph_of_encodesGraph`, and the arena the two fills open has
every vertex alive.

**The target array is wider than the encoding** (rebase F-c-4). The
level below reads `tgt` at the allocation width `Ws`, so the decode is
handed `Ws` cells with the `Ws - ns` above the encoding zeroed and has
to hand them back that way: `readLoop_specW` is the read loop at a
prefix of a wider array, and its tail clause is the whole of the extra
obligation. `hpad0` says what `T` is up there, which only the caller can
say — the walk's contribution is that the loop does not write there. -/
theorem decodeImplements {B n ns Ws K : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < ns, T j = target x j)
    (hK : decodeCost n ns ≤ K) :
    RamDriver.DecodeImplements B x G ns Ws O T K := by
  intro hxB hnB hnsB hWsB hnsW hpad0
  subst hns
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hoffL, htgtL, htgtZ, halvL, hgamL⟩,
    ⟨hOle, hOsz, hz₁, hz₂, hz₃, hz₄, hz₅, hz₆, hz₇, hz₈, hw₁, hw₂⟩,
    hinp, hout⟩ := hσ
  -- the word: the two header entries, the offsets, the targets
  have hlen := hx.length_eq
  obtain ⟨rest, hxr⟩ : ∃ rest, x = n :: edgeCount x :: rest := by
    rcases x with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · exact absurd hlen (by simp; omega)
    · exact absurd hlen (by simp; omega)
    · have hp : p = n := by
        have h := hx.vertexCount_eq
        rwa [vertexCount_eq, List.getD_cons_zero] at h
      have hq : edgeCount (p :: q :: rest) = q := by
        rw [edgeCount_eq, List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨rest, by rw [hq, hp]⟩
  have hxlen : x.length = rest.length + 2 := by rw [hxr]; simp
  have hrest : rest.length = 1 + n + 2 * edgeCount x := by omega
  have hmemx : ∀ v ∈ rest, v < B := fun v hv =>
    hxB v (by rw [hxr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
  have hecB : edgeCount x < B :=
    hxB _ (by rw [hxr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨ys, zs, hys, hzs, hsplit, hyd, hzd⟩ :
      ∃ ys zs, ys.length = n + 1 ∧ zs.length = 2 * edgeCount x ∧ rest = ys ++ zs ∧
        (∀ i < n + 1, ys.getD i 0 = offset x i) ∧
        (∀ j < 2 * edgeCount x, zs.getD j 0 = target x j) := by
    refine ⟨rest.take (n + 1), rest.drop (n + 1), by simp; omega, by simp; omega,
      (List.take_append_drop _ _).symm, fun i hi => ?_, fun j _ => ?_⟩
    · rw [getD_take hi, offset_eq, hxr, getD_cons_cons]
    · rw [getD_drop, target_eq, hx.vertexCount_eq, hxr,
        show 3 + n + j = 2 + (n + 1 + j) by omega, getD_cons_cons]
  have hysB : ∀ v ∈ ys, v < B :=
    fun v hv => hmemx v (by rw [hsplit]; exact List.mem_append_left _ hv)
  have hzsB : ∀ v ∈ zs, v < B :=
    fun v hv => hmemx v (by rw [hsplit]; exact List.mem_append_right _ hv)
  -- the two counts
  obtain ⟨σ₁, hσ₁⟩ : ∃ τ : Env, τ = { σ.setVar "n" n with inp := edgeCount x :: rest } := ⟨_, rfl⟩
  have r₁ : Run B (.read "n") σ σ₁ 1 := hσ₁ ▸ Run.read (by rw [hinp]; exact hxr)
  obtain ⟨σ₂, hσ₂⟩ : ∃ τ : Env, τ = { σ₁.setVar "m" (edgeCount x) with inp := rest } := ⟨_, rfl⟩
  have r₂ : Run B (.read "m") σ₁ σ₂ 1 := hσ₂ ▸ Run.read (by simp [hσ₁])
  have hn₂ : σ₂.vars "n" = n := by simp [hσ₂, hσ₁]
  have hm₂ : σ₂.vars "m" = edgeCount x := by simp [hσ₂]
  have ha₂ : σ₂.arrs = σ.arrs := by simp [hσ₂, hσ₁]
  have hi₂ : σ₂.inp = rest := by simp [hσ₂]
  have ho₂ : σ₂.out = [] := by simp [hσ₂, hσ₁, hout]
  -- the offsets
  obtain ⟨σ₃, hσ₃⟩ : ∃ τ : Env, τ = σ₂.setVar "len" (n + 1) := ⟨_, rfl⟩
  have r₃ : Run B (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    hσ₃ ▸ (Run.assign (v := n + 1) (by
      rw [evalB_bin (evalB_var (by rw [hn₂]; omega)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; rw [hn₂]; omega)]
      simp only [Bop.apply_add]; rw [hn₂])).mono (by norm_num)
  obtain ⟨σ₄, r₄, ⟨O', hoff₄, hO₄⟩, hinp₄⟩ :=
    (readLoop_spec (a := "off") (lim := "len") (ys := ys) (rest := zs) (by decide) (by decide)
      hys (by omega) hysB).run (σ := σ₃)
      ⟨by simpa [hσ₃, ha₂] using hoffL, by simp [hσ₃],
        by simp [hσ₃, hi₂, hsplit]⟩
  have hfv₄ : ∀ y, y ≠ "i" → y ≠ "t" → σ₄.vars y = σ₃.vars y := fun y h1 h2 =>
    r₄.frame_var y (by rw [wvars_readLoop]; simp [h1, h2])
  have hfa₄ : ∀ a, a ≠ "off" → σ₄.arrs a = σ₃.arrs a := fun a ha =>
    r₄.frame_arr a (by rw [warrs_readLoop]; simpa using ha)
  have hn₄ : σ₄.vars "n" = n := by
    rw [hfv₄ "n" (by decide) (by decide), hσ₃]; simpa using hn₂
  have hm₄ : σ₄.vars "m" = edgeCount x := by
    rw [hfv₄ "m" (by decide) (by decide), hσ₃]; simpa using hm₂
  have ho₄ : σ₄.out = [] := by
    rw [r₄.out_eq (noWrite_readLoop ..), hσ₃]; simpa using ho₂
  -- the targets
  obtain ⟨σ₅, hσ₅⟩ : ∃ τ : Env, τ = σ₄.setVar "len" (2 * edgeCount x) := ⟨_, rfl⟩
  have r₅ : Run B (.assign "len" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    hσ₅ ▸ (Run.assign (v := 2 * edgeCount x) (by
      rw [evalB_bin (evalB_var (by rw [hm₄]; omega)) (evalB_var (by rw [hm₄]; omega))
        (by simp only [Bop.apply_add]; rw [hm₄]; omega)]
      simp only [Bop.apply_add]
      rw [hm₄, show edgeCount x + edgeCount x = 2 * edgeCount x by omega])).mono (by norm_num)
  obtain ⟨σ₆, r₆, ⟨T', htgt₆, hT₆, hT₆pad⟩, -⟩ :=
    (readLoop_specW (a := "tgt") (lim := "len") (ys := zs) (rest := []) (by decide) (by decide)
      hzs hnsB hnsW hzsB).run (σ := σ₅)
      ⟨by simpa [hσ₅, hfa₄ "tgt" (by decide), hσ₃, ha₂] using htgtL,
        by
          intro j hj₁ hj₂
          rw [show σ₅.arrs "tgt" = σ.arrs "tgt" by
            rw [hσ₅]; simp only [arrs_setVar]; rw [hfa₄ "tgt" (by decide), hσ₃]
            simp only [arrs_setVar]; rw [ha₂]]
          exact htgtZ j hj₁ hj₂,
        by simp [hσ₅], by simpa [hσ₅] using hinp₄⟩
  have hfv₆ : ∀ y, y ≠ "i" → y ≠ "t" → σ₆.vars y = σ₅.vars y := fun y h1 h2 =>
    r₆.frame_var y (by rw [wvars_readLoop]; simp [h1, h2])
  have hfa₆ : ∀ a, a ≠ "tgt" → σ₆.arrs a = σ₅.arrs a := fun a ha =>
    r₆.frame_arr a (by rw [warrs_readLoop]; simpa using ha)
  have hn₆ : σ₆.vars "n" = n := by
    rw [hfv₆ "n" (by decide) (by decide), hσ₅]; simpa using hn₄
  have ho₆ : σ₆.out = [] := by rw [r₆.out_eq (noWrite_readLoop ..), hσ₅]; simpa using ho₄
  -- the two masks
  have hall : ∀ a, a ≠ "off" → a ≠ "tgt" → σ₆.arrs a = σ.arrs a := by
    intro a h1 h2
    rw [hfa₆ a h2, hσ₅]
    simp only [arrs_setVar]
    rw [hfa₄ a h1, hσ₃]
    simp only [arrs_setVar]
    rw [ha₂]
  obtain ⟨σ₇, r₇, M, halv₇, hM₇⟩ :=
    (fill_spec (B := B) (n := n) (a := RamDriver.alvName 0) (c := 1) (by omega)
      (by omega)).run (σ := σ₆)
      ⟨by rw [hall _ (by decide) (by decide)]; exact halvL, hn₆⟩
  have hfa₇ : ∀ a, a ≠ RamDriver.alvName 0 → σ₇.arrs a = σ₆.arrs a := fun a ha =>
    r₇.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have hn₇ : σ₇.vars "n" = n := by
    rw [r₇.frame_var "n" (by rw [wvars_fillCom]; decide)]; exact hn₆
  obtain ⟨σ₈, r₈, Gm, hgam₈, hGm₈⟩ :=
    (fill_spec (B := B) (n := n) (a := RamDriver.gamName 0) (c := 1) (by omega)
      (by omega)).run (σ := σ₇)
      ⟨by rw [hfa₇ _ (by decide), hall _ (by decide) (by decide)]; exact hgamL, hn₇⟩
  have hfa₈ : ∀ a, a ≠ RamDriver.gamName 0 → σ₈.arrs a = σ₇.arrs a := fun a ha =>
    r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  -- everything but the four arrays the phase writes comes back untouched
  have hall₈ : ∀ a, a ≠ "off" → a ≠ "tgt" → a ≠ RamDriver.alvName 0 →
      a ≠ RamDriver.gamName 0 → σ₈.arrs a = σ.arrs a := by
    intro a h1 h2 h3 h4
    rw [hfa₈ a h4, hfa₇ a h3, hall a h1 h2]
  have hm₈ : σ₈.vars "m" = edgeCount x := by
    rw [r₈.frame_var "m" (by rw [wvars_fillCom]; decide),
      r₇.frame_var "m" (by rw [wvars_fillCom]; decide),
      hfv₆ "m" (by decide) (by decide), hσ₅]
    simpa using hm₄
  have rall : Run B RamDriver.decodeCom σ σ₈ _ :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈))))))
  refine ⟨σ₈, _, rall, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [decodeCost] at hK; omega
  · rw [r₈.out_eq (noWrite_fillCom ..), r₇.out_eq (noWrite_fillCom ..)]; exact ho₆
  · exact csrGraph_of_encodesGraph hx hO hT
  · rw [r₈.frame_var "n" (by rw [wvars_fillCom]; decide)]; exact hn₇
  · rw [hfa₈ _ (by decide), hfa₇ _ (by decide), hfa₆ _ (by decide), hσ₅]
    simp only [arrs_setVar]
    rw [hoff₄]
    exact arrOf_congr fun i hi => by rw [hO₄ i hi, hyd i hi, hO i (by omega)]
  · rw [hfa₈ _ (by decide), hfa₇ _ (by decide), htgt₆]
    refine arrOf_congr fun j hj => ?_
    rcases lt_or_ge j (2 * edgeCount x) with hjs | hjs
    · rw [hT₆ j hjs, hzd j hjs, hT j hjs]
    · rw [hT₆pad j hjs hj, hpad0 j hjs hj]
  · rw [hm₈]; omega
  · exact ⟨hOle, hOsz.run rall,
      by rw [hall₈ "elm" (by decide) (by decide) (by decide) (by decide)]; exact hz₁,
      by rw [hall₈ "bh" (by decide) (by decide) (by decide) (by decide)]; exact hz₂,
      by rw [hall₈ "ooff" (by decide) (by decide) (by decide) (by decide)]; exact hz₃,
      by rw [hall₈ "noff" (by decide) (by decide) (by decide) (by decide)]; exact hz₄,
      by rw [hall₈ "stf" (by decide) (by decide) (by decide) (by decide)]; exact hz₅,
      by rw [hall₈ "sta" (by decide) (by decide) (by decide) (by decide)]; exact hz₆,
      by rw [hall₈ "std" (by decide) (by decide) (by decide) (by decide)]; exact hz₇,
      by rw [hall₈ "ste" (by decide) (by decide) (by decide) (by decide)]; exact hz₈,
      run_mem_arrs_lt rall "itg" hw₁, run_mem_arrs_lt rall "ntg" hw₂⟩
  · exact ⟨M, by rw [hfa₈ _ (by decide)]; exact halv₇, hM₇⟩
  · exact ⟨Gm, hgam₈, hGm₈⟩

/-! ### The arithmetic of the bits

`RamDriver.bcExpr` turns a boolean combination into an expression by
truncated subtraction and multiplication. Over values in `{0, 1}` those
are negation and conjunction, which is the one thing the readback needs
of the combination and the only induction in this file. -/

/-- **A boolean combination of bits is a bit, and it is the right
one.** -/
theorem evalB_bcExpr {B : ℕ} {α : Type*} {val : α → Expr} {P : α → Prop} {σ : Env}
    (hB : 1 < B) : ∀ b : BC α,
      (∀ a ∈ b.atoms, ∃ v, (val a).evalB B σ = some v ∧ v ≤ 1 ∧ (v = 1 ↔ P a)) →
      ∃ v, (RamDriver.bcExpr val b).evalB B σ = some v ∧ v ≤ 1 ∧ (v = 1 ↔ BC.eval P b) := by
  intro b
  induction b with
  | atom a =>
      intro h
      obtain ⟨v, hv, hle, hiff⟩ := h a (by rw [BCAlgebra.atoms_atom]; simp)
      exact ⟨v, by rw [RamDriver.bcExpr]; exact hv, hle, by rw [BCAlgebra.eval_atom]; exact hiff⟩
  | tru =>
      intro _
      exact ⟨1, by rw [RamDriver.bcExpr]; exact evalB_lit hB, le_rfl,
        by rw [BCAlgebra.eval_tru]; simp⟩
  | not c ih =>
      intro h
      obtain ⟨v, hv, hle, hiff⟩ := ih (by rw [BCAlgebra.atoms_not] at h; exact h)
      refine ⟨1 - v, ?_, by omega, ?_⟩
      · rw [RamDriver.bcExpr,
          evalB_bin (evalB_lit hB) hv (by simp only [Bop.apply_sub]; omega)]
        simp only [Bop.apply_sub]
      · rw [BCAlgebra.eval_not]
        constructor
        · intro h1 hev
          have : v = 1 := hiff.mpr hev
          omega
        · intro hnev
          have : v ≠ 1 := fun hc => hnev (hiff.mp hc)
          omega
  | and c d ihc ihd =>
      intro h
      obtain ⟨v₁, hv₁, hle₁, hiff₁⟩ :=
        ihc (fun a ha => h a (by rw [BCAlgebra.atoms_and]; exact List.mem_append_left _ ha))
      obtain ⟨v₂, hv₂, hle₂, hiff₂⟩ :=
        ihd (fun a ha => h a (by rw [BCAlgebra.atoms_and]; exact List.mem_append_right _ ha))
      have hmul : v₁ * v₂ ≤ 1 := by
        rcases (by omega : v₁ = 0 ∨ v₁ = 1) with rfl | rfl <;>
          rcases (by omega : v₂ = 0 ∨ v₂ = 1) with rfl | rfl <;> simp
      refine ⟨v₁ * v₂, ?_, hmul, ?_⟩
      · rw [RamDriver.bcExpr, evalB_bin hv₁ hv₂ (by simp only [Bop.apply_mul]; omega)]
        simp only [Bop.apply_mul]
      · rw [BCAlgebra.eval_and, ← hiff₁, ← hiff₂]
        rcases (by omega : v₁ = 0 ∨ v₁ = 1) with rfl | rfl <;>
          rcases (by omega : v₂ = 0 ∨ v₂ = 1) with rfl | rfl <;> simp

/-! ### The sentence readback

One `RamScatter.scatter_spec` per scatter atom of the top sentence, each
at the depth-zero table row of the atom's own formula, and then the
boolean combination of the flags and the construction-time constants,
written to the output tape. -/

section Sentence

open Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables

variable {q_top cap mb n ns Ws B : ℕ} {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
  {O T M : ℕ → ℕ} {C : ℕ → ℕ → ℕ}

/-- The value of one scatter atom of the top sentence in the root
arena: the greedy scatter value of the atom's own formula, which is what
`RamScatter.scatterCom` decides. -/
def AtomValue {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (L : ℕ) (C : ℕ → ℕ → ℕ)
    (s : ScatterSentence L) : Prop :=
  s.t ≤ (greedySet (masked G M) s.r
    {a | Sat (masked G M) (RamDriver.colRead n C L) (fun _ => a) s.β}).ncard

/-- **The memory clause of the sentence readback.** The five scratch
arrays of the scatter pass at the carrier's length — two of them holding
words, as `RamScatter.Words` asks — and the depth-zero table arrays
holding words, since the calling convention's copy reads their cells and
a cell at or above the bound makes the read stuck. It is not a conjunct
of `RamDriver.SentenceImplements`: `rootMem_of_levelPre` below derives
all of it from `RamDriver.LevelPre`'s own `RamDriver.LevelMem` and
`RamDriver.TableInv`'s bit clause. -/
def RootMem (q_top cap mb B n : ℕ) (φ : Lax3.FirstOrder.FO 0) (σ : Env) : Prop :=
  (σ.arrs "alv").length = n ∧ (σ.arrs "tab").length = n ∧
    (σ.arrs "dist").length = n ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
    (σ.arrs "q").length = n ∧ (∀ v ∈ σ.arrs "q", v < B) ∧
    (σ.arrs "exc").length = n ∧
    ∀ i < (tablesAt q_top cap mb φ 0).length, ∀ v ∈ σ.arrs (RamDriver.tabName 0 i), v < B

/-- **The memory clause survives any run that does not write a table.**
The lengths survive because a store never changes one, the two word
clauses because a bounded run stores only words — neither is a frame
condition, which is why the scatter pass may be called twice. -/
theorem rootMem_run {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hm : RootMem q_top cap mb B n φ σ) (htab : ∀ i, RamDriver.tabName 0 i ∉ c.warrs) :
    RootMem q_top cap mb B n φ σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hm
  exact ⟨(run_length_arrs h "alv").trans h1, (run_length_arrs h "tab").trans h2,
    (run_length_arrs h "dist").trans h3, run_mem_arrs_lt h "dist" h4,
    (run_length_arrs h "q").trans h5, run_mem_arrs_lt h "q" h6,
    (run_length_arrs h "exc").trans h7,
    fun i hi => by rw [h.frame_arr _ (htab i)]; exact h8 i hi⟩

/-- **The memory clause is a level's own state.** Everything `RootMem`
asks for beyond the tables is `RamDriver.LevelMem`, which
`RamDriver.LevelPre` carries; and that the tables hold words is
`RamDriver.TableInv`'s bit clause together with `1 < B`. So the
sentence obligation needs no memory conjunct of its own. -/
theorem rootMem_of_levelPre {Gm : ℕ → ℕ} {σ : Env} (h1B : 1 < B)
    (hlev : RamDriver.LevelPre B n cap mb ns Ws O T 0 M Gm C σ)
    (htab : RamDriver.TableInv q_top cap mb φ G 0 M C σ) :
    RootMem q_top cap mb B n φ σ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨hsz, hd, hq⟩, -, -, -⟩ := hlev
  refine ⟨hsz.length (p := ("alv", n)) (by simp), hsz.length (p := ("tab", n)) (by simp),
    hsz.length (p := ("dist", n)) (by simp), hd,
    hsz.length (p := ("q", n)) (by simp), hq,
    hsz.length (p := ("exc", n)) (by simp), fun i hi v hv => ?_⟩
  obtain ⟨Tb, hTb, hTb1, -⟩ := htab i hi
  rw [hTb] at hv
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
  exact lt_of_le_of_lt (hTb1 z (List.mem_range.1 hz)) h1B

/-- What the root readback reads and does not write: the block
structure, the root mask, the depth-zero tables, and the memory
clause. This is `RamDriver.LevelPre` at depth zero together with
`RamDriver.TableInv`, with the colour arrays dropped — the palette at
depth zero is empty — and `RootMem` added. -/
def RootPre (q_top cap mb ns B : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs (RamDriver.alvName 0) = arrOf n M ∧
    RamDriver.TableInv q_top cap mb φ G 0 M C σ ∧ RootMem q_top cap mb B n φ σ

/-! **The readback reads `tgt` at the allocation width** (rebase F-c-4).
`RootPre`'s slot-count parameter is instantiated at `W` and not at `ns`
by every caller below, because that is what `RamDriver.LevelPre` now
holds; the scatter pass enters through `RamScatter.scatter_specW`, whose
`nt` is a caller's choice above the block structure's own `ns`, so
nothing here is re-walked and `RootPre` itself does not move. -/

open Classical in
/-- One atom of the top sentence: the two copies the calling convention
asks for, the scatter pass, and the flag. -/
noncomputable def atomCom (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : ℕ)
    (s : ScatterSentence (sigL cap mb 0)) : Com :=
  .seq (RamDriver.copyCom (RamDriver.alvName 0) "alv")
    (.seq (RamDriver.copyCom
        (RamDriver.tabName 0 (RamDriver.posOf s.β (tablesAt q_top cap mb φ 0))) "tab")
      (.seq (RamScatter.scatterCom s.r s.t)
        (.assign (RamDriver.rootFlgName k) (.var "flag"))))

open Classical in
/-- The root scatter pass is the fold of `atomCom` over the top
sentence's scatter atoms. -/
theorem rootScatterCom_eq (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    RamDriver.rootScatterCom q_top cap mb φ =
      RamDriver.foldIdx (fun k s => atomCom q_top cap mb φ k s) 0
        (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2 := rfl

/-- What one atom costs: the two copies, the scatter pass, the flag. -/
def atomCost (n ns t : ℕ) : ℕ := 12 * n + 6 + (12 * n + 6) + (RamScatter.scatterCost n ns t + 2)

open Classical in
/-- **One scatter atom of the top sentence.** The mask and the atom's
own depth-zero table row are copied into the names the scatter pass
addresses, the pass runs, and its answer is kept in the atom's flag.
Everything the readback reads is given back, and every other flag is
where it was. -/
theorem atom_spec (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ Ws)
    (hMB : ∀ z < n, M z < B) (h1B : 1 < B) (k : ℕ) {s : ScatterSentence (sigL cap mb 0)}
    (hs : s.β ∈ tablesAt q_top cap mb φ 0) (hrB : s.r + 1 < B) (htB : s.t < B) {Kb : ℕ}
    (hKb : atomCost n ns s.t ≤ Kb) :
    Spec B (RootPre q_top cap mb Ws B φ G O T M C) (atomCom q_top cap mb φ k s)
      (fun σ σ' => RootPre q_top cap mb Ws B φ G O T M C σ' ∧ σ'.out = σ.out ∧
        (∀ j, j ≠ k → σ'.vars (RamDriver.rootFlgName j) = σ.vars (RamDriver.rootFlgName j)) ∧
        σ'.vars (RamDriver.rootFlgName k) ≤ 1 ∧
        (σ'.vars (RamDriver.rootFlgName k) = 1 ↔ AtomValue G M (sigL cap mb 0) C s)) Kb := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hoff, htgt, halv0, htabInv, hmem⟩ := hσ
  obtain ⟨hp, hpβ⟩ := RamDriver.getElem_posOf hs
  obtain ⟨Tb, hTbArr, -, hTbSat⟩ := htabInv _ hp
  have hTbB : ∀ z < n, Tb z < B := by
    intro z hz
    refine hmem.2.2.2.2.2.2.2 _ hp (Tb z) ?_
    rw [hTbArr]
    exact List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩
  -- the copies address fixed names, and no table array is one of them
  have htabAlv : ∀ i, RamDriver.tabName 0 i ∉
      (RamDriver.copyCom (RamDriver.alvName 0) "alv").warrs := fun i => by
    rw [copyCom_eq, warrs_fillCom]
    exact fun hm => tabName_zero_ne i "alv" (by decide) (by simpa using hm)
  have htabTab : ∀ (a : String) (i : ℕ), RamDriver.tabName 0 i ∉
      (RamDriver.copyCom a "tab").warrs := fun a i => by
    rw [copyCom_eq, warrs_fillCom]
    exact fun hm => tabName_zero_ne i "tab" (by decide) (by simpa using hm)
  -- the mask, into the name the pass reads
  obtain ⟨σ₁, r₁, hn₁, halv0₁, halv₁⟩ :=
    (copy_spec (B := B) (n := n) (src := RamDriver.alvName 0) (dst := "alv") (by decide) M
      hnB hMB).run (σ := σ) ⟨hn, halv0, hmem.1⟩
  have ha₁ : ∀ a, a ≠ "alv" → σ₁.arrs a = σ.arrs a := fun a ha =>
    r₁.frame_arr a (by rw [copyCom_eq, warrs_fillCom]; simpa using ha)
  have hmem₁ : RootMem q_top cap mb B n φ σ₁ := rootMem_run r₁ hmem htabAlv
  have htabInv₁ : RamDriver.TableInv q_top cap mb φ G 0 M C σ₁ := fun i hi => by
    obtain ⟨Tc, hc, hc1, hcs⟩ := htabInv i hi
    exact ⟨Tc, by rw [ha₁ _ (tabName_zero_ne i "alv" (by decide))]; exact hc, hc1, hcs⟩
  -- the table row, into the name the pass reads
  obtain ⟨σ₂, r₂, hn₂, htab₂, htabArr₂⟩ :=
    (copy_spec (B := B) (n := n)
      (src := RamDriver.tabName 0 (RamDriver.posOf s.β (tablesAt q_top cap mb φ 0)))
      (dst := "tab") (tabName_zero_ne _ "tab" (by decide)) Tb hnB hTbB).run (σ := σ₁)
      ⟨hn₁, by rw [ha₁ _ (tabName_zero_ne _ "alv" (by decide))]; exact hTbArr, hmem₁.2.1⟩
  have ha₂ : ∀ a, a ≠ "tab" → σ₂.arrs a = σ₁.arrs a := fun a ha =>
    r₂.frame_arr a (by rw [copyCom_eq, warrs_fillCom]; simpa using ha)
  have hmem₂ : RootMem q_top cap mb B n φ σ₂ := rootMem_run r₂ hmem₁ (htabTab _)
  have htabInv₂ : RamDriver.TableInv q_top cap mb φ G 0 M C σ₂ := fun i hi => by
    obtain ⟨Tc, hc, hc1, hcs⟩ := htabInv₁ i hi
    exact ⟨Tc, by rw [ha₂ _ (tabName_zero_ne i "tab" (by decide))]; exact hc, hc1, hcs⟩
  -- the pass
  obtain ⟨σ₃, r₃, hflag₃, hflagle₃⟩ :=
    (RamScatter.scatter_specW (G := G) (M := M) (Tab := Tb) (O := O) (T := T) (r := s.r)
      (t := s.t)
      (X := {a | Sat (masked G M) (RamDriver.colRead n C (sigL cap mb 0)) (fun _ => a) s.β})
      hcsr hnB hnsB hnt hrB htB hMB hTbB
      (fun v => by rw [hTbSat v, hpβ]; exact Iff.rfl)).run (σ := σ₂)
      ⟨hn₂, by rw [ha₂ _ (by decide), ha₁ _ (by decide)]; exact hoff,
        by rw [ha₂ _ (by decide), ha₁ _ (by decide)]; exact htgt,
        by rw [ha₂ _ (by decide)]; exact halv₁, htabArr₂,
        words_of_length hmem₂.2.2.1 hmem₂.2.2.2.1,
        words_of_length hmem₂.2.2.2.2.1 hmem₂.2.2.2.2.2.1,
        exists_arrOf hmem₂.2.2.2.2.2.2.1⟩
  have ha₃ : ∀ a : String, a ∉ (RamScatter.scatterCom 0 0).warrs → σ₃.arrs a = σ₂.arrs a :=
    fun a ha => r₃.frame_arr a (by rw [warrs_scatterCom]; exact ha)
  have hv₃ : ∀ y : String, y ∉ (RamScatter.scatterCom 0 0).wvars → σ₃.vars y = σ₂.vars y :=
    fun y hy => r₃.frame_var y (by rw [wvars_scatterCom]; exact hy)
  have hmem₃ : RootMem q_top cap mb B n φ σ₃ :=
    rootMem_run r₃ hmem₂ (fun i => tab_notMem_scatter_warrs s.r s.t i)
  have htabInv₃ : RamDriver.TableInv q_top cap mb φ G 0 M C σ₃ := fun i hi => by
    obtain ⟨Tc, hc, hc1, hcs⟩ := htabInv₂ i hi
    refine ⟨Tc, ?_, hc1, hcs⟩
    rw [r₃.frame_arr _ (tab_notMem_scatter_warrs s.r s.t i)]; exact hc
  -- the flag
  have hflagB : σ₃.vars "flag" < B := by omega
  refine ⟨σ₃.setVar (RamDriver.rootFlgName k) (σ₃.vars "flag"), _,
    r₁.seq (r₂.seq (r₃.seq (Run.assign (v := σ₃.vars "flag") (evalB_var hflagB)))),
    by rw [atomCost] at hKb; simp only [Expr.size]; omega, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_, ?_, ?_, ?_⟩
  · rw [vars_setVar, if_neg (Ne.symm (rootFlgName_ne k "n" (by decide))),
      hv₃ "n" (by decide), hn₂]
  · rw [arrs_setVar, ha₃ "off" (by decide), ha₂ _ (by decide), ha₁ _ (by decide)]
    exact hoff
  · rw [arrs_setVar, ha₃ "tgt" (by decide), ha₂ _ (by decide), ha₁ _ (by decide)]
    exact htgt
  · rw [arrs_setVar, ha₃ (RamDriver.alvName 0) (by decide), ha₂ _ (by decide)]
    exact halv0₁
  · intro i hi
    obtain ⟨Tc, hc, hc1, hcs⟩ := htabInv₃ i hi
    exact ⟨Tc, by rw [arrs_setVar]; exact hc, hc1, hcs⟩
  · exact rootMem_run (Run.assign (v := σ₃.vars "flag") (evalB_var hflagB)) hmem₃
      (fun i => by simp [Com.warrs])
  · rw [out_setVar, r₃.out_eq (noWrite_scatterCom ..),
      r₂.out_eq (by rw [copyCom_eq]; exact noWrite_fillCom ..),
      r₁.out_eq (by rw [copyCom_eq]; exact noWrite_fillCom ..)]
  · intro j hj
    rw [vars_setVar, if_neg (fun hc => hj (rootFlgName_inj hc)),
      r₃.frame_var _ (rootFlg_notMem_scatter_wvars s.r s.t j),
      r₂.frame_var _ (rootFlg_notMem_copy_wvars _ _ j),
      r₁.frame_var _ (rootFlg_notMem_copy_wvars _ _ j)]
  · rw [vars_setVar, if_pos rfl]; exact hflagle₃
  · rw [vars_setVar, if_pos rfl]; exact hflag₃

open Classical in
/-- **The root scatter phase**, over any list of atoms starting at any
index: each atom's flag holds the atom's value, and every flag the list
does not name is where it was. The induction is the list's. -/
theorem rootScatter_aux (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ Ws) (hMB : ∀ z < n, M z < B) (h1B : 1 < B) {Kb : ℕ} :
    ∀ (l : List (ScatterSentence (sigL cap mb 0))) (i₀ : ℕ),
      (∀ s ∈ l, s.β ∈ tablesAt q_top cap mb φ 0 ∧ s.r + 1 < B ∧ s.t < B ∧
        atomCost n ns s.t ≤ Kb) →
      Spec B (RootPre q_top cap mb Ws B φ G O T M C)
        (RamDriver.foldIdx (fun k s => atomCom q_top cap mb φ k s) i₀ l)
        (fun σ σ' => RootPre q_top cap mb Ws B φ G O T M C σ' ∧ σ'.out = σ.out ∧
          (∀ j, (∀ p < l.length, j ≠ i₀ + p) →
            σ'.vars (RamDriver.rootFlgName j) = σ.vars (RamDriver.rootFlgName j)) ∧
          ∀ p, ∀ hp : p < l.length,
            σ'.vars (RamDriver.rootFlgName (i₀ + p)) ≤ 1 ∧
            (σ'.vars (RamDriver.rootFlgName (i₀ + p)) = 1 ↔
              AtomValue G M (sigL cap mb 0) C l[p]))
        (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro i₀ _
      refine (Spec.skip (B := B) (P := RootPre q_top cap mb Ws B φ G O T M C)).post ?_
        |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, fun j _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro i₀ hall
      obtain ⟨hxβ, hxr, hxt, hxK⟩ := hall x (by simp)
      refine ((atom_spec hcsr hnB hnsB hnt hMB h1B i₀ hxβ hxr hxt hxK).seq
        (ih (i₀ + 1) (fun s hs => hall s (by simp [hs]))) (fun _ _ _ hq => hq.1) ?_).mono
        (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' _ ⟨-, hout', hflg', hle', hval'⟩ ⟨hpre'', hout'', hflg'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], ?_, ?_⟩
      · intro j hj
        rw [hflg'' j (fun p hp => by have := hj (p + 1) (by simp; omega); omega),
          hflg' j (by have := hj 0 (by simp); omega)]
      · intro p hp
        match p with
        | 0 =>
            rw [Nat.add_zero, hflg'' i₀ (fun q _ => by omega)]
            exact ⟨hle', hval'⟩
        | q + 1 =>
            rw [show i₀ + (q + 1) = i₀ + 1 + q from by omega]
            simpa using hval'' q (by simpa using hp)

open Classical in
/-- The expression the root writes: the boolean combination of the
construction-time constants and the flags. -/
noncomputable def sentenceExpr (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) : Expr :=
  if h : ∃ q' : ℕ, q' ≤ q_top ∧
      DRank 0 q' (Reduction.toDistFO (L := sigL cap mb 0) φ) then
    RamDriver.bcExpr (RamDriver.rootAtomExpr q_top cap mb φ)
      (bcOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ) h)
  else .lit 0

open Classical in
/-- The sentence readback is the scatter phase and one write. -/
theorem sentenceCom_eq (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    RamDriver.sentenceCom q_top cap mb φ =
      .seq (RamDriver.rootScatterCom q_top cap mb φ) (.write (sentenceExpr q_top cap mb φ)) :=
  rfl

open Classical in
/-- **The sentence readback implements its specification.** Everything
but the first conjunct of the precondition is
`RamDriver.SentenceImplements B q_top cap mb ns φ G O T M Gm C K`
verbatim; that first conjunct is the memory clause that obligation
omits.

The scatter atoms enter through `RamScatter.scatter_spec`, one call per
atom at the depth-zero table row of the atom's own formula — which
`RamDriver.TableInv` says is the set the atom speaks about — and the
write is `Spec.write` at `RamDriver.bcExpr` of the combination, whose
local atoms are the constants `Evaluator.localSentenceEval` decides at
construction time. What the bit *means* is
`RamDriver.sat_iff_eval_sentence`, and is no part of this walk. -/
theorem sentenceImplements {Kb K : ℕ} {Gm : ℕ → ℕ}
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcsr : CsrGraph G ns O T)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ atomCost n ns s.t ≤ Kb)
    (hK : Kb * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (sentenceExpr q_top cap mb φ).size) ≤ K) :
    RamDriver.SentenceImplements B q_top cap mb ns Ws φ G O T M Gm C K := by
  intro hB _
  have hnB : n < B := hB.n_lt
  have hnsB : ns < B := hB.ns_lt
  have h1B : 1 < B := hB.one_lt
  have hrk : ∃ q' : ℕ, q' ≤ q_top ∧
      DRank 0 q' (Reduction.toDistFO (L := sigL cap mb 0) φ) :=
    ⟨q_top, le_rfl, Reduction.drank_toDistFO φ hrank⟩
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htabInv, hout⟩ := hσ
  have hmem : RootMem q_top cap mb B n φ σ := rootMem_of_levelPre h1B hlev htabInv
  obtain ⟨hn, hoff, htgt, halv0, -, -, hMB, -, -, -, -, -, hordmem, -⟩ := hlev
  -- the block structure sits in the first `ns` of the level's `Ws` slots
  have hnt : ns ≤ Ws := hordmem.1
  -- the scatter atoms
  obtain ⟨σ₁, r₁, -, hout₁, -, hval₁⟩ :=
    (rootScatter_aux (Kb := Kb) hcsr hnB hnsB hnt hMB h1B
      (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2 0
      (fun s hs => ⟨by
        rw [tablesAt_zero]; exact List.mem_map.mpr ⟨s, hs, rfl⟩,
        (hatoms s hs).1, (hatoms s hs).2.1, (hatoms s hs).2.2⟩)).run
      (σ := σ) ⟨hn, hoff, htgt, halv0, htabInv, hmem⟩
  -- the atoms of the combination are bits, and the right ones
  have hbits : ∀ a ∈ (bcOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ) hrk).atoms,
      ∃ v, ((RamDriver.rootAtomExpr q_top cap mb φ) a).evalB B σ₁ = some v ∧ v ≤ 1 ∧
        (v = 1 ↔ Sum.elim Evaluator.localSentenceEval
          (AtomValue G M (sigL cap mb 0) C) a) := by
    rintro (γ | s) hmemA
    · by_cases hγ : Evaluator.localSentenceEval γ
      · exact ⟨1, by rw [RamDriver.rootAtomExpr, if_pos hγ]; exact evalB_lit h1B, le_rfl,
          by simpa using hγ⟩
      · exact ⟨0, by rw [RamDriver.rootAtomExpr, if_neg hγ]; exact evalB_lit (by omega),
          by omega, by simpa using hγ⟩
    · have hs : s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2 :=
        (mem_bcAtomsOf₀_right hrk).mpr hmemA
      obtain ⟨hpos, hposβ⟩ := RamDriver.getElem_posOf hs
      obtain ⟨hle, hiff⟩ := hval₁ _ hpos
      rw [Nat.zero_add] at hle hiff
      refine ⟨σ₁.vars (RamDriver.rootFlgName
        (RamDriver.posOf s (bcAtomsOf₀ q_top
          (Reduction.toDistFO (L := sigL cap mb 0) φ)).2)), ?_, hle, ?_⟩
      · rw [RamDriver.rootAtomExpr]; exact evalB_var (by omega)
      · rw [hiff, hposβ]; exact Iff.rfl
  obtain ⟨v, hv, hvle, hviff⟩ := evalB_bcExpr (val := RamDriver.rootAtomExpr q_top cap mb φ)
    (P := Sum.elim Evaluator.localSentenceEval (AtomValue G M (sigL cap mb 0) C))
    h1B (bcOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ) hrk) hbits
  have hvE : (sentenceExpr q_top cap mb φ).evalB B σ₁ = some v := by
    rw [sentenceExpr, dif_pos hrk]; exact hv
  -- the write
  refine ⟨{ σ₁ with out := σ₁.out ++ [v] }, _,
    by rw [sentenceCom_eq, rootScatterCom_eq]; exact r₁.seq (Run.write hvE), by omega, hrk, ?_⟩
  have hveq : v = if (bcOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ) hrk).eval
      (Sum.elim Evaluator.localSentenceEval (AtomValue G M (sigL cap mb 0) C)) then 1 else 0 := by
    by_cases hev : (bcOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ) hrk).eval
        (Sum.elim Evaluator.localSentenceEval (AtomValue G M (sigL cap mb 0) C))
    · rw [if_pos hev]; exact hviff.mpr hev
    · rw [if_neg hev]
      have : v ≠ 1 := fun hc => hev (hviff.mp hc)
      omega
  rw [hout₁, hout, hveq]
  rfl

end Sentence

end Lax3Proofs.RamDriverIO
