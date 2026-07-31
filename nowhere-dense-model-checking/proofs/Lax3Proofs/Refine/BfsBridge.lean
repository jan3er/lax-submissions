import Lax3Proofs.RamBfs
import Lax13Proofs.Refine.Examples.BfsQSynth

/-!
The **tower search under the driver stack**: the refinement tower's
synthesized queue BFS (`Lax13Proofs.Refine.BfsQSynth.bfsQ_spec`, cost
`56·n + 40·ns + 33`), presented in the exact shape
`Lax3Proofs.RamBfs.bfs_spec` was consumed in — so the cover pass can
embed it in place of the hand-walked search and nothing above the
obligation boundary moves.

### What the two statements say, and where they differ

The tower's export and the hand-walked one decide the same thing: at
every threshold up to the cap, whether the vertex is within that
distance of the source **in the arena the mask cuts out**. Neither the
arena nor the threshold direction is taken on trust here — both are
re-derived (`masked_eq`, `wd_iff_withinDist`) and both are checked
against a negative control (§ *Refutation*).

Four differences are real, and each is a numbered bridge below.

* **P1/B-a — the arena.** The tower measures distance in
  `Bfs.masked G (BfsQ.maskOf n alv)`: an edge survives iff both ends
  have a **nonzero** entry in the mask array. `RamBfs.masked G M`
  isolates the vertices with `M v = 0`. With `alv = arrOf n M` the two
  graphs are *equal*, not merely isomorphic — `masked_eq` — and the
  distance predicates follow (`wd_iff_withinDist`). The direction of
  the mask convention is exactly the class the campaign's falsification
  gates catch, so it carries a negative control.

* **P1/B-b — the block structure.** The tower reads the CSR arrays as
  `List ℕ` through `BfsQ.Csr`; the driver stack carries them as
  functions through `RamBfs.CsrGraph`. `csr_of_csrGraph` is the
  translation. Its one non-trivial step is that the target index of an
  adjacency always lies inside the target array — `O (u+1) ≤ O n = ns`
  — without which `(arrOf ns T)[j]!` would fall through to the `default`
  and the adjacency clause would be refutable in the `←` direction.

* **P1/B-c — the pinned entry store (tower ledger P7/D-bp).** The
  synthesized program's precondition owns eighteen scalar cells: the
  four parameters (`n`, `src`, `sent = d+1`, `d`), the constant `one`,
  and thirteen junk cells pinned at zero, because assertion-level
  ownership makes them part of the footprint. `bfsSetup` writes the
  sixteen the caller does not already hold; it is straight-line code,
  sixteen literal assignments, `32` time units, and it writes no array.
  The caller still supplies `n` and `src`.

* **P1/B-d — state-global word bounds (tower ledger P7/D-bo).**
  `Ir.StateBound` is state-global where the baseline's `BigStepB`
  bounded only what the run evaluates, so the export asks that the
  **initial** entries of both scratch arrays be words. For `dist` the
  cover pass already carries that clause (`RamCover.CoverState`, for
  its own emission scan); for `q` it did not, and the clause is added —
  it is free, since `RamDriver.LevelMem` has carried
  `∀ v ∈ σ.arrs "q", v < B` all along.

### Where this file sits

`Lax13Proofs.Refine.Examples.BfsQSynth` is an *Examples* module of the
tower package; importing it from a consumer is sanctioned for the P1
gate. Relocating the export out of `Examples/` is a P5 concern and is
not done here.
-/

namespace Lax3Proofs.Refine.BfsBridge

open Lax3.ColoredGraphs
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Refine

variable {n ns d s : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}

/-! ### Reading a function array at a point

The tower indexes lists with `getElem!`; `arrOf` is the driver stack's
function array. In range the two agree, and out of range they do not —
which is why every use below carries its range condition. -/

/-- In range, the `getElem!` of a function array is the function. -/
theorem getElem!_arrOf {m i : ℕ} (f : ℕ → ℕ) (h : i < m) : (arrOf m f)[i]! = f i := by
  rw [getElem!_pos (arrOf m f) i (by simpa using h)]
  simp

/-- The entries of a function array are the values of the function, in
the membership form the tower's word hypotheses are stated in. -/
theorem mem_arrOf_lt {m B : ℕ} {f : ℕ → ℕ} (h : ∀ z < m, f z < B) :
    ∀ w ∈ arrOf m f, w < B := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  exact h k (List.mem_range.1 hk)

/-! ### P1/B-a — the arena -/

/-- **The two masked graphs are the same graph.** The tower's mask reads
`0 < alv[v]!`; the driver stack's kills `M v = 0`. On `arrOf n M` those
are each other's contrapositives, vertex by vertex. -/
theorem masked_eq (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) :
    Bfs.masked G (BfsQ.maskOf n (arrOf n M)) = RamBfs.masked G M := by
  ext u v
  rw [Bfs.masked_adj, RamBfs.masked_adj, BfsQ.maskOf_iff, BfsQ.maskOf_iff,
    getElem!_arrOf M u.isLt, getElem!_arrOf M v.isLt]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, by omega, by omega⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, by omega, by omega⟩

/-- Walks of equal graphs are the same walks. -/
private theorem exists_walk_congr {A A' : SimpleGraph (Fin n)} (h : A = A') (k : ℕ)
    (u v : Fin n) :
    (∃ w : A.Walk u v, w.length ≤ k) ↔ (∃ w : A'.Walk u v, w.length ≤ k) := by
  subst h; exact Iff.rfl

/-- **The distance predicates agree.** The tower's `Bfs.WD` and the
concepts' `WithinDist` are the same existential over walks, and by
`masked_eq` over walks of the same graph. -/
theorem wd_iff_withinDist {k : ℕ} {u v : Fin n} :
    Bfs.WD G (BfsQ.maskOf n (arrOf n M)) k u v ↔ WithinDist (RamBfs.masked G M) k u v :=
  exists_walk_congr (masked_eq G M) k u v

/-! ### P1/B-b — the block structure -/

/-- **The block structure, as the tower reads it, at a target array
materialized wider than the structure occupies** (rebase F-c-3). The
slot count `ns` is the last offset; `nt` is the physical width of the
array the caller allocated, and `ns ≤ nt` is all that relates them —
`BfsQ.Csr` was decoupled at exactly that by F-a (`tlen`), so nothing
here is a re-proof of the relation.

**The padding hypothesis is F-a's own residual, and it is not
removable.** `BfsQ.Shape`'s range clause is `∀ j < tgt.length,
tgt[j]! < n` — over the *whole* array, not the occupied prefix —
because the tower's state bound `Ir.StateBound` is state-global and
four ND-MC passes read the same clause at full width (F-a's ledger note
records this deliberately). So a widened caller owes `T j < n` at the
padding slots too, which is `hpad`. Everything the *run* addresses is
still below `ns`: `hrow` is unchanged, and the adjacency clause is
proved from `hcsr` alone.

`csr_of_csrGraph` is the case `nt = ns`, where `hpad` is vacuous. -/
theorem csr_of_csrGraphW {nt : ℕ} (hcsr : RamBfs.CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hpad : ∀ j, ns ≤ j → j < nt → T j < n) :
    BfsQ.Csr n ns G (arrOf (n + 1) O) (arrOf nt T) (arrOf n M) := by
  have hO : ∀ i < n + 1, (arrOf (n + 1) O)[i]! = O i := fun i hi => getElem!_arrOf O hi
  have hT : ∀ j < nt, (arrOf nt T)[j]! = T j := fun j hj => getElem!_arrOf T hj
  -- a slot named by an adjacency lies inside the *occupied prefix*
  have hrow : ∀ u : Fin n, O ((u : ℕ) + 1) ≤ ns := by
    intro u
    have := hcsr.mono' (show (u : ℕ) + 1 ≤ n from u.isLt) (le_refl n)
    rw [hcsr.last] at this
    exact this
  refine ⟨⟨by simp, by simp, fun i hi => ?_, ?_, fun j hj => ?_⟩, ?_, ?_, fun u v => ?_⟩
  · rw [hO i (by omega), hO (i + 1) (by omega)]
    exact hcsr.mono i hi
  · rw [hO n (by omega), hcsr.last, length_arrOf]
    exact hnt
  · rw [length_arrOf] at hj
    rw [hT j hj]
    rcases Nat.lt_or_ge j ns with h | h
    · exact hcsr.target_lt j h
    · exact hpad j h hj
  · rw [length_arrOf]; exact hnt
  · rw [hO n (by omega), hcsr.last]
  · rw [hO (u : ℕ) (by omega), hO ((u : ℕ) + 1) (by omega)]
    constructor
    · intro h
      obtain ⟨j, h₁, h₂, h₃⟩ := (hcsr.adj_iff u v).1 h
      exact ⟨j, h₁, h₂,
        by rw [hT j (lt_of_lt_of_le (lt_of_lt_of_le h₂ (hrow u)) hnt)]; exact h₃⟩
    · rintro ⟨j, h₁, h₂, h₃⟩
      refine (hcsr.adj_iff u v).2 ⟨j, h₁, h₂, ?_⟩
      rwa [hT j (lt_of_lt_of_le (lt_of_lt_of_le h₂ (hrow u)) hnt)] at h₃

/-- **The block structure, as the tower reads it.** `RamBfs.CsrGraph`'s
five clauses, restated on the lists the arrays actually hold — the
widened relation at the pinned width, where the padding is empty. -/
theorem csr_of_csrGraph (hcsr : RamBfs.CsrGraph G ns O T) :
    BfsQ.Csr n ns G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) :=
  csr_of_csrGraphW hcsr le_rfl (fun _ h₁ h₂ => absurd h₁ (by omega))

/-! ### P1/B-c — the pinned entry store -/

/-- **The caller's setup block.** The sixteen cells the synthesized
program's precondition pins and the cover pass does not already hold:
the sentinel, the cap, the constant `one`, and the thirteen junk cells,
each written with a literal. Straight-line code; it writes no array, and
neither `n` nor `src`. -/
def bfsSetup (d : ℕ) : Com :=
  .seq (.assign "sent" (.lit (d + 1)))
    (.seq (.assign "d" (.lit d))
      (.seq (.assign "one" (.lit 1))
        (.seq (.assign "i" (.lit 0))
          (.seq (.assign "head" (.lit 0))
            (.seq (.assign "a" (.lit 0))
              (.seq (.assign "tl" (.lit 0))
                (.seq (.assign "v" (.lit 0))
                  (.seq (.assign "dv" (.lit 0))
                    (.seq (.assign "dv1" (.lit 0))
                      (.seq (.assign "k0" (.lit 0))
                        (.seq (.assign "v1" (.lit 0))
                          (.seq (.assign "kend" (.lit 0))
                            (.seq (.assign "u" (.lit 0))
                              (.seq (.assign "au" (.lit 0))
                                (.assign "du" (.lit 0))))))))))))))))

/-- **The bridged search**: the setup block and the synthesized program,
embedded into IMP+. One program for every cap — the cap enters through
the cells `d` and `sent`, which the setup writes. -/
def bfsQCom (d : ℕ) : Com := .seq (bfsSetup d) (Codegen.embed BfsQSynth.bfsQSynth_impl)

/-- The bridged search's cost: the tower's own `56·n + 40·ns + 33`, plus
the sixteen literal assignments of the setup block at two units each. -/
def bfsQCost (n ns : ℕ) : ℕ := 32 + BfsQSynth.bfsQK n ns

theorem bfsSetup_wvars (d : ℕ) : (bfsSetup d).wvars =
    ["sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend",
      "u", "au", "du"] := rfl

theorem bfsSetup_warrs (d : ℕ) : (bfsSetup d).warrs = [] := rfl

/-- The setup block, walked: sixteen assignments, thirty-two units. -/
theorem bfsSetup_spec {B : ℕ} (hdB : d + 1 < B) :
    Spec B (fun _ => True) (bfsSetup d)
      (fun _ σ' => σ'.vars "sent" = d + 1 ∧ σ'.vars "d" = d ∧ σ'.vars "one" = 1 ∧
        σ'.vars "i" = 0 ∧ σ'.vars "head" = 0 ∧ σ'.vars "a" = 0 ∧ σ'.vars "tl" = 0 ∧
        σ'.vars "v" = 0 ∧ σ'.vars "dv" = 0 ∧ σ'.vars "dv1" = 0 ∧ σ'.vars "k0" = 0 ∧
        σ'.vars "v1" = 0 ∧ σ'.vars "kend" = 0 ∧ σ'.vars "u" = 0 ∧ σ'.vars "au" = 0 ∧
        σ'.vars "du" = 0)
      32 := by
  have h0 : (0 : ℕ) < B := by omega
  have h1 : (1 : ℕ) < B ∨ d + 1 = 1 := by omega
  have hone : (1 : ℕ) < B := by
    rcases h1 with h | h
    · exact h
    · omega
  have hd : d < B := by omega
  refine Spec.of_exists fun σ _ => ?_
  refine ⟨_, _,
    (Run.assign (evalB_lit hdB)).seq ((Run.assign (evalB_lit hd)).seq
      ((Run.assign (evalB_lit hone)).seq ((Run.assign (evalB_lit h0)).seq
        ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq
          ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq
            ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq
              ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq
                ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq
                  ((Run.assign (evalB_lit h0)).seq
                    (Run.assign (evalB_lit h0)))))))))))))))),
    by simp only [size_lit]; omega, ?_⟩
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-! ### The bridge lemma

`RamBfs.bfs_spec`'s statement, at `bfsQCom` and the tower's cost, with
the two word clauses of P1/B-d added to the precondition. Everything
else — the vocabulary of the pre, the shape of the post, the arena, the
threshold direction — is the baseline's, verbatim. -/

/-- **The tower's search, in the driver stack's shape, at a widened
target array** (rebase F-c-3). `bfsQCom_spec` with the `tgt` clause
stated at the allocation width `nt` rather than at the slot count `ns`;
`hnt` and `hpad` are `csr_of_csrGraphW`'s two, and nothing else moves —
the cost is still read at `ns`, since the search scans only the
occupied prefix. `bfsQCom_spec` is this at `nt = ns`. -/
theorem bfsQCom_specW {B nt : ℕ} (hcsr : RamBfs.CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) (hnt : ns ≤ nt)
    (hpad : ∀ j, ns ≤ j → j < nt → T j < n) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧
        (∀ w ∈ σ.arrs "dist", w < B) ∧ (∀ w ∈ σ.arrs "q", w < B))
      (bfsQCom d)
      (fun _ σ' => ∃ D, σ'.arrs "dist" = arrOf n D ∧
        ∀ (v : Fin n) (k : ℕ), k ≤ d →
          (D (v : ℕ) ≤ k ↔ WithinDist (RamBfs.masked G M) k ⟨s, hs⟩ v))
      (bfsQCost n ns) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hsrc, hoff, htgt, halv, ⟨gd, hdist⟩, ⟨gq, hq⟩, hdw, hqw⟩ := hσ
  -- the setup block
  obtain ⟨σ₁, hrun₁, ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅,
      e₁₆⟩, hfv, hfa, -, -⟩ := (bfsSetup_spec (d := d) hdB).frame.run (σ := σ) trivial
  have harr : ∀ a, σ₁.arrs a = σ.arrs a := fun a => hfa a (by rw [bfsSetup_warrs]; simp)
  have hn₁ : σ₁.vars "n" = n := by rw [hfv "n" (by rw [bfsSetup_wvars]; decide)]; exact hn
  have hsrc₁ : σ₁.vars "src" = s := by
    rw [hfv "src" (by rw [bfsSetup_wvars]; decide)]; exact hsrc
  -- the synthesized program
  obtain ⟨σ₂, hrun₂, D, hD, hDlen, hDspec⟩ :=
    (BfsQSynth.bfsQ_spec (n := n) (ns := ns) (d := d) (B := B) (src := s) (G := G)
      (off := arrOf (n + 1) O) (tgt := arrOf nt T) (alv := arrOf n M)
      (csr_of_csrGraphW (M := M) hcsr hnt hpad) hs ⟨hnB, hnsB, hdB⟩ (mem_arrOf_lt hMB)).run
      (σ := σ₁)
      ⟨hn₁, hsrc₁, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅, e₁₆,
        by rw [harr, hoff], by rw [harr, htgt], by rw [harr, halv],
        ⟨σ₁.arrs "dist", rfl, by rw [harr, hdist, length_arrOf],
          by rw [harr]; exact hdw⟩,
        ⟨σ₁.arrs "q", rfl, by rw [harr, hq, length_arrOf], by rw [harr]; exact hqw⟩⟩
  -- the answer, read back as a function array
  refine ⟨σ₂, _, hrun₁.seq hrun₂, by rw [bfsQCost], fun i => D[i]!, ?_, fun v k hk => ?_⟩
  · rw [hD]
    refine List.ext_getElem (by rw [length_arrOf, hDlen]) fun i h₁ h₂ => ?_
    rw [getElem_arrOf, getElem!_pos D i (by omega)]
  · exact (hDspec v k hk).trans wd_iff_withinDist

/-- **The tower's search, in the driver stack's shape.** Handed a block
structure for `G`, a mask, a source and two scratch arrays of the right
length whose entries are words, `bfsQCom d` leaves in `dist` a function
that decides, at every threshold up to the cap, the distance bound of
the arena — `G` with the mask's dead vertices isolated.

This is the widened statement at `nt = ns`, on the nose, so the pinned
export is a hypothesis instance and not a second walk. -/
theorem bfsQCom_spec {B : ℕ} (hcsr : RamBfs.CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧
        (∀ w ∈ σ.arrs "dist", w < B) ∧ (∀ w ∈ σ.arrs "q", w < B))
      (bfsQCom d)
      (fun _ σ' => ∃ D, σ'.arrs "dist" = arrOf n D ∧
        ∀ (v : Fin n) (k : ℕ), k ≤ d →
          (D (v : ℕ) ≤ k ↔ WithinDist (RamBfs.masked G M) k ⟨s, hs⟩ v))
      (bfsQCost n ns) :=
  bfsQCom_specW hcsr hs hnB hnsB hdB hMB le_rfl (fun _ h₁ h₂ => absurd h₁ (by omega))

/-- info: 'Lax3Proofs.Refine.BfsBridge.bfsQCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bfsQCom_spec

/-- info: 'Lax3Proofs.Refine.BfsBridge.bfsQCom_specW' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bfsQCom_specW

/-! ### Refutation

Two negative controls, one per direction that a bridge of this kind can
be got wrong. Both are `#guard`s: they are checks the build runs, not
prose.

The first is the mask convention (P1/B-a). `0 < alv[v]!` and `M v ≠ 0`
agree at every vertex of a mask that kills one of five; the *flipped*
reading `M v = 0` disagrees, so the check can tell a wrong direction.

The second is the range condition of the target array (P1/B-b). Inside
the array `getElem!` is the function; at the first index past its end it
falls through to `0`, so an adjacency clause that forgot
`j < O n = ns` would be satisfied by a spurious slot naming vertex `0`.

The threshold direction and the arena are checked end to end, on real
runs of the swapped program, by the worked example of
`Lax3Proofs.RamCover`: its four `#guard`ed answers are the hand
computation, and they are unchanged by the swap. -/

section Refutation

/-- Five vertices, vertex `1` killed. -/
private def ctlMask : ℕ → ℕ := fun v => if v = 1 then 0 else 1

-- the mask conventions agree, vertex by vertex …
#guard (List.range 5).all fun v =>
  decide (0 < (arrOf 5 ctlMask)[v]!) == decide (ctlMask v ≠ 0)
-- … and the flipped reading does not, so the check has teeth
#guard ! ((List.range 5).all fun v =>
  decide (0 < (arrOf 5 ctlMask)[v]!) == decide (ctlMask v = 0))

/-- Six slots, every one naming vertex `4`. -/
private def ctlTgt : ℕ → ℕ := fun _ => 4

-- in range the list read is the function …
#guard (List.range 6).all fun j => (arrOf 6 ctlTgt)[j]! == ctlTgt j
-- … and one past the end there is nothing to read, so a slot the row
-- bound did not exclude would be answered by the fall-through and not
-- by `T`
#guard (arrOf 6 ctlTgt)[6]? == none
#guard ! ((arrOf 6 ctlTgt)[6]? == some (ctlTgt 6))

end Refutation

end Lax3Proofs.Refine.BfsBridge
