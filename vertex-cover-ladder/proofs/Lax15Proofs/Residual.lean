import Lax11Proofs.VCSpec
import Mathlib.Data.Sym.Sym2.Order

/-!
The graph side of the pure model: what the search sees at a node.

A node of the search is a marking `M` — the vertices already committed
to the cover — and everything the algorithm decides there it decides
from the *residual* graph, the part of `G` no mark touches yet: the
residual neighbourhood `ResNbhd M v` of a vertex, its size `resDeg M v`,
and the set `ResEdges M` of edges with both endpoints unmarked.

Three facts drive the search, and they are the three ways a node can be
disposed of. If the residual edges are no more numerous than the budget,
picking one endpoint of each of them extends the marking to a cover, so
the answer is yes; that is the early exit, and it is sound in every
graph, not just at leaves. If no unmarked vertex has two residual edges
on it — the residual graph is a matching — then a cover must spend one
vertex per residual edge, so a budget below their number is hopeless.
Between the two lies the branch: a vertex of residual degree at least
two is either in the cover, at one unit of budget, or out of it, and
then its whole residual neighbourhood is in, at `resDeg` units. The
budget spent on the second branch is what turns 2^k into `fib (k+2)`.

The search predicate `Ok` and the facts it lives on come from
`Lax11Proofs.VCSpec` unchanged: this file adds the residual layer on
top of them and nothing else. Decidability is classical throughout —
these are definitions of a specification, never of a program.

The last section transports the residual quantities to the compressed
sparse row encoding, where the machine meets them as counts over the
slots of the target array, and the transport is not an identity. An
encoding may list a neighbour of a vertex several times, so a count of
slots overshoots the number of residual edges, and a block with two
unmarked slots need not be a block with two unmarked *neighbours*. Two
counts are therefore given: the plain slot count `ResSlots`, which is
never below the number of residual edges, and the count `ResOwners`
capped at one slot per block, which is never above it and meets it on a
matching. The branching test comes in the only form faithful to the
residual degree — two slots of one block whose unmarked targets
differ.
-/

namespace Lax15Proofs.VC

open Lax11Proofs.VC Lax11.GraphEncoding Lax11Proofs.CC

variable {n : ℕ} {G : SimpleGraph (Fin n)} {M : Finset (Fin n)} {b : ℕ}

/-! ### The residual graph -/

open Classical in
/-- The residual neighbourhood of `v`: its neighbours that the marking
`M` has not taken. -/
noncomputable def ResNbhd (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  {w ∈ Finset.univ | G.Adj v w ∧ w ∉ M}

/-- The residual degree of `v`: how many of its edges are still
uncovered by the marking. -/
noncomputable def resDeg (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (v : Fin n) : ℕ :=
  (ResNbhd G M v).card

open Classical in
/-- The residual edges: the edges of `G` neither endpoint of which is
marked. These are exactly the edges the marking still has to pay for. -/
noncomputable def ResEdges (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  {e ∈ Finset.univ | e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∉ M}

@[simp] theorem mem_resNbhd {v w : Fin n} :
    w ∈ ResNbhd G M v ↔ G.Adj v w ∧ w ∉ M := by
  classical
  simp [ResNbhd]

theorem resDeg_eq_card (v : Fin n) : resDeg G M v = (ResNbhd G M v).card := rfl

@[simp] theorem mem_resEdges {u v : Fin n} :
    s(u, v) ∈ ResEdges G M ↔ G.Adj u v ∧ u ∉ M ∧ v ∉ M := by
  classical
  simp only [ResEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_edgeSet, Sym2.ball]

/-- A residual neighbour is unmarked: the residual neighbourhood and the
marking are disjoint. -/
theorem resNbhd_disjoint (v : Fin n) : Disjoint (ResNbhd G M v) M :=
  Finset.disjoint_left.2 fun _ hw => (mem_resNbhd.1 hw).2

theorem resNbhd_inter_eq_empty (v : Fin n) : ResNbhd G M v ∩ M = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.1 (resNbhd_disjoint v)

/-- Marking more vertices can only shrink a residual neighbourhood. -/
theorem resNbhd_subset_of_subset {M M' : Finset (Fin n)} (h : M ⊆ M') (v : Fin n) :
    ResNbhd G M' v ⊆ ResNbhd G M v := fun _ hw => by
  obtain ⟨hadj, hw'⟩ := mem_resNbhd.1 hw
  exact mem_resNbhd.2 ⟨hadj, fun hm => hw' (h hm)⟩

theorem resDeg_le_of_subset {M M' : Finset (Fin n)} (h : M ⊆ M') (v : Fin n) :
    resDeg G M' v ≤ resDeg G M v :=
  Finset.card_le_card (resNbhd_subset_of_subset h v)

/-- Marking more vertices can only shrink the residual edges. -/
theorem resEdges_subset_of_subset {M M' : Finset (Fin n)} (h : M ⊆ M') :
    ResEdges G M' ⊆ ResEdges G M := by
  intro e he
  induction e with | _ u v =>
  obtain ⟨hadj, hu, hv⟩ := mem_resEdges.1 he
  exact mem_resEdges.2 ⟨hadj, fun hm => hu (h hm), fun hm => hv (h hm)⟩

/-! ### The early exit -/

/-- The smaller of the two endpoints of an edge is one of them. -/
theorem inf_mem (e : Sym2 (Fin n)) : e.inf ∈ e := by
  induction e with | _ u v =>
  rcases le_total u v with h | h
  · simp [Sym2.inf_mk, min_eq_left h]
  · simp [Sym2.inf_mk, min_eq_right h]

/-- **The early exit**: as soon as the residual edges are no more
numerous than the budget, the marking extends to a cover — pick one
endpoint of each residual edge. Every other edge already meets the
marking, so nothing else has to be bought. This is sound at every node
of the search, not only at leaves. -/
theorem ok_of_card_resEdges_le (h : (ResEdges G M).card ≤ b) : Ok G M b := by
  classical
  refine ⟨M ∪ (ResEdges G M).image Sym2.inf, ?_, Finset.subset_union_left, ?_⟩
  · intro a c hac
    by_cases ha : a ∈ M
    · exact Or.inl (Finset.mem_coe.2 (Finset.mem_union_left _ ha))
    by_cases hc : c ∈ M
    · exact Or.inr (Finset.mem_coe.2 (Finset.mem_union_left _ hc))
    have he : s(a, c) ∈ ResEdges G M := mem_resEdges.2 ⟨hac, ha, hc⟩
    have hin : (s(a, c) : Sym2 (Fin n)).inf ∈ M ∪ (ResEdges G M).image Sym2.inf :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    rcases Sym2.mem_iff.1 (inf_mem (s(a, c) : Sym2 (Fin n))) with h1 | h1
    · exact Or.inl (Finset.mem_coe.2 (by rw [← h1]; exact hin))
    · exact Or.inr (Finset.mem_coe.2 (by rw [← h1]; exact hin))
  · have hsub : (M ∪ (ResEdges G M).image Sym2.inf) \ M ⊆ (ResEdges G M).image Sym2.inf := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union] at hx
      tauto
    calc ((M ∪ (ResEdges G M).image Sym2.inf) \ M).card
        ≤ ((ResEdges G M).image Sym2.inf).card := Finset.card_le_card hsub
      _ ≤ (ResEdges G M).card := Finset.card_image_le
      _ ≤ b := h

/-! ### The matching leaf -/

/-- **The matching lower bound**: if no unmarked vertex has two residual
edges on it, the residual graph is a matching, and a cover has to spend
a vertex on each of its edges — so a budget below their number is
hopeless. The map sending a residual edge to the endpoint that covers it
is injective precisely because two residual edges through one vertex
would give it residual degree two. -/
theorem not_ok_of_lt_card_resEdges (hdeg : ∀ v, v ∉ M → resDeg G M v ≤ 1)
    (hb : b < (ResEdges G M).card) : ¬ Ok G M b := by
  classical
  rintro ⟨S, hS, hMS, hcard⟩
  have hex : ∀ e ∈ ResEdges G M, ∃ x, x ∈ e ∧ x ∈ S ∧ x ∉ M := by
    intro e he
    induction e with | _ a c =>
    obtain ⟨hac, ha, hc⟩ := mem_resEdges.1 he
    rcases hS hac with h | h
    · exact ⟨a, Sym2.mem_mk_left _ _, by simpa using h, ha⟩
    · exact ⟨c, Sym2.mem_mk_right _ _, by simpa using h, hc⟩
  set f : Sym2 (Fin n) → Fin n :=
    fun e => if h : ∃ x, x ∈ e ∧ x ∈ S ∧ x ∉ M then h.choose else e.inf with hf
  have hfspec : ∀ e ∈ ResEdges G M, f e ∈ e ∧ f e ∈ S ∧ f e ∉ M := by
    intro e he
    have h := hex e he
    simp only [hf, dif_pos h]
    exact h.choose_spec
  have hmaps : ∀ e ∈ ResEdges G M, f e ∈ S \ M := fun e he =>
    Finset.mem_sdiff.2 ⟨(hfspec e he).2.1, (hfspec e he).2.2⟩
  have hinj : Set.InjOn f (ResEdges G M) := by
    intro e₁ h₁ e₂ h₂ heq
    obtain ⟨hm₁, -, hnM⟩ := hfspec e₁ (Finset.mem_coe.1 h₁)
    obtain ⟨hm₂, -, -⟩ := hfspec e₂ (Finset.mem_coe.1 h₂)
    rw [← heq] at hm₂
    obtain ⟨y₁, hy₁⟩ := Sym2.mem_iff_exists.1 hm₁
    obtain ⟨y₂, hy₂⟩ := Sym2.mem_iff_exists.1 hm₂
    have hres : ∀ y : Fin n, s(f e₁, y) ∈ ResEdges G M → y ∈ ResNbhd G M (f e₁) := by
      intro y hy
      obtain ⟨hadj, -, hyM⟩ := mem_resEdges.1 hy
      exact mem_resNbhd.2 ⟨hadj, hyM⟩
    have h1 : y₁ ∈ ResNbhd G M (f e₁) := hres y₁ (hy₁ ▸ Finset.mem_coe.1 h₁)
    have h2 : y₂ ∈ ResNbhd G M (f e₁) := hres y₂ (hy₂ ▸ Finset.mem_coe.1 h₂)
    have : y₁ = y₂ :=
      Finset.card_le_one.1 (by simpa [resDeg_eq_card] using hdeg _ hnM) y₁ h1 y₂ h2
    rw [hy₁, hy₂, this]
  have := Finset.card_le_card_of_injOn f hmaps hinj
  omega

/-! ### The branch -/

/-- Giving back a whole marked set costs its size in budget. The
one-vertex case is `Ok.insert_out` of the imported model. -/
theorem ok_of_ok_union {N : Finset (Fin n)} (h : Ok G (M ∪ N) b) :
    Ok G M (b + N.card) := by
  classical
  obtain ⟨S, hS, hsub, hcard⟩ := h
  refine ⟨S, hS, Finset.subset_union_left.trans hsub, ?_⟩
  have hsub2 : S \ M ⊆ (S \ (M ∪ N)) ∪ N := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hxN : x ∈ N
    · exact Finset.mem_union_right _ hxN
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.2 ⟨hx.1, by simp [Finset.mem_union, hx.2, hxN]⟩)
  calc (S \ M).card ≤ ((S \ (M ∪ N)) ∪ N).card := Finset.card_le_card hsub2
    _ ≤ (S \ (M ∪ N)).card + N.card := Finset.card_union_le _ _
    _ ≤ b + N.card := by omega

/-- **The branch on a vertex**: either `v` joins the cover, at one unit
of budget, or it does not, and then its whole residual neighbourhood
does, at `resDeg M v` units — which is at least two whenever the
algorithm branches, and that is where the Fibonacci recurrence comes
from. The equivalence itself needs no lower bound on the residual
degree; only the potential does. -/
theorem ok_branch_resNbhd {v : Fin n} (hv : v ∉ M) (hb : 1 ≤ b) :
    Ok G M b ↔ Ok G (insert v M) (b - 1) ∨
      (resDeg G M v ≤ b ∧ Ok G (M ∪ ResNbhd G M v) (b - resDeg G M v)) := by
  classical
  constructor
  · rintro ⟨S, hS, hMS, hcard⟩
    by_cases hvS : v ∈ S
    · refine Or.inl ⟨S, hS, Finset.insert_subset hvS hMS, ?_⟩
      have hmem : v ∈ S \ M := Finset.mem_sdiff.2 ⟨hvS, hv⟩
      have hpos : 0 < (S \ M).card := Finset.card_pos.2 ⟨v, hmem⟩
      have hdiff : S \ insert v M = (S \ M).erase v := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rw [hdiff, Finset.card_erase_of_mem hmem]
      omega
    · have hNS : ResNbhd G M v ⊆ S := by
        intro w hw
        obtain ⟨hadj, -⟩ := mem_resNbhd.1 hw
        rcases hS hadj with h | h
        · exact absurd (by simpa using h) hvS
        · simpa using h
      have hNSM : ResNbhd G M v ⊆ S \ M := fun w hw =>
        Finset.mem_sdiff.2 ⟨hNS hw, (mem_resNbhd.1 hw).2⟩
      have hdcard : resDeg G M v ≤ (S \ M).card := Finset.card_le_card hNSM
      refine Or.inr ⟨by omega, S, hS, Finset.union_subset hMS hNS, ?_⟩
      have hdiff : S \ (M ∪ ResNbhd G M v) = (S \ M) \ ResNbhd G M v := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
      rw [hdiff, Finset.card_sdiff_of_subset hNSM, ← resDeg_eq_card]
      omega
  · rintro (h | ⟨hd, h⟩)
    · exact h.insert_out.mono (by omega)
    · have h' := ok_of_ok_union h
      rw [← resDeg_eq_card] at h'
      exact h'.mono (by omega)

/-! ### Transport to the encoding -/

/-- The marking as the machine holds it: the vertex numbers whose mark
is set. -/
def markedVals (M : Finset (Fin n)) : Finset ℕ := M.map Fin.valEmbedding

@[simp] theorem mem_markedVals {v : Fin n} : (v : ℕ) ∈ markedVals M ↔ v ∈ M := by
  simp [markedVals, Fin.valEmbedding]

theorem mem_markedVals_iff {t : ℕ} (h : t < n) :
    t ∈ markedVals M ↔ (⟨t, h⟩ : Fin n) ∈ M := by
  constructor
  · intro hm
    obtain ⟨a, ha, hat⟩ := Finset.mem_map.1 hm
    have : (⟨t, h⟩ : Fin n) = a := Fin.ext hat.symm
    rw [this]
    exact ha
  · intro hm
    exact Finset.mem_map.2 ⟨⟨t, h⟩, hm, rfl⟩

variable {g : List ℕ} {J : ℕ}

open Classical in
/-- The residual slots below `J`: positions of the target array inside
the block of an unmarked owner, whose target is unmarked and larger than
the owner. This is the count the descend scan accumulates — one turn of
the loop per slot, the owner advancing alongside — with the comparison
against the owner keeping each residual edge to its smaller endpoint. -/
noncomputable def ResSlots (g : List ℕ) (M : Finset (Fin n)) (J : ℕ) :
    Finset (Fin n × ℕ) :=
  {p ∈ Finset.univ ×ˢ Finset.range J |
    p.1 ∉ M ∧ offset g (p.1 : ℕ) ≤ p.2 ∧ p.2 < offset g ((p.1 : ℕ) + 1) ∧
      (p.1 : ℕ) < target g p.2 ∧ target g p.2 ∉ markedVals M}

theorem mem_resSlots {p : Fin n × ℕ} :
    p ∈ ResSlots g M J ↔ p.2 < J ∧ p.1 ∉ M ∧ offset g (p.1 : ℕ) ≤ p.2 ∧
      p.2 < offset g ((p.1 : ℕ) + 1) ∧ (p.1 : ℕ) < target g p.2 ∧
      target g p.2 ∉ markedVals M := by
  classical
  simp only [ResSlots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and]

/-- A residual neighbour is named by a slot of the block, and that slot
has an unmarked target. -/
theorem exists_slot_of_mem_resNbhd (hg : EncodesGraph g n G) {v w : Fin n}
    (hw : w ∈ ResNbhd G M v) :
    ∃ j, offset g (v : ℕ) ≤ j ∧ j < offset g ((v : ℕ) + 1) ∧ target g j = (w : ℕ) ∧
      target g j ∉ markedVals M := by
  obtain ⟨hadj, hwM⟩ := mem_resNbhd.1 hw
  obtain ⟨j, h1, h2, h3⟩ := slot_of_adjn hg
    (show Adjn G (v : ℕ) (w : ℕ) from ⟨v.2, w.2, by simpa using hadj⟩)
  exact ⟨j, h1, h2, h3, by rw [h3]; simpa using hwM⟩

/-- Every residual edge occupies at least one residual slot: the block
of its smaller endpoint names its larger one. -/
theorem exists_resSlot (hg : EncodesGraph g n G) {u v : Fin n} (huv : G.Adj u v)
    (hu : u ∉ M) (hv : v ∉ M) (hlt : (u : ℕ) < v) :
    ∃ j, ((u, j) : Fin n × ℕ) ∈ ResSlots g M (2 * edgeCount g) ∧
      target g j = (v : ℕ) := by
  obtain ⟨j, h1, h2, h3, h4⟩ :=
    exists_slot_of_mem_resNbhd hg (mem_resNbhd.2 ⟨huv, hv⟩ : v ∈ ResNbhd G M u)
  have hjlt : j < 2 * edgeCount g :=
    lt_of_lt_of_le h2 (offset_le hg (show (u : ℕ) + 1 ≤ n from u.2))
  exact ⟨j, mem_resSlots.2 ⟨hjlt, hu, h1, h2, by rw [h3]; exact hlt, h4⟩, h3⟩

/-- **The residual edges are no more numerous than the residual slots**:
each of them owns a slot in the block of its smaller endpoint, and the
slot names the edge back. The inequality is one-sided on purpose — a
block may list a neighbour repeatedly, so the scan's count can exceed
the number of residual edges. -/
theorem card_resEdges_le_card_resSlots (hg : EncodesGraph g n G) :
    (ResEdges G M).card ≤ (ResSlots g M (2 * edgeCount g)).card := by
  classical
  have hex : ∀ e ∈ ResEdges G M, ∃ p : Fin n × ℕ,
      p ∈ ResSlots g M (2 * edgeCount g) ∧ (p.1 : ℕ) = (e.inf : ℕ) ∧
        target g p.2 = (e.sup : ℕ) := by
    intro e he
    induction e with | _ a c =>
    obtain ⟨hac, ha, hc⟩ := mem_resEdges.1 he
    have hne : a ≠ c := hac.ne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨j, hj, htj⟩ := exists_resSlot hg hac ha hc h
      exact ⟨(a, j), hj, by simp [Sym2.inf_mk, min_eq_left h.le],
        by simp [htj, Sym2.sup_mk, max_eq_right h.le]⟩
    · obtain ⟨j, hj, htj⟩ := exists_resSlot hg hac.symm hc ha h
      exact ⟨(c, j), hj, by simp [Sym2.inf_mk, min_eq_right h.le],
        by simp [htj, Sym2.sup_mk, max_eq_left h.le]⟩
  set F : Sym2 (Fin n) → Fin n × ℕ := fun e =>
    if h : ∃ p : Fin n × ℕ, p ∈ ResSlots g M (2 * edgeCount g) ∧
        (p.1 : ℕ) = (e.inf : ℕ) ∧ target g p.2 = (e.sup : ℕ)
      then h.choose else (e.inf, 0) with hF
  have hFspec : ∀ e ∈ ResEdges G M, F e ∈ ResSlots g M (2 * edgeCount g) ∧
      ((F e).1 : ℕ) = (e.inf : ℕ) ∧ target g (F e).2 = (e.sup : ℕ) := by
    intro e he
    have h := hex e he
    simp only [hF, dif_pos h]
    exact h.choose_spec
  refine Finset.card_le_card_of_injOn F (fun e he => (hFspec e he).1) ?_
  intro e₁ h₁ e₂ h₂ heq
  obtain ⟨-, hi₁, hs₁⟩ := hFspec e₁ (Finset.mem_coe.1 h₁)
  obtain ⟨-, hi₂, hs₂⟩ := hFspec e₂ (Finset.mem_coe.1 h₂)
  rw [heq] at hi₁ hs₁
  refine Sym2.inf_eq_inf_and_sup_eq_sup.1 ⟨Fin.ext ?_, Fin.ext ?_⟩
  · rw [← hi₁, hi₂]
  · rw [← hs₁, hs₂]

/-- The residual blocks are thin: the unmarked slots in the block of an
unmarked vertex all name the same vertex. This is what the descend scan
certifies when it fails to find a vertex to branch on — note that it is
*targets* that have to agree, not slots: a block may name a neighbour
twice. -/
def ThinBlocks (g : List ℕ) (M : Finset (Fin n)) : Prop :=
  ∀ o : Fin n, o ∉ M → ∀ j₁ j₂, offset g (o : ℕ) ≤ j₁ → j₁ < offset g ((o : ℕ) + 1) →
    offset g (o : ℕ) ≤ j₂ → j₂ < offset g ((o : ℕ) + 1) →
    target g j₁ ∉ markedVals M → target g j₂ ∉ markedVals M →
    target g j₁ = target g j₂

/-- The slots themselves are thin: an unmarked vertex has at most one
slot with an unmarked target in its block. Stronger than `ThinBlocks`,
and false on encodings that repeat a neighbour — it is what an exact
slot count needs. -/
def ThinSlots (g : List ℕ) (M : Finset (Fin n)) : Prop :=
  ∀ o : Fin n, o ∉ M → ∀ j₁ j₂, offset g (o : ℕ) ≤ j₁ → j₁ < offset g ((o : ℕ) + 1) →
    offset g (o : ℕ) ≤ j₂ → j₂ < offset g ((o : ℕ) + 1) →
    target g j₁ ∉ markedVals M → target g j₂ ∉ markedVals M → j₁ = j₂

theorem ThinBlocks.of_thinSlots (h : ThinSlots g M) : ThinBlocks g M :=
  fun o ho j₁ j₂ a b c d e f => by rw [h o ho j₁ j₂ a b c d e f]

/-- **Thin blocks are a matching**, and conversely: an unmarked vertex
with two residual neighbours is exactly an unmarked vertex whose block
names two different unmarked vertices. This is the hypothesis of the
matching lower bound, read off the scan's flag. -/
theorem thinBlocks_iff (hg : EncodesGraph g n G) :
    ThinBlocks g M ↔ ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 1 := by
  constructor
  · intro hthin v hv
    rw [resDeg_eq_card, Finset.card_le_one]
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨j₁, h₁, h₂, h₃, h₄⟩ := exists_slot_of_mem_resNbhd hg hw₁
    obtain ⟨j₂, i₁, i₂, i₃, i₄⟩ := exists_slot_of_mem_resNbhd hg hw₂
    exact Fin.ext (by rw [← h₃, ← i₃, hthin v hv j₁ j₂ h₁ h₂ i₁ i₂ h₄ i₄])
  · intro hdeg o ho j₁ j₂ h₁ h₂ i₁ i₂ hu₁ hu₂
    have key : ∀ j, offset g (o : ℕ) ≤ j → (hj : j < offset g ((o : ℕ) + 1)) →
        target g j ∉ markedVals M →
        (⟨target g j, target_lt' hg o.2 hj⟩ : Fin n) ∈ ResNbhd G M o := by
      intro j hj₁ hj₂ hj₃
      obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg o.2 hj₁ hj₂
      refine mem_resNbhd.2 ⟨?_, fun hm => hj₃ ((mem_markedVals_iff _).2 hm)⟩
      have : (⟨target g j, hb⟩ : Fin n) = ⟨target g j, target_lt' hg o.2 hj₂⟩ := rfl
      rw [← this]
      simpa using hadj
    have h := Finset.card_le_one.1 (by simpa [resDeg_eq_card] using hdeg o ho)
      _ (key j₁ h₁ h₂ hu₁) _ (key j₂ i₁ i₂ hu₂)
    exact congrArg Fin.val h

/-- Thin blocks are a matching. -/
theorem resDeg_le_one_of_thinBlocks (hg : EncodesGraph g n G)
    (hthin : ThinBlocks g M) : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 1 :=
  (thinBlocks_iff hg).1 hthin

/-- **The residual slots are no more numerous than the residual edges**,
once the blocks are thin: the edge a slot names determines the slot,
because its smaller endpoint has only the one unmarked slot. Together
with the opposite inequality this pins the scan's count to the number of
residual edges exactly at the leaf where the count decides the answer. -/
theorem card_resSlots_le_card_resEdges (hg : EncodesGraph g n G)
    (hthin : ThinSlots g M) : (ResSlots g M J).card ≤ (ResEdges G M).card := by
  classical
  set F : Fin n × ℕ → Sym2 (Fin n) := fun p =>
    if h : ∃ y : Fin n, (y : ℕ) = target g p.2 then s(p.1, h.choose)
      else s(p.1, p.1) with hF
  have hFval : ∀ p ∈ ResSlots g M J, ∃ y : Fin n,
      (y : ℕ) = target g p.2 ∧ F p = s(p.1, y) := by
    intro p hp
    obtain ⟨-, -, -, hlt, -, -⟩ := mem_resSlots.1 hp
    have hy : ∃ y : Fin n, (y : ℕ) = target g p.2 :=
      ⟨⟨target g p.2, target_lt' hg p.1.2 hlt⟩, rfl⟩
    exact ⟨hy.choose, hy.choose_spec, by simp only [hF, dif_pos hy]⟩
  have hmaps : ∀ p ∈ ResSlots g M J, F p ∈ ResEdges G M := by
    intro p hp
    obtain ⟨-, ho, h1, h2, h3, h4⟩ := mem_resSlots.1 hp
    obtain ⟨y, hyv, hFp⟩ := hFval p hp
    have hadj : G.Adj p.1 y := by
      obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg p.1.2 h1 h2
      have hy : (⟨target g p.2, hb⟩ : Fin n) = y := Fin.ext hyv.symm
      rw [hy] at hadj
      simpa using hadj
    rw [hFp]
    exact mem_resEdges.2 ⟨hadj, ho, by rw [← mem_markedVals, hyv]; exact h4⟩
  refine Finset.card_le_card_of_injOn F hmaps ?_
  intro p₁ hp₁ p₂ hp₂ heq
  obtain ⟨-, ho₁, ha₁, hb₁, hlt₁, hu₁⟩ := mem_resSlots.1 (Finset.mem_coe.1 hp₁)
  obtain ⟨-, ho₂, ha₂, hb₂, hlt₂, hu₂⟩ := mem_resSlots.1 (Finset.mem_coe.1 hp₂)
  obtain ⟨y₁, hy₁, hF₁⟩ := hFval p₁ (Finset.mem_coe.1 hp₁)
  obtain ⟨y₂, hy₂, hF₂⟩ := hFval p₂ (Finset.mem_coe.1 hp₂)
  rw [hF₁, hF₂, Sym2.eq_iff] at heq
  have hsame : p₁.1 = p₂.1 ∧ y₁ = y₂ := by
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exfalso
      have e₁ : (p₁.1 : ℕ) < (y₁ : ℕ) := by rw [hy₁]; exact hlt₁
      have e₂ : (p₂.1 : ℕ) < (y₂ : ℕ) := by rw [hy₂]; exact hlt₂
      rw [h1, h2] at e₁
      omega
  obtain ⟨ho, hy⟩ := hsame
  have htgt : target g p₁.2 = target g p₂.2 := by rw [← hy₁, ← hy₂, hy]
  refine Prod.ext ho ?_
  refine hthin p₁.1 ho₁ p₁.2 p₂.2 ha₁ hb₁ ?_ ?_ hu₁ hu₂
  · rw [ho]; exact ha₂
  · rw [ho]; exact hb₂

/-! ### The count capped at one slot per block -/

open Classical in
/-- The residual owners below `J`: the unmarked vertices whose block
names, below `J`, an unmarked vertex larger than themselves. This is the
same count as `ResSlots` capped at one slot per block — what a scan that
counts a block's *first* unmarked slot accumulates — and unlike the slot
count it never exceeds the number of residual edges. -/
noncomputable def ResOwners (g : List ℕ) (M : Finset (Fin n)) (J : ℕ) : Finset (Fin n) :=
  {o ∈ Finset.univ | o ∉ M ∧ ∃ j, j < J ∧ offset g (o : ℕ) ≤ j ∧
    j < offset g ((o : ℕ) + 1) ∧ (o : ℕ) < target g j ∧ target g j ∉ markedVals M}

theorem mem_resOwners {o : Fin n} :
    o ∈ ResOwners g M J ↔ o ∉ M ∧ ∃ j, j < J ∧ offset g (o : ℕ) ≤ j ∧
      j < offset g ((o : ℕ) + 1) ∧ (o : ℕ) < target g j ∧
      target g j ∉ markedVals M := by
  classical
  simp only [ResOwners, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An owner of a residual slot is an owner of a residual slot. -/
theorem mem_resOwners_of_mem_resSlots {p : Fin n × ℕ} (hp : p ∈ ResSlots g M J) :
    p.1 ∈ ResOwners g M J := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := mem_resSlots.1 hp
  exact mem_resOwners.2 ⟨h₁, p.2, h₀, h₂, h₃, h₄, h₅⟩

/-- The smaller endpoint of a residual edge is unmarked and has the
larger one as a residual neighbour. -/
theorem inf_notMem_and_sup_mem_resNbhd {e : Sym2 (Fin n)} (he : e ∈ ResEdges G M) :
    e.inf ∉ M ∧ e.sup ∈ ResNbhd G M e.inf ∧ (e.inf : ℕ) < (e.sup : ℕ) := by
  induction e with | _ a c =>
  obtain ⟨hac, ha, hc⟩ := mem_resEdges.1 he
  rcases lt_or_gt_of_ne hac.ne with h | h
  · refine ⟨by simpa [Sym2.inf_mk, min_eq_left h.le] using ha, ?_, ?_⟩
    · simp only [Sym2.inf_mk, Sym2.sup_mk, min_eq_left h.le, max_eq_right h.le]
      exact mem_resNbhd.2 ⟨hac, hc⟩
    · simpa [Sym2.inf_mk, Sym2.sup_mk, min_eq_left h.le, max_eq_right h.le] using h
  · refine ⟨by simpa [Sym2.inf_mk, min_eq_right h.le] using hc, ?_, ?_⟩
    · simp only [Sym2.inf_mk, Sym2.sup_mk, min_eq_right h.le, max_eq_left h.le]
      exact mem_resNbhd.2 ⟨hac.symm, ha⟩
    · simpa [Sym2.inf_mk, Sym2.sup_mk, min_eq_right h.le, max_eq_left h.le] using h

/-- **The residual owners are no more numerous than the residual
edges**: each of them owns one, and the edge names it back as its
smaller endpoint. This inequality needs no thinness — it is the capped
count's whole point. -/
theorem card_resOwners_le_card_resEdges (hg : EncodesGraph g n G) :
    (ResOwners g M J).card ≤ (ResEdges G M).card := by
  classical
  have hex : ∀ o ∈ ResOwners g M J, ∃ y : Fin n,
      s(o, y) ∈ ResEdges G M ∧ (o : ℕ) < (y : ℕ) := by
    intro o ho
    obtain ⟨ho', j, -, h₁, h₂, h₃, h₄⟩ := mem_resOwners.1 ho
    obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg o.2 h₁ h₂
    refine ⟨⟨target g j, hb⟩, mem_resEdges.2 ⟨by simpa using hadj, ho', ?_⟩, h₃⟩
    exact fun hm => h₄ ((mem_markedVals_iff hb).2 hm)
  set F : Fin n → Sym2 (Fin n) := fun o =>
    if h : ∃ y : Fin n, s(o, y) ∈ ResEdges G M ∧ (o : ℕ) < (y : ℕ)
      then s(o, h.choose) else s(o, o) with hF
  have hFspec : ∀ o ∈ ResOwners g M J, ∃ y : Fin n,
      F o = s(o, y) ∧ s(o, y) ∈ ResEdges G M ∧ (o : ℕ) < (y : ℕ) := by
    intro o ho
    have h := hex o ho
    exact ⟨h.choose, by simp only [hF, dif_pos h], h.choose_spec⟩
  refine Finset.card_le_card_of_injOn F (fun o ho => ?_) ?_
  · obtain ⟨y, hFo, hmem, -⟩ := hFspec o ho
    rw [hFo]; exact hmem
  · intro o₁ h₁ o₂ h₂ heq
    obtain ⟨y₁, hF₁, -, hlt₁⟩ := hFspec o₁ (Finset.mem_coe.1 h₁)
    obtain ⟨y₂, hF₂, -, hlt₂⟩ := hFspec o₂ (Finset.mem_coe.1 h₂)
    rw [hF₁, hF₂, Sym2.eq_iff] at heq
    rcases heq with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exfalso
      rw [h] at hlt₁
      rw [h'] at hlt₁
      omega

/-- **The residual edges are no more numerous than the residual owners**
once the blocks are thin: each edge is owned by its smaller endpoint, and
that endpoint has no other residual neighbour to be confused with. With
the previous lemma the capped count is exactly the number of residual
edges at the leaf where it decides the answer — and, unlike the slot
count, it is never an overcount anywhere. -/
theorem card_resEdges_le_card_resOwners (hg : EncodesGraph g n G)
    (hdeg : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 1) :
    (ResEdges G M).card ≤ (ResOwners g M (2 * edgeCount g)).card := by
  classical
  have hmaps : ∀ e ∈ ResEdges G M, e.inf ∈ ResOwners g M (2 * edgeCount g) := by
    intro e he
    obtain ⟨hinf, hsup, hlt⟩ := inf_notMem_and_sup_mem_resNbhd he
    obtain ⟨hadj, hsupM⟩ := mem_resNbhd.1 hsup
    obtain ⟨j, hj, -⟩ := exists_resSlot hg hadj hinf hsupM hlt
    exact mem_resOwners_of_mem_resSlots hj
  refine Finset.card_le_card_of_injOn Sym2.inf hmaps ?_
  intro e₁ h₁ e₂ h₂ heq
  obtain ⟨hinf₁, hsup₁, -⟩ := inf_notMem_and_sup_mem_resNbhd (Finset.mem_coe.1 h₁)
  obtain ⟨-, hsup₂, -⟩ := inf_notMem_and_sup_mem_resNbhd (Finset.mem_coe.1 h₂)
  rw [← heq] at hsup₂
  have hsup : e₁.sup = e₂.sup :=
    Finset.card_le_one.1 (by simpa [resDeg_eq_card] using hdeg _ hinf₁) _ hsup₁ _ hsup₂
  exact Sym2.inf_eq_inf_and_sup_eq_sup.1 ⟨heq, hsup⟩

/-- **The branching test**: the scan finds a vertex to branch on exactly
when one exists. A block may name a neighbour twice, so what the scan has
to look for is two unmarked slots with *different* targets, not two
unmarked slots: the residual degree counts neighbours, the block counts
occurrences. -/
theorem exists_two_slots_iff (hg : EncodesGraph g n G) :
    (∃ o : Fin n, o ∉ M ∧ ∃ j₁ j₂, offset g (o : ℕ) ≤ j₁ ∧ j₁ < offset g ((o : ℕ) + 1) ∧
        offset g (o : ℕ) ≤ j₂ ∧ j₂ < offset g ((o : ℕ) + 1) ∧
        target g j₁ ∉ markedVals M ∧ target g j₂ ∉ markedVals M ∧
        target g j₁ ≠ target g j₂) ↔
      ∃ v : Fin n, v ∉ M ∧ 2 ≤ resDeg G M v := by
  constructor
  · rintro ⟨o, ho, j₁, j₂, h₁, h₂, h₃, h₄, h₅, h₆, hne⟩
    refine ⟨o, ho, ?_⟩
    rw [resDeg_eq_card]
    have key : ∀ j, offset g (o : ℕ) ≤ j → (hj : j < offset g ((o : ℕ) + 1)) →
        target g j ∉ markedVals M →
        (⟨target g j, target_lt' hg o.2 hj⟩ : Fin n) ∈ ResNbhd G M o := by
      intro j hj₁ hj₂ hj₃
      obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg o.2 hj₁ hj₂
      refine mem_resNbhd.2 ⟨?_, fun hm => hj₃ ((mem_markedVals_iff _).2 hm)⟩
      have : (⟨target g j, hb⟩ : Fin n) = ⟨target g j, target_lt' hg o.2 hj₂⟩ := rfl
      rw [← this]
      simpa using hadj
    have hw₁ := key j₁ h₁ h₂ h₅
    have hw₂ := key j₂ h₃ h₄ h₆
    exact Finset.one_lt_card.2 ⟨_, hw₁, _, hw₂, fun h => hne (congrArg Fin.val h)⟩
  · rintro ⟨v, hv, hd⟩
    rw [resDeg_eq_card] at hd
    obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ :=
      Finset.one_lt_card.1 (show 1 < (ResNbhd G M v).card by omega)
    obtain ⟨j₁, h₁, h₂, h₃, h₄⟩ := exists_slot_of_mem_resNbhd hg hw₁
    obtain ⟨j₂, i₁, i₂, i₃, i₄⟩ := exists_slot_of_mem_resNbhd hg hw₂
    exact ⟨v, hv, j₁, j₂, h₁, h₂, i₁, i₂, h₄, i₄, by
      rw [h₃, i₃]; exact fun h => hne (Fin.ext h)⟩

end Lax15Proofs.VC
