import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
Shallow minors in the idiom of the ported sparsity development: graph
classes over varying finite vertex types, minor models carrying paths,
nowhere denseness by an excluded-clique bound, and the composition of
shallow minors (`ShallowReduct`).  This is the merge of the catalog
modules `Preliminaries`, `ShallowMinor`, `NowhereDense` and
`ShallowMinorComposition`.
-/

namespace Lax12Proofs.ShallowMinors

/-- A graph class is a predicate on finite simple graphs, where the vertex type
    may vary. -/
abbrev GraphClass :=
  ∀ {V : Type}, [DecidableEq V] → [Fintype V] → SimpleGraph V → Prop

/-- A depth-`d` minor model of `H` in `G`.

For each vertex of `H` we choose a branch set in `G` together with a fixed
center. Every vertex of the branch set is connected to the center by a path of
length at most `d` that stays inside the branch set; distinct branch sets are
disjoint; and every edge of `H` is witnessed by an edge of `G` between the
corresponding branch sets. (Defs 1.10, 2.2-2.4) -/
structure ShallowMinorModel {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V)
    (d : ℕ) where
  branchSet : W → Set V
  center : W → V
  center_mem : ∀ v, center v ∈ branchSet v
  branchDisjoint : ∀ u v, u ≠ v → Disjoint (branchSet u) (branchSet v)
  branchRadius : ∀ v x, x ∈ branchSet v →
    ∃ p : G.Walk (center v) x, p.IsPath ∧ p.length ≤ d ∧
      ∀ w ∈ p.support, w ∈ branchSet v
  branchEdge : ∀ u v, H.Adj u v →
    ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

/-- `H` is a depth-`d` minor of `G`. -/
def IsShallowMinor {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V)
    (d : ℕ) : Prop :=
  Nonempty (ShallowMinorModel H G d)

/-- A uniform excluded-clique bound on depth-`d` minors of graphs in `C`.
    The parameter `t` is the allowed clique size, so the excluded graph is
    `K_{t+1}`. -/
def HasShallowCliqueBound (C : GraphClass) (d t : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
    C G → ¬IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G d

/-- A class `C` of graphs is nowhere dense if for every depth `d` there is a
    bound `t` such that no graph in `C` contains `K_{t+1}` as a depth-`d`
    minor. (Def 2.6) -/
def IsNowhereDense (C : GraphClass) : Prop :=
  ∀ d : ℕ, ∃ t : ℕ, HasShallowCliqueBound C d t

private def composedBranchSet {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a) (u : U) : Set V :=
  {x | ∃ v, v ∈ mJH.branchSet u ∧ x ∈ mHG.branchSet v}

private def composedCenter {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a) (u : U) : V :=
  mHG.center (mJH.center u)

private theorem composedCenter_mem {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a) (u : U) :
    composedCenter mJH mHG u ∈ composedBranchSet mJH mHG u := by
  refine ⟨mJH.center u, mJH.center_mem u, mHG.center_mem _⟩

private theorem composedBranchSet_disjoint {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a)
    {u v : U} (huv : u ≠ v) :
    Disjoint (composedBranchSet mJH mHG u) (composedBranchSet mJH mHG v) := by
  refine Set.disjoint_left.mpr ?_
  intro x hxU hxV
  rcases hxU with ⟨u', hu', hxu'⟩
  rcases hxV with ⟨v', hv', hxv'⟩
  by_cases huv' : u' = v'
  · subst huv'
    exact Set.disjoint_left.mp (mJH.branchDisjoint u v huv) hu' hv'
  · exact Set.disjoint_left.mp (mHG.branchDisjoint u' v' huv') hxu' hxv'

private theorem lift_center_walk {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a)
    (u : U) {s t : W} (p : H.Walk s t)
    (hp : ∀ z ∈ p.support, z ∈ mJH.branchSet u) :
    ∃ q : G.Walk (mHG.center s) (mHG.center t),
      q.length ≤ (2 * a + 1) * p.length ∧
      ∀ w ∈ q.support, w ∈ composedBranchSet mJH mHG u := by
  induction p with
  | @nil s =>
      refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
      intro w hw
      simp at hw
      subst w
      exact ⟨s, hp s (by simp), mHG.center_mem s⟩
  | @cons s s' t h p ih =>
      have hs : s ∈ mJH.branchSet u := hp s (by simp)
      have hs' : s' ∈ mJH.branchSet u := hp s' (by simp)
      have hp' : ∀ z ∈ p.support, z ∈ mJH.branchSet u := by
        intro z hz
        exact hp z (by simp [hz])
      rcases ih hp' with ⟨q, hq_len, hq_support⟩
      rcases mHG.branchEdge s s' h with ⟨xs, hxs, ys, hys, hxy⟩
      rcases mHG.branchRadius s xs hxs with ⟨ps, _, hps_len, hps_support⟩
      rcases mHG.branchRadius s' ys hys with ⟨pt, _, hpt_len, hpt_support⟩
      let step : G.Walk (mHG.center s) (mHG.center s') :=
        ps.append (hxy.toWalk.append pt.reverse)
      have hstep_len : step.length ≤ 2 * a + 1 := by
        dsimp [step]
        rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_reverse]
        omega
      have hstep_support_right :
          ∀ w ∈ (hxy.toWalk.append pt.reverse).support, w ∈ composedBranchSet mJH mHG u := by
        intro w hw
        rw [SimpleGraph.Walk.mem_support_append_iff] at hw
        rcases hw with hw | hw
        · have hw' : w = xs ∨ w = ys := by
            simpa using hw
          rcases hw' with rfl | rfl
          · exact ⟨s, hs, hxs⟩
          · exact ⟨s', hs', hys⟩
        · exact ⟨s', hs', hpt_support w (by simpa [SimpleGraph.Walk.support_reverse] using hw)⟩
      have hstep_support_left : ∀ w ∈ ps.support, w ∈ composedBranchSet mJH mHG u := by
        intro w hw
        exact ⟨s, hs, hps_support w hw⟩
      have hstep_support : ∀ w ∈ step.support, w ∈ composedBranchSet mJH mHG u := by
        intro w hw
        dsimp [step] at hw
        rw [SimpleGraph.Walk.mem_support_append_iff] at hw
        rcases hw with hw | hw
        · exact hstep_support_left w hw
        · exact hstep_support_right w hw
      refine ⟨step.append q, ?_, ?_⟩
      · have hsum : step.length + q.length ≤ (2 * a + 1) + (2 * a + 1) * p.length := by
          exact add_le_add hstep_len hq_len
        simpa [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
      · intro w hw
        rw [SimpleGraph.Walk.mem_support_append_iff] at hw
        rcases hw with hw | hw
        · exact hstep_support w hw
        · exact hq_support w hw

private theorem composedBranchSet_radius {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a)
    (u : U) (x : V) (hx : x ∈ composedBranchSet mJH mHG u) :
    ∃ p : G.Walk (composedCenter mJH mHG u) x, p.IsPath ∧ p.length ≤ 2 * a * b + a + b ∧
      ∀ w ∈ p.support, w ∈ composedBranchSet mJH mHG u := by
  classical
  rcases hx with ⟨v, hv, hxv⟩
  rcases mJH.branchRadius u v hv with ⟨pH, _, hpH_len, hpH_support⟩
  rcases lift_center_walk mJH mHG u pH hpH_support with ⟨q, hq_len, hq_support⟩
  rcases mHG.branchRadius v x hxv with ⟨px, _, hpx_len, hpx_support⟩
  let raw : G.Walk (composedCenter mJH mHG u) x := q.append px
  refine ⟨raw.bypass, raw.bypass_isPath, ?_, ?_⟩
  · have hq_len' : q.length ≤ (2 * a + 1) * b := by
      exact le_trans hq_len (Nat.mul_le_mul_left (2 * a + 1) hpH_len)
    have hraw_len : raw.length ≤ (2 * a + 1) * b + a := by
      have hraw_eq : raw.length = q.length + px.length := by
        dsimp [raw]
        exact SimpleGraph.Walk.length_append q px
      rw [hraw_eq]
      exact add_le_add hq_len' hpx_len
    have hrewrite : (2 * a + 1) * b + a = 2 * a * b + a + b := by
      ring
    exact le_trans raw.length_bypass_le (hrewrite ▸ hraw_len)
  · intro w hw
    have hw' : w ∈ raw.support := raw.support_bypass_subset hw
    dsimp [raw] at hw'
    have hw'' : w ∈ q.support ∨ w ∈ px.support :=
      (SimpleGraph.Walk.mem_support_append_iff q px).mp hw'
    rcases hw'' with hw'' | hw''
    · exact hq_support w hw''
    · exact ⟨v, hv, hpx_support w hw''⟩

private theorem composedBranchSet_edge {U V W : Type}
    {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (mJH : ShallowMinorModel J H b) (mHG : ShallowMinorModel H G a)
    {u v : U} (huv : J.Adj u v) :
    ∃ x ∈ composedBranchSet mJH mHG u, ∃ y ∈ composedBranchSet mJH mHG v, G.Adj x y := by
  rcases mJH.branchEdge u v huv with ⟨u', hu', v', hv', hu'v'⟩
  rcases mHG.branchEdge u' v' hu'v' with ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, ⟨u', hu', hx⟩, y, ⟨v', hv', hy⟩, hxy⟩

/-- The depth-`d` reduct of a graph class `C`: the class of all graphs
    that are depth-`d` shallow minors of some graph in `C`. (Def 2.13) -/
def ShallowReduct (C : GraphClass) (d : ℕ) : GraphClass :=
  fun {V : Type} [DecidableEq V] [Fintype V] (H : SimpleGraph V) =>
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W) (G : SimpleGraph W),
      C G ∧ IsShallowMinor H G d

/-- Lemma 2.12: Composition of shallow minors. -/
theorem shallowMinor_trans
    {V W U : Type} {J : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}
    {a b : ℕ} :
    IsShallowMinor J H b → IsShallowMinor H G a →
    IsShallowMinor J G (2 * a * b + a + b) := by
  intro hJH hHG
  rcases hJH with ⟨mJH⟩
  rcases hHG with ⟨mHG⟩
  refine ⟨{
    branchSet := composedBranchSet mJH mHG
    center := composedCenter mJH mHG
    center_mem := composedCenter_mem mJH mHG
    branchDisjoint := fun u v huv => composedBranchSet_disjoint mJH mHG huv
    branchRadius := fun u x hx => composedBranchSet_radius mJH mHG u x hx
    branchEdge := fun u v huv => composedBranchSet_edge mJH mHG huv
  }⟩

/-- Corollary 2.14: If C is nowhere dense, then C ∇ d is nowhere dense. -/
theorem nowhereDense_shallowReduct (C : GraphClass) (d : ℕ) :
    IsNowhereDense C → IsNowhereDense (ShallowReduct C d) := by
  intro hC d'
  obtain ⟨t, ht⟩ := hC (2 * d * d' + d + d')
  refine ⟨t, ?_⟩
  intro V hV _ H hH hminor
  rcases hH with ⟨W, _, _, G, hCG, hHG⟩
  exact ht G hCG (shallowMinor_trans hminor hHG)

end Lax12Proofs.ShallowMinors
