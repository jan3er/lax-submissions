import Lax3Proofs.AugmentedDensity
import Lax3Proofs.OrderedCovers

/-!
What the cover the program computes costs: the analysis capstone of the
cover phase, in the vocabulary the driver's cost accounting cites.

# The three deliverables

The pieces the earlier files leave are a recursion, a composition and a
counting statement, each stated over data rather than over an optimal
choice.  This file closes them into three numbers.

*The budget.*  `AugmentedDensity.joint` is the joint in-degree/density
recursion a greedy chain runs; `joint_fst_le` reads its first component
in closed form, `(d + D₁ + 2) ^ 16 ^ i`, so that no consumer has to
unfold the recursion.  The starting in-degree is bounded the same way:
a graph whose depth-1 minors are sparse has a vertex of small degree
inside every set (`lowDegreeVertices_of_densityAtMost`), and the greedy
guarantee of the elimination engine turns that into `d₀ ≤ 2 · D₁`
(`inDeg_zero_le`).

*The cover.*  `exists_cover_degree` is the end-to-end statement: on a
nowhere dense class, for every cover radius, every number of
augmentation rounds and every `δ > 0` there is a constant `c` such that
the cover the program computes — the fibers of weak `2r`-reachability
under the ordering of its last elimination pass — is an `r`-neighborhood
cover of degree at most `⌈c · m ^ δ⌉`.  Its hypotheses are exactly the
postconditions of the two engines: an augmentation chain whose rounds
orient their fraternity graphs greedily, and two greedy eliminations,
one at the start and one at the end, each delivering an in-degree or
back-degree bound together with the guarantee that it is at most every
bound a `LowDegreeVertices` argument can prove.  Nothing about `d₀` or
about the density of `G` is assumed: both are supplied from nowhere
denseness inside the proof.

*The mass.*  `sum_ncard_le_mul` is the double count that turns a degree
bound into a bound on the total size of all clusters, which is what the
driver charges its per-cluster work against: a family of sets in which
no vertex lies in more than `d` members has total size at most `m · d`.

# The arithmetic

The budget grows by squaring at every round, so the closed bound is a
tower in the number of rounds and the theorem is stated for a fixed
round count `R`, with the constant `c` allowed to depend on it — the
quantifier shape of `AugmentedDensity.exists_chain_density`.  The final
composition picks the inner exponent `δ / (2 · 16 ^ R)` so that the
`2 · 16 ^ R`-th power the two squarings cost lands on the requested
`δ`; everything else is a constant factor absorbed into `c`.
-/

namespace Lax3Proofs.CoverDegree

open scoped SimpleGraph
open Lax3.NeighborhoodCovers
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12.ColoringNumbers
open Lax3Proofs.Augmentation
open Lax3Proofs.AugmentedDensity
open Lax3Proofs.OrderedCovers

variable {n : ℕ}

/-! ### The budget in closed form

`joint` squares its first component at every round and feeds it into an
exponent of the density budget, so both components are bounded by powers
of the single number `d + D₁ + 2`: the in-degree budget by its
`16 ^ i`-th power, the depth-`a` density budget by its
`2 · 16 ^ i · (a + 1)`-th.  The two halves have to be carried together —
the in-degree of a round is charged the density of the previous one. -/

/-- **The joint budget, in closed form.**  Both components of the
recursion of a greedy chain are powers of `d + D₁ + 2`: the in-degree
budget of round `i` is at most its `16 ^ i`-th power, and the depth-`a`
density budget of round `i` at most its `2 · 16 ^ i · (a + 1)`-th.

# Proof

Induction on `i`, carrying both halves.  At the successor the density
budget is `(b + 2) ^ (6a + 6)` times the previous density budget at
depth `4a + 4`, and `b + 2 ≤ (d + D₁ + 2) ^ (16 ^ i + 1)` because the
base is at least `2`; the exponents add up to at most
`2 · 16 ^ (i+1) · (a + 1)`.  The in-degree budget is a sum of four
terms, each at most the `5 · 16 ^ i`-th power, and `4` is at most the
square of the base. -/
theorem joint_le (d D₁ : ℕ) : ∀ i : ℕ,
    (joint d D₁ i).1 ≤ (d + D₁ + 2) ^ 16 ^ i ∧
      ∀ a : ℕ, (joint d D₁ i).2 a ≤ (d + D₁ + 2) ^ (2 * 16 ^ i * (a + 1)) := by
  intro i
  induction i with
  | zero =>
      refine ⟨?_, fun a => ?_⟩
      · rw [show (joint d D₁ 0).1 = d from rfl]
        simp only [pow_zero, pow_one]
        omega
      · rw [show (joint d D₁ 0).2 a = D₁ from rfl]
        calc D₁ ≤ d + D₁ + 2 := by omega
          _ = (d + D₁ + 2) ^ 1 := (pow_one _).symm
          _ ≤ (d + D₁ + 2) ^ (2 * 16 ^ 0 * (a + 1)) :=
              Nat.pow_le_pow_right (by omega) (by simp; omega)
  | succ i ih =>
      obtain ⟨hb, hs⟩ := ih
      have hB : 2 ≤ d + D₁ + 2 := by omega
      have hN : 1 ≤ 16 ^ i := Nat.one_le_pow _ _ (by omega)
      have hBN : 2 ≤ (d + D₁ + 2) ^ 16 ^ i :=
        hB.trans (Nat.le_self_pow (by omega) _)
      have hb2 : (joint d D₁ i).1 + 2 ≤ (d + D₁ + 2) ^ (16 ^ i + 1) := by
        calc (joint d D₁ i).1 + 2
            ≤ (d + D₁ + 2) ^ 16 ^ i + (d + D₁ + 2) ^ 16 ^ i := by omega
          _ = 2 * (d + D₁ + 2) ^ 16 ^ i := by ring
          _ ≤ (d + D₁ + 2) * (d + D₁ + 2) ^ 16 ^ i := Nat.mul_le_mul_right _ hB
          _ = (d + D₁ + 2) ^ (16 ^ i + 1) := by ring
      constructor
      · rw [show (joint d D₁ (i + 1)).1 =
              (joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).1 +
                ((joint d D₁ i).1 * (joint d D₁ i).1 +
                  (joint d D₁ i).1 * (joint d D₁ i).2 1) from rfl, pow_succ]
        have hs1 : (joint d D₁ i).2 1 ≤ (d + D₁ + 2) ^ (4 * 16 ^ i) := by
          calc (joint d D₁ i).2 1 ≤ (d + D₁ + 2) ^ (2 * 16 ^ i * (1 + 1)) := hs 1
            _ = (d + D₁ + 2) ^ (4 * 16 ^ i) := by
                rw [show 2 * 16 ^ i * (1 + 1) = 4 * 16 ^ i by ring]
        have e1 : (joint d D₁ i).1 ≤ (d + D₁ + 2) ^ (5 * 16 ^ i) :=
          hb.trans (Nat.pow_le_pow_right (by omega) (by omega))
        have e2 : (joint d D₁ i).1 * (joint d D₁ i).1 ≤ (d + D₁ + 2) ^ (5 * 16 ^ i) := by
          calc (joint d D₁ i).1 * (joint d D₁ i).1
              ≤ (d + D₁ + 2) ^ 16 ^ i * (d + D₁ + 2) ^ 16 ^ i := Nat.mul_le_mul hb hb
            _ = (d + D₁ + 2) ^ (16 ^ i + 16 ^ i) := (pow_add _ _ _).symm
            _ ≤ (d + D₁ + 2) ^ (5 * 16 ^ i) := Nat.pow_le_pow_right (by omega) (by omega)
        have e3 : (joint d D₁ i).1 * (joint d D₁ i).2 1 ≤ (d + D₁ + 2) ^ (5 * 16 ^ i) := by
          calc (joint d D₁ i).1 * (joint d D₁ i).2 1
              ≤ (d + D₁ + 2) ^ 16 ^ i * (d + D₁ + 2) ^ (4 * 16 ^ i) := Nat.mul_le_mul hb hs1
            _ = (d + D₁ + 2) ^ (16 ^ i + 4 * 16 ^ i) := (pow_add _ _ _).symm
            _ = (d + D₁ + 2) ^ (5 * 16 ^ i) := by
                rw [show 16 ^ i + 4 * 16 ^ i = 5 * 16 ^ i by ring]
        calc (joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).1 +
              ((joint d D₁ i).1 * (joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).2 1)
            ≤ 4 * (d + D₁ + 2) ^ (5 * 16 ^ i) := by omega
          _ ≤ (d + D₁ + 2) ^ 2 * (d + D₁ + 2) ^ (5 * 16 ^ i) := by
              refine Nat.mul_le_mul_right _ ?_
              calc (4 : ℕ) = 2 ^ 2 := by norm_num
                _ ≤ (d + D₁ + 2) ^ 2 := Nat.pow_le_pow_left hB 2
          _ = (d + D₁ + 2) ^ (2 + 5 * 16 ^ i) := (pow_add _ _ _).symm
          _ ≤ (d + D₁ + 2) ^ (16 ^ i * 16) := Nat.pow_le_pow_right (by omega) (by omega)
      · intro a
        rw [show (joint d D₁ (i + 1)).2 a =
              stepFactor (joint d D₁ i).1 a * (joint d D₁ i).2 (stepDepth a) from rfl, pow_succ]
        have h1 : stepFactor (joint d D₁ i).1 a
            ≤ (d + D₁ + 2) ^ ((16 ^ i + 1) * (6 * a + 6)) := by
          rw [stepFactor, Nat.pow_mul]
          exact Nat.pow_le_pow_left hb2 _
        have h2 : (joint d D₁ i).2 (stepDepth a)
            ≤ (d + D₁ + 2) ^ (2 * 16 ^ i * (stepDepth a + 1)) := hs (stepDepth a)
        calc stepFactor (joint d D₁ i).1 a * (joint d D₁ i).2 (stepDepth a)
            ≤ (d + D₁ + 2) ^ ((16 ^ i + 1) * (6 * a + 6)) *
                (d + D₁ + 2) ^ (2 * 16 ^ i * (stepDepth a + 1)) := Nat.mul_le_mul h1 h2
          _ = (d + D₁ + 2) ^
                ((16 ^ i + 1) * (6 * a + 6) + 2 * 16 ^ i * (stepDepth a + 1)) :=
              (pow_add _ _ _).symm
          _ ≤ (d + D₁ + 2) ^ (2 * (16 ^ i * 16) * (a + 1)) := by
              refine Nat.pow_le_pow_right (by omega) ?_
              rw [stepDepth]
              nlinarith [hN]

/-- The in-degree half of the closed budget: after `i` greedy rounds
from a starting in-degree `d`, with depth-1 density `D₁`, every
in-degree is at most `(d + D₁ + 2) ^ 16 ^ i`. -/
theorem joint_fst_le (d D₁ i : ℕ) : (joint d D₁ i).1 ≤ (d + D₁ + 2) ^ 16 ^ i :=
  (joint_le d D₁ i).1

/-! ### Small degree from density

The plain-graph companion of `OrderedCovers.lowDegreeVertices_toGraph`,
which reads the same conclusion off an orientation: what a *density*
bound gives is that the subgraph induced on any vertex set — a depth-1
minor of the graph, with singleton branch sets — has few edges, hence a
vertex of small degree.  This is what the greedy pass at round zero is
measured against. -/

/-- The ordered pairs of adjacent vertices inside `S` number at most
`2 · D₁ · |S|` when every depth-1 minor on `k` vertices has at most
`D₁ · k` edges: the subgraph induced on `S` is such a minor, and its
edges each carry two ordered pairs. -/
private theorem card_pairsIn_le_of_density {G : SimpleGraph (Fin n)} {D₁ : ℕ}
    (hdens : HasDensityAtMost G 1 D₁) (S : Finset (Fin n)) :
    (pairsIn G S).card ≤ 2 * (D₁ * S.card) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hempty : pairsIn G ∅ = ∅ :=
      Finset.eq_empty_iff_forall_notMem.2 fun p hp => by simpa using (mem_pairsIn.1 hp).1
    rw [hempty]
    simp
  have hs : 0 < S.card := Finset.card_pos.mpr hS
  set f : Fin S.card → Fin n := fun i => ((S.equivFin.symm i : {x // x ∈ S}) : Fin n)
    with hfdef
  have hfinj : Function.Injective f := fun i j hij =>
    S.equivFin.symm.injective (Subtype.ext hij)
  set g : Fin n → Fin S.card := fun x => if h : x ∈ S then S.equivFin ⟨x, h⟩ else ⟨0, hs⟩
    with hgdef
  have hfg : ∀ x ∈ S, f (g x) = x := by
    intro x hx
    simp [hfdef, hgdef, hx]
  set J : SimpleGraph (Fin S.card) :=
    { Adj := fun i j => G.Adj (f i) (f j)
      symm := fun _ _ h => h.symm
      loopless := ⟨fun i h => G.irrefl h⟩ }
  have hJadj : ∀ i j, J.Adj i j ↔ G.Adj (f i) (f j) := fun _ _ => Iff.rfl
  have hminor : HasShallowMinor G 1 J :=
    ⟨{ branch := fun i => {f i}
       center := f
       center_mem := fun _ => rfl
       disjoint := fun i j hij => by
         refine Set.disjoint_left.2 ?_
         rintro x rfl hx
         exact hij (hfinj (Set.mem_singleton_iff.1 hx))
       radius_le := fun i x hx => by
         rw [Set.mem_singleton_iff] at hx
         subst hx
         exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
       adj := fun i j hij => ⟨f i, rfl, f j, rfl, hij⟩ }⟩
  have hJcard : J.edgeSet.ncard ≤ D₁ * S.card := hdens S.card J hminor
  -- every ordered pair inside `S` names an edge of the minor
  have himg : ((pairsIn G S).image (fun p => s(g p.1, g p.2))).card ≤ J.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro e he
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨h1, h2, hadj⟩ := mem_pairsIn.1 hp
    refine (SimpleGraph.mem_edgeSet J).2 ((hJadj _ _).2 ?_)
    rw [hfg _ h1, hfg _ h2]
    exact hadj
  -- and each edge is named by at most two of them
  have hfib : ∀ e : Sym2 (Fin S.card),
      ((pairsIn G S).filter (fun p => s(g p.1, g p.2) = e)).card ≤ 2 := by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
        have hsub : (pairsIn G S).filter (fun p => s(g p.1, g p.2) = s(x, y)) ⊆
            {(f x, f y), (f y, f x)} := by
          intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
          obtain ⟨h1, h2, -⟩ := mem_pairsIn.1 hq1
          have e1 : f (g q.1) = q.1 := hfg _ h1
          have e2 : f (g q.2) = q.2 := hfg _ h2
          rcases Sym2.eq_iff.1 hq2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · refine Finset.mem_insert.2 (Or.inl (Prod.ext ?_ ?_))
            · rw [← e1, ha]
            · rw [← e2, hb]
          · refine Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (Prod.ext ?_ ?_)))
            · rw [← e1, ha]
            · rw [← e2, hb]
        refine (Finset.card_le_card hsub).trans ?_
        exact (Finset.card_insert_le _ _).trans (by simp)
  calc (pairsIn G S).card
      ≤ 2 * ((pairsIn G S).image (fun p => s(g p.1, g p.2))).card :=
        Finset.card_le_mul_card_image _ 2 (fun e _ => hfib e)
    _ ≤ 2 * (D₁ * S.card) := Nat.mul_le_mul_left _ (himg.trans hJcard)

/-- **Small degree from density.**  A graph every depth-1 minor of which,
on `k` vertices, has at most `D₁ · k` edges carries, inside every
nonempty vertex set, a vertex of degree at most `2 · D₁` there.  This is
what the greedy elimination of the input graph is measured against. -/
theorem lowDegreeVertices_of_densityAtMost {G : SimpleGraph (Fin n)} {D₁ : ℕ}
    (hdens : HasDensityAtMost G 1 D₁) : LowDegreeVertices G (2 * D₁) := by
  classical
  intro S hS
  by_contra hcon
  push Not at hcon
  have hlow : S.card * (2 * D₁ + 1) ≤ (pairsIn G S).card := by
    rw [card_pairsIn]
    calc S.card * (2 * D₁ + 1) = ∑ _v ∈ S, (2 * D₁ + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ S, (nbrsIn G S v).card := Finset.sum_le_sum fun v hv => hcon v hv
  have hhigh := card_pairsIn_le_of_density hdens S
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hexp : S.card * (2 * D₁ + 1) = 2 * (D₁ * S.card) + S.card := by ring
  omega

/-- **The starting in-degree.**  The greedy elimination of the input
graph produces an orientation of in-degree at most twice the depth-1
density: its own bound is at most every bound a `LowDegreeVertices`
argument proves, and the density proves `2 · D₁`. -/
theorem inDeg_zero_le {G : SimpleGraph (Fin n)} {D₁ d₀ : ℕ}
    (hdens : HasDensityAtMost G 1 D₁)
    (hmin : ∀ k', LowDegreeVertices G k' → d₀ ≤ k') : d₀ ≤ 2 * D₁ :=
  hmin _ (lowDegreeVertices_of_densityAtMost hdens)

/-! ### The degree of the computed cover, as a number -/

/-- A neighborhood cover of degree `d` is one of every larger degree. -/
theorem isNeighborhoodCover_mono {G : SimpleGraph (Fin n)} {r : ℕ} {X : Fin n → Set (Fin n)}
    {d d' : ℕ} (h : IsNeighborhoodCover G r X d) (hd : d ≤ d') :
    IsNeighborhoodCover G r X d' :=
  ⟨h.ball_subset, h.subset_ball, fun v => (h.degree_le v).trans hd⟩

/-- **The cover degree in closed form.**  With a starting in-degree at
most `2 · D₁` and a final ordering as good as the greedy elimination of
the last round's graph, the degree `(d + 1) · (k + 1)` of the cover of
`OrderedCovers.isNeighborhoodCover_of_augChain` is at most
`6 · (3 · D₁ + 2) ^ (2 · 16 ^ R)`: two squarings of the round budget. -/
theorem degree_le_of_budget (d₀ D₁ R k : ℕ) (hd₀ : d₀ ≤ 2 * D₁)
    (hk : k ≤ 2 * (joint d₀ D₁ R).1) :
    ((joint d₀ D₁ R).1 + 1) * (k + 1) ≤ 6 * (3 * D₁ + 2) ^ (2 * 16 ^ R) := by
  have hjoint : (joint d₀ D₁ R).1 ≤ (3 * D₁ + 2) ^ 16 ^ R :=
    (joint_fst_le d₀ D₁ R).trans (Nat.pow_le_pow_left (by omega) _)
  have hQ1 : 1 ≤ (3 * D₁ + 2) ^ 16 ^ R := Nat.one_le_pow _ _ (by omega)
  have hsq : (3 * D₁ + 2) ^ 16 ^ R * (3 * D₁ + 2) ^ 16 ^ R
      = (3 * D₁ + 2) ^ (2 * 16 ^ R) := by
    rw [← pow_add, show 16 ^ R + 16 ^ R = 2 * 16 ^ R by ring]
  calc ((joint d₀ D₁ R).1 + 1) * (k + 1)
      ≤ ((3 * D₁ + 2) ^ 16 ^ R + 1) * (2 * (3 * D₁ + 2) ^ 16 ^ R + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 6 * ((3 * D₁ + 2) ^ 16 ^ R * (3 * D₁ + 2) ^ 16 ^ R) := by nlinarith [hQ1]
    _ = 6 * (3 * D₁ + 2) ^ (2 * 16 ^ R) := by rw [hsq]

/-! ### The end-to-end theorem -/

/--
**The degree of the computed cover.**  Fix a nowhere dense class `C`, a
cover radius `rc`, a number of augmentation rounds `R` with a `t`
satisfying the radius arithmetic `3 · t ≤ R` and `2 · rc ≤ 2 ^ t`, and
a `δ > 0`.  Then there is a constant `c` — depending on the class, on
`R` and on `δ`, not on the graph — such that on every subgraph `G` of a
member, on `m` vertices:

given an `R`-round augmentation chain of `G` whose rounds orient their
fraternity graphs greedily, a starting in-degree `d₀` that is at most
every bound a `LowDegreeVertices` argument proves of `G`, and a final
vertex ordering `π` under which the last round's graph has back-degrees
at most `k`, again with `k` at most every such bound,

the fibers of weak `2 · rc`-reachability under `π` form an
`rc`-neighborhood cover of `G` of radius `2 · rc` and degree at most
`⌈c · m ^ δ⌉`.

# What supplies the hypotheses

All of them are postconditions of the two engines and nothing else.
The chain and the greedy rounds come from the augmentation pass
(`AugStep` per round plus `RamElim.greedyFratRound_of_cert`); `d₀` and
its minimality, and `k` and its minimality, are the in-degree and
back-degree bounds of the two elimination passes together with the
greedy guarantee `∀ k', LowDegreeVertices _ k' → k ≤ k'` of `ElimPost`;
`π` is the permutation the rank array of the last pass defines
(`RamCover.rankPerm`).  Nothing is assumed about the density of `G` or
about the size of `d₀`: both come from nowhere denseness inside.

# Proof

`AugmentedDensity.exists_densityAtMost_of_nowhereDense` at depth
`chainDepth R 1` and exponent `δ / (2 · 16 ^ R)` gives a depth-1 density
`D₁ = ⌈c₀ · m ^ (δ / (2 · 16 ^ R))⌉` of `G`.  That bounds `d₀` by
`2 · D₁` (`inDeg_zero_le`), and then
`AugmentedDensity.greedy_chain_joint_inDegLE` bounds the in-degree of
the last round by `(joint d₀ D₁ R).1`, and the greedy guarantee of the
final pass bounds `k` by twice that
(`OrderedCovers.lowDegreeVertices_toGraph`).
`OrderedCovers.isNeighborhoodCover_of_augChain` produces the cover with
degree `(d + 1) · (k + 1)`, which `degree_le_of_budget` closes into
`6 · (3 · D₁ + 2) ^ (2 · 16 ^ R)`.  Since `D₁ ≤ c₀ · m ^ δ' + 1` and
`m ^ δ' ≥ 1`, that is at most `6 · (3 c₀ + 5) ^ (2 · 16 ^ R) · m ^ δ`:
the inner exponent was chosen so that its `2 · 16 ^ R`-th power is the
requested one.
-/
theorem exists_cover_degree (C : GraphClass) (hC : NowhereDense C) (rc R t : ℕ)
    (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ (D : ℕ → Orientation m) (π : Equiv.Perm (Fin m)) (d₀ k : ℕ),
          IsAugChain G D R →
          (∀ i < R, GreedyFratRound (D i) (D (i + 1))) →
          (D 0).InDegLE d₀ →
          (∀ k', LowDegreeVertices G k' → d₀ ≤ k') →
          BackDegLE (D R).toGraph (fun v => ((π v : Fin m) : ℕ)) k →
          (∀ k', LowDegreeVertices (D R).toGraph k' → k ≤ k') →
          IsNeighborhoodCover G rc (fun u => {w | u ∈ wreach G π (2 * rc) w})
            ⌈c * (m : ℝ) ^ δ⌉₊ := by
  classical
  have hPpos : 0 < (2 * 16 ^ R : ℕ) := by positivity
  have hPR : (0 : ℝ) < ((2 * 16 ^ R : ℕ) : ℝ) := by exact_mod_cast hPpos
  have hε : 0 < δ / ((2 * 16 ^ R : ℕ) : ℝ) := div_pos hδ hPR
  obtain ⟨c₀, hc₀⟩ :=
    exists_densityAtMost_of_nowhereDense C hC (chainDepth R 1) (δ / ((2 * 16 ^ R : ℕ) : ℝ)) hε
  refine ⟨6 * (3 * max c₀ 0 + 5) ^ (2 * 16 ^ R), ?_⟩
  intro n Gn hGn m G hsub D π d₀ k hchain hgreedy hd0 hd0min hback hkmin
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun v => v.elim0, fun u => u.elim0, fun v => v.elim0⟩
  -- `X` is the subpolynomial factor at the inner exponent and `D₁` the
  -- depth-1 density of `G` it bounds
  set X : ℝ := (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) with hXdef
  have hXnn : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hc₁0 : (0 : ℝ) ≤ max c₀ 0 := le_max_right _ _
  set D₁ : ℕ := ⌈max c₀ 0 * X⌉₊ with hD₁def
  have hdensR : HasDensityAtMost G (chainDepth R 1) D₁ :=
    hasDensityAtMost_mono
      (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn))
      (hc₀ n Gn hGn m G hsub)
  have hdens1 : HasDensityAtMost G 1 D₁ :=
    hasDensityAtMost_mono_depth
      (show (1 : ℕ) ≤ chainDepth R 1 from chainDepth_mono_round 1 (Nat.zero_le R)) hdensR
  -- the two greedy passes, measured against it
  have hd₀le := inDeg_zero_le hdens1 hd0min
  have hdR := greedy_chain_joint_inDegLE hchain hgreedy hd0 hdensR R le_rfl
  have hkle := hkmin _ (lowDegreeVertices_toGraph hdR)
  refine isNeighborhoodCover_mono (isNeighborhoodCover_of_augChain hchain ht hrt hdR π hback) ?_
  -- the numeric massage: the two squarings of the budget against
  -- `X ^ (2 · 16 ^ R) = m ^ δ`, which is how the inner exponent was chosen
  have hdeg := degree_le_of_budget d₀ D₁ R k hd₀le hkle
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmd : (1 : ℝ) ≤ X := by
    rw [hXdef]
    calc (1 : ℝ) = (1 : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) := (Real.one_rpow _).symm
      _ ≤ (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) hm1 hε.le
  have hceil : ((D₁ : ℕ) : ℝ) ≤ max c₀ 0 * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc₁0 hXnn)).le
  have hbase : 3 * ((D₁ : ℕ) : ℝ) + 2 ≤ (3 * max c₀ 0 + 5) * X := by
    nlinarith [hceil, hmd, hc₁0]
  have hXP : X ^ (2 * 16 ^ R : ℕ) = (m : ℝ) ^ δ := by
    rw [hXdef, ← Real.rpow_natCast ((m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) (2 * 16 ^ R),
      ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hfinal : ((((joint d₀ D₁ R).1 + 1) * (k + 1) : ℕ) : ℝ)
      ≤ 6 * (3 * max c₀ 0 + 5) ^ (2 * 16 ^ R) * (m : ℝ) ^ δ := by
    calc ((((joint d₀ D₁ R).1 + 1) * (k + 1) : ℕ) : ℝ)
        ≤ ((6 * (3 * D₁ + 2) ^ (2 * 16 ^ R) : ℕ) : ℝ) := by exact_mod_cast hdeg
      _ = 6 * (3 * ((D₁ : ℕ) : ℝ) + 2) ^ (2 * 16 ^ R) := by push_cast; ring
      _ ≤ 6 * ((3 * max c₀ 0 + 5) * X) ^ (2 * 16 ^ R) := by gcongr
      _ = 6 * (3 * max c₀ 0 + 5) ^ (2 * 16 ^ R) * X ^ (2 * 16 ^ R) := by rw [mul_pow]; ring
      _ = 6 * (3 * max c₀ 0 + 5) ^ (2 * 16 ^ R) * (m : ℝ) ^ δ := by rw [hXP]
  exact_mod_cast hfinal.trans (Nat.le_ceil _)

/-! ### Cluster mass

The driver charges its per-cluster work against the total size of all
clusters, which a degree bound controls by double counting: summing the
sizes of the clusters and summing the number of clusters each vertex
lies in count the same incidences. -/

/-- The incidences of a cluster family: the pairs `(u, w)` with `w` in
the cluster of `u`. -/
private noncomputable def incid {N : ℕ} (X : Fin N → Set (Fin N)) : Finset (Fin N × Fin N) :=
  @Finset.filter _ (fun p : Fin N × Fin N => p.2 ∈ X p.1) (Classical.decPred _) Finset.univ

private theorem mem_incid {N : ℕ} {X : Fin N → Set (Fin N)} {p : Fin N × Fin N} :
    p ∈ incid X ↔ p.2 ∈ X p.1 := by
  rw [incid, @Finset.mem_filter _ _ (Classical.decPred _)]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

private theorem card_pick_eq_ncard {N : ℕ} (p : Fin N → Prop) :
    (pick p).card = {u : Fin N | p u}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.mem_coe, mem_pick, Set.mem_setOf_eq]

/-- The incidences counted by their first coordinate: the sizes of the
clusters. -/
private theorem card_incid_clusters {N : ℕ} (X : Fin N → Set (Fin N)) :
    (incid X).card = ∑ u : Fin N, (X u).ncard := by
  classical
  have hEq : incid X = Finset.univ.biUnion
      (fun u : Fin N => (pick (fun w => w ∈ X u)).image (fun w => (u, w))) := by
    ext p
    simp only [mem_incid, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨p.1, p.2, mem_pick.2 h, rfl⟩
    · rintro ⟨u, w, hw, rfl⟩
      have hw' := mem_pick.1 hw
      exact hw'
  rw [hEq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).2),
      card_pick_eq_ncard, Set.setOf_mem_eq]
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun p hp hp' => hxy ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hp'
    exact ((Prod.ext_iff.1 hw').1).symm

/-- The same incidences counted by their second coordinate: the number
of clusters each vertex lies in. -/
private theorem card_incid_fibers {N : ℕ} (X : Fin N → Set (Fin N)) :
    (incid X).card = ∑ w : Fin N, {u : Fin N | w ∈ X u}.ncard := by
  classical
  have hEq : incid X = Finset.univ.biUnion
      (fun w : Fin N => (pick (fun u => w ∈ X u)).image (fun u => (u, w))) := by
    ext p
    simp only [mem_incid, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨p.2, p.1, mem_pick.2 h, rfl⟩
    · rintro ⟨w, u, hu, rfl⟩
      have hu' := mem_pick.1 hu
      exact hu'
  rw [hEq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1),
      card_pick_eq_ncard]
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun p hp hp' => hxy ?_
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨u', -, hu'⟩ := Finset.mem_image.1 hp'
    exact ((Prod.ext_iff.1 hu').2).symm

/-- **Cluster mass.**  A family of vertex sets no vertex of which lies
in more than `d` members has total size at most `N · d`: both sides
count the incidences of the family. -/
theorem sum_ncard_le_mul {N : ℕ} (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ w : Fin N, {u : Fin N | w ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, (X u).ncard ≤ N * d := by
  rw [← card_incid_clusters, card_incid_fibers]
  calc ∑ w : Fin N, {u : Fin N | w ∈ X u}.ncard ≤ ∑ _w : Fin N, d :=
        Finset.sum_le_sum fun w _ => h w
    _ = N * d := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- Cluster mass of a neighborhood cover: the clusters of an
`r`-neighborhood cover of degree `d` have total size at most `N · d`.
This is the form the driver's cost accounting cites — the work it does
per cluster is charged to the vertices of that cluster. -/
theorem sum_ncard_le_of_isNeighborhoodCover {N r d : ℕ} {G : SimpleGraph (Fin N)}
    {X : Fin N → Set (Fin N)} (h : IsNeighborhoodCover G r X d) :
    ∑ u : Fin N, (X u).ncard ≤ N * d :=
  sum_ncard_le_mul X d h.degree_le

end Lax3Proofs.CoverDegree
