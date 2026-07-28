import Lax15Proofs.Phases3

/-!
The solver block, run.

`Phases3.lean` stops one turn short: it runs the row scan of a single
dequeued vertex. What is left is the two loops around it — the drain of
one component's queue and the sweep over the roots — and the block that
holds them, `solveBlock`, whose final comparison against the budget is
the leaf's verdict.

Three things are proved here and nothing else.

**The pure identity.** The machine adds up, over the vertices it
expands, the residual edges each of them owns as its *smaller*
endpoint; over a whole component that is the component's edge count,
each edge counted once. That is `sum_upDeg_compVerts`, a fibrewise
count of `compEdges` along `Sym2.inf`.

**The drain.** `drain3_run` empties the queue. Its invariant carries
two queues over the same array — the visited set `V` between `head` and
`tl`, and the *expanded* set `W` as the prefix below `head` — because
the closed form of the toggle is a sum over `W`, and `W` is what turns
into the component at the exit, where `head = tl` forces `W = V`. Its
potential has to read the queue array, this rung having no slot
counter: the drain has paid for the blocks of everything below `head`,
and those blocks are disjoint subintervals of `[0, 2m)` because the
queue is injective.

**The sweep and the block.** The sweep's invariant says that the
visited set is closed under residual neighbourhoods — a union of
components — that it contains every unmarked vertex below `r`, and that
`s` is the cost of the components it has met, indexed as
`V.image (connectedComponentMk ·)`. At `r = n` the components it has
not met carry no vertex outside the marking, hence no edge, so the sum
is `compCost`. `solve_run` then wraps the whole block, final `ite`
included, so that the outer body consumes it with a single `Run.seq`.
-/

namespace Lax15Proofs.VC3

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC
open Lax15Proofs.VC SimpleGraph

variable {g : List ℕ} {n m B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {M : Finset (Fin n)}

attribute [local instance] decAdj decEqComp

/-! ### What one component contributes

The count the machine keeps is per vertex: how many residual edges it
owns as the smaller endpoint. Summed over a component that is the
component's edge count. -/

/-- The residual edges a vertex owns: those whose smaller endpoint it
is. This is the number the row scan of `v` adds to the toggle. -/
noncomputable def upDeg (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (v : Fin n) : ℕ :=
  ((ResNbhd G M v).filter (fun x : Fin n => (v : ℕ) < (x : ℕ))).card

/-- The vertices of one component of the residual graph. -/
noncomputable def compVerts (G : SimpleGraph (Fin n)) (M : Finset (Fin n))
    (C : (R G M).ConnectedComponent) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (R G M).connectedComponentMk v = C)

theorem mem_compVerts {C : (R G M).ConnectedComponent} {v : Fin n} :
    v ∈ compVerts G M C ↔ (R G M).connectedComponentMk v = C := by
  simp [compVerts]

/-- An edge is the pair of its two ends. -/
theorem eq_mk_inf_sup (e : Sym2 (Fin n)) : e = s(e.inf, e.sup) := by
  induction e with | _ a c =>
  rcases le_total a c with h | h
  · rw [Sym2.inf_mk, Sym2.sup_mk, min_eq_left h, max_eq_right h]
  · rw [Sym2.inf_mk, Sym2.sup_mk, min_eq_right h, max_eq_left h, Sym2.eq_swap]

/-- A marked vertex is isolated in the residual graph, so it is alone in
its component: a component that meets the unmarked vertices consists of
them. -/
theorem notMem_of_mem_compVerts {C : (R G M).ConnectedComponent} {u : Fin n}
    (hu : u ∉ M) (huC : u ∈ compVerts G M C) {v : Fin n} (hv : v ∈ compVerts G M C) :
    v ∉ M := by
  intro hvM
  have hiso : ∀ z, ¬ (R G M).Adj v z := fun z h => h.2.1 hvM
  have hr : (R G M).Reachable v u :=
    ConnectedComponent.exact (by rw [mem_compVerts.1 huC, mem_compVerts.1 hv])
  exact hu (eq_of_reachable_isolated hiso hr ▸ hvM)

/-- The residual edges of a component with a given smaller endpoint are
that vertex's upward residual neighbours. -/
theorem card_fiber_compEdges {C : (R G M).ConnectedComponent} {v : Fin n} (hv : v ∉ M)
    (hvC : (R G M).connectedComponentMk v = C) :
    ((compEdges (R G M) C).filter (fun e => (Sym2.inf e : Fin n) = v)).card = upDeg G M v := by
  classical
  have himg : (compEdges (R G M) C).filter (fun e => (Sym2.inf e : Fin n) = v)
      = ((ResNbhd G M v).filter (fun x : Fin n => (v : ℕ) < (x : ℕ))).image
          (fun w => s(v, w)) := by
    refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
    · rw [Finset.mem_filter] at he
      have hres : e ∈ ResEdges G M := by
        rw [← edgeFinset_R]; exact compEdges_subset he.1
      obtain ⟨-, hsup, hlt⟩ := inf_notMem_and_sup_mem_resNbhd hres
      rw [he.2] at hsup hlt
      refine Finset.mem_image.2 ⟨e.sup, Finset.mem_filter.2 ⟨hsup, hlt⟩, ?_⟩
      conv_rhs => rw [eq_mk_inf_sup e, he.2]
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
      rw [Finset.mem_filter] at hw
      obtain ⟨hadj, hwM⟩ := mem_resNbhd.1 hw.1
      have hvw : v ≤ w := by rw [Fin.le_def]; omega
      refine Finset.mem_filter.2 ⟨mem_compEdges.2 ⟨⟨hadj, hv, hwM⟩, hvC⟩, ?_⟩
      rw [Sym2.inf_mk, min_eq_left hvw]
  rw [himg, upDeg, Finset.card_image_of_injOn]
  intro a _ b _ hab
  exact Sym2.congr_right.1 hab

/-- **What a component contributes**: summing over its vertices the
residual edges each owns as smaller endpoint counts its edges once
each. -/
theorem sum_upDeg_compVerts (C : (R G M).ConnectedComponent)
    (hM : ∀ v ∈ compVerts G M C, v ∉ M) :
    ∑ v ∈ compVerts G M C, upDeg G M v = (compEdges (R G M) C).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun e => (Sym2.inf e : Fin n)) (t := compVerts G M C)
    (fun e he => mem_compVerts.2 (mem_of_mem_compEdges he (inf_mem e)))]
  exact Finset.sum_congr rfl fun v hv =>
    (card_fiber_compEdges (hM v hv) (mem_compVerts.1 hv)).symm

/-- A set closed under residual neighbourhoods contains everything its
members reach. -/
theorem mem_of_reachable_closed {W : Finset (Fin n)}
    (hcl : ∀ v ∈ W, ResNbhd G M v ⊆ W) {a c : Fin n} (ha : a ∈ W)
    (h : (R G M).Reachable a c) : c ∈ W := by
  have key : ∀ {x y : Fin n}, (R G M).Walk x y → x ∈ W → y ∈ W := by
    intro x y p
    induction p with
    | nil => exact fun h => h
    | @cons x z y hadj _ ih =>
        intro hx
        exact ih (hcl x hx (mem_resNbhd.2 ⟨hadj.1, hadj.2.2⟩))
  obtain ⟨p⟩ := h
  exact key p ha

/-! ### Blocks and the queue

The drain's potential counts the slots it has already paid for. They
are the blocks of the vertices below `head` in the queue, which are
disjoint subintervals of `[0, 2m)` because the queue is injective. -/

/-- The number of slots in a vertex's block. -/
def blockLen (g : List ℕ) (v : ℕ) : ℕ := offset g (v + 1) - offset g v

/-- The offsets telescope: the blocks below `k` are the slots below
`offset g k`. -/
theorem sum_blockLen_range (hg : EncodesGraph g n G) :
    ∀ k, k ≤ n → ∑ i ∈ Finset.range k, blockLen g i = offset g k := by
  intro k
  induction k with
  | zero => intro _; simpa [blockLen] using hg.offset_zero.symm
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ih (by omega), blockLen]
      have := hg.offset_mono k (by omega)
      omega

/-- **The blocks fit in the target array**: any set of vertices owns at
most `2m` slots between them. -/
theorem sum_blockLen_le (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (S : Finset (Fin n)) : ∑ v ∈ S, blockLen g (v : ℕ) ≤ 2 * m := by
  classical
  calc ∑ v ∈ S, blockLen g (v : ℕ)
      ≤ ∑ v : Fin n, blockLen g (v : ℕ) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = ∑ i ∈ Finset.range n, blockLen g i := Fin.sum_univ_eq_sum_range _ n
    _ = offset g n := sum_blockLen_range hg n le_rfl
    _ = 2 * m := by rw [hg.offset_last, hm]

/-- A sum along the expanded prefix of the queue is a sum over the
expanded set: the queue names each of its members exactly once. -/
theorem sum_range_queue {W : Finset (Fin n)} {Q : ℕ → ℕ} {head : ℕ}
    (h : Queue W Q head head) (φ : ℕ → ℕ) :
    ∑ i ∈ Finset.range head, φ (Q i) = ∑ v ∈ W, φ (v : ℕ) := by
  classical
  have hinj : Set.InjOn Q ↑(Finset.range head) := fun x hx y hy hxy =>
    h.inj x (by simpa using hx) y (by simpa using hy) hxy
  have himg : (Finset.range head).image Q = W.map Fin.valEmbedding := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨v, hv, hvW⟩ := h.mem i hi
      exact ⟨v, hvW, hv⟩
    · rintro ⟨v, hvW, rfl⟩
      obtain ⟨i, hi, hQ⟩ := h.all v hvW
      exact ⟨i, hi, hQ⟩
  rw [← Finset.sum_image (g := Q) (f := φ) hinj, himg, Finset.sum_map]
  rfl

/-- The slots the drain has already paid for, read out of the queue
array — this rung has no slot counter, so the potential reads the
array. -/
def qsum (g : List ℕ) (ν : Env) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, blockLen g ((ν.arrs "q").getD i 0)

theorem qsum_eq {ν : Env} {Q : ℕ → ℕ} {k : ℕ} (hq : ν.arrs "q" = arrOf n Q) (hk : k ≤ n) :
    qsum g ν k = ∑ i ∈ Finset.range k, blockLen g (Q i) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hq, getD_arrOf Q (by simp only [Finset.mem_range] at hi; omega)]

/-- The partial count of a drain never exceeds the component's. -/
theorem sum_upDeg_le_comp {W₀ W : Finset (Fin n)} {CR : (R G M).ConnectedComponent}
    (hsub : W \ W₀ ⊆ compVerts G M CR) (hM : ∀ v ∈ compVerts G M CR, v ∉ M) :
    ∑ v ∈ W \ W₀, upDeg G M v ≤ (compEdges (R G M) CR).card := by
  rw [← sum_upDeg_compVerts CR hM]
  exact Finset.sum_le_sum_of_subset hsub

/-! ### The drain

`while head < tl do expandBody3`, entered at a fresh root `r` that has
just been visited, enqueued and had the toggle reset. Two queues run
over the same array: the visited set between `head` and `tl`, and the
expanded set below `head`. The second is what the toggle's closed form
sums over, and at the exit — where `head = tl` — the two coincide, so
the expanded set is closed under residual neighbourhoods and is exactly
`r`'s component on top of what was already there. -/

/-- **The drain.** One component of the residual graph is searched
breadth-first, its edges counted once each at their smaller endpoint,
and `s` grows by half of them, rounded up. -/
theorem drain3_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h1B : 1 < B) (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B)
    {W₀ : Finset (Fin n)} {MK VIS Q : ℕ → ℕ} {r : Fin n} {head₀ : ℕ} {σ : Env}
    (hthin : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2)
    (hWM : ∀ v ∈ W₀, v ∉ M) (hrM : r ∉ M) (hrW : r ∉ W₀)
    (hcl : ∀ v ∈ W₀, ResNbhd G M v ⊆ W₀)
    (hoff : σ.arrs "off" = arrOf (n + 1) O)
    (hmark : σ.arrs "mark" = arrOf n MK) (hMK : Indicator M MK)
    (htgt : σ.arrs "tgt" = arrOf (2 * m) T)
    (hvis : σ.arrs "vis" = arrOf n VIS) (hVIS : Indicator (insert r W₀) VIS)
    (hq : σ.arrs "q" = arrOf n Q)
    (hQ : Queue (insert r W₀) Q head₀ (head₀ + 1)) (hW : Queue W₀ Q head₀ head₀)
    (hhead : σ.vars "head" = head₀) (htl : σ.vars "tl" = head₀ + 1)
    (htog : σ.vars "tog" = 0)
    (hsB : σ.vars "s" +
      ((compEdges (R G M) ((R G M).connectedComponentMk r)).card + 1) / 2 + 2 < B) :
    ∃ (τ' : Env) (VIS' Q' : ℕ → ℕ) (K : ℕ), Run B drain3 σ τ' K ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      (∀ a, a ≠ "vis" → a ≠ "q" → τ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
        y ≠ "j" → y ≠ "w" → y ≠ "u" → y ≠ "jend" → y ≠ "head" →
        τ'.vars y = σ.vars y) ∧
      τ'.arrs "vis" = arrOf n VIS' ∧
      Indicator (W₀ ∪ compVerts G M ((R G M).connectedComponentMk r)) VIS' ∧
      τ'.arrs "q" = arrOf n Q' ∧
      Queue (W₀ ∪ compVerts G M ((R G M).connectedComponentMk r)) Q'
        (τ'.vars "head") (τ'.vars "tl") ∧
      τ'.vars "head" = τ'.vars "tl" ∧ τ'.vars "tl" ≤ n ∧
      τ'.vars "s" = σ.vars "s" +
        ((compEdges (R G M) ((R G M).connectedComponentMk r)).card + 1) / 2 ∧
      K + 300 * (2 * m - qsum g τ' (τ'.vars "head")) + 70 * (n - τ'.vars "head")
        ≤ 300 * (2 * m - qsum g σ head₀) + 70 * (n - head₀) + 10 := by
  classical
  set CR := (R G M).connectedComponentMk r with hCR
  have hrC : r ∈ compVerts G M CR := mem_compVerts.2 rfl
  have hUM : ∀ v ∈ W₀ ∪ compVerts G M CR, v ∉ M := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact hWM v hv
    · exact notMem_of_mem_compVerts hrM hrC hv
  -- the component and the earlier components are disjoint
  have hreach : ∀ v ∈ compVerts G M CR, (R G M).Reachable r v := by
    intro v hv
    refine ConnectedComponent.exact ?_
    rw [mem_compVerts.1 hv, hCR]
  have hdisj : ∀ v ∈ compVerts G M CR, v ∉ W₀ := by
    intro v hv hvW
    exact hrW (mem_of_reachable_closed hcl hvW (hreach v hv).symm)
  have hVsub0 : insert r W₀ ⊆ W₀ ∪ compVerts G M CR := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact Finset.mem_union_right _ hrC
    · exact Finset.mem_union_left _ hv
  have hclV0 : ∀ v ∈ W₀, ResNbhd G M v ⊆ insert r W₀ :=
    fun v hv x hx => Finset.mem_insert_of_mem (hcl v hv hx)
  obtain ⟨τ', K, hrun, hI, hfalse, hpay⟩ :=
    Run.while_pot (B := B) (b := Cond.lt (.var "head") (.var "tl")) (c := expandBody3)
      (σ := σ)
      (fun ν => ∃ (V W : Finset (Fin n)) (VISν Qν : ℕ → ℕ),
        ν.inp = σ.inp ∧ ν.out = σ.out ∧
        (∀ a, a ≠ "vis" → a ≠ "q" → ν.arrs a = σ.arrs a) ∧
        (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
          y ≠ "j" → y ≠ "w" → y ≠ "u" → y ≠ "jend" → y ≠ "head" →
          ν.vars y = σ.vars y) ∧
        ν.arrs "vis" = arrOf n VISν ∧ Indicator V VISν ∧
        ν.arrs "q" = arrOf n Qν ∧
        Queue V Qν (ν.vars "head") (ν.vars "tl") ∧
        Queue W Qν (ν.vars "head") (ν.vars "head") ∧
        W₀ ⊆ W ∧ W ⊆ V ∧ insert r W₀ ⊆ V ∧ V ⊆ W₀ ∪ compVerts G M CR ∧
        (∀ v ∈ W, ResNbhd G M v ⊆ V) ∧
        ν.vars "tog" = (∑ v ∈ W \ W₀, upDeg G M v) % 2 ∧
        ν.vars "s" = σ.vars "s" + ((∑ v ∈ W \ W₀, upDeg G M v) + 1) / 2 ∧
        ν.vars "tl" ≤ n)
      (fun ν => 300 * (2 * m - qsum g ν (ν.vars "head")) + 70 * (n - ν.vars "head"))
      (by
        rintro ν ⟨V, W, VISν, Qν, -, -, -, -, -, -, -, hQν, -, -, -, -, -, -, -, -, htln⟩
        exact evalB_condLt_vars (by have := hQν.hd; omega) (by omega))
      (by
        rintro ν ⟨V, W, VISν, Qν, hinp, hout, harr, hfr, hvisν, hVISν, hqν, hQν, hWν,
          hW₀W, hWV, hrV, hVsub, hclV, htogν, hsν, htlν⟩ hcond
        have hlt : ν.vars "head" < ν.vars "tl" := lt_of_condLt_true hcond
        have hVM : ∀ v ∈ V, v ∉ M := fun v hv => hUM v (hVsub hv)
        have hEle : ∑ v ∈ W \ W₀, upDeg G M v ≤ (compEdges (R G M) CR).card :=
          sum_upDeg_le_comp (fun v hv => by
            rcases Finset.mem_union.1 (hVsub (hWV (Finset.mem_sdiff.1 hv).1)) with h | h
            · exact absurd h (Finset.mem_sdiff.1 hv).2
            · exact h) (fun v hv => hUM v (Finset.mem_union_right _ hv))
        have hsBν : ν.vars "s" + 2 < B := by rw [hsν]; omega
        obtain ⟨ρ, VIS', Q', u, Kb, hrunb, huval, huV, hinpb, houtb, harrb, hfrb,
            hheadb, hvisb, hVISb, hqb, hQb, hpreb, htlgeb, htlnb, hsb, htgb, htgleb,
            hKb⟩ :=
          expandBody3_run (B := B) (V := V) (MK := MK) (VIS := VISν) (Q := Qν)
            (head := ν.vars "head") (tl := ν.vars "tl") (σ := ν)
            hg hm hO hT h1B h2B hnB hmB hthin hVM
            (by rw [harr "off" (by decide) (by decide)]; exact hoff)
            (by rw [harr "mark" (by decide) (by decide)]; exact hmark) hMK
            (by rw [harr "tgt" (by decide) (by decide)]; exact htgt)
            hvisν hVISν hqν hQν rfl rfl hlt (by omega) hsBν
        have hcu' : ((ResNbhd G M u).filter (fun x : Fin n => (u : ℕ) < (x : ℕ))).card
            = upDeg G M u := rfl
        rw [hcu'] at hsb htgb
        -- the dequeued vertex is new to the expanded set
        have huW : u ∉ W := by
          intro huW
          obtain ⟨i, hi, hQi⟩ := hWν.all u huW
          have := hQν.inj i (by omega) (ν.vars "head") (by omega) (by rw [hQi, huval])
          omega
        have huW₀ : u ∉ W₀ := fun h => huW (hW₀W h)
        have hcu : upDeg G M u ≤ 2 := by
          rw [← hcu']
          refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
          exact hthin u (hVM u huV)
        -- the new expanded set
        have hWnew : Queue (insert u W) Q' (ν.vars "head" + 1) (ν.vars "head" + 1) := by
          refine ⟨?_, le_rfl, ?_, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem huW, hWν.card]
          · intro i hi
            rcases Nat.lt_or_ge i (ν.vars "head") with hih | hih
            · obtain ⟨v, hv, hvW⟩ := hWν.mem i hih
              exact ⟨v, by rw [hpreb i (by omega), hv], Finset.mem_insert_of_mem hvW⟩
            · have : i = ν.vars "head" := by omega
              subst this
              exact ⟨u, by rw [hpreb _ (by omega), huval], Finset.mem_insert_self _ _⟩
          · intro v hv
            rcases Finset.mem_insert.1 hv with rfl | hv
            · exact ⟨ν.vars "head", by omega, by rw [hpreb _ (by omega), huval]⟩
            · obtain ⟨i, hi, hQi⟩ := hWν.all v hv
              exact ⟨i, by omega, by rw [hpreb i (by omega), hQi]⟩
          · intro i hi j hj hij
            exact hQb.inj i (by omega) j (by omega) hij
        have hWVnew : insert u W ⊆ V ∪ ResNbhd G M u := by
          intro v hv
          rcases Finset.mem_insert.1 hv with rfl | hv
          · exact Finset.mem_union_left _ huV
          · exact Finset.mem_union_left _ (hWV hv)
        have hVsubnew : V ∪ ResNbhd G M u ⊆ W₀ ∪ compVerts G M CR := by
          intro v hv
          rcases Finset.mem_union.1 hv with hv | hv
          · exact hVsub hv
          · obtain ⟨hadj, hvM⟩ := mem_resNbhd.1 hv
            rcases Finset.mem_union.1 (hVsub huV) with hu0 | huC
            · exact Finset.mem_union_left _ (hcl u hu0 hv)
            · refine Finset.mem_union_right _ (mem_compVerts.2 ?_)
              rw [← mem_compVerts.1 huC]
              exact (ConnectedComponent.sound
                (SimpleGraph.Adj.reachable
                  (show (R G M).Adj u v from ⟨hadj, hVM u huV, hvM⟩))).symm
        have hEnew : ∑ v ∈ insert u W \ W₀, upDeg G M v
            = upDeg G M u + ∑ v ∈ W \ W₀, upDeg G M v := by
          rw [Finset.insert_sdiff_of_notMem _ huW₀,
            Finset.sum_insert (fun h => huW (Finset.mem_sdiff.1 h).1)]
        refine ⟨ρ, Kb, hrunb, ⟨V ∪ ResNbhd G M u, insert u W, VIS', Q', ?_, ?_, ?_, ?_,
          hvisb, hVISb, hqb, ?_, ?_, ?_, hWVnew, ?_, hVsubnew, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hinpb, hinp]
        · rw [houtb, hout]
        · intro a h1 h2; rw [harrb a h1 h2]; exact harr a h1 h2
        · intro y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
          rw [hfrb y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
          exact hfr y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        · rw [hheadb]; exact hQb
        · rw [hheadb]; exact hWnew
        · exact fun v hv => Finset.mem_insert_of_mem (hW₀W hv)
        · exact fun v hv => Finset.mem_union_left _ (hrV hv)
        · intro v hv
          rcases Finset.mem_insert.1 hv with rfl | hv
          · exact Finset.subset_union_right
          · exact fun x hx => Finset.mem_union_left _ (hclV v hv hx)
        · rw [htgb, htogν, hEnew]; omega
        · rw [hsb, hsν, htogν, hEnew]; omega
        · omega
        · -- the potential drops
          have hqsν : qsum g ν (ν.vars "head") = ∑ i ∈ Finset.range (ν.vars "head"),
              blockLen g (Qν i) := qsum_eq hqν (by omega)
          have hqsρ : qsum g ρ (ρ.vars "head") = ∑ i ∈ Finset.range (ν.vars "head" + 1),
              blockLen g (Q' i) := by rw [hheadb]; exact qsum_eq hqb (by omega)
          have hsplit : ∑ i ∈ Finset.range (ν.vars "head" + 1), blockLen g (Q' i)
              = (∑ i ∈ Finset.range (ν.vars "head"), blockLen g (Qν i))
                + blockLen g (u : ℕ) := by
            rw [Finset.sum_range_succ, hpreb _ (by omega), huval]
            have hcg : ∀ i ∈ Finset.range (ν.vars "head"),
                blockLen g (Q' i) = blockLen g (Qν i) := by
              intro i hi
              simp only [Finset.mem_range] at hi
              rw [hpreb i (by omega)]
            rw [Finset.sum_congr rfl hcg]
          have hle2m : (∑ i ∈ Finset.range (ν.vars "head"), blockLen g (Qν i))
              + blockLen g (u : ℕ) ≤ 2 * m := by
            rw [← hsplit, sum_range_queue hWnew (blockLen g)]
            exact sum_blockLen_le hg hm _
          have hbl : Kb ≤ 300 * blockLen g (u : ℕ) + 60 := hKb
          simp only [size_condLt, size_var]
          rw [hqsρ, hsplit, hheadb, hqsν]
          omega)
      ⟨insert r W₀, W₀, VIS, Q, rfl, rfl, fun a _ _ => rfl, fun y _ _ _ _ _ _ _ _ _ _ _ => rfl,
        hvis, hVIS, hq, by rw [hhead, htl]; exact hQ, by rw [hhead]; exact hW,
        Finset.Subset.refl _, fun v hv => Finset.mem_insert_of_mem hv, Finset.Subset.refl _,
        hVsub0, hclV0, by rw [htog, Finset.sdiff_self]; simp,
        by rw [Finset.sdiff_self]; simp, by rw [htl]; exact hQ.tl_le⟩
  -- the conclusion at the exit
  · obtain ⟨V, W, VIS', Q', hinp, hout, harr, hfr, hvis', hVIS', hq', hQ', hW',
      hW₀W, hWV, hrV, hVsub, hclV, htog', hs', htln'⟩ := hI
    have hht : τ'.vars "head" = τ'.vars "tl" := by
      have := le_of_condLt_false hfalse
      have := hQ'.hd
      omega
    have hWeqV : W = V := by
      refine Finset.eq_of_subset_of_card_le hWV (le_of_eq ?_)
      rw [← hQ'.card, ← hW'.card, hht]
    subst hWeqV
    have hclosed : ∀ v ∈ W, ResNbhd G M v ⊆ W := hclV
    have hcomp : W = W₀ ∪ compVerts G M CR := by
      refine Finset.Subset.antisymm hVsub (fun v hv => ?_)
      rcases Finset.mem_union.1 hv with hv | hv
      · exact hrV (Finset.mem_insert_of_mem hv)
      · exact mem_of_reachable_closed hclosed (hrV (Finset.mem_insert_self _ _))
          (hreach v hv)
    have hEexit : ∑ v ∈ W \ W₀, upDeg G M v = (compEdges (R G M) CR).card := by
      have hsd : W \ W₀ = compVerts G M CR := by
        rw [hcomp]
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd h1 h2
          · exact h1
        · exact fun h => ⟨Or.inr h, hdisj v h⟩
      rw [hsd, sum_upDeg_compVerts CR (fun v hv => hUM v (Finset.mem_union_right _ hv))]
    refine ⟨τ', VIS', Q', K, hrun, hinp, hout, harr, hfr, hvis', by rw [← hcomp]; exact hVIS',
      hq', by rw [← hcomp]; exact hQ', hht, htln', by rw [hs', hEexit], ?_⟩
    simp only [size_condLt, size_var] at hpay
    rw [hhead] at hpay
    omega


end Lax15Proofs.VC3
