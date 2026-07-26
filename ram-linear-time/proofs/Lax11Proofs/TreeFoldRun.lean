import Lax11Proofs.TreeFold

/-!
The tree fold, run: what the schema's three phases do to an environment,
and what they cost.

The mathematics is already finished in `TreeFold.lean` — `sweep_eq_val`
says the one forward pass computes the tree fold — so nothing here is
about trees. Every lemma below has the same shape as the phase lemmas of
the connected-components driver: the array is `arrOf` of a named
function, the loop moves that function, the frame conditions say what
was not touched, and `Run.while_count` pays for the loop. Uniform cost
suffices at every loop, so the global potential the driver needed does
not appear: a node is visited once, a table entry is stored once.

The one place where something has to be checked rather than copied is
the combination lookup. `tab` is a square table read at `a * V + b`, and
the machine has no multiplication, so the row bases live in a second
array `row`. The lookup is in range, and lands on the entry it should,
exactly because both accumulators are below `V` — which is `sweep_lt`,
and which is why the push loop's invariant is stated with `sweep` rather
than with an anonymous function.
-/

namespace Lax11Proofs.TreeFold

open Lax11.Ram Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning
open Lax11Proofs.CC (readLoop)

/-! ### The table, materialized

The prologue is a straight line of stores, one per table entry, so both
its cost and its effect are an induction on the list. -/

/-- The prologue compiles into any layout that has the array. -/
theorem storesFrom_ok {L : Layout} {a : String} (ha : a ∈ L.arrays) (ht : 0 < L.temps) :
    ∀ (i : ℕ) (vs : List ℕ), Com.Ok L (storesFrom a i vs) := by
  intro i vs
  induction vs generalizing i with
  | nil => trivial
  | cons v vs ih => exact ⟨⟨ha, trivial, trivial, ht⟩, ih (i + 1)⟩

/-- Storing `vs` from position `i` on: the entries land where they
should, the earlier positions are untouched, and it costs three units
per entry. -/
theorem storesFrom_run {a : String} {n : ℕ} :
    ∀ (vs : List ℕ) (i : ℕ) (σ : Env) (f : ℕ → ℕ), σ.arrs a = arrOf n f → i + vs.length ≤ n →
      ∃ (σ' : Env) (g : ℕ → ℕ), Run (storesFrom a i vs) σ σ' (3 * vs.length + 1) ∧
        σ'.arrs a = arrOf n g ∧ (∀ j < vs.length, g (i + j) = vs.getD j 0) ∧
        (∀ k < i, g k = f k) ∧ (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) ∧
        σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  intro vs
  induction vs with
  | nil =>
      intro i σ f harr _
      exact ⟨σ, f, Run.skip.mono (by simp), harr, by simp, fun _ _ => rfl,
        fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons v vs ih =>
      intro i σ f harr hlen
      simp only [List.length_cons] at hlen
      have hstore : Run (.store a (.lit i) (.lit v)) σ (σ.setArr a i v) 3 :=
        (Run.store rfl rfl (by rw [harr]; simpa using (by omega : i < n))).mono (by simp)
      obtain ⟨σ', g, hrun, hg, hgv, hgk, hb, hvars, hinp, hout⟩ :=
        ih (i + 1) (σ.setArr a i v) (fun k => if k = i then v else f k)
          (by simp [harr, set_arrOf]) (by omega)
      refine ⟨σ', g, (Run.seq hstore hrun).mono (by simp only [List.length_cons]; omega),
        hg, ?_, ?_, ?_, hvars, hinp, hout⟩
      · intro j hj
        match j with
        | 0 => simpa using hgk i (Nat.lt_succ_self i)
        | j + 1 =>
            rw [show i + (j + 1) = (i + 1) + j from by omega]
            simpa using hgv j (by simpa using hj)
      · intro k hk
        rw [hgk k (by omega)]
        simp [Nat.ne_of_lt hk]
      · intro b hbne
        rw [hb b hbne]; simp [hbne]

/-- Materializing a table generated from a function: the array is left
holding that very function. This is the form the schema uses — its three
tables are `arrOf` by construction — and it keeps the function out of
the existential, so the loops downstream can name it. -/
theorem stores_arrOf_run {a : String} {n : ℕ} {σ : Env} {f h : ℕ → ℕ}
    (harr : σ.arrs a = arrOf n f) :
    ∃ σ', Run (stores a (arrOf n h)) σ σ' (3 * n + 1) ∧ σ'.arrs a = arrOf n h ∧
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) ∧
      σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ', g, hrun, hg, hgv, _, hb, hvars, hinp, hout⟩ :=
    storesFrom_run (arrOf n h) 0 σ f harr (by simp)
  refine ⟨σ', hrun.mono (by simp), ?_, hb, hvars, hinp, hout⟩
  rw [hg]
  refine arrOf_congr fun i hi => ?_
  have hi' := hgv i (by simpa using hi)
  rw [Nat.zero_add] at hi'
  rw [hi', getD_arrOf h hi]

/-! ### Seeding

Every node is given its label's entry before the sweep starts, because a
node's children push into it earlier than it is reached itself. -/

/-- The invariant of `seedLoop`: the first `i` accumulators hold their
node's seed, and nothing else has moved. -/
def SeedInv (T : Table) (lab : ℕ → ℕ) (N : ℕ) (σ τ : Env) : Prop :=
  τ.vars "i" ≤ N ∧ τ.vars "N" = N ∧
  (∃ g, τ.arrs "acc" = arrOf N g ∧ ∀ i < τ.vars "i", g i = T.init (lab i)) ∧
  (∀ b, b ≠ "acc" → τ.arrs b = σ.arrs b) ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
  (∀ y, y ≠ "i" → τ.vars y = σ.vars y)

/-- Seeding the accumulators, at `13` per node. Two array reads and a
store per node: the label, then the table entry it names. -/
theorem seedLoop_run {T : Table} {lab : ℕ → ℕ} {N : ℕ} {σ : Env} {f : ℕ → ℕ}
    (hacc : σ.arrs "acc" = arrOf N f) (hlabarr : σ.arrs "lab" = arrOf N lab)
    (hini : σ.arrs "ini" = arrOf T.L T.init) (hN : σ.vars "N" = N)
    (hlab : ∀ i < N, lab i < T.L) :
    ∃ σ', Run seedLoop σ σ' (13 * N + 6) ∧
      σ'.arrs "acc" = arrOf N (fun i => T.init (lab i)) ∧
      (∀ b, b ≠ "acc" → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) := by
  have hstep : ∀ τ : Env, SeedInv T lab N σ τ →
      (Cond.lt (.var "i") (.var "N")).eval τ = some true →
      ∃ τ', Run (.seq (.store "acc" (.var "i") (.get "ini" (.get "lab" (.var "i"))))
        (.assign "i" (.add (.var "i") (.lit 1)))) τ τ' 9 ∧
        SeedInv T lab N σ τ' ∧ (N - τ'.vars "i") < (N - τ.vars "i") := by
    rintro τ ⟨hle, hNv, ⟨g, hg, hgv⟩, hb, hinp, hout, hy⟩ hcond
    have hlt : τ.vars "i" < N := by simp [hNv] at hcond; omega
    have hlabτ : τ.arrs "lab" = arrOf N lab := by rw [hb "lab" (by decide), hlabarr]
    have hiniτ : τ.arrs "ini" = arrOf T.L T.init := by rw [hb "ini" (by decide), hini]
    have heval : (Expr.get "ini" (.get "lab" (.var "i"))).eval τ =
        some (T.init (lab (τ.vars "i"))) := by
      simp [hlabτ, hiniτ, getElem?_arrOf _ hlt, getElem?_arrOf _ (hlab _ hlt)]
    refine ⟨_, (Run.seq (Run.store (idx := τ.vars "i") (by simp) heval (by simp [hg]; omega))
        (Run.assign (v := τ.vars "i" + 1) (by simp))).mono (by simp),
      ⟨by simp; omega, by simp [hNv], ?_, ?_, by simp [hinp], by simp [hout], ?_⟩, by simp; omega⟩
    · refine ⟨fun k => if k = τ.vars "i" then T.init (lab (τ.vars "i")) else g k,
        by simp [hg, set_arrOf], ?_⟩
      intro j hj
      simp at hj
      by_cases hje : j = τ.vars "i"
      · simp [hje]
      · simp only [if_neg hje]; exact hgv j (by omega)
    · intro b hbne; simp [hbne, hb b hbne]
    · intro y hy1; simp [hy1, hy y hy1]
  obtain ⟨σ', hrun, ⟨hle', hNv', ⟨g', hg', hgv'⟩, hb', hinp', hout', hy'⟩, hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "i") (.var "N"))
      (SeedInv T lab N σ) (fun τ => N - τ.vars "i") 9
      (fun τ _ => ⟨_, rfl⟩) hstep
      (σ := σ.setVar "i" 0)
      ⟨by simp, by simp [hN], ⟨f, by simp [hacc], by simp⟩, by simp, by simp, by simp,
        by intro y hy1; simp [hy1]⟩
  have hik : σ'.vars "i" = N := by simp [hNv'] at hfalse; omega
  rw [hik] at hgv'
  refine ⟨σ', (Run.seq (Run.assign (v := 0) rfl) hrun).mono (by simp; omega), ?_,
    fun b hbne => by simp [hb' b hbne], by simp [hinp'], by simp [hout'],
    fun y hy1 => by simp [hy' y hy1]⟩
  rw [hg']
  exact arrOf_congr hgv'

/-! ### The sweep

The one pass. Node `i` is finished when the loop reaches it — all of its
children are earlier — so it is pushed into its parent, which is later
and therefore still open. -/

/-- The invariant of `pushLoop`: the accumulator array *is* the pure
sweep after `i` pushes. There is nothing weaker to say — the array holds
partial folds at every node at once, and that is exactly what `sweep`
was defined to be. -/
def PushInv (T : Table) (par lab : ℕ → ℕ) (N : ℕ) (σ τ : Env) : Prop :=
  τ.vars "i" ≤ N - 1 ∧ τ.vars "N" = N ∧
  τ.arrs "acc" = arrOf N (sweep T par lab (τ.vars "i")) ∧
  (∀ b, b ≠ "acc" → τ.arrs b = σ.arrs b) ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
  (∀ y, y ≠ "i" → y ≠ "p" → τ.vars y = σ.vars y)

/-- The sweep, at `22` per node: every node holds its value afterwards.
This is the schema's theorem — `sweep_eq_val` turns the invariant into
the tree fold — and the cost is one visit per node, with no search for
children anywhere. -/
theorem pushLoop_run {T : Table} (hT : T.Wf) {par lab : ℕ → ℕ} {N : ℕ} {σ : Env}
    (hacc : σ.arrs "acc" = arrOf N (fun i => T.init (lab i)))
    (hpararr : σ.arrs "par" = arrOf N par)
    (hrow : σ.arrs "row" = arrOf T.V (fun a => a * T.V))
    (htab : σ.arrs "tab" = arrOf (T.V * T.V) (fun k => T.step (k / T.V) (k % T.V)))
    (hN : σ.vars "N" = N) (hNpos : 1 ≤ N)
    (hpar : ∀ i, i + 1 < N → i < par i ∧ par i < N)
    (hlab : ∀ i < N, lab i < T.L) :
    ∃ σ', Run pushLoop σ σ' (22 * N + 8) ∧
      σ'.arrs "acc" = arrOf N (val T par lab) ∧
      (∀ b, b ≠ "acc" → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ y, y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y) := by
  have hparN : ∀ i, i + 1 < N → par i < N := fun i hi => (hpar i hi).2
  have hstep : ∀ τ : Env, PushInv T par lab N σ τ →
      (Cond.lt (.var "i") (.sub (.var "N") (.lit 1))).eval τ = some true →
      ∃ τ', Run (.seq (.assign "p" (.get "par" (.var "i")))
        (.seq (.store "acc" (.var "p")
                (.get "tab" (.add (.get "row" (.get "acc" (.var "p")))
                  (.get "acc" (.var "i")))))
          (.assign "i" (.add (.var "i") (.lit 1))))) τ τ' 16 ∧
        PushInv T par lab N σ τ' ∧
        (N - 1 - τ'.vars "i") < (N - 1 - τ.vars "i") := by
    rintro τ ⟨hle, hNv, hg, hb, hinp, hout, hy⟩ hcond
    have hlt : τ.vars "i" < N - 1 := by simp [hNv] at hcond; omega
    have hjN : τ.vars "i" + 1 < N := by omega
    have hparτ : τ.arrs "par" = arrOf N par := by rw [hb "par" (by decide), hpararr]
    have hrowτ : τ.arrs "row" = arrOf T.V (fun a => a * T.V) := by
      rw [hb "row" (by decide), hrow]
    have htabτ : τ.arrs "tab" = arrOf (T.V * T.V) (fun k => T.step (k / T.V) (k % T.V)) := by
      rw [hb "tab" (by decide), htab]
    have hpj : par (τ.vars "i") < N := hparN _ hjN
    have hA : sweep T par lab (τ.vars "i") (par (τ.vars "i")) < T.V :=
      sweep_lt hT hlab hparN _ (by omega) _ hpj
    have hB : sweep T par lab (τ.vars "i") (τ.vars "i") < T.V :=
      sweep_lt hT hlab hparN _ (by omega) _ (by omega)
    have hV : 0 < T.V := Nat.lt_of_le_of_lt (Nat.zero_le _) hB
    -- the lookup lands inside the square table, and on the entry it should
    have hidx : sweep T par lab (τ.vars "i") (par (τ.vars "i")) * T.V +
        sweep T par lab (τ.vars "i") (τ.vars "i") < T.V * T.V := by
      calc sweep T par lab (τ.vars "i") (par (τ.vars "i")) * T.V +
            sweep T par lab (τ.vars "i") (τ.vars "i")
          < sweep T par lab (τ.vars "i") (par (τ.vars "i")) * T.V + T.V := by omega
        _ = (sweep T par lab (τ.vars "i") (par (τ.vars "i")) + 1) * T.V := by ring
        _ ≤ T.V * T.V := Nat.mul_le_mul_right _ (by omega)
    have hdiv : (sweep T par lab (τ.vars "i") (par (τ.vars "i")) * T.V +
        sweep T par lab (τ.vars "i") (τ.vars "i")) / T.V =
        sweep T par lab (τ.vars "i") (par (τ.vars "i")) := by
      rw [Nat.mul_comm _ T.V, Nat.mul_add_div hV, Nat.div_eq_of_lt hB, Nat.add_zero]
    have hmod : (sweep T par lab (τ.vars "i") (par (τ.vars "i")) * T.V +
        sweep T par lab (τ.vars "i") (τ.vars "i")) % T.V =
        sweep T par lab (τ.vars "i") (τ.vars "i") := by
      rw [Nat.mul_comm _ T.V, Nat.mul_add_mod, Nat.mod_eq_of_lt hB]
    -- the parent pointer
    have hpeval : (Expr.get "par" (.var "i")).eval τ = some (par (τ.vars "i")) := by
      simp [hparτ, getElem?_arrOf _ (show τ.vars "i" < N by omega)]
    -- the combination lookup, in the environment with `p` already set
    have hveval : (Expr.get "tab" (.add (.get "row" (.get "acc" (.var "p")))
        (.get "acc" (.var "i")))).eval (τ.setVar "p" (par (τ.vars "i"))) =
        some (T.step (sweep T par lab (τ.vars "i") (par (τ.vars "i")))
          (sweep T par lab (τ.vars "i") (τ.vars "i"))) := by
      simp [hg, hrowτ, htabτ, getElem?_arrOf _ hpj, getElem?_arrOf _ (show τ.vars "i" < N by omega),
        getElem?_arrOf _ hA, getElem?_arrOf _ hidx, hdiv, hmod]
    refine ⟨_, (Run.seq (Run.assign (v := par (τ.vars "i")) hpeval)
        (Run.seq (Run.store (idx := par (τ.vars "i")) (by simp) hveval (by simp [hg]; omega))
          (Run.assign (v := τ.vars "i" + 1) (by simp)))).mono (by simp),
      ⟨by simp; omega, by simp [hNv], ?_, ?_, by simp [hinp], by simp [hout], ?_⟩, by simp; omega⟩
    · simp only [vars_setVar, arrs_setVar, arrs_setArr, hg, set_arrOf]
      exact arrOf_congr fun k _ => (sweep_succ T par lab (τ.vars "i") k).symm
    · intro b hbne; simp [hbne, hb b hbne]
    · intro y hy1 hy2; simp [hy1, hy2, hy y hy1 hy2]
  obtain ⟨σ', hrun, ⟨hle', hNv', hg', hb', hinp', hout', hy'⟩, hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "i") (.sub (.var "N") (.lit 1)))
      (PushInv T par lab N σ) (fun τ => N - 1 - τ.vars "i") 16
      (fun τ _ => ⟨_, rfl⟩) hstep
      (σ := σ.setVar "i" 0)
      ⟨by simp, by simp [hN], by simpa [sweep_zero] using hacc, by simp, by simp, by simp,
        by intro y hy1 _; simp [hy1]⟩
  have hik : σ'.vars "i" = N - 1 := by simp [hNv'] at hfalse; omega
  rw [hik] at hg'
  refine ⟨σ', (Run.seq (Run.assign (v := 0) rfl) hrun).mono (by simp; omega), ?_,
    fun b hbne => by simp [hb' b hbne], by simp [hinp'], by simp [hout'],
    fun y hy1 hy2 => by simp [hy' y hy1 hy2]⟩
  rw [hg']
  exact arrOf_congr fun i hi =>
    sweep_eq_val T par lab (fun c hc => (hpar c (by omega)).1) (by omega)

/-! ### The schema, compilable -/

/-- The generated program fits its layout, whatever the table is: the
prologue's length depends on the table, its shape does not. -/
theorem foldCom_ok (T : Table) : Com.Ok layout (foldCom T) := by
  refine ⟨?_, ?_, ?_, storesFrom_ok ?_ ?_ 0 _, storesFrom_ok ?_ ?_ 0 _,
    storesFrom_ok ?_ ?_ 0 _, ?_, ?_, ?_⟩ <;>
    simp [readLoop, seedLoop, pushLoop, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

end Lax11Proofs.TreeFold
