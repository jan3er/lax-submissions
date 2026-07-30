import Lax13Proofs.Lib.Fill

/-!
The I/O harness: the prelude and the epilogue an IR program is wrapped
in so that it can be handed to `Transfer.Solves`.

The tower's programs have no tapes. `Ir.Com` reads and writes named
cells and named arrays and nothing else, and the code generator turns
one IR op into one IMP+ command, so what comes out of it is a *body*: a
command that computes with cells and arrays but never touches `inp` or
`out`. What `Transfer.Solves` asks for is a command that runs from
`initEnv ext x` — the input sitting on the tape, every array of the
length `ext` declares, every scalar zero — and leaves `f x` on the
output tape. The difference between the two is marshalling, and this
file is the marshalling, proved once in the `Spec` interface of
`Spec.lean` so that no program pays for it again.

Nothing here mentions the IR. The file lives under `Refine/Codegen/`
and in the `Codegen` namespace because that is the component it belongs
to, but it imports only the IMP+ kit; wave B's cashing theorem is where
the two halves meet.

### The four pieces

* **`readScalars xs`** — one `read` per name, in order. This is the
  whole of the scalar prelude: the input's first `|xs|` entries land in
  the cells `xs` names, at a cost of `|xs| + 1`.
* **`readArr a x m tmp`** — a counted scan filling the array `a` from
  the tape, as many entries as the cell `m` holds, with `x` the counter
  and `tmp` the cell the `read` lands in. The loop is
  `Spec.forRangeZero`'s and the body's store and counter bump are
  `Lib.Fill.put`'s, so what is new here is only the tape: the invariant
  carries `inp = ys.drop i ++ rest`, and the `read` is the one command
  of the body `Fill` does not already own. Cost `12·n + 6`.
* **`writeScalar r`** — one `write`, cost `2`.
* **`writeArr a x m`** — the entries of `a` below what `m` holds,
  appended to the output in index order; again a `Spec.forRangeZero`
  scan, cost `11·n + 6`.

### Two conventions, pinned here

*The array is pre-sized, never allocated.* `initEnv ext x` gives the
array `a` the length `ext a`, and `ext` is chosen per input by whoever
uses the simulation theorem — an algorithm sizes its arrays by what it
reads. The prelude therefore does not create the array; it *fills* an
array that already has the right length, by `store`, and the
correspondence `ext a = ys.length` is a hypothesis of every lemma below
that reads one. An IR `aset` requires its cell to exist, so this is
also what makes a generated body run at all.

*The length lives in a cell.* `Spec.forRangeZero` tests `x < m` on two
scalars, so the number of array entries to read is whatever the cell
`m` holds — which for the shapes below is one of the scalars the
prelude has just read. That is the length-prefixed input convention of
the repo, stated as a membership `(m, ys.length) ∈ xs.zip vs` rather
than as a separate argument.

P5/D-s: the design record sketched the array prelude as `readArr a n`
with the count a function `n : Env → ℕ` of the state. It is a cell
instead, because the loop rule of `Spec.lean` compares two *scalars* and
a state function would have to be materialized into one anyway — at
which point the caller owes the same membership, one command later and
with the cost of the assignment on top.

### The marshal descriptors

`ScalarsIn` and `ScalarsArrIn` say what a prelude leaves behind: the
named cells hold the input's entries, every other cell is still zero,
the arrays are what `ext` declared except the one that was filled, and
both tapes are where marshalling put them. They are the *interface* of
this file — a body's specification is written against one of them, and
the three glue lemmas at the end turn such a specification into a
statement about `initEnv`. Keeping them small is deliberate: everything
a body could want to know about its initial state is here, and nothing
else is promised.

### The three stock shapes

`marshal_scalars_scalar`, `marshal_scalarsArr_scalar` and
`marshal_scalarsArr_arr` are the design record's three descriptors,
each one `Spec` from `fun σ => σ = initEnv ext x` to `σ'.out = f x`
with the body's own specification as its single interesting hypothesis.
The body is asked for exactly two things: that it computes from the
descriptor, and that it is syntactically `NoWrite` — a generated body
has no `write` in it, so the second is `by decide` at every call site,
and the harness owes the output tape to nobody else.
-/

namespace Lax13Proofs.Codegen

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### A list as a cell function

`Fill` states what an array holds as `arrOf n g` for a cell function
`g`; the harness states it as the list of values that were read. These
two are the bridge, and it is needed in both directions: a list of
length `n` *is* an `arrOf`, and an entry of a list is a `getD`. -/

/-- An entry of a list, as the `getD` that `arrOf` produces. -/
theorem getD_eq_getElem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] :=
  (List.getElem_eq_getD 0).symm

/-- A list is the array of its own entries. -/
theorem arrOf_getD (l : List ℕ) : arrOf l.length (fun j => l.getD j 0) = l := by
  refine List.ext_getElem (by simp) (fun i h₁ h₂ => ?_)
  simp [arrOf, List.getElem?_eq_getElem h₂]

/-! ### The scalar prelude -/

/-- Read one input entry into each of the named cells, in order. -/
def readScalars : List String → Com
  | [] => .skip
  | x :: xs => .seq (.read x) (readScalars xs)

@[simp] theorem readScalars_nil : readScalars [] = .skip := rfl

@[simp] theorem readScalars_cons (x : String) (xs : List String) :
    readScalars (x :: xs) = .seq (.read x) (readScalars xs) := rfl

/-- The prelude assigns to exactly the cells it names. -/
@[simp] theorem wvars_readScalars (xs : List String) : (readScalars xs).wvars = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Com.wvars, ih]

/-- It stores into no array. -/
@[simp] theorem warrs_readScalars (xs : List String) : (readScalars xs).warrs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Com.warrs, ih]

/-- And it writes nothing. -/
@[simp] theorem noWrite_readScalars (xs : List String) : (readScalars xs).NoWrite := by
  induction xs with
  | nil => exact Com.noWrite_skip
  | cons x xs ih => exact ⟨trivial, ih⟩

/-- **The scalar prelude.** Started on a tape beginning with `vs`, one
entry per name, the prelude leaves each named cell holding its entry and
the tape advanced past them. The names have to be distinct: they are
read in order, and a name read twice would keep only its second entry.

The frame condition on the cells rides in the postcondition rather than
being left to `Spec.frame`, because the induction needs it one step at a
time — the head cell survives the tail only because the tail cannot
assign to it.

The cost is `|xs| + 1`: one for each `read`, and one for the `skip` the
recursion ends in (P5/D-q: the recursion is `foldr`-shaped rather than
special-casing the singleton, so the constant is `+1` and every caller
carries it; a marshalling constant is not worth a second equation). -/
theorem readScalars_spec (B : ℕ) (xs : List String) (vs rest : List ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) :
    Spec B (fun σ => σ.inp = vs ++ rest) (readScalars xs)
      (fun σ σ' => (∀ p ∈ xs.zip vs, σ'.vars p.1 = p.2) ∧ σ'.inp = rest ∧
        (∀ y, y ∉ xs → σ'.vars y = σ.vars y))
      (xs.length + 1) := by
  induction xs generalizing vs rest with
  | nil =>
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      refine Spec.skip.post ?_
      rintro σ σ' hσ rfl
      exact ⟨by simp, by simpa using hσ, fun _ _ => rfl⟩
  | cons x xs ih =>
      obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp at hlen
        | cons v vs' => exact ⟨v, vs', rfl⟩
      have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
      refine (Spec.seq (Spec.read (x := x) (v := fun _ => v) (rest := fun _ => vs' ++ rest)
          (fun σ hσ => by simpa using hσ))
        (ih vs' rest (List.nodup_cons.1 hnd).2 (by simpa using hlen))
        (fun σ σ' _ hq => by rw [hq]) ?_).mono (by simp only [List.length_cons]; omega)
      rintro σ σ' σ'' hσ rfl ⟨hzip, hinp, hfr⟩
      refine ⟨?_, hinp, fun y hy => ?_⟩
      · rintro ⟨y, w⟩ hp
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with hp | hp
        · rw [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simpa using hfr y hx
        · exact hzip _ hp
      · have hyx : y ≠ x := by rintro rfl; exact hy (List.mem_cons_self ..)
        rw [hfr y (fun h => hy (List.mem_cons_of_mem _ h))]
        simp [hyx]

/-! ### The array prelude -/

/-- Read as many further entries into the array `a` as the cell `m`
holds, in order: `x` is the counter, and each entry passes through `tmp`
on its way into the array. The array is *not* created — it already has
the length `ext` declared. -/
def readArr (a x m tmp : String) : Com :=
  .seq (.assign x (.lit 0))
    (.while (.lt (.var x) (.var m)) (.seq (.read tmp) (Fill.put a x (.var tmp))))

@[simp] theorem wvars_readArr (a x m tmp : String) :
    (readArr a x m tmp).wvars = [x, tmp, x] := by
  simp [readArr, Com.wvars]

@[simp] theorem warrs_readArr (a x m tmp : String) : (readArr a x m tmp).warrs = [a] := by
  simp [readArr, Com.warrs]

@[simp] theorem noWrite_readArr (a x m tmp : String) : (readArr a x m tmp).NoWrite := by
  simp [readArr, Com.NoWrite]

/-- **The array prelude.** The array has the right length already and
the cell `m` holds it; what comes back is the array holding exactly the
entries that were on the tape, the tape advanced past them, and the
counter at the end.

A turn costs `8` — the `read`'s `1` and `Fill.put`'s `7` — so the phase
costs `12·n + 6`. The four names have to be distinct in the three ways
the proof uses them: neither the counter nor the temporary may be the
length cell, and the `read` must not land on the counter. -/
theorem readArr_spec (B : ℕ) (a x m tmp : String) (ys rest : List ℕ)
    (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => (σ.arrs a).length = ys.length ∧ σ.vars m = ys.length ∧
        σ.inp = ys ++ rest)
      (readArr a x m tmp)
      (fun _ σ' => σ'.arrs a = ys ∧ σ'.inp = rest ∧ σ'.vars x = ys.length)
      (12 * ys.length + 6) := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ j, F j = ys.getD j 0 := ⟨_, fun _ => rfl⟩
  have hFe : ∀ j, (h : j < ys.length) → F j = ys[j] := fun j h => by
    rw [hF]; exact getD_eq_getElem h
  have hFB : ∀ j, j < ys.length → F j < B := fun j h => by
    rw [hFe j h]; exact hyB _ (List.getElem_mem h)
  have hFarr : arrOf ys.length F = ys := by
    rw [show F = fun j => ys.getD j 0 from funext hF]; exact arrOf_getD ys
  have hbody : Spec B
      (fun τ => (Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
        τ.inp = ys.drop (τ.vars x) ++ rest) ∧ τ.vars x < ys.length)
      (.seq (.read tmp) (Fill.put a x (.var tmp)))
      (fun τ τ' => (Fill.Below a x ys.length F τ' ∧ τ'.vars m = ys.length ∧
        τ'.inp = ys.drop (τ'.vars x) ++ rest) ∧ τ'.vars x = τ.vars x + 1) 8 := by
    refine (Spec.seq
      (Spec.read (x := tmp) (v := fun τ => F (τ.vars x))
        (rest := fun τ => ys.drop (τ.vars x + 1) ++ rest) ?_)
      ((Fill.put_spec B ys.length a x (.var tmp) F
        (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧ τ.vars x < ys.length ∧
          τ.vars tmp = F (τ.vars x) ∧ τ.inp = ys.drop (τ.vars x + 1) ++ rest)
        (fun τ hτ => ⟨hτ.1, hτ.2.2.1⟩) hnB
        (fun τ hτ => by
          rw [← hτ.2.2.2.1]
          exact evalB_var (by rw [hτ.2.2.2.1]; exact hFB _ hτ.2.2.1))).frame)
      ?_ ?_).mono (by simp)
    · rintro τ ⟨⟨-, -, hinp⟩, hlt⟩
      show τ.inp = F (τ.vars x) :: (ys.drop (τ.vars x + 1) ++ rest)
      rw [hinp, List.drop_eq_getElem_cons hlt, hFe _ hlt, List.cons_append]
    · rintro τ τ' ⟨⟨hb, hm, -⟩, hlt⟩ rfl
      exact ⟨hb.of_eq (by simp) (by simp [Ne.symm htx]), by simpa [Ne.symm htm] using hm,
        by simpa [Ne.symm htx] using hlt, by simp [Ne.symm htx], by simp [Ne.symm htx]⟩
    · rintro τ τ' τ'' ⟨⟨-, hm, -⟩, hlt⟩ rfl ⟨⟨hb'', hxx⟩, hfv, -, hfi, -⟩
      simp only [vars_setVar, if_neg (Ne.symm htx)] at hxx
      refine ⟨⟨hb'', ?_, ?_⟩, hxx⟩
      · rw [hfv m (by simp [Ne.symm hxm])]
        simpa [Ne.symm htm] using hm
      · rw [hfi (by simp), hxx]
  refine (((Spec.forRangeZero x m
    (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
      τ.inp = ys.drop (τ.vars x) ++ rest)
    ys.length 8 hnB (fun τ hτ => hτ.1.le) (fun τ hτ => hτ.2.1) hbody).pre ?_).post ?_).mono
      (by omega)
  · rintro σ ⟨hlen, hm, hinp⟩
    refine ⟨Fill.below_zero (g := fun j => (σ.arrs a).getD j 0) ?_ (by simp), ?_, ?_⟩
    · rw [arrs_setVar, ← hlen, arrOf_getD]
    · simpa [Ne.symm hxm] using hm
    · simp [hinp]
  · rintro σ σ' - ⟨⟨hb, -, hinp⟩, hxe⟩
    obtain ⟨g, harr, hg⟩ := hb.done hxe
    exact ⟨by rw [harr, arrOf_congr hg, hFarr], by rw [hinp, hxe]; simp, hxe⟩

/-- The prelude of the length-prefixed shape: the scalars, then the
array whose length is one of them. -/
def readScalarsThenArr (xs : List String) (a x m tmp : String) : Com :=
  .seq (readScalars xs) (readArr a x m tmp)

@[simp] theorem noWrite_readScalarsThenArr (xs : List String) (a x m tmp : String) :
    (readScalarsThenArr xs a x m tmp).NoWrite :=
  ⟨noWrite_readScalars xs, noWrite_readArr a x m tmp⟩

/-! ### The epilogues -/

/-- Write one cell to the output. -/
def writeScalar (r : String) : Com := .write (.var r)

@[simp] theorem wvars_writeScalar (r : String) : (writeScalar r).wvars = [] := rfl

@[simp] theorem warrs_writeScalar (r : String) : (writeScalar r).warrs = [] := rfl

@[simp] theorem not_reads_writeScalar (r : String) : ¬ (writeScalar r).reads := by
  simp [writeScalar, Com.reads]

/-- **One value out**, at a cost of `2`. The postcondition is the
environment itself: an epilogue that appends one entry changes nothing
else, and saying so as an equality saves every caller a frame. -/
theorem writeScalar_spec (B : ℕ) (r : String) (v : ℕ) (hv : v < B) :
    Spec B (fun σ => σ.vars r = v) (writeScalar r)
      (fun σ σ' => σ' = { σ with out := σ.out ++ [v] }) 2 :=
  (Spec.write (e := .var r) (f := fun _ => v) (fun σ hσ => by
    have h : σ.vars r < B := by rw [hσ]; exact hv
    simpa [hσ] using evalB_var h)).mono (by simp)

/-- Write the entries of `a` below what `m` holds to the output, in
index order, with `x` the counter. -/
def writeArr (a x m : String) : Com :=
  .seq (.assign x (.lit 0))
    (.while (.lt (.var x) (.var m))
      (.seq (.write (.get a (.var x))) (.assign x (.add (.var x) (.lit 1)))))

@[simp] theorem wvars_writeArr (a x m : String) : (writeArr a x m).wvars = [x, x] := by
  simp [writeArr, Com.wvars]

@[simp] theorem warrs_writeArr (a x m : String) : (writeArr a x m).warrs = [] := by
  simp [writeArr, Com.warrs]

@[simp] theorem not_reads_writeArr (a x m : String) : ¬ (writeArr a x m).reads := by
  simp [writeArr, Com.reads]

/-- **The array epilogue.** The whole of `a` — which is `A`, and whose
length the cell `m` holds — is appended to the output in index order. A
turn costs `7`, the `write`'s `3` and the bump's `4`, so the phase costs
`11·n + 6`.

The postcondition is relational in the output tape, as every tape
statement in the kit is: what the epilogue promises is that it *added*
`A`, not what the tape then is. -/
theorem writeArr_spec (B : ℕ) (a x m : String) (A : List ℕ)
    (hxm : x ≠ m) (hnB : A.length < B) (hAB : ∀ v ∈ A, v < B) :
    Spec B (fun σ => σ.arrs a = A ∧ σ.vars m = A.length) (writeArr a x m)
      (fun σ σ' => σ'.out = σ.out ++ A ∧ σ'.vars x = A.length) (11 * A.length + 6) := by
  intro σ hσ
  set I : Env → Prop := fun τ => τ.arrs a = A ∧ τ.vars m = A.length ∧ τ.vars x ≤ A.length ∧
    τ.out = σ.out ++ A.take (τ.vars x) with hI
  have hbody : Spec B (fun τ => I τ ∧ τ.vars x < A.length)
      (.seq (.write (.get a (.var x))) (.assign x (.add (.var x) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars x = τ.vars x + 1) 7 := by
    refine (Spec.seq
      (Spec.write (e := .get a (.var x)) (f := fun τ => A.getD (τ.vars x) 0) ?_)
      (Spec.assign (P := fun τ => τ.vars x < A.length) (x := x)
        (e := .add (.var x) (.lit 1)) (f := fun τ => τ.vars x + 1) ?_)
      (fun τ τ' hτ hq => by rw [hq]; simpa using hτ.2)
      ?_).mono (by simp)
    · rintro τ ⟨⟨harr, -, -, -⟩, hlt⟩
      show (Expr.get a (Expr.var x)).evalB B τ = some (A.getD (τ.vars x) 0)
      refine evalB_get (evalB_var (by omega)) ?_ ?_
      · rw [harr, getD_eq_getElem hlt]
        exact List.getElem?_eq_getElem hlt
      · rw [getD_eq_getElem hlt]; exact hAB _ (List.getElem_mem hlt)
    · rintro τ hlt
      show (Expr.bin .add (.var x) (.lit 1)).evalB B τ = some (τ.vars x + 1)
      exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using by omega)
    · rintro τ τ' τ'' ⟨⟨harr, hm, -, hout⟩, hlt⟩ rfl rfl
      refine ⟨⟨by simpa using harr, by simpa [Ne.symm hxm] using hm, by simp; omega, ?_⟩,
        by simp⟩
      have hstep : A.take (τ.vars x + 1) = A.take (τ.vars x) ++ [A.getD (τ.vars x) 0] := by
        rw [getD_eq_getElem hlt, List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      simp [hout, hstep]
  obtain ⟨σ', hrun, hIe, hxe⟩ :=
    (Spec.forRangeZero x m I A.length 7 hnB (fun τ hτ => hτ.2.2.1) (fun τ hτ => hτ.2.1)
      hbody).run (show I (σ.setVar x 0) from
        ⟨by simpa using hσ.1, by simpa [Ne.symm hxm] using hσ.2, by simp, by simp⟩)
  exact ⟨σ', hrun.mono (by omega), by rw [hIe.2.2.2, hxe, List.take_length], hxe⟩

/-! ### The marshal descriptors

What a prelude leaves behind, as the precondition a body's
specification is written against. -/

/-- The scalar shape: the named cells hold the input, every other cell
is still zero, every array is what `ext` declared, and both tapes are
empty. -/
def ScalarsIn (ext : String → ℕ) (xs : List String) (vs : List ℕ) (σ : Env) : Prop :=
  (∀ p ∈ xs.zip vs, σ.vars p.1 = p.2) ∧ (∀ y, y ∉ xs → σ.vars y = 0) ∧
    (∀ b, σ.arrs b = List.replicate (ext b) 0) ∧ σ.inp = [] ∧ σ.out = []

namespace ScalarsIn

variable {ext : String → ℕ} {xs : List String} {vs : List ℕ} {σ : Env}

/-- The cells the input was read into. -/
theorem cells (h : ScalarsIn ext xs vs σ) : ∀ p ∈ xs.zip vs, σ.vars p.1 = p.2 := h.1

/-- Every other cell is still zero. -/
theorem zero (h : ScalarsIn ext xs vs σ) : ∀ y, y ∉ xs → σ.vars y = 0 := h.2.1

/-- Every array is what `ext` declared. -/
theorem arrs (h : ScalarsIn ext xs vs σ) : ∀ b, σ.arrs b = List.replicate (ext b) 0 := h.2.2.1

/-- The input tape is spent. -/
theorem inp (h : ScalarsIn ext xs vs σ) : σ.inp = [] := h.2.2.2.1

/-- Nothing has been written yet. -/
theorem out (h : ScalarsIn ext xs vs σ) : σ.out = [] := h.2.2.2.2

end ScalarsIn

/-- The scalars-and-array shape: as above, except that `a` now holds the
entries that followed the scalars on the tape, the counter `x` stands at
their number, and the temporary `tmp` is spent.

P5/D-t: the counter and the temporary are *excluded* from the clause
that says every unnamed cell is still zero, rather than being cleared by
two more assignments. The prelude spends them and says so; a body that
wants them zero can zero them, and a body that reuses the counter's
value — which is the array's length, and often wanted — gets it for
free. -/
def ScalarsArrIn (ext : String → ℕ) (xs : List String) (a x tmp : String)
    (vs ys : List ℕ) (σ : Env) : Prop :=
  (∀ p ∈ xs.zip vs, σ.vars p.1 = p.2) ∧ σ.arrs a = ys ∧ σ.vars x = ys.length ∧
    (∀ y, y ∉ xs → y ≠ x → y ≠ tmp → σ.vars y = 0) ∧
    (∀ b, b ≠ a → σ.arrs b = List.replicate (ext b) 0) ∧ σ.inp = [] ∧ σ.out = []

namespace ScalarsArrIn

variable {ext : String → ℕ} {xs : List String} {a x tmp : String} {vs ys : List ℕ} {σ : Env}

/-- The cells the scalars were read into. -/
theorem cells (h : ScalarsArrIn ext xs a x tmp vs ys σ) :
    ∀ p ∈ xs.zip vs, σ.vars p.1 = p.2 := h.1

/-- The array holds what followed the scalars on the tape. -/
theorem arr (h : ScalarsArrIn ext xs a x tmp vs ys σ) : σ.arrs a = ys := h.2.1

/-- The counter stands at the number of entries read. -/
theorem count (h : ScalarsArrIn ext xs a x tmp vs ys σ) : σ.vars x = ys.length := h.2.2.1

/-- Every cell but the named ones, the counter and the temporary is
still zero. -/
theorem zero (h : ScalarsArrIn ext xs a x tmp vs ys σ) :
    ∀ y, y ∉ xs → y ≠ x → y ≠ tmp → σ.vars y = 0 := h.2.2.2.1

/-- Every other array is what `ext` declared. -/
theorem arrs (h : ScalarsArrIn ext xs a x tmp vs ys σ) :
    ∀ b, b ≠ a → σ.arrs b = List.replicate (ext b) 0 := h.2.2.2.2.1

/-- The input tape is spent. -/
theorem inp (h : ScalarsArrIn ext xs a x tmp vs ys σ) : σ.inp = [] := h.2.2.2.2.2.1

/-- Nothing has been written yet. -/
theorem out (h : ScalarsArrIn ext xs a x tmp vs ys σ) : σ.out = [] := h.2.2.2.2.2.2

end ScalarsArrIn

/-! ### The preludes at `initEnv` -/

/-- **The scalar prelude on an initial environment**, with whatever it
did not read left on the tape. This is the form the length-prefixed
shape composes with; the shape that reads nothing else is the case
`rest = []` below. -/
theorem readScalars_initEnv_rest_spec (B : ℕ) (ext : String → ℕ) (xs : List String)
    (vs rest : List ℕ) (hnd : xs.Nodup) (hlen : vs.length = xs.length) :
    Spec B (fun σ => σ = initEnv ext (vs ++ rest)) (readScalars xs)
      (fun _ σ' => (∀ p ∈ xs.zip vs, σ'.vars p.1 = p.2) ∧ (∀ y, y ∉ xs → σ'.vars y = 0) ∧
        (∀ b, σ'.arrs b = List.replicate (ext b) 0) ∧ σ'.inp = rest ∧ σ'.out = [])
      (xs.length + 1) := by
  refine ((readScalars_spec B xs vs rest hnd hlen).frame.pre
    (fun σ hσ => by rw [hσ]; rfl)).post ?_
  rintro σ σ' rfl ⟨⟨hzip, hinp, hfr⟩, -, hfa, -, hout⟩
  exact ⟨hzip, fun y hy => by rw [hfr y hy]; rfl, fun b => by rw [hfa b (by simp)]; rfl,
    hinp, by rw [hout (noWrite_readScalars xs)]; rfl⟩

/-- **The scalar prelude at `initEnv`**, in descriptor form. -/
theorem readScalars_initEnv_spec (B : ℕ) (ext : String → ℕ) (xs : List String) (vs : List ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) :
    Spec B (fun σ => σ = initEnv ext vs) (readScalars xs)
      (fun _ σ' => ScalarsIn ext xs vs σ') (xs.length + 1) :=
  (readScalars_initEnv_rest_spec B ext xs vs [] hnd hlen).pre
    (fun σ hσ => by rw [hσ]; simp)

/-- **The length-prefixed prelude at `initEnv`.** The scalars come
first, one of them is the array's length, and the array's declared
length has to agree with it — the pre-sizing convention, as a
hypothesis. The counter and the temporary must be names of their own,
or the prelude would overwrite what it had just read.

The cost is the two phases': `|xs| + 12·n + 7`. -/
theorem readScalarsThenArr_spec (B : ℕ) (ext : String → ℕ) (xs : List String)
    (a x m tmp : String) (vs ys : List ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) (hm : (m, ys.length) ∈ xs.zip vs)
    (hx : x ∉ xs) (htmp : tmp ∉ xs) (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hext : ext a = ys.length) (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => σ = initEnv ext (vs ++ ys)) (readScalarsThenArr xs a x m tmp)
      (fun _ σ' => ScalarsArrIn ext xs a x tmp vs ys σ')
      (xs.length + 12 * ys.length + 7) := by
  refine (Spec.seq (readScalars_initEnv_rest_spec B ext xs vs ys hnd hlen)
    ((readArr_spec B a x m tmp ys [] hxm htm htx hnB hyB).frame) ?_ ?_).mono (by omega)
  · rintro σ σ' - ⟨hzip, -, harr, hinp, -⟩
    exact ⟨by rw [harr a]; simp [hext], hzip _ hm, by simp [hinp]⟩
  · rintro σ σ' σ'' - ⟨hzip, hzero, harr, -, hout⟩ ⟨⟨harr', hinp', hcnt'⟩, hfv, hfa, -, hfo⟩
    have hne : ∀ p ∈ xs.zip vs, p.1 ≠ x ∧ p.1 ≠ tmp := fun p hp => by
      have hp1 : p.1 ∈ xs := (List.of_mem_zip hp).1
      exact ⟨fun h => hx (h ▸ hp1), fun h => htmp (h ▸ hp1)⟩
    refine ⟨fun p hp => ?_, harr', hcnt', fun y hy hyx hyt => ?_, fun b hb => ?_, hinp', ?_⟩
    · rw [hfv p.1 (by simp [(hne p hp).1, (hne p hp).2])]
      exact hzip p hp
    · rw [hfv y (by simp [hyx, hyt])]; exact hzero y hy
    · rw [hfa b (by simp [hb])]; exact harr b
    · rw [hfo (noWrite_readArr a x m tmp)]; exact hout

/-! ### The three stock shapes

Each of these is the design record's marshal descriptor, assembled: the
prelude establishes the descriptor, the body computes from it, the
epilogue puts the answer on the tape, and what comes out is one `Spec`
from `initEnv`. The body's own specification is the only interesting
hypothesis; the rest are the distinctness and pre-sizing side conditions
the preludes already asked for.

P5/D-r: the body is asked for `Com.NoWrite` and nothing else about the
tapes. A body that read the (empty) input tape could not get a
derivation, so `¬ body.reads` would be a hypothesis with no work to do;
`NoWrite` is the one the output-tape frame needs, and on generated
syntax it is `by decide`. -/

/-- **Shape 1: a scalar tuple in, one scalar out.** -/
theorem marshal_scalars_scalar (B : ℕ) (ext : String → ℕ) (xs : List String) (r : String)
    (vs : List ℕ) (body : Com) (Kb res : ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) (hnw : body.NoWrite) (hres : res < B)
    (hbody : Spec B (ScalarsIn ext xs vs) body (fun _ σ' => σ'.vars r = res) Kb) :
    Spec B (fun σ => σ = initEnv ext vs)
      (.seq (readScalars xs) (.seq body (writeScalar r)))
      (fun _ σ' => σ'.out = [res]) (xs.length + Kb + 3) := by
  have htail : Spec B (ScalarsIn ext xs vs) (.seq body (writeScalar r))
      (fun σ σ'' => σ''.out = σ.out ++ [res]) (Kb + 2) :=
    Spec.seq hbody.frame (writeScalar_spec B r res hres) (fun _ _ _ hq => hq.1)
      (fun _ _ _ _ hq hq' => by simp [hq', hq.2.2.2.2 hnw])
  exact (Spec.seq (readScalars_initEnv_spec B ext xs vs hnd hlen) htail
    (fun _ _ _ hq => hq)
    (fun _ _ _ _ hq hq' => by rw [hq', hq.out]; simp)).mono (by omega)

/-- **Shape 2: scalars and an array in, one scalar out.** -/
theorem marshal_scalarsArr_scalar (B : ℕ) (ext : String → ℕ) (xs : List String)
    (a x m tmp r : String) (vs ys : List ℕ) (body : Com) (Kb res : ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) (hm : (m, ys.length) ∈ xs.zip vs)
    (hx : x ∉ xs) (htmp : tmp ∉ xs) (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hext : ext a = ys.length) (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B)
    (hnw : body.NoWrite) (hres : res < B)
    (hbody : Spec B (ScalarsArrIn ext xs a x tmp vs ys) body
      (fun _ σ' => σ'.vars r = res) Kb) :
    Spec B (fun σ => σ = initEnv ext (vs ++ ys))
      (.seq (readScalarsThenArr xs a x m tmp) (.seq body (writeScalar r)))
      (fun _ σ' => σ'.out = [res]) (xs.length + 12 * ys.length + Kb + 9) := by
  have htail : Spec B (ScalarsArrIn ext xs a x tmp vs ys) (.seq body (writeScalar r))
      (fun σ σ'' => σ''.out = σ.out ++ [res]) (Kb + 2) :=
    Spec.seq hbody.frame (writeScalar_spec B r res hres) (fun _ _ _ hq => hq.1)
      (fun _ _ _ _ hq hq' => by simp [hq', hq.2.2.2.2 hnw])
  exact (Spec.seq (readScalarsThenArr_spec B ext xs a x m tmp vs ys hnd hlen hm hx htmp
      hxm htm htx hext hnB hyB) htail
    (fun _ _ _ hq => hq)
    (fun _ _ _ _ hq hq' => by rw [hq', hq.out]; simp)).mono (by omega)

/-- **Shape 3: scalars and an array in, an array out** — the shape P7's
BFS has. The body says which array holds the answer and which cell holds
its length; the epilogue needs its own counter, distinct from that
cell. -/
theorem marshal_scalarsArr_arr (B : ℕ) (ext : String → ℕ) (xs : List String)
    (a x m tmp c y m' : String) (vs ys res : List ℕ) (body : Com) (Kb : ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) (hm : (m, ys.length) ∈ xs.zip vs)
    (hx : x ∉ xs) (htmp : tmp ∉ xs) (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hext : ext a = ys.length) (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B)
    (hym : y ≠ m') (hresN : res.length < B) (hresB : ∀ v ∈ res, v < B)
    (hnw : body.NoWrite)
    (hbody : Spec B (ScalarsArrIn ext xs a x tmp vs ys) body
      (fun _ σ' => σ'.arrs c = res ∧ σ'.vars m' = res.length) Kb) :
    Spec B (fun σ => σ = initEnv ext (vs ++ ys))
      (.seq (readScalarsThenArr xs a x m tmp) (.seq body (writeArr c y m')))
      (fun _ σ' => σ'.out = res)
      (xs.length + 12 * ys.length + Kb + 11 * res.length + 13) := by
  have htail : Spec B (ScalarsArrIn ext xs a x tmp vs ys) (.seq body (writeArr c y m'))
      (fun σ σ'' => σ''.out = σ.out ++ res) (Kb + (11 * res.length + 6)) :=
    Spec.seq hbody.frame (writeArr_spec B c y m' res hym hresN hresB)
      (fun _ _ _ hq => hq.1)
      (fun _ _ _ _ hq hq' => by rw [hq'.1, hq.2.2.2.2 hnw])
  exact (Spec.seq (readScalarsThenArr_spec B ext xs a x m tmp vs ys hnd hlen hm hx htmp
      hxm htm htx hext hnB hyB) htail
    (fun _ _ _ hq => hq)
    (fun _ _ _ _ hq hq' => by rw [hq', hq.out]; simp)).mono (by omega)

/-! ### The gates

The specifications above are read off the machine, not only proved: two
small programs built from the harness alone are compiled and run, and
what they leave on the output tape is `#guard`ed together with the
number of machine steps it took. The second gate carries a negative
control — the array epilogue writes the entries in index order, and the
reversal is pinned as *not* what comes out.

The step counts are also checked against the cost this file claims:
`compileProgram` costs at most `L.const` machine steps per unit of IMP+
cost, so `steps ≤ L.const * K` is a genuine cross-check of the constants
in the specifications above, and the one thing a `#guard` on the output
alone would not catch. -/

namespace Gate

open Lax13Proofs.Compile

/-! #### Shape 1: two scalars in, one scalar out

The body is one assignment, chosen so that the number written pins
*both* cells: `p + 10·q` on the input `[7, 9]` is `97` and nothing
else. -/

/-- Read two numbers and write `p + 10·q`. -/
def scalarsBody : Com :=
  .assign "s" (.add (.var "p") (.mul (.var "q") (.lit 10)))

/-- The whole program, in the shape `marshal_scalars_scalar` is about. -/
def scalarsCom : Com :=
  .seq (readScalars ["p", "q"]) (.seq scalarsBody (writeScalar "s"))

/-- **The gate on the specification side.** Every hypothesis of shape 1
is discharged on concrete syntax, and what comes out is the statement
wave B will end at: from `initEnv`, the output tape is `[97]`, at a cost
of `11`. -/
theorem scalarsCom_spec (B : ℕ) (hB : 97 < B) (ext : String → ℕ) :
    Spec B (fun σ => σ = initEnv ext [7, 9]) scalarsCom
      (fun _ σ' => σ'.out = [97]) 11 := by
  have hbody : Spec B (ScalarsIn ext ["p", "q"] [7, 9]) scalarsBody
      (fun _ σ' => σ'.vars "s" = 97) 6 := by
    refine (Spec.assign (f := fun _ => 97) (x := "s")
      (e := .add (.var "p") (.mul (.var "q") (.lit 10))) ?_).post ?_
    · intro σ h
      have hp : σ.vars "p" = 7 := h.cells ("p", 7) (by simp)
      have hq : σ.vars "q" = 9 := h.cells ("q", 9) (by simp)
      have h1 : (Expr.var "q").evalB B σ = some 9 := by rw [← hq]; exact evalB_var (by omega)
      have h2 : (Expr.var "p").evalB B σ = some 7 := by rw [← hp]; exact evalB_var (by omega)
      have h3 : (Expr.mul (.var "q") (.lit 10)).evalB B σ = some 90 := by
        simpa using evalB_bin (op := .mul) h1 (evalB_lit (B := B) (n := 10) (by omega))
          (by show 9 * 10 < B; omega)
      simpa using evalB_bin (op := .add) h2 h3 (by show 7 + 90 < B; omega)
    · rintro σ σ' - rfl
      simp
  exact (marshal_scalars_scalar B ext ["p", "q"] "s" [7, 9] scalarsBody 6 97
    (by simp) rfl (by simp [scalarsBody, Com.NoWrite]) hB hbody).mono (by simp)

/-- Three scalars, no arrays, two temporaries. -/
def scalarsLayout : Layout := ⟨["p", "q", "s"], [], 2⟩

theorem scalarsCom_ok : Com.Ok scalarsLayout scalarsCom := by
  simp [scalarsCom, scalarsBody, writeScalar, scalarsLayout, Com.Ok, Expr.Ok]

/-- The machine program. -/
def scalarsProg : Lax13.Ram.Program := compileProgram scalarsLayout scalarsCom

/-- Run it on `[7, 9]`. -/
def scalarsRun : Option (List ℕ × ℕ) :=
  runOut 16 1000 scalarsProg (Lax13.Ram.initState [7, 9]) 0

/-! The two cells hold what the two `read`s put in them, in that order:
`7 + 10·9`, and no other pair of the two entries gives `97`. -/

#guard scalarsRun.map Prod.fst = some [97]

/-! **The negative control**: the cells are not read the other way
round, which would give `9 + 10·7 = 79`. -/

#guard scalarsRun.map Prod.fst ≠ some [79]

/-! And the run stays inside the cost `scalarsCom_spec` claims: the
compiler costs at most `L.const` machine steps per unit of IMP+ cost. -/

#guard (scalarsRun.map Prod.snd).getD 0 ≤ scalarsLayout.const * 11

/-! #### Shape 3: a length-prefixed array in, an array out

The body is `skip`, so what the gate exercises is the marshalling
itself: the array that comes back out is the array that went in. -/

/-- Read a length and that many numbers, do nothing, write them out. -/
def arrCom : Com :=
  .seq (readScalarsThenArr ["n"] "A" "i" "n" "t") (.seq .skip (writeArr "A" "j" "n"))

/-- The array `A` is declared with room for the three entries that
follow the length on the tape — the pre-sizing convention. -/
def arrExt : String → ℕ := fun b => if b = "A" then 3 else 0

/-- **The gate on the specification side**, shape 3 at `ext = arrExt`
and the input `[3, 5, 6, 7]`: the output tape is the array, at a cost of
`84`. -/
theorem arrCom_spec (B : ℕ) (hB : 7 < B) :
    Spec B (fun σ => σ = initEnv arrExt ([3] ++ [5, 6, 7])) arrCom
      (fun _ σ' => σ'.out = [5, 6, 7]) 84 := by
  have hbody : Spec B (ScalarsArrIn arrExt ["n"] "A" "i" "t" [3] [5, 6, 7]) .skip
      (fun _ σ' => σ'.arrs "A" = [5, 6, 7] ∧ σ'.vars "n" = [5, 6, 7].length) 1 :=
    Spec.skip.post (by
      rintro σ σ' h rfl
      exact ⟨h.arr, by simpa using h.cells ("n", 3) (by simp)⟩)
  have hvB : ∀ v ∈ [5, 6, 7], v < B := by simp; omega
  have hnB : [5, 6, 7].length < B := by simp; omega
  exact (marshal_scalarsArr_arr B arrExt ["n"] "A" "i" "n" "t" "A" "j" "n" [3] [5, 6, 7]
    [5, 6, 7] .skip 1 (by simp) rfl (by simp) (by simp) (by simp) (by decide) (by decide)
    (by decide) (by simp [arrExt]) hnB hvB (by decide) hnB hvB
    Com.noWrite_skip hbody).mono (by simp)

/-- Four scalars — the length, the two counters and the temporary — one
array, two temporaries. -/
def arrLayout : Layout := ⟨["n", "i", "t", "j"], ["A"], 2⟩

theorem arrCom_ok : Com.Ok arrLayout arrCom := by
  simp [arrCom, readScalarsThenArr, readArr, writeArr, Fill.put, arrLayout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

/-- The machine program. -/
def arrProg : Lax13.Ram.Program := compileProgram arrLayout arrCom

/-- Run it on `[3, 5, 6, 7]`. -/
def arrRun : Option (List ℕ × ℕ) :=
  runOut 16 5000 arrProg (Lax13.Ram.initState [3, 5, 6, 7]) 0

/-! The array comes back in index order. -/

#guard arrRun.map Prod.fst = some [5, 6, 7]

/-! **The negative control.** Index order is not reverse index order,
and a `writeArr` that counted down would still write three entries and
fail only here. -/

#guard arrRun.map Prod.fst ≠ some [7, 6, 5]

/-! And the run stays inside the cost `arrCom_spec` claims. -/

#guard (arrRun.map Prod.snd).getD 0 ≤ arrLayout.const * 84

end Gate

end Lax13Proofs.Codegen
