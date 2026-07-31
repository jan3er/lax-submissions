import Lax13Proofs.Refine.NREST.Foreach

/-!
# RECT-compatible nested for combinators

Tower-expansion P2.B port of Sepreftime's pinned
`Examples/FloydWarshall/Recursion_Combinators.thy`.  The source proves its
recursive one-, two-, and three-index traversals equal nested `nfoldli`
walks over `[0..<n+1]`; Lean's `List.range (n + 1)` is that interval.
-/

namespace Lax13Proofs.Refine.NRest

variable {σ : Type}

/-- Source `for_rec`: visit `0, …, n` in ascending order. -/
noncomputable def forRec (f : σ → ℕ → NRest σ ECost) (a : σ) : ℕ → NRest σ ECost
  | 0 => f a 0
  | n + 1 => bindT (forRec f a n) fun x => f x (n + 1)

@[simp] theorem forRec_zero (f : σ → ℕ → NRest σ ECost) (a : σ) :
    forRec f a 0 = f a 0 := rfl

@[simp] theorem forRec_succ (f : σ → ℕ → NRest σ ECost) (a : σ) (n : ℕ) :
    forRec f a (n + 1) = bindT (forRec f a n) fun x => f x (n + 1) := rfl

/-- Right identity at ECost, needed by the source's singleton base case. -/
theorem bindT_returnT_ecost (M : NRest σ ECost) : bindT M returnT = M := by
  cases M with
  | fail => rfl
  | rest X =>
      rw [bindT_rest_eq_iSup,
        show (⨆ x, consumeB (returnT x : NRest σ ECost) (X x)) =
            ⨆ x, rest (single x (X x)) from
          iSup_congr fun x => consumeB_returnT x (X x), iSup_rest]
      congr 1
      funext v
      rw [iSup_apply]
      refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le v ?_)
      · by_cases h : v = x
        · subst h; simp
        · simp [h]
      · simp

/-- The source's `for_rec_eq`. -/
theorem forRec_eq (f : σ → ℕ → NRest σ ECost) (a : σ) (n : ℕ) :
    forRec f a n =
      nfoldli (fun _ => true) (fun k a => f a k) (List.range (n + 1)) a := by
  induction n with
  | zero =>
      simpa only [forRec_zero, Nat.zero_add, List.range_one, nfoldli_cons,
        if_pos, nfoldli_nil] using (bindT_returnT_ecost (f a 0)).symm
  | succ n ih =>
      rw [forRec_succ, ih]
      calc
        bindT (nfoldli (fun _ => true) (fun k a => f a k)
            (List.range (n + 1)) a) (fun x => f x (n + 1)) =
            bindT (nfoldli (fun _ => true) (fun k a => f a k)
              (List.range (n + 1)) a)
              (nfoldli (fun _ => true) (fun k a => f a k) [n + 1]) := by
                congr 1
                funext s
                simp only [nfoldli_cons, if_pos]
                exact (bindT_returnT_ecost (f s (n + 1))).symm
        _ = nfoldli (fun _ => true) (fun k a => f a k)
              (List.range (n + 1) ++ [n + 1]) a :=
            (nfoldli_append _ _ _ _ _).symm
        _ = nfoldli (fun _ => true) (fun k a => f a k)
              (List.range (n + 1 + 1)) a := by
            exact congrArg
              (fun l => nfoldli (fun _ => true) (fun k a => f a k) l a)
              (List.range_succ (n := n + 1)).symm

/-- Source `for_rec2'`, the proved closed form of its lexicographic
two-index recursion. `i,j` describe the current prefix endpoint. -/
noncomputable def forRec2 (f : σ → ℕ → ℕ → NRest σ ECost)
    (a : σ) (n i j : ℕ) : NRest σ ECost :=
  bindT
    (if i = 0 then returnT a
      else forRec (fun a i => forRec (fun a j => f a i j) a n) a (i - 1))
    fun a => forRec (fun a j => f a i j) a j

/-- Full square traversal as two nested `nfoldli`s. -/
theorem forRec2_eq (f : σ → ℕ → ℕ → NRest σ ECost) (a : σ) (n : ℕ) :
    forRec2 f a n n n =
      nfoldli (fun _ => true)
        (fun i => nfoldli (fun _ => true) (fun j a => f a i j)
          (List.range (n + 1))) (List.range (n + 1)) a := by
  have hrec : forRec2 f a n n n =
      forRec (fun a i => forRec (fun a j => f a i j) a n) a n := by
    cases n with
    | zero => simp [forRec2]
    | succ n => simp [forRec2, forRec_succ]
  rw [hrec, forRec_eq]
  congr 1
  funext i s
  exact forRec_eq (fun a j => f a i j) s n

/-- Source `for_rec3'`, the proved closed form of its lexicographic
three-index recursion. -/
noncomputable def forRec3 (f : σ → ℕ → ℕ → ℕ → NRest σ ECost)
    (a : σ) (n k i j : ℕ) : NRest σ ECost :=
  bindT
    (if k = 0 then returnT a
      else forRec (fun a k => forRec2 (fun a i j => f a k i j) a n n n) a (k - 1))
    fun a => forRec2 (fun a i j => f a k i j) a n i j

/-- Full cube traversal as three nested `nfoldli`s. -/
theorem forRec3_eq (f : σ → ℕ → ℕ → ℕ → NRest σ ECost) (a : σ) (n : ℕ) :
    forRec3 f a n n n n =
      nfoldli (fun _ => true)
        (fun k => nfoldli (fun _ => true)
          (fun i => nfoldli (fun _ => true) (fun j a => f a k i j)
            (List.range (n + 1))) (List.range (n + 1)))
        (List.range (n + 1)) a := by
  have hrec : forRec3 f a n n n n =
      forRec (fun a k => forRec2 (fun a i j => f a k i j) a n n n) a n := by
    cases n with
    | zero => simp [forRec3]
    | succ n => simp [forRec3, forRec_succ]
  rw [hrec, forRec_eq]
  congr 1
  funext k s
  exact forRec2_eq (fun a i j => f a k i j) s n

namespace ForGate

def step (a i j k : ℕ) : ℕ := a + 1 + i * 0 + j * 0 + k * 0

theorem cube_shape :
    forRec3 (fun a i j k => returnT (step a i j k)) 0 1 1 1 1 =
      nfoldli (fun _ => true)
        (fun k =>
          nfoldli (fun _ => true)
            (fun i =>
              nfoldli (fun _ => true) (fun j a => returnT (step a i j k))
                (List.range 2))
            (List.range 2))
        (List.range 2) 0 := by
  simpa using forRec3_eq (fun a i j k => returnT (step a i j k)) 0 1

/-- info: 'Lax13Proofs.Refine.NRest.ForGate.cube_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cube_shape

end ForGate

end Lax13Proofs.Refine.NRest
