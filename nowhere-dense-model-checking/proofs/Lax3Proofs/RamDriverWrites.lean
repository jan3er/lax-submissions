import Lax3Proofs.RamDriverCompose
import Lax3Proofs.RamDriverDescend

/-!
**What the driver writes, read off its text.**

`Lax3Proofs.RamDriverCluster.InnerFrames` is a frame of the *nested*
driver, and `inner` is a program variable there: the obligation says
nothing about it, so a caller that wants to instantiate the nested call
with `RamDriver.driverAt … (j + 1)` has to know what that program writes.
This file is that knowledge.

# The invariant

A level at depth `d` writes

* fixed scratch names — the engines' arrays, the search's, the cover's
  and the calling convention's — every one of which is a literal of
  letters, and
* per-depth names at depths **at or above** `d`.

So an array or a scalar of a depth *below* `d` survives the whole
recursion, and that is `belowArr_notMem_warrs_driverAt` and
`belowVar_notMem_wvars_driverAt` at the end.

# How it is proved

Two ideas, and no case analysis over the fifty-odd literals of a phase.

* **A per-depth name carries a digit and a literal does not.**
  `HasDigit` is that predicate; `∀ a ∈ <a concrete list>, ¬ HasDigit a`
  is `decide`, and every one of the phases' write sets is a concrete
  list of literals together with the handful of per-depth names the
  phase's own text mentions. So each phase contributes one lemma of the
  form "an array it writes either carries no digit or is one of *these*".
* **The depth is recoverable from the name.** Every per-depth name is a
  fixed prefix with a decimal numeral appended, and
  `RamDriverBase.toString_inj` reads the numeral back, so
  `ordName b = ordName d` forces `b = d`. That is what turns "the phase
  writes the depth's own order array" into "it does not write an earlier
  depth's".

The recursion itself is then one induction on the fuel `ℓ - d`, with the
base case `RamDriverBot.warrs_baseCom`.

The ordering phase is taken at `R = 0`, which is where
`RamDriverCompose.orderImplements₀` is: at `R > 0` the augmentation fold
is not `Com.skip` and its write set is the augmentation round's, which
this file does not read.
-/

namespace Lax3Proofs.RamDriverWrites

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverFrames (scratchArrs underscore_notMem_prefixed)
open Lax13Proofs.Imp

/-! ### A digit in a name -/

/-- **The name carries a decimal digit.** Every per-depth name of the
driver does, since it ends in a numeral; no fixed scratch name does. -/
def HasDigit (a : String) : Prop := ∃ c ∈ a.toList, c.isDigit

instance (a : String) : Decidable (HasDigit a) := by
  unfold HasDigit; infer_instance

/-- A decimal digit character is a digit. -/
theorem isDigit_digitChar {d : ℕ} (h : d < 10) : (Nat.digitChar d).isDigit := by
  interval_cases d <;> decide

/-- **The last digit of a numeral occurs in it.** -/
theorem digitChar_mem_toDigits (b : ℕ) : Nat.digitChar (b % 10) ∈ Nat.toDigits 10 b := by
  rw [Nat.toDigits_eq_if (by omega)]
  split
  · rename_i h
    rw [Nat.mod_eq_of_lt h]
    simp
  · simp

/-- **A decimal numeral carries a digit.** -/
theorem hasDigit_toString (b : ℕ) : HasDigit (toString b) :=
  ⟨Nat.digitChar (b % 10),
    by rw [RamDriverCompose.toList_toString]; exact digitChar_mem_toDigits b,
    isDigit_digitChar (Nat.mod_lt _ (by omega))⟩

/-- **A name with a numeral appended carries a digit.** -/
theorem hasDigit_append_right (p : String) {s : String} (h : HasDigit s) :
    HasDigit (p ++ s) := by
  obtain ⟨c, hc, hd⟩ := h
  exact ⟨c, by rw [String.toList_append]; exact List.mem_append_right _ hc, hd⟩

theorem hasDigit_append_left {p : String} (s : String) (h : HasDigit p) :
    HasDigit (p ++ s) := by
  obtain ⟨c, hc, hd⟩ := h
  exact ⟨c, by rw [String.toList_append]; exact List.mem_append_left _ hc, hd⟩

theorem hasDigit_alvName (b : ℕ) : HasDigit (alvName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_gamName (b : ℕ) : HasDigit (gamName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_cluName (b : ℕ) : HasDigit (cluName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_resName (b : ℕ) : HasDigit (resName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_batName (b : ℕ) : HasDigit (batName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_ordName (b : ℕ) : HasDigit (ordName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_xofName (b : ℕ) : HasDigit (xofName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_xmmName (b : ℕ) : HasDigit (xmmName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_asgName (b : ℕ) : HasDigit (asgName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_colName (b c : ℕ) : HasDigit (colName b c) := by
  rw [colName]; exact hasDigit_append_right _ (hasDigit_toString c)

theorem hasDigit_tabName (b i : ℕ) : HasDigit (tabName b i) := by
  rw [tabName]; exact hasDigit_append_right _ (hasDigit_toString i)

theorem hasDigit_ctrName (b : ℕ) : HasDigit (ctrName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_xpName (b : ℕ) : HasDigit (xpName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_curName (b : ℕ) : HasDigit (curName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

/-! ### The depth is recoverable from the name -/

/-- **A fixed prefix with a numeral appended determines the number.** -/
theorem append_toString_inj {p : String} {b b' : ℕ} (h : p ++ toString b = p ++ toString b') :
    b = b' := by
  refine RamDriverBase.toString_inj (String.ext ?_)
  have h' : p.toList ++ (toString b).toList = p.toList ++ (toString b').toList := by
    rw [← String.toList_append, ← String.toList_append, h]
  exact List.append_cancel_left h'

theorem alvName_inj {b b' : ℕ} (h : alvName b = alvName b') : b = b' :=
  append_toString_inj (p := "alv") h

theorem gamName_inj {b b' : ℕ} (h : gamName b = gamName b') : b = b' :=
  append_toString_inj (p := "gam") h

theorem cluName_inj {b b' : ℕ} (h : cluName b = cluName b') : b = b' :=
  append_toString_inj (p := "clu") h

theorem resName_inj {b b' : ℕ} (h : resName b = resName b') : b = b' :=
  append_toString_inj (p := "res") h

theorem batName_inj {b b' : ℕ} (h : batName b = batName b') : b = b' :=
  append_toString_inj (p := "bat") h

theorem ordName_inj {b b' : ℕ} (h : ordName b = ordName b') : b = b' :=
  append_toString_inj (p := "od") h

theorem xofName_inj {b b' : ℕ} (h : xofName b = xofName b') : b = b' :=
  append_toString_inj (p := "xf") h

theorem xmmName_inj {b b' : ℕ} (h : xmmName b = xmmName b') : b = b' :=
  append_toString_inj (p := "xm") h

theorem asgName_inj {b b' : ℕ} (h : asgName b = asgName b') : b = b' :=
  append_toString_inj (p := "ag") h

theorem ctrName_inj {b b' : ℕ} (h : ctrName b = ctrName b') : b = b' :=
  append_toString_inj (p := "ctr") h

theorem xpName_inj {b b' : ℕ} (h : xpName b = xpName b') : b = b' :=
  append_toString_inj (p := "xq") h

theorem curName_inj {b b' : ℕ} (h : curName b = curName b') : b = b' :=
  append_toString_inj (p := "cu") h

/-- **The colour arrays are addressed injectively**, by the same reading
as `RamDriverBase.tabName_inj`. -/
theorem colName_inj {b c b' c' : ℕ} (h : colName b c = colName b' c') : b = b' ∧ c = c' := by
  simp only [colName, String.ext_iff] at h
  simp at h
  obtain ⟨h1, h2⟩ := RamDriverBase.append_cons_inj
    (RamDriverBase.underscore_not_mem_toDigits b) (RamDriverBase.underscore_not_mem_toDigits b') h
  exact ⟨RamDriverBase.toDigits_injective h1, RamDriverBase.toDigits_injective h2⟩

/-! ### The names of the depths below

`BelowArr d` and `BelowVar d` are what a level at depth `d` must leave
alone: the arrays and the scalars of the depths strictly below it. Every
one of them carries a digit, so no literal is one; and the depth is
recoverable, so the depth's *own* names are not either. -/

/-- **A per-depth array of a depth below `d`.** -/
def BelowArr (d : ℕ) (a : String) : Prop :=
  ∃ b < d, a = alvName b ∨ a = gamName b ∨ a = cluName b ∨ a = resName b ∨
    a = batName b ∨ a = ordName b ∨ a = xofName b ∨ a = xmmName b ∨ a = asgName b ∨
    (∃ c, a = colName b c) ∨ (∃ i, a = tabName b i)

/-- **A per-depth scalar of a depth below `d`.** -/
def BelowVar (d : ℕ) (y : String) : Prop :=
  ∃ b < d, y = ctrName b ∨ y = xpName b ∨ y = curName b

theorem BelowArr.mono {d d' : ℕ} {a : String} (h : BelowArr d a) (hd : d ≤ d') :
    BelowArr d' a := by
  obtain ⟨b, hb, hc⟩ := h; exact ⟨b, by omega, hc⟩

theorem BelowVar.mono {d d' : ℕ} {y : String} (h : BelowVar d y) (hd : d ≤ d') :
    BelowVar d' y := by
  obtain ⟨b, hb, hc⟩ := h; exact ⟨b, by omega, hc⟩

theorem hasDigit_of_belowArr {d : ℕ} {a : String} (h : BelowArr d a) : HasDigit a := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨c, rfl⟩ | ⟨i, rfl⟩
  exacts [hasDigit_alvName b, hasDigit_gamName b, hasDigit_cluName b, hasDigit_resName b,
    hasDigit_batName b, hasDigit_ordName b, hasDigit_xofName b, hasDigit_xmmName b,
    hasDigit_asgName b, hasDigit_colName b c, hasDigit_tabName b i]

theorem hasDigit_of_belowVar {d : ℕ} {y : String} (h : BelowVar d y) : HasDigit y := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl
  exacts [hasDigit_ctrName b, hasDigit_xpName b, hasDigit_curName b]

set_option maxHeartbeats 2000000 in
/-- **A name of a depth below is not a name of a depth at or above.**
The whole distinctness table of the driver's per-depth arrays, in one
statement: different prefixes are told apart by their first differing
letter, and the same prefix by the numeral, which
`append_toString_inj` reads back. -/
theorem belowArr_ne {d : ℕ} {a : String} (h : BelowArr d a) {b' : ℕ} (hb : d ≤ b')
    {a' : String}
    (h' : a' = alvName b' ∨ a' = gamName b' ∨ a' = cluName b' ∨ a' = resName b' ∨
      a' = balName b' ∨ a' = balAltName b' ∨ a' = batName b' ∨ a' = ordName b' ∨
      a' = xofName b' ∨ a' = xmmName b' ∨ a' = asgName b' ∨ (∃ c, a' = colName b' c) ∨
      (∃ i, a' = tabName b' i)) : a ≠ a' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨c, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases h' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨c', rfl⟩ | ⟨i', rfl⟩ <;>
    first
      | (intro hq; exact hbb (alvName_inj hq))
      | (intro hq; exact hbb (gamName_inj hq))
      | (intro hq; exact hbb (cluName_inj hq))
      | (intro hq; exact hbb (resName_inj hq))
      | (intro hq; exact hbb (batName_inj hq))
      | (intro hq; exact hbb (ordName_inj hq))
      | (intro hq; exact hbb (xofName_inj hq))
      | (intro hq; exact hbb (xmmName_inj hq))
      | (intro hq; exact hbb (asgName_inj hq))
      | (intro hq; exact hbb (colName_inj hq).1)
      | (intro hq; exact hbb (RamDriverBase.tabName_inj hq).1)
      | simp [alvName, gamName, cluName, resName, balName, balAltName, batName, ordName,
          xofName, xmmName, asgName, colName, tabName, String.ext_iff]

theorem belowVar_ne {d : ℕ} {y : String} (h : BelowVar d y) {b' : ℕ} (hb : d ≤ b')
    {y' : String} (h' : y' = ctrName b' ∨ y' = xpName b' ∨ y' = curName b') : y ≠ y' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl <;>
    first
      | (intro hq; exact hbb (ctrName_inj hq))
      | (intro hq; exact hbb (xpName_inj hq))
      | (intro hq; exact hbb (curName_inj hq))
      | simp [ctrName, xpName, curName, String.ext_iff]

/-- No scalar of a depth below carries the separator, so none is a
scatter flag. -/
theorem belowVar_notMem_underscore {d : ℕ} {y : String} (h : BelowVar d y) :
    '_' ∉ y.toList := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl
  exacts [by rw [ctrName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [xpName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [curName]; exact underscore_notMem_prefixed (by decide) b]

/-- Nor is any of them one of the base evaluator's own scalars. -/
theorem belowVar_ne_envName {d : ℕ} {y : String} (h : BelowVar d y) (i : ℕ) :
    y ≠ envName i := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl <;> simp [ctrName, xpName, curName, envName, String.ext_iff]

/-! ### The generated evaluator's names

`RamDriverBot.warrs_baseCom` leaves a third possibility open — an array
below the base evaluator's output name `"bb"` — and no per-depth name is
one, since none of them begins `bb`. -/

/-- A name whose first two letters are not `bb` is not below `"bb"`. -/
theorem not_ext_bb_append {p : String} (hlen : 2 ≤ p.toList.length)
    (hp : ¬ ("bb".toList <+: p.toList)) (s : String) :
    ¬ RamDriverBot.Ext "bb" (p ++ s) := by
  intro hpre
  rw [RamDriverBot.Ext, String.toList_append] at hpre
  exact hp (List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) (by simpa using hlen))

theorem not_ext_bb_of_belowArr {d : ℕ} {a : String} (h : BelowArr d a) :
    ¬ RamDriverBot.Ext "bb" a := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨c, rfl⟩ | ⟨i, rfl⟩
  exacts [by rw [alvName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [gamName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [cluName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [resName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [batName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [ordName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xofName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xmmName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [asgName]; exact not_ext_bb_append (by decide) (by decide) _,
    fun hq => RamDriverBot.not_ext_b_colName b c (RamDriverCompose.ext_b_of_ext_bb hq),
    fun hq => RamDriverBot.not_ext_b_tabName b i (RamDriverCompose.ext_b_of_ext_bb hq)]

/-- And none of them is the representative table. -/
theorem belowArr_ne_rep {d : ℕ} {a : String} (h : BelowArr d a) : a ≠ "rep" :=
  fun hq => (by decide : ¬ HasDigit "rep") (hq ▸ hasDigit_of_belowArr h)

/-! ### Folds

The driver's phases are folds of commands, and a fold writes what its
pieces write. `RamDriverFrames.mem_warrs_foldr` is the array half; these
are the scalar half and the indexed fold. -/

/-! The three structural readings of a write set, so that a phase's
decomposition never has to guess a `simp` normal form. -/

theorem mem_wvars_seq {c d : Com} {y : String} (h : y ∈ (Com.seq c d).wvars) :
    y ∈ c.wvars ∨ y ∈ d.wvars := List.mem_append.mp h

theorem mem_warrs_seq {c d : Com} {a : String} (h : a ∈ (Com.seq c d).warrs) :
    a ∈ c.warrs ∨ a ∈ d.warrs := List.mem_append.mp h

theorem wvars_store (a : String) (i e : Expr) : (Com.store a i e).wvars = [] := rfl

theorem warrs_store (a : String) (i e : Expr) : (Com.store a i e).warrs = [a] := rfl

theorem wvars_assign (x : String) (e : Expr) : (Com.assign x e).wvars = [x] := rfl

theorem warrs_assign (x : String) (e : Expr) : (Com.assign x e).warrs = [] := rfl

theorem wvars_while (b : Cond) (c : Com) : (Com.while b c).wvars = c.wvars := rfl

theorem warrs_while (b : Cond) (c : Com) : (Com.while b c).warrs = c.warrs := rfl

theorem mem_wvars_ite {b : Cond} {c d : Com} {y : String} (h : y ∈ (Com.ite b c d).wvars) :
    y ∈ c.wvars ∨ y ∈ d.wvars := List.mem_append.mp h

theorem mem_warrs_ite {b : Cond} {c d : Com} {a : String} (h : a ∈ (Com.ite b c d).warrs) :
    a ∈ c.warrs ∨ a ∈ d.warrs := List.mem_append.mp h

/-- A name in a list of literals carries no digit. On a concrete list
the hypothesis is `decide`. -/
theorem notHasDigit_mem {l : List String} (hl : ∀ q ∈ l, ¬ HasDigit q) {y : String}
    (hy : y ∈ l) : ¬ HasDigit y := hl y hy

theorem mem_wvars_foldr {X : Type*} (f : X → Com) :
    ∀ (l : List X) {y : String},
      y ∈ (l.foldr (fun x c => Com.seq (f x) c) .skip).wvars → ∃ x ∈ l, y ∈ (f x).wvars := by
  intro l
  induction l with
  | nil => intro y hy; exact absurd hy (by simp)
  | cons x xs ih =>
      intro y hy
      simp only [List.foldr_cons, Com.wvars, List.mem_append] at hy
      rcases hy with h | h
      · exact ⟨x, by simp, h⟩
      · obtain ⟨z, hz, hm⟩ := ih h
        exact ⟨z, by simp [hz], hm⟩

theorem mem_wvars_foldRange (f : ℕ → Com) (mm : ℕ) {y : String}
    (h : y ∈ (foldRange f mm).wvars) : ∃ b < mm, y ∈ (f b).wvars := by
  obtain ⟨b, hb, hm⟩ := mem_wvars_foldr f (List.range mm) h
  exact ⟨b, List.mem_range.mp hb, hm⟩

theorem mem_wvars_foldIdx {X : Type*} (f : ℕ → X → Com) :
    ∀ (l : List X) (i₀ : ℕ) {y : String},
      y ∈ (foldIdx f i₀ l).wvars → ∃ i, ∃ x ∈ l, y ∈ (f i x).wvars := by
  intro l
  induction l with
  | nil => intro i₀ y hy; exact absurd hy (by rw [foldIdx]; simp [Com.wvars])
  | cons x xs ih =>
      intro i₀ y hy
      rw [foldIdx, Com.wvars, List.mem_append] at hy
      rcases hy with h | h
      · exact ⟨i₀, x, by simp, h⟩
      · obtain ⟨i, z, hz, hm⟩ := ih (i₀ + 1) h
        exact ⟨i, z, by simp [hz], hm⟩

theorem mem_warrs_foldIdx' {X : Type*} (f : ℕ → X → Com) :
    ∀ (l : List X) (i₀ : ℕ) {a : String},
      a ∈ (foldIdx f i₀ l).warrs → ∃ i, ∃ x ∈ l, a ∈ (f i x).warrs := by
  intro l
  induction l with
  | nil => intro i₀ a ha; exact absurd ha (by rw [foldIdx]; simp [Com.warrs])
  | cons x xs ih =>
      intro i₀ a ha
      rw [foldIdx, Com.warrs, List.mem_append] at ha
      rcases ha with h | h
      · exact ⟨i₀, x, by simp, h⟩
      · obtain ⟨i, z, hz, hm⟩ := ih (i₀ + 1) h
        exact ⟨i, z, by simp [hz], hm⟩

/-! ### The ordering phase -/

theorem warrs_orderCom_split (W j : ℕ) : (orderCom 0 W j).warrs =
    ["gof", "gtg", "alv", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "doff", "dtg", "off", "tgt",
      "alv", "elm", "bh", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl"] ++
    (ordName j :: ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"]) :=
  RamDriverCompose.warrs_orderCom₀ W j

theorem belowArr_notMem_warrs_orderCom (W d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (orderCom 0 W d).warrs := by
  rw [warrs_orderCom_split, List.mem_append]
  rintro (hm | hm)
  · exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)
  · rcases List.mem_cons.mp hm with hq | hm'
    · exact belowArr_ne h (le_refl d) (by tauto) hq
    · exact notHasDigit_mem (by decide) hm' (hasDigit_of_belowArr h)

theorem belowVar_notMem_wvars_orderCom (W d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (orderCom 0 W d).wvars := by
  rw [RamDriverCompose.wvars_orderCom₀]
  intro hm
  exact (by decide : ∀ q ∈ ["i", "c", "j", "jend", "u", "sp", "ls", "d", "mind", "cnt",
      "kmax", "sc", "p", "w", "s", "z"], ¬ HasDigit q) _
    (RamDriverCompose.mem_wvars_orderCom₀ y hm) (hasDigit_of_belowVar h)

/-! ### The cover phase -/

theorem warrs_coverPhase_split (cap j : ℕ) : (coverPhase cap j).warrs =
    ["ord", "alv", "asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv",
      "xoff"] ++ [xofName j, xmmName j, asgName j] :=
  RamDriverCompose.warrs_coverPhase cap j

/-- The scalars the cover phase writes, other than its own per-depth
write pointer: the pass's own, and — since rebase P1 — the tower
search's eighteen cells. **Ledger P1/B-f**: three of them (`dv1`, `v1`,
`k0`) carry a digit, so the "no per-depth name is digit-free" argument
that covers every other phase no longer covers this list on its own;
`coverPhaseScalars_ok` splits it, and the three exceptions are told
apart from `ctrName`/`xpName`/`curName` by their first letters. -/
def coverPhaseScalars : List String :=
  ["i", "i", "i", "i", "i", "i", "xp", "c", "src",
    "sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend",
    "u", "au", "du",
    "i", "a", "tl", "tl", "v", "dv", "head", "dv1", "k0", "v1", "kend", "u", "au",
    "du", "tl", "k0",
    "z", "dz", "xp", "z", "c",
    "i", "i", "i", "i", "i", "i"]

theorem wvars_coverPhase_split (cap j : ℕ) :
    (coverPhase cap j).wvars = coverPhaseScalars ++ [xpName j] :=
  RamDriverCompose.wvars_coverPhase cap j

/-- Every scalar the phase writes is either digit-free — and so not a
per-depth name — or one of the tower search's three digit-carrying junk
cells. -/
theorem coverPhaseScalars_ok :
    ∀ z ∈ coverPhaseScalars, ¬ HasDigit z ∨ z = "dv1" ∨ z = "v1" ∨ z = "k0" := by decide

/-- None of those three is a per-depth scalar: `ctrName`, `xpName` and
`curName` all begin with a letter none of them begins with. -/
theorem belowVar_ne_junk {d : ℕ} {y : String} (h : BelowVar d y) :
    y ≠ "dv1" ∧ y ≠ "v1" ∧ y ≠ "k0" := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl <;>
    exact ⟨by simp [ctrName, xpName, curName, String.ext_iff],
      by simp [ctrName, xpName, curName, String.ext_iff],
      by simp [ctrName, xpName, curName, String.ext_iff]⟩

theorem belowArr_notMem_warrs_coverPhase (cap d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (coverPhase cap d).warrs := by
  rw [warrs_coverPhase_split, List.mem_append]
  rintro (hm | hm)
  · exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hq | hq | hq <;> exact belowArr_ne h (le_refl d) (by tauto) hq

theorem belowVar_notMem_wvars_coverPhase (cap d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (coverPhase cap d).wvars := by
  have hj := belowVar_ne_junk h
  rw [wvars_coverPhase_split, List.mem_append]
  rintro (hm | hm)
  · rcases coverPhaseScalars_ok y hm with hnd | hq
    · exact hnd (hasDigit_of_belowVar h)
    · rcases hq with rfl | rfl | rfl
      exacts [hj.1 rfl, hj.2.1 rfl, hj.2.2 rfl]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact belowVar_ne h (le_refl d) (by tauto) hm

/-! ### The padding, the colouring, the scatter phase and the readback -/

theorem wvars_enumBatch_eq (bat : String) (mb : ℕ) :
    (enumBatch bat mb).wvars = (enumBatch "" 0).wvars := rfl

theorem belowArr_notMem_warrs_enumBatch (bat : String) (mb : ℕ) {d : ℕ} {a : String}
    (h : BelowArr d a) : a ∉ (enumBatch bat mb).warrs := by
  rw [RamDriverFrames.warrs_enumBatch]
  intro hm
  exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)

theorem belowVar_notMem_wvars_enumBatch (bat : String) (mb : ℕ) {d : ℕ} {y : String}
    (h : BelowVar d y) : y ∉ (enumBatch bat mb).wvars := by
  rw [wvars_enumBatch_eq]
  intro hm
  exact notHasDigit_mem (l := (enumBatch "" 0).wvars) (by decide) hm (hasDigit_of_belowVar h)

theorem belowArr_notMem_warrs_colourCom (cap mb d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (colourCom cap mb d).warrs := by
  intro hm
  obtain ⟨c, hc⟩ := RamDriverFrames.mem_warrs_colourCom cap mb d hm
  exact belowArr_ne h (Nat.le_succ d) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))))))))))) hc

theorem wvars_expandCom_eq (msk src dst : String) :
    (expandCom msk src dst).wvars = (expandCom "" "" "").wvars := rfl

theorem notHasDigit_wvars_expandCom (msk src dst : String) :
    ∀ y ∈ (expandCom msk src dst).wvars, ¬ HasDigit y := by
  rw [wvars_expandCom_eq]
  decide

theorem notHasDigit_wvars_chainCom (msk : String) (nm : ℕ → String) (r : ℕ) :
    ∀ y ∈ (chainCom msk nm r).wvars, ¬ HasDigit y := by
  intro y hy
  obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ r hy
  exact notHasDigit_wvars_expandCom _ _ _ y hm

theorem notHasDigit_wvars_oldCom (cap mb j : ℕ) :
    ∀ y ∈ (oldCom cap mb j).wvars, ¬ HasDigit y := by
  intro y hy
  rw [oldCom] at hy
  rcases mem_wvars_seq hy with hm | hm
  · obtain ⟨b, -, hm'⟩ := mem_wvars_foldRange _ _ hm
    rw [andCom, RamDriverIO.wvars_fillCom] at hm'
    exact notHasDigit_mem (by decide) hm'
  · rw [RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom] at hm
    exact notHasDigit_mem (by decide) hm

theorem notHasDigit_wvars_pdCom (cap mb j : ℕ) :
    ∀ y ∈ (pdCom cap mb j).wvars, ¬ HasDigit y := by
  intro y hy
  rw [pdCom] at hy
  obtain ⟨i, -, hm⟩ := mem_wvars_foldr _ (List.finRange mb) hy
  rcases mem_wvars_seq hm with hm' | hm'
  · rw [RamDriverIO.wvars_fillCom] at hm'
    exact notHasDigit_mem (by decide) hm'
  · rcases mem_wvars_seq hm' with hm'' | hm''
    · rw [wvars_store] at hm''
      exact absurd hm'' (List.not_mem_nil)
    · exact notHasDigit_wvars_chainCom _ _ _ y hm''

theorem notHasDigit_wvars_puCom (cap mb j : ℕ) :
    ∀ y ∈ (puCom cap mb j).wvars, ¬ HasDigit y := by
  intro y hy
  rw [puCom] at hy
  obtain ⟨c, -, hm⟩ := mem_wvars_foldRange _ _ hy
  rcases mem_wvars_seq hm with hm' | hm'
  · rw [RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom] at hm'
    exact notHasDigit_mem (by decide) hm'
  · exact notHasDigit_wvars_chainCom _ _ _ y hm'

theorem notHasDigit_wvars_colourCom (cap mb j : ℕ) :
    ∀ y ∈ (colourCom cap mb j).wvars, ¬ HasDigit y := by
  intro y hy
  rw [colourCom] at hy
  rcases mem_wvars_seq hy with hm | hm
  · exact notHasDigit_wvars_oldCom cap mb j y hm
  · rcases mem_wvars_seq hm with hm' | hm'
    · exact notHasDigit_wvars_pdCom cap mb j y hm'
    · exact notHasDigit_wvars_puCom cap mb j y hm'

theorem belowVar_notMem_wvars_colourCom (cap mb d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (colourCom cap mb d).wvars :=
  fun hm => notHasDigit_wvars_colourCom cap mb d y hm (hasDigit_of_belowVar h)

open Classical in
theorem belowArr_notMem_warrs_scatterFold (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {a : String} (h : BelowArr d a) :
    a ∉ (foldIdx (fun i β => scatterCom q_top cap mb φ d i β) 0
      (tablesAt q_top cap mb φ d)).warrs := by
  intro hm
  have := RamDriverFrames.warrs_scatterFold q_top cap mb φ d _ 0 a hm
  exact (by decide : ∀ q ∈ scratchArrs, ¬ HasDigit q) _ this (hasDigit_of_belowArr h)

open Classical in
theorem belowVar_notMem_wvars_scatterFold (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {y : String} (hb : BelowVar d y) :
    y ∉ (foldIdx (fun i β => scatterCom q_top cap mb φ d i β) 0
      (tablesAt q_top cap mb φ d)).wvars := by
  have hy1 : '_' ∉ y.toList := belowVar_notMem_underscore hb
  have hy2 : y ≠ "i" := fun hq => (by decide : ¬ HasDigit "i") (hq ▸ hasDigit_of_belowVar hb)
  have hy3 : y ∉ (RamScatter.scatterCom 0 0).wvars := fun hq =>
    (by decide : ∀ q ∈ (RamScatter.scatterCom 0 0).wvars, ¬ HasDigit q) _ hq
      (hasDigit_of_belowVar hb)
  intro hm
  obtain ⟨i, β, -, hm'⟩ := mem_wvars_foldIdx _ _ 0 hm
  rw [RamDriverFrames.scatterCom_eq] at hm'
  obtain ⟨k, σs, -, hm''⟩ := mem_wvars_foldIdx _ _ 0 hm'
  exact RamDriverFrames.notMem_wvars_atomCom hy1 hy2 hy3 hm''

theorem belowArr_notMem_warrs_readbackCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {a : String} (h : BelowArr d a) : a ∉ (readbackCom q_top cap mb φ d).warrs := by
  intro hm
  obtain ⟨i, hi⟩ := RamDriverBase.mem_warrs_readbackCom hm
  exact belowArr_ne h (le_refl d) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))))))))))))  hi

theorem belowVar_notMem_wvars_readbackCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {y : String} (h : BelowVar d y) : y ∉ (readbackCom q_top cap mb φ d).wvars :=
  RamDriverBase.not_mem_wvars_readbackCom
    (fun hq => (by decide : ¬ HasDigit "z") (hq ▸ hasDigit_of_belowVar h))

/-! ### The descent

The one phase whose write set is not already read off in
`Lax3Proofs.RamDriverFrames`: that file bounds the *characters* of the
arrays the descent writes, and what is needed here is the arrays
themselves. -/

theorem ballStage_cases (j a : ℕ) :
    ballStage j a = balName j ∨ ballStage j a = balAltName j := by
  rw [ballStage]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem wvars_bfsParCom (r : ℕ) :
    (RamBfsPaths.bfsParCom r).wvars = (RamBfsPaths.bfsParCom 0).wvars := rfl

theorem wvars_markPath (bat : String) : (markPath bat).wvars = ["i", "plen", "i"] := rfl

theorem wvars_clusterLoad (j : ℕ) : (clusterLoad j).wvars = ["i", "i", "p", "pend", "p"] := rfl

/-- **What one earlier round's contribution writes**: the batch, and
literals. -/
theorem hasDigit_warrs_ancestorStep (cap j a : ℕ) {x : String}
    (hx : x ∈ (ancestorStep cap j a).warrs) (hd : HasDigit x) : x = batName j := by
  rw [ancestorStep] at hx
  rcases mem_warrs_seq hx with h | h
  · rw [warrs_assign] at h; exact absurd h List.not_mem_nil
  rcases mem_warrs_seq h with h | h
  · rw [warrs_assign] at h; exact absurd h List.not_mem_nil
  rcases mem_warrs_seq h with h | h
  · rw [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)
  rcases mem_warrs_seq h with h | h
  · rw [RamDriverFrames.warrs_bfsParCom] at h
    exact absurd hd (notHasDigit_mem (l := (RamBfsPaths.bfsParCom 0).warrs) (by decide) h)
  rcases mem_warrs_ite h with h | h
  · rcases mem_warrs_seq h with h | h
    · exact absurd hd
        (notHasDigit_mem (l := RamBfsPaths.extractPathCom.warrs) (by decide) h)
    · rw [RamDriverFrames.warrs_markPath] at h
      exact List.eq_of_mem_singleton h
  · exact absurd h (by rw [Com.warrs_skip]; exact List.not_mem_nil)

theorem hasDigit_wvars_ancestorStep (cap j a : ℕ) {y : String}
    (hy : y ∈ (ancestorStep cap j a).wvars) : ¬ HasDigit y := by
  rw [ancestorStep] at hy
  rcases mem_wvars_seq hy with h | h
  · rw [wvars_assign] at h; exact notHasDigit_mem (by decide) h
  rcases mem_wvars_seq h with h | h
  · rw [wvars_assign] at h; exact notHasDigit_mem (by decide) h
  rcases mem_wvars_seq h with h | h
  · rw [RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom] at h
    exact notHasDigit_mem (by decide) h
  rcases mem_wvars_seq h with h | h
  · rw [wvars_bfsParCom] at h
    exact notHasDigit_mem (l := (RamBfsPaths.bfsParCom 0).wvars) (by decide) h
  rcases mem_wvars_ite h with h | h
  · rcases mem_wvars_seq h with h | h
    · exact notHasDigit_mem (l := RamBfsPaths.extractPathCom.wvars) (by decide) h
    · rw [wvars_markPath] at h; exact notHasDigit_mem (by decide) h
  · exact absurd h (by rw [Com.wvars_skip]; exact List.not_mem_nil)

theorem hasDigit_warrs_batchCom (cap j : ℕ) {x : String}
    (hx : x ∈ (batchCom cap j).warrs) (hd : HasDigit x) : x = batName j := by
  rw [batchCom] at hx
  rcases mem_warrs_seq hx with h | h
  · rw [RamDriverIO.warrs_fillCom] at h; exact List.eq_of_mem_singleton h
  rcases mem_warrs_seq h with h | h
  · rw [warrs_store] at h; exact List.eq_of_mem_singleton h
  rcases mem_warrs_seq h with h | h
  · obtain ⟨b, -, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ j h
    exact hasDigit_warrs_ancestorStep cap j b hm hd
  · rw [andCom, RamDriverIO.warrs_fillCom] at h; exact List.eq_of_mem_singleton h

theorem hasDigit_wvars_batchCom (cap j : ℕ) {y : String}
    (hy : y ∈ (batchCom cap j).wvars) : ¬ HasDigit y := by
  rw [batchCom] at hy
  rcases mem_wvars_seq hy with h | h
  · rw [RamDriverIO.wvars_fillCom] at h; exact notHasDigit_mem (by decide) h
  rcases mem_wvars_seq h with h | h
  · rw [wvars_store] at h; exact absurd h List.not_mem_nil
  rcases mem_wvars_seq h with h | h
  · obtain ⟨b, -, hm⟩ := mem_wvars_foldRange _ j h
    exact hasDigit_wvars_ancestorStep cap j b hm
  · rw [andCom, RamDriverIO.wvars_fillCom] at h; exact notHasDigit_mem (by decide) h

/-- **What the descent writes**: the cluster, the restricted mask, the
two halves of the ball's ping-pong, the batch, and the two masks of the
next depth. -/
theorem hasDigit_warrs_descendCom (cap j : ℕ) {x : String}
    (hx : x ∈ (descendCom cap j).warrs) (hd : HasDigit x) :
    x = cluName j ∨ x = resName j ∨ x = balName j ∨ x = balAltName j ∨ x = batName j ∨
      x = alvName (j + 1) ∨ x = gamName (j + 1) := by
  rw [descendCom] at hx
  rcases mem_warrs_seq hx with h | h
  · rw [warrs_assign] at h; exact absurd h List.not_mem_nil
  rcases mem_warrs_seq h with h | h
  · rw [RamDriverFrames.warrs_clusterLoad] at h
    rcases List.mem_cons.mp h with hq | hq
    · exact Or.inl hq
    · exact Or.inl (List.eq_of_mem_singleton hq)
  rcases mem_warrs_seq h with h | h
  · rw [andCom, RamDriverIO.warrs_fillCom] at h
    exact Or.inr (Or.inl (List.eq_of_mem_singleton h))
  rcases mem_warrs_seq h with h | h
  · rcases mem_warrs_seq h with h | h
    · rw [RamDriverIO.warrs_fillCom] at h
      exact Or.inr (Or.inr (Or.inl (List.eq_of_mem_singleton h)))
    rcases mem_warrs_seq h with h | h
    · rw [warrs_store] at h
      exact Or.inr (Or.inr (Or.inl (List.eq_of_mem_singleton h)))
    · obtain ⟨b, -, rfl⟩ := RamDriverFrames.mem_warrs_chainCom _ _ _ h
      rcases ballStage_cases j (b + 1) with hq | hq
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
  rcases mem_warrs_seq h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hasDigit_warrs_batchCom cap j h hd)))))
  rcases mem_warrs_seq h with h | h
  · rw [subCom, RamDriverIO.warrs_fillCom] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.eq_of_mem_singleton h))))))
  rcases mem_warrs_seq h with h | h
  · rw [andCom, RamDriverIO.warrs_fillCom] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.eq_of_mem_singleton h))))))
  · rw [subCom, RamDriverIO.warrs_fillCom] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.eq_of_mem_singleton h))))))

/-- **What the descent assigns**: the depth's own connector, and
literals. -/
theorem hasDigit_wvars_descendCom (cap j : ℕ) {y : String}
    (hy : y ∈ (descendCom cap j).wvars) (hd : HasDigit y) : y = ctrName j := by
  rw [descendCom] at hy
  rcases mem_wvars_seq hy with h | h
  · rw [wvars_assign] at h; exact List.eq_of_mem_singleton h
  rcases mem_wvars_seq h with h | h
  · rw [wvars_clusterLoad] at h; exact absurd hd (notHasDigit_mem (by decide) h)
  rcases mem_wvars_seq h with h | h
  · rw [andCom, RamDriverIO.wvars_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)
  rcases mem_wvars_seq h with h | h
  · rcases mem_wvars_seq h with h | h
    · rw [RamDriverIO.wvars_fillCom] at h; exact absurd hd (notHasDigit_mem (by decide) h)
    rcases mem_wvars_seq h with h | h
    · rw [wvars_store] at h; exact absurd h List.not_mem_nil
    · exact absurd hd (notHasDigit_wvars_chainCom _ _ _ y h)
  rcases mem_wvars_seq h with h | h
  · exact absurd hd (hasDigit_wvars_batchCom cap j h)
  rcases mem_wvars_seq h with h | h
  · rw [subCom, RamDriverIO.wvars_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)
  rcases mem_wvars_seq h with h | h
  · rw [andCom, RamDriverIO.wvars_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)
  · rw [subCom, RamDriverIO.wvars_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)

theorem belowArr_notMem_warrs_descendCom (cap d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (descendCom cap d).warrs := by
  intro hm
  rcases hasDigit_warrs_descendCom cap d hm (hasDigit_of_belowArr h) with
    hq | hq | hq | hq | hq | hq | hq
  exacts [belowArr_ne h (le_refl d) (by tauto) hq, belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (le_refl d) (by tauto) hq, belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (Nat.le_succ d) (by tauto) hq,
    belowArr_ne h (Nat.le_succ d) (by tauto) hq]

theorem belowVar_notMem_wvars_descendCom (cap d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (descendCom cap d).wvars := fun hm =>
  belowVar_ne h (le_refl d) (by tauto) (hasDigit_wvars_descendCom cap d hm
    (hasDigit_of_belowVar h))

/-! ### The base case -/

theorem not_ext_bb_of_belowVar {d : ℕ} {y : String} (h : BelowVar d y) :
    ¬ RamDriverBot.Ext "bb" y := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl
  exacts [by rw [ctrName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xpName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [curName]; exact not_ext_bb_append (by decide) (by decide) _]

theorem belowArr_notMem_warrs_baseCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {a : String} (h : BelowArr d a) : a ∉ (baseCom q_top cap mb d φ).warrs := by
  intro hm
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ d, IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt d β hβ).1
  rcases RamDriverBot.warrs_baseCom hlocal a hm with hq | ⟨i, hq⟩ | hq
  · exact belowArr_ne_rep h hq
  · exact belowArr_ne h (le_refl d) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))))))))))) hq
  · exact not_ext_bb_of_belowArr h hq

theorem belowVar_notMem_wvars_baseCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {y : String} (h : BelowVar d y) : y ∉ (baseCom q_top cap mb d φ).wvars := by
  intro hm
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ d, IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt d β hβ).1
  rcases RamDriverBot.wvars_baseCom hlocal y hm with hq | ⟨i, hq⟩ | hq
  · exact notHasDigit_mem (by decide) hq (hasDigit_of_belowVar h)
  · exact belowVar_ne_envName h i hq
  · exact not_ext_bb_of_belowVar h hq

/-! ### The recursion

One induction on the fuel. Every phase of a level writes only fixed
scratch names and per-depth names at its own depth or the next, and the
nested call is the induction hypothesis at `d + 1`, where the frame is
one depth weaker and `BelowArr.mono` bridges the two. -/

open Classical in
/-- **A level writes no array of a depth below its own.** -/
theorem belowArr_notMem_warrs_driverAux (q_top cap mb ℓ W : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {a : String}, BelowArr d a →
      a ∉ (driverAux q_top cap mb 0 ℓ W φ f d).warrs := by
  intro f
  induction f with
  | zero =>
      intro d a h hm
      rw [driverAux] at hm
      exact belowArr_notMem_warrs_baseCom q_top cap mb d φ h hm
  | succ f ih =>
      intro d a h hm
      rw [driverAux] at hm
      rcases mem_warrs_seq hm with hq | hq
      · exact belowArr_notMem_warrs_orderCom W d h hq
      rcases mem_warrs_seq hq with hq | hq
      · exact belowArr_notMem_warrs_coverPhase cap d h hq
      rcases mem_warrs_seq hq with hq | hq
      · rw [warrs_assign] at hq; exact absurd hq List.not_mem_nil
      rw [warrs_while] at hq
      rcases mem_warrs_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases mem_warrs_seq hq with hr | hr
        · exact belowArr_notMem_warrs_descendCom cap d h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_enumBatch (batName d) mb h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_colourCom cap mb d h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_scatterFold q_top cap mb d φ h hr
        · exact belowArr_notMem_warrs_readbackCom q_top cap mb d φ h hr
      · rw [warrs_assign] at hq; exact absurd hq List.not_mem_nil

open Classical in
/-- **A level assigns no scalar of a depth below its own.** -/
theorem belowVar_notMem_wvars_driverAux (q_top cap mb ℓ W : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {y : String}, BelowVar d y →
      y ∉ (driverAux q_top cap mb 0 ℓ W φ f d).wvars := by
  intro f
  induction f with
  | zero =>
      intro d y h hm
      rw [driverAux] at hm
      exact belowVar_notMem_wvars_baseCom q_top cap mb d φ h hm
  | succ f ih =>
      intro d y h hm
      rw [driverAux] at hm
      rcases mem_wvars_seq hm with hq | hq
      · exact belowVar_notMem_wvars_orderCom W d h hq
      rcases mem_wvars_seq hq with hq | hq
      · exact belowVar_notMem_wvars_coverPhase cap d h hq
      rcases mem_wvars_seq hq with hq | hq
      · rw [wvars_assign] at hq
        exact belowVar_ne h (le_refl d) (by tauto) (List.eq_of_mem_singleton hq)
      rw [wvars_while] at hq
      rcases mem_wvars_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases mem_wvars_seq hq with hr | hr
        · exact belowVar_notMem_wvars_descendCom cap d h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_enumBatch (batName d) mb h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_colourCom cap mb d h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_scatterFold q_top cap mb d φ h hr
        · exact belowVar_notMem_wvars_readbackCom q_top cap mb d φ h hr
      · rw [wvars_assign] at hq
        exact belowVar_ne h (le_refl d) (by tauto) (List.eq_of_mem_singleton hq)

/-- **The driver at a depth writes no array of a depth below it.** -/
theorem belowArr_notMem_warrs_driverAt {q_top cap mb ℓ W d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {a : String} (h : BelowArr d a) : a ∉ (driverAt q_top cap mb 0 ℓ W φ d).warrs := by
  rw [driverAt]
  exact belowArr_notMem_warrs_driverAux q_top cap mb ℓ W φ (ℓ - d) d h

/-- **Nor does it assign a scalar of one.** -/
theorem belowVar_notMem_wvars_driverAt {q_top cap mb ℓ W d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {y : String} (h : BelowVar d y) : y ∉ (driverAt q_top cap mb 0 ℓ W φ d).wvars := by
  rw [driverAt]
  exact belowVar_notMem_wvars_driverAux q_top cap mb ℓ W φ (ℓ - d) d h

/-! ### Two names that are **not** frames of the recursion

Wave E2's counterexamples. `RamDriverFrames.TurnFrozen` used to ask the
nested call to leave the padding buffer `"wa"` and the eight
accumulators of `RamDriver.OrderMem` alone; a level writes both, so at
`RamDriver.driverAt` the old obligation was refuted rather than
unproved. The buffer moved out of `RamDriverCluster.ClusterData` into
`ClusterWa`, and the accumulators come back from
`RamDriver.LevelPost` instead of from a frame. -/

theorem mem_warrs_seq_left {c d : Com} {a : String} (h : a ∈ c.warrs) :
    a ∈ (Com.seq c d).warrs := List.mem_append_left _ h

theorem mem_warrs_seq_right {c d : Com} {a : String} (h : a ∈ d.warrs) :
    a ∈ (Com.seq c d).warrs := List.mem_append_right _ h

theorem mem_warrs_while_body {b : Cond} {c : Com} {a : String} (h : a ∈ c.warrs) :
    a ∈ (Com.while b c).warrs := h

open Classical in
/-- **A level writes the padding buffer.** -/
theorem wa_mem_warrs_driverAt {q_top cap mb ℓ W d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (h : d < ℓ) : "wa" ∈ (driverAt q_top cap mb 0 ℓ W φ d).warrs := by
  rw [driverAt_succ q_top cap mb 0 ℓ W φ h]
  refine mem_warrs_seq_right (mem_warrs_seq_right (mem_warrs_seq_right
    (mem_warrs_while_body (mem_warrs_seq_left ?_))))
  rw [clusterCom]
  refine mem_warrs_seq_right (mem_warrs_seq_left ?_)
  rw [RamDriverFrames.warrs_enumBatch]
  exact List.mem_cons_self

open Classical in
/-- **And the elimination's accumulator.** -/
theorem elm_mem_warrs_driverAt {q_top cap mb ℓ W d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (h : d < ℓ) : "elm" ∈ (driverAt q_top cap mb 0 ℓ W φ d).warrs := by
  rw [driverAt_succ q_top cap mb 0 ℓ W φ h]
  refine mem_warrs_seq_left ?_
  rw [warrs_orderCom_split]
  exact List.mem_append_left _ (by decide)

end Lax3Proofs.RamDriverWrites
