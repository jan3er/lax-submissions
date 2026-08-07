import Lax3Proofs.RamDriverCompose
import Lax3Proofs.RamDriverDescend
import Lax3Proofs.Refine.ScatterDeadPass

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

theorem hasDigit_cpsName (b : ℕ) : HasDigit (cpsName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_cnumName (b : ℕ) : HasDigit (cnumName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_cixName (b : ℕ) : HasDigit (cixName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_mnumName (b : ℕ) : HasDigit (mnumName b) :=
  hasDigit_append_right _ (hasDigit_toString b)

theorem hasDigit_memName (b : ℕ) : HasDigit (memName b) :=
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

theorem cpsName_inj {b b' : ℕ} (h : cpsName b = cpsName b') : b = b' :=
  append_toString_inj (p := "cs") h

theorem cnumName_inj {b b' : ℕ} (h : cnumName b = cnumName b') : b = b' :=
  append_toString_inj (p := "cq") h

theorem cixName_inj {b b' : ℕ} (h : cixName b = cixName b') : b = b' :=
  append_toString_inj (p := "ci") h

theorem mnumName_inj {b b' : ℕ} (h : mnumName b = mnumName b') : b = b' :=
  append_toString_inj (p := "mm") h

theorem memName_inj {b b' : ℕ} (h : memName b = memName b') : b = b' :=
  append_toString_inj (p := "mem") h

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
    a = cpsName b ∨ a = memName b ∨ (∃ c, a = colName b c) ∨ (∃ i, a = tabName b i)

/-- **A per-depth scalar of a depth below `d`.** -/
def BelowVar (d : ℕ) (y : String) : Prop :=
  ∃ b < d, y = ctrName b ∨ y = xpName b ∨ y = curName b ∨ y = cnumName b ∨ y = cixName b ∨
    y = mnumName b

theorem BelowArr.mono {d d' : ℕ} {a : String} (h : BelowArr d a) (hd : d ≤ d') :
    BelowArr d' a := by
  obtain ⟨b, hb, hc⟩ := h; exact ⟨b, by omega, hc⟩

theorem BelowVar.mono {d d' : ℕ} {y : String} (h : BelowVar d y) (hd : d ≤ d') :
    BelowVar d' y := by
  obtain ⟨b, hb, hc⟩ := h; exact ⟨b, by omega, hc⟩

theorem hasDigit_of_belowArr {d : ℕ} {a : String} (h : BelowArr d a) : HasDigit a := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    ⟨c, rfl⟩ | ⟨i, rfl⟩
  exacts [hasDigit_alvName b, hasDigit_gamName b, hasDigit_cluName b, hasDigit_resName b,
    hasDigit_batName b, hasDigit_ordName b, hasDigit_xofName b, hasDigit_xmmName b,
    hasDigit_asgName b, hasDigit_cpsName b, hasDigit_memName b, hasDigit_colName b c,
    hasDigit_tabName b i]

theorem hasDigit_of_belowVar {d : ℕ} {y : String} (h : BelowVar d y) : HasDigit y := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hasDigit_ctrName b, hasDigit_xpName b, hasDigit_curName b, hasDigit_cnumName b,
    hasDigit_cixName b, hasDigit_mnumName b]

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
      a' = xofName b' ∨ a' = xmmName b' ∨ a' = asgName b' ∨ a' = cpsName b' ∨
      (∃ c, a' = colName b' c) ∨ (∃ i, a' = tabName b' i)) : a ≠ a' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨c, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases h' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      | (intro hq; exact hbb (cpsName_inj hq))
      | (intro hq; exact hbb (colName_inj hq).1)
      | (intro hq; exact hbb (RamDriverBase.tabName_inj hq).1)
      | simp [alvName, gamName, cluName, resName, balName, balAltName, batName, ordName,
          xofName, xmmName, asgName, cpsName, memName, colName, tabName, String.ext_iff]

/-- **A name of a depth below is not a member list** (rebase E-mem):
`memName` is a fresh prefix, so the whole table is settled by the first
letter. -/
theorem belowArr_ne_memName {d : ℕ} {a : String} (h : BelowArr d a) {b' : ℕ}
    (hb : d ≤ b') : a ≠ memName b' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨c, rfl⟩ | ⟨i, rfl⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl => exact fun hq => hbb (memName_inj hq)
  all_goals simp [alvName, gamName, cluName, resName, batName, ordName, xofName, xmmName,
    asgName, cpsName, colName, tabName, memName, String.ext_iff]

theorem belowVar_ne {d : ℕ} {y : String} (h : BelowVar d y) {b' : ℕ} (hb : d ≤ b')
    {y' : String} (h' : y' = ctrName b' ∨ y' = xpName b' ∨ y' = curName b' ∨
      y' = cnumName b' ∨ y' = cixName b') : y ≠ y' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h' with rfl | rfl | rfl | rfl | rfl <;>
    first
      | (intro hq; exact hbb (ctrName_inj hq))
      | (intro hq; exact hbb (xpName_inj hq))
      | (intro hq; exact hbb (curName_inj hq))
      | (intro hq; exact hbb (cnumName_inj hq))
      | (intro hq; exact hbb (cixName_inj hq))
      | simp [ctrName, xpName, curName, cnumName, cixName, mnumName, String.ext_iff]

/-- No scalar of a depth below carries the separator, so none is a
scatter flag. -/
theorem belowVar_notMem_underscore {d : ℕ} {y : String} (h : BelowVar d y) :
    '_' ∉ y.toList := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [by rw [ctrName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [xpName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [curName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [cnumName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [cixName]; exact underscore_notMem_prefixed (by decide) b,
    by rw [mnumName]; exact underscore_notMem_prefixed (by decide) b]

/-- Nor is any of them one of the base evaluator's own scalars. -/
theorem belowVar_ne_envName {d : ℕ} {y : String} (h : BelowVar d y) (i : ℕ) :
    y ≠ envName i := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ctrName, xpName, curName, cnumName, cixName, mnumName, envName, String.ext_iff]

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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    ⟨c, rfl⟩ | ⟨i, rfl⟩
  exacts [by rw [alvName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [gamName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [cluName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [resName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [batName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [ordName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xofName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xmmName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [asgName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [cpsName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [memName]; exact not_ext_bb_append (by decide) (by decide) _,
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

theorem warrs_orderCom_split (j : ℕ) : (orderCom 0 j).warrs =
    ["gof", "gtg", "alv", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "doff", "dtg",
      "ooff", "ooff", "ofl", "otg", "ofl", "off", "tgt", "tgt",
      "alv", "elm", "bh", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "off", "tgt"] ++
    (ordName j :: ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"]) :=
  RamDriverCompose.warrs_orderCom₀ j

theorem belowArr_notMem_warrs_orderCom (d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (orderCom 0 d).warrs := by
  rw [warrs_orderCom_split, List.mem_append]
  rintro (hm | hm)
  · exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)
  · rcases List.mem_cons.mp hm with hq | hm'
    · exact belowArr_ne h (le_refl d) (by tauto) hq
    · exact notHasDigit_mem (by decide) hm' (hasDigit_of_belowArr h)

theorem belowVar_notMem_wvars_orderCom (d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (orderCom 0 d).wvars := by
  rw [RamDriverCompose.wvars_orderCom₀]
  intro hm
  exact (by decide : ∀ q ∈ ["i", "c", "j", "jend", "u", "sp", "ls", "d", "mind", "cnt",
      "kmax", "sc", "p", "w", "s", "z", "sy"], ¬ HasDigit q) _
    (RamDriverCompose.mem_wvars_orderCom₀ y hm) (hasDigit_of_belowVar h)

/-! ### The cover phase -/

theorem warrs_coverPhase_split (cap j : ℕ) : (coverPhase cap j).warrs =
    ["ord", "alv", "asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv",
      "xoff"] ++ [xofName j, xmmName j, asgName j, cpsName j] :=
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
    (coverPhase cap j).wvars =
      coverPhaseScalars ++ [xpName j, cnumName j, "i", cnumName j, "i"] :=
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [ctrName, xpName, curName, cnumName, cixName, mnumName, String.ext_iff],
      by simp [ctrName, xpName, curName, cnumName, cixName, mnumName, String.ext_iff],
      by simp [ctrName, xpName, curName, cnumName, cixName, mnumName, String.ext_iff]⟩

theorem belowArr_notMem_warrs_coverPhase (cap d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (coverPhase cap d).warrs := by
  rw [warrs_coverPhase_split, List.mem_append]
  rintro (hm | hm)
  · exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hq | hq | hq | hq <;> exact belowArr_ne h (le_refl d) (by tauto) hq

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
    rcases hm with hq | hq | hq | hq | hq
    exacts [belowVar_ne h (le_refl d) (by tauto) hq,
      belowVar_ne h (le_refl d) (by tauto) hq,
      absurd (hq ▸ hasDigit_of_belowVar h) (by decide),
      belowVar_ne h (le_refl d) (by tauto) hq,
      absurd (hq ▸ hasDigit_of_belowVar h) (by decide)]

/-! ### The padding, the colouring, the scatter phase and the readback -/

theorem wvars_enumBatch_eq (bat clu : String) (mb : ℕ) :
    (enumBatch bat clu mb).wvars = (enumBatch "" "" 0).wvars := rfl

theorem belowArr_notMem_warrs_enumBatch (bat clu : String) (mb : ℕ) {d : ℕ} {a : String}
    (h : BelowArr d a) : a ∉ (enumBatch bat clu mb).warrs := by
  rw [RamDriverFrames.warrs_enumBatch]
  intro hm
  exact notHasDigit_mem (by decide) hm (hasDigit_of_belowArr h)

theorem belowVar_notMem_wvars_enumBatch (bat clu : String) (mb : ℕ) {d : ℕ} {y : String}
    (h : BelowVar d y) : y ∉ (enumBatch bat clu mb).wvars := by
  rw [wvars_enumBatch_eq]
  intro hm
  exact notHasDigit_mem (l := (enumBatch "" "" 0).wvars) (by decide) hm (hasDigit_of_belowVar h)

theorem belowArr_notMem_warrs_colourCom (cap mb d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (colourCom cap mb d).warrs := by
  intro hm
  obtain ⟨c, hc⟩ := RamDriverFrames.mem_warrs_colourCom cap mb d hm
  exact belowArr_ne h (Nat.le_succ d) (by tauto) hc

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
  exact belowArr_ne h (le_refl d) (by tauto) hi

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

theorem wvars_clusterLoad (j : ℕ) :
    (clusterLoad j).wvars = ["i", "i", "bq", "p", "pend", "bq", "p"] := rfl

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
      x = alvName (j + 1) ∨ x = gamName (j + 1) ∨ x = memName (j + 1) := by
  rw [descendCom] at hx
  rcases mem_warrs_seq hx with h | h
  · rw [warrs_assign] at h; exact absurd h List.not_mem_nil
  rcases mem_warrs_seq h with h | h
  · rw [RamDriverFrames.warrs_clusterLoad] at h
    rcases List.mem_cons.mp h with hq | hq
    · exact Or.inl hq
    rcases List.mem_cons.mp hq with hq' | hq'
    · exact Or.inl hq'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (List.eq_of_mem_singleton hq')))))))
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
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.eq_of_mem_singleton h)))))))
  rcases mem_warrs_seq h with h | h
  · rw [subCom, RamDriverIO.warrs_fillCom] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.eq_of_mem_singleton h)))))))
  · rw [RamDriverFrames.warrs_memFilterCom] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (List.eq_of_mem_singleton h)))))))

/-- **What the descent assigns**: the depth's own connector, its child's
member count, and literals. -/
theorem hasDigit_wvars_descendCom (cap j : ℕ) {y : String}
    (hy : y ∈ (descendCom cap j).wvars) (hd : HasDigit y) :
    y = ctrName j ∨ y = mnumName (j + 1) := by
  rw [descendCom] at hy
  rcases mem_wvars_seq hy with h | h
  · rw [wvars_assign] at h; exact Or.inl (List.eq_of_mem_singleton h)
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
  rcases mem_wvars_seq h with h | h
  · rw [subCom, RamDriverIO.wvars_fillCom] at h
    exact absurd hd (notHasDigit_mem (by decide) h)
  · rw [RamDriverFrames.wvars_memFilterCom] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (by decide)
    · exact Or.inr rfl
    · exact absurd hd (by decide)
    · exact Or.inr rfl
    · exact absurd hd (by decide)

theorem belowVar_ne_mnumName {d : ℕ} {y : String} (h : BelowVar d y) {b' : ℕ}
    (hb : d ≤ b') : y ≠ mnumName b' := by
  obtain ⟨b, hbd, hc⟩ := h
  have hbb : b ≠ b' := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr => exact fun hq => hbb (mnumName_inj hq)
  all_goals simp [ctrName, xpName, curName, cnumName, cixName, mnumName, String.ext_iff]

theorem belowArr_notMem_warrs_descendCom (cap d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (descendCom cap d).warrs := by
  intro hm
  rcases hasDigit_warrs_descendCom cap d hm (hasDigit_of_belowArr h) with
    hq | hq | hq | hq | hq | hq | hq | hq
  exacts [belowArr_ne h (le_refl d) (by tauto) hq, belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (le_refl d) (by tauto) hq, belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (le_refl d) (by tauto) hq,
    belowArr_ne h (Nat.le_succ d) (by tauto) hq,
    belowArr_ne h (Nat.le_succ d) (by tauto) hq,
    belowArr_ne_memName h (Nat.le_succ d) hq]

theorem belowVar_notMem_wvars_descendCom (cap d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (descendCom cap d).wvars := by
  intro hm
  rcases hasDigit_wvars_descendCom cap d hm (hasDigit_of_belowVar h) with hq | hq
  · exact belowVar_ne h (le_refl d) (by tauto) hq
  · exact belowVar_ne_mnumName h (Nat.le_succ d) hq

/-! ### The base case -/

theorem not_ext_bb_of_belowVar {d : ℕ} {y : String} (h : BelowVar d y) :
    ¬ RamDriverBot.Ext "bb" y := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [by rw [ctrName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [xpName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [curName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [cnumName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [cixName]; exact not_ext_bb_append (by decide) (by decide) _,
    by rw [mnumName]; exact not_ext_bb_append (by decide) (by decide) _]

theorem belowArr_notMem_warrs_baseCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {a : String} (h : BelowArr d a) : a ∉ (baseCom q_top cap mb d φ).warrs := by
  intro hm
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ d, IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt d β hβ).1
  rcases RamDriverBot.warrs_baseCom hlocal a hm with hq | ⟨i, hq⟩ | hq
  · exact belowArr_ne_rep h hq
  · exact belowArr_ne h (le_refl d) (by tauto) hq
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

/-! ### The kill pass (wave R1.8-T2)

`RamDriver.killCom` is the base case's row body run at a *buffer entry*
instead of at a carrier counter, so its write set is
`RamDriverBot.warrs_baseFold`'s — the depth's tables and the generated
evaluator's scratch — with two scalars of its own, the buffer index
`"kk"` and the entry `"kv"`. Neither carries a digit, so neither is a
per-depth name; and the tables it writes are the **child**'s, which is
why a `BelowArr d` name survives it at the successor depth. -/

/-- The row body of the kill pass, as a write set: it is
`RamDriverBot.warrs_baseFold` at the store index `"kv"`. The two folds
differ only in that expression, which `Com.warrs` does not read, but they
are different terms, so the induction is run again here. -/
theorem warrs_killFold {L : ℕ} (jd : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (∀ β ∈ l, IsLocal β) → ∀ a ∈ (foldIdx (fun i β =>
      Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p l).warrs,
      (∃ i, a = tabName jd i) ∨ RamDriverBot.Ext "bb" a := by
  intro l
  induction l with
  | nil => intro p _ a ha; exact absurd ha List.not_mem_nil
  | cons β l ih =>
    intro p hloc a ha
    have he : (foldIdx (fun i β =>
        Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom jd β "bb") (.store (tabName jd p) (.var "kv") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb")))
              (p + 1) l) := rfl
    rw [he, Com.warrs, Com.warrs] at ha
    rcases List.mem_append.mp ha with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact Or.inr (RamDriverBot.warrs_botCom β (hloc β List.mem_cons_self) "bb" a h')
      · rw [Com.warrs, List.mem_singleton] at h'
        exact Or.inl ⟨p, h'⟩
    · exact ih (p + 1) (fun γ hγ => hloc γ (List.mem_cons_of_mem _ hγ)) a h

theorem wvars_killFold {L : ℕ} (jd : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (∀ β ∈ l, IsLocal β) → ∀ y ∈ (foldIdx (fun i β =>
      Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p l).wvars,
      RamDriverBot.Ext "bb" y ∨ ∃ i, 1 ≤ i ∧ y = envName i := by
  intro l
  induction l with
  | nil => intro p _ y hy; exact absurd hy List.not_mem_nil
  | cons β l ih =>
    intro p hloc y hy
    have he : (foldIdx (fun i β =>
        Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom jd β "bb") (.store (tabName jd p) (.var "kv") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb")))
              (p + 1) l) := rfl
    rw [he, Com.wvars, Com.wvars] at hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact RamDriverBot.wvars_botCom β (hloc β List.mem_cons_self) "bb" y h'
      · exact absurd h' (by rw [Com.wvars]; simp)
    · exact ih (p + 1) (fun γ hγ => hloc γ (List.mem_cons_of_mem _ hγ)) y h

/-- **What the kill pass writes**: the child depth's tables, and the
evaluator's scratch. -/
theorem warrs_killCom {q_top cap mb d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β) :
    ∀ a ∈ (killCom q_top cap mb d φ).warrs,
      (∃ i, a = tabName (d + 1) i) ∨ RamDriverBot.Ext "bb" a := by
  intro a ha
  rw [show (killCom q_top cap mb d φ).warrs =
    [] ++ ([] ++ ((([] ++ (foldIdx (fun i β => Com.seq (botCom (d + 1) β "bb")
      (.store (tabName (d + 1) i) (.var "kv") (.var "bb"))) 0
      (tablesAt q_top cap mb φ (d + 1))).warrs) ++ []) ++ [])) from rfl] at ha
  simp only [List.append_nil, List.nil_append] at ha
  exact warrs_killFold (d + 1) _ 0 hlocal a ha

/-- **And which scalars it assigns**: its own two, the environment slots,
and the evaluator's own. -/
theorem wvars_killCom {q_top cap mb d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β) :
    ∀ y ∈ (killCom q_top cap mb d φ).wvars,
      y = "kk" ∨ y = "kv" ∨ (∃ i, y = envName i) ∨ RamDriverBot.Ext "bb" y := by
  intro y hy
  rw [show (killCom q_top cap mb d φ).wvars =
    ["kk"] ++ (["kv"] ++ ((([envName 0] ++ (foldIdx (fun i β =>
      Com.seq (botCom (d + 1) β "bb")
        (.store (tabName (d + 1) i) (.var "kv") (.var "bb"))) 0
      (tablesAt q_top cap mb φ (d + 1))).wvars) ++ []) ++ ["kk"])) from rfl] at hy
  simp only [List.append_nil, List.mem_append, List.mem_singleton] at hy
  rcases hy with h | h | (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨0, h⟩))
  · rcases wvars_killFold (d + 1) _ 0 hlocal y h with h' | ⟨i, -, h'⟩
    · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inr (Or.inr (Or.inl ⟨i, h'⟩))
  · exact Or.inl h

/-! ### The kill list's write set

**Wave R1.8-T3-flip (a2).** `RamDriver.killListCom` writes one array —
the depth's own kill list — and five scalars: its count and the four
fixed scratch names of the two loops. Both are one `simp` off the fixed
syntax, and they live here beside their `killCom` twins because this is
where a pass's write-set syntax facts belong. -/

/-- **What the kill list pass writes**: the depth's kill list, and
nothing else. -/
theorem warrs_killListCom (mb j : ℕ) {a : String} (ha : a ∈ (killListCom mb j).warrs) :
    a = klName j := by
  simpa [killListCom, Com.warrs] using ha

/-- **And which scalars it assigns**: its count, and its four scratch
scalars — the buffer counter, the probed entry, the scan's flag and the
scan's counter. -/
theorem wvars_killListCom (mb j : ℕ) {y : String} (hy : y ∈ (killListCom mb j).wvars) :
    y = kkName j ∨ y = "kk" ∨ y = "kv" ∨ y = "kf" ∨ y = "kt" := by
  simp only [killListCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem notMem_warrs_killListCom {mb j : ℕ} {a : String} (ha : a ≠ klName j) :
    a ∉ (killListCom mb j).warrs :=
  fun h => ha (warrs_killListCom mb j h)

theorem notMem_wvars_killListCom {mb j : ℕ} {y : String} (h₁ : y ≠ kkName j)
    (h₂ : y ≠ "kk") (h₃ : y ≠ "kv") (h₄ : y ≠ "kf") (h₅ : y ≠ "kt") :
    y ∉ (killListCom mb j).wvars := by
  intro h
  rcases wvars_killListCom mb j h with h | h | h | h | h
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h
  · exact h₄ h
  · exact h₅ h

/-- The kill list pass does not touch the output tape. -/
theorem noWrite_killListCom (mb j : ℕ) : (killListCom mb j).NoWrite := by
  simp [killListCom, Com.NoWrite]

/-! ### The dead-aware atom pass's write sets

**Wave R1.8-T3-flip (b).** The four driver-side passes of the atom
program (`RamDriver.atomMemCom`, `killSumCom`, `outProbeCom`,
`outCntCom`, `atomFlagCom`) against the names the composite threads
across them. Each is one `simp` off fixed syntax, and they live here
beside their `killListCom` twins because this is where a pass's
write-set syntax facts belong.

The one that carries weight is the filter's: it writes the engine's
`"mem"` and **not** the child's `memName (j + 1)`, which is the
compiled content of `Refine.ScatterDeadPass.inplace_filter_refuted` —
the child's list has to survive every atom of the turn. -/

/-- **What the atom's filter writes**: the engine's member array, and
nothing else — in particular not the child's own list. -/
theorem warrs_atomMemCom (j ti : ℕ) {a : String} (ha : a ∈ (atomMemCom j ti).warrs) :
    a = "mem" := by
  simpa [atomMemCom, Com.warrs] using ha

theorem notMem_warrs_atomMemCom {j ti : ℕ} {a : String} (ha : a ≠ "mem") :
    a ∉ (atomMemCom j ti).warrs :=
  fun h => ha (warrs_atomMemCom j ti h)

/-- And which scalars it assigns: the engine's count and its two scratch
scalars. -/
theorem wvars_atomMemCom (j ti : ℕ) {y : String} (hy : y ∈ (atomMemCom j ti).wvars) :
    y = "mm" ∨ y = "ak" ∨ y = "av" := by
  simp only [atomMemCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem notMem_wvars_atomMemCom {j ti : ℕ} {y : String} (h₁ : y ≠ "mm") (h₂ : y ≠ "ak")
    (h₃ : y ≠ "av") : y ∉ (atomMemCom j ti).wvars := by
  intro h
  rcases wvars_atomMemCom j ti h with h | h | h
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h

theorem noWrite_atomMemCom (j ti : ℕ) : (atomMemCom j ti).NoWrite := by
  simp [atomMemCom, Com.NoWrite]

/-- **The kill walk writes no array at all** — it reads the depth's kill
list and the child's table row and accumulates in a scalar. -/
theorem warrs_killSumCom (j ti : ℕ) : (killSumCom j ti).warrs = [] := by
  simp [killSumCom, Com.warrs]

theorem notMem_warrs_killSumCom {j ti : ℕ} {a : String} : a ∉ (killSumCom j ti).warrs := by
  simp [warrs_killSumCom]

theorem wvars_killSumCom (j ti : ℕ) {y : String} (hy : y ∈ (killSumCom j ti).wvars) :
    y = "kc" ∨ y = "ke" := by
  simp only [killSumCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem notMem_wvars_killSumCom {j ti : ℕ} {y : String} (h₁ : y ≠ "kc") (h₂ : y ≠ "ke") :
    y ∉ (killSumCom j ti).wvars := by
  intro h
  rcases wvars_killSumCom j ti h with h | h
  · exact h₁ h
  · exact h₂ h

theorem noWrite_killSumCom (j ti : ℕ) : (killSumCom j ti).NoWrite := by
  simp [killSumCom, Com.NoWrite]

/-- **The outside probe writes no array either**: a flag, a register and
a counter. -/
theorem warrs_outProbeCom (j : ℕ) : (outProbeCom j).warrs = [] := by
  simp [outProbeCom, Com.warrs]

theorem notMem_warrs_outProbeCom {j : ℕ} {a : String} : a ∉ (outProbeCom j).warrs := by
  simp [warrs_outProbeCom]

theorem wvars_outProbeCom (j : ℕ) {y : String} (hy : y ∈ (outProbeCom j).wvars) :
    y = "of" ∨ y = "oz" ∨ y = "oi" := by
  simp only [outProbeCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem notMem_wvars_outProbeCom {j : ℕ} {y : String} (h₁ : y ≠ "of") (h₂ : y ≠ "oz")
    (h₃ : y ≠ "oi") : y ∉ (outProbeCom j).wvars := by
  intro h
  rcases wvars_outProbeCom j h with h | h | h
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h

theorem noWrite_outProbeCom (j : ℕ) : (outProbeCom j).NoWrite := by
  simp [outProbeCom, Com.NoWrite]

/-- The outside count and the verdict are straight-line assignments. -/
theorem warrs_outCntCom (j : ℕ) : (outCntCom j).warrs = [] := by
  simp [outCntCom, Com.warrs]

theorem wvars_outCntCom (j : ℕ) : (outCntCom j).wvars = ["oc"] := by
  simp [outCntCom, Com.wvars]

theorem noWrite_outCntCom (j : ℕ) : (outCntCom j).NoWrite := by
  simp [outCntCom, Com.NoWrite]

theorem warrs_atomFlagCom (t : ℕ) : (atomFlagCom t).warrs = [] := by
  simp [atomFlagCom, Com.warrs]

theorem wvars_atomFlagCom (t : ℕ) {y : String} (hy : y ∈ (atomFlagCom t).wvars) :
    y = "os" ∨ y = "flag" := by
  simp only [atomFlagCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem noWrite_atomFlagCom (t : ℕ) : (atomFlagCom t).NoWrite := by
  simp [atomFlagCom, Com.NoWrite]

/-! ### The dead-aware atom program, and the phase it folds into

**Wave R1.8-T3-flip (c1).** The composite `RamDriver.scatDeadCom` and
the phase `RamDriver.scatterDeadCom` that replaces the fold of
`scatterCom` in the turn, as write sets. The nine passes' own facts are
above; what is added here is their union, read once so that the frame
conditions of the turn — that the phase writes no table, and that the
depth's own arrays and the driver's scalars survive it — can be
discharged against it.

Six fixed arrays and the generated evaluator's scratch is the whole of
it. Five of the six are the engine's own calling convention and working
set (`"alv"`, `"mem"`, `"dist"`, `"exc"`, `"q"`, `"qd"`), which
`Refine.ScatterDeadPass.warrs_scatBlockCom` settles for the engine and
which the two copies before it settle for the convention; the scratch is
`RamDriverBot.Ext "bb"`, exactly as for the kill pass, since the outside
class's bit is one `botCom` fragment. **No table row is written**, which
is what a turn's frame needs, and no per-depth name at all — the atom
program only ever *reads* the depth's arrays. -/

/-- **What one dead-aware atom writes.** -/
theorem warrs_scatDeadCom {L : ℕ} (j ti : ℕ) (β : DistFO L 1) (r t : ℕ) (hloc : IsLocal β)
    {a : String} (ha : a ∈ (scatDeadCom j ti β r t).warrs) :
    a ∈ ["mem", "alv", "dist", "exc", "q", "qd"] ∨ RamDriverBot.Ext "bb" a := by
  rw [scatDeadCom, Com.warrs, Com.warrs, Com.warrs, Com.warrs, Com.warrs, Com.warrs,
    Com.warrs, Com.warrs, warrs_killSumCom, warrs_outProbeCom, warrs_outCntCom,
    warrs_atomFlagCom, atomBitCom, Com.warrs, Com.warrs, Com.warrs,
    RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom, RamDriverIO.warrs_fillCom] at ha
  simp only [List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at ha
  rcases ha with (hemp | hb) | ha | ha | ha | ha
  · exact absurd hemp (by simp [Com.warrs])
  · exact Or.inr (RamDriverBot.warrs_botCom β hloc "bb" a hb)
  · exact Or.inl (by simp [warrs_atomMemCom j ti ha])
  · exact Or.inl (by simp [ha])
  · exact Or.inl (by simp [ha])
  · rcases Refine.ScatterDeadPass.warrs_scatBlockCom r t ha with h | h | h | h <;>
      exact Or.inl (by simp [h])

/-- **The atom program writes no table row.** The row of the atom's own
formula is *read*, at the child's member list and at the turn's kill
list, and never written — which is the whole reason the phase can run
after the nested call. -/
theorem tabName_notMem_warrs_scatDeadCom {L : ℕ} {j ti d i : ℕ} {β : DistFO L 1} {r t : ℕ}
    (hloc : IsLocal β) : tabName d i ∉ (scatDeadCom j ti β r t).warrs := by
  intro ha
  rcases warrs_scatDeadCom j ti β r t hloc ha with h | h
  · revert h; simp [tabName, String.ext_iff]
  · exact RamDriverBot.not_ext_b_tabName d i (RamDriverCompose.ext_b_of_ext_bb h)

open Classical in
/-- **What the scatter phase of one tabled formula writes**, over any
list of atoms starting at any position. -/
theorem warrs_scatterDeadFold {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} (j i : ℕ)
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ) :
    ∀ (l : List (Lax3.ScatterSentences.ScatterSentence (sigL cap mb (j + 1)))) (k₀ : ℕ),
      (∀ σs ∈ l, σs.β ∈ tablesAt q_top cap mb φ (j + 1)) →
      ∀ a ∈ (foldIdx (fun k σs =>
          Com.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1))) σs.β σs.r σs.t)
            (.assign (flgName j i k) (.var "flag"))) k₀ l).warrs,
        a ∈ ["mem", "alv", "dist", "exc", "q", "qd"] ∨ RamDriverBot.Ext "bb" a := by
  intro l
  induction l with
  | nil => intro k₀ _ a ha; exact absurd ha (by rw [foldIdx]; simp [Com.warrs])
  | cons x xs ih =>
      intro k₀ hmem a ha
      rw [foldIdx, Com.warrs, Com.warrs, List.mem_append, List.mem_append] at ha
      rcases ha with (h | h) | h
      · exact warrs_scatDeadCom j _ x.β x.r x.t (hloc _ (hmem x List.mem_cons_self)) h
      · exact absurd h (by simp [Com.warrs])
      · exact ih (k₀ + 1) (fun s hs => hmem s (List.mem_cons_of_mem _ hs)) a h

open Classical in
/-- **And what the whole phase writes**, over any list of tabled
formulas — the union is the same six arrays and the same scratch. -/
theorem warrs_scatterDeadPhase {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} (j : ℕ)
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ) :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ),
      (∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) →
      ∀ a ∈ (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) i₀ l).warrs,
        a ∈ ["mem", "alv", "dist", "exc", "q", "qd"] ∨ RamDriverBot.Ext "bb" a := by
  intro l
  induction l with
  | nil => intro i₀ _ a ha; exact absurd ha (by rw [foldIdx]; simp [Com.warrs])
  | cons x xs ih =>
      intro i₀ hmem a ha
      rw [foldIdx, Com.warrs, List.mem_append] at ha
      rcases ha with h | h
      · exact warrs_scatterDeadFold j i₀ hloc _ 0
          (fun s hs => mem_tablesAt_succ_of_mem_bcAtomsOf_right (hmem x List.mem_cons_self) hs)
          a (by rwa [scatterDeadCom] at h)
      · exact ih (i₀ + 1) (fun β hβ => hmem β (List.mem_cons_of_mem _ hβ)) a h

open Classical in
/-- **The scatter phase leaves every table of every depth alone.** This
is the phase's whole contribution to `RamDriverCluster.ClusterFrames`,
and it is the clause the swap has to reproduce: the landed fold of
`scatterCom` wrote `"tab"`, a *copy* of the row, and this one does not
copy at all. -/
theorem tabName_notMem_warrs_scatterDeadPhase {q_top cap mb : ℕ}
    {φ : Lax3.FirstOrder.FO 0} (j d i : ℕ)
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ)
    (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ)
    (hmem : ∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) :
    tabName d i ∉ (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) i₀ l).warrs := by
  intro ha
  rcases warrs_scatterDeadPhase j hloc l i₀ hmem _ ha with h | h
  · revert h; simp [tabName, String.ext_iff]
  · exact RamDriverBot.not_ext_b_tabName d i (RamDriverCompose.ext_b_of_ext_bb h)

/-- **No name of a depth below is the kill list of any depth** — `"kl"`
is a fresh prefix, so the whole table is settled by the first two
characters. -/
theorem belowArr_ne_klName {d : ℕ} {a : String} (h : BelowArr d a) (b' : ℕ) :
    a ≠ klName b' := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨c, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [alvName, gamName, cluName, resName, batName, ordName, xofName, xmmName,
      asgName, cpsName, memName, colName, tabName, klName, String.ext_iff]

/-- **Nor is any scalar of a depth below the kill count of any depth.** -/
theorem belowVar_ne_kkName {d : ℕ} {y : String} (h : BelowVar d y) (b' : ℕ) :
    y ≠ kkName b' := by
  obtain ⟨b, -, hc⟩ := h
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ctrName, xpName, curName, cnumName, cixName, mnumName, kkName, String.ext_iff]

theorem belowArr_notMem_warrs_killListCom (mb d : ℕ) {a : String} (h : BelowArr d a) :
    a ∉ (killListCom mb d).warrs :=
  notMem_warrs_killListCom (belowArr_ne_klName h d)

theorem belowVar_notMem_wvars_killListCom (mb d : ℕ) {y : String} (h : BelowVar d y) :
    y ∉ (killListCom mb d).wvars :=
  notMem_wvars_killListCom (belowVar_ne_kkName h d)
    (fun hq => absurd (hq ▸ hasDigit_of_belowVar h) (by decide))
    (fun hq => absurd (hq ▸ hasDigit_of_belowVar h) (by decide))
    (fun hq => absurd (hq ▸ hasDigit_of_belowVar h) (by decide))
    (fun hq => absurd (hq ▸ hasDigit_of_belowVar h) (by decide))

theorem noWrite_killFold {L : ℕ} (jd : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (foldIdx (fun i β =>
      Com.seq (botCom jd β "bb")
        (.store (tabName jd i) (.var "kv") (.var "bb"))) p l).NoWrite := by
  intro l
  induction l with
  | nil => exact fun p => Com.noWrite_skip
  | cons β l ih =>
    intro p
    have he : (foldIdx (fun i β =>
        Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom jd β "bb") (.store (tabName jd p) (.var "kv") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb")))
              (p + 1) l) := rfl
    rw [he]
    exact ⟨⟨RamDriverBot.noWrite_botCom β "bb", trivial⟩, ih (p + 1)⟩

/-- The kill pass does not touch the output tape. -/
theorem noWrite_killCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    (killCom q_top cap mb d φ).NoWrite :=
  ⟨trivial, trivial, ⟨⟨⟨trivial, noWrite_killFold (d + 1) _ 0⟩, trivial⟩, trivial⟩⟩

theorem belowArr_notMem_warrs_killCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {a : String} (h : BelowArr d a) : a ∉ (killCom q_top cap mb d φ).warrs := by
  intro hm
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (d + 1) β hβ).1
  rcases warrs_killCom hlocal a hm with ⟨i, hq⟩ | hq
  · exact belowArr_ne h (Nat.le_succ d) (by tauto) hq
  · exact not_ext_bb_of_belowArr h hq

theorem belowVar_notMem_wvars_killCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {y : String} (h : BelowVar d y) : y ∉ (killCom q_top cap mb d φ).wvars := by
  intro hm
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (d + 1) β hβ).1
  rcases wvars_killCom hlocal y hm with hq | hq | ⟨i, hq⟩ | hq
  · exact absurd (hq ▸ hasDigit_of_belowVar h) (by decide)
  · exact absurd (hq ▸ hasDigit_of_belowVar h) (by decide)
  · exact belowVar_ne_envName h i hq
  · exact not_ext_bb_of_belowVar h hq

/-! ### The recursion

One induction on the fuel. Every phase of a level writes only fixed
scratch names and per-depth names at its own depth or the next, and the
nested call is the induction hypothesis at `d + 1`, where the frame is
one depth weaker and `BelowArr.mono` bridges the two. -/

open Classical in
/-- **A level writes no array of a depth below its own.** -/
theorem belowArr_notMem_warrs_driverAux (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {a : String}, BelowArr d a →
      a ∉ (driverAux q_top cap mb 0 ℓ φ f d).warrs := by
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
      · exact belowArr_notMem_warrs_orderCom d h hq
      rcases mem_warrs_seq hq with hq | hq
      · exact belowArr_notMem_warrs_coverPhase cap d h hq
      rcases mem_warrs_seq hq with hq | hq
      · -- the dead-row sweep (rebase B8): the base case's own text, which
        -- since R1.8-T4a is exactly this pass at the bottom depth
        refine belowArr_notMem_warrs_baseCom q_top cap mb d φ h ?_
        rw [show (baseCom q_top cap mb d φ).warrs
            = (sweepCom q_top cap mb d φ).warrs from rfl]
        exact hq
      rcases mem_warrs_seq hq with hq | hq
      · rw [warrs_assign] at hq; exact absurd hq List.not_mem_nil
      rw [warrs_while] at hq
      rcases mem_warrs_seq hq with hq | hq
      · rw [warrs_assign] at hq; exact absurd hq List.not_mem_nil
      rcases mem_warrs_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases mem_warrs_seq hq with hr | hr
        · exact belowArr_notMem_warrs_descendCom cap d h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_enumBatch (batName d) (cluName d) mb h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_colourCom cap mb d h hr
        rcases mem_warrs_seq hr with hr | hr
        · -- the kill pass (wave R1.8-T2): the child depth's tables and the
          -- evaluator's scratch, so a name of a depth below `d` survives it
          exact belowArr_notMem_warrs_killCom q_top cap mb d φ h hr
        rcases mem_warrs_seq hr with hr | hr
        · -- the kill list (wave R1.8-T3-flip): this depth's own list
          exact belowArr_notMem_warrs_killListCom mb d h hr
        rcases mem_warrs_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases mem_warrs_seq hr with hr | hr
        · exact belowArr_notMem_warrs_scatterFold q_top cap mb d φ h hr
        · exact belowArr_notMem_warrs_readbackCom q_top cap mb d φ h hr
      · rw [warrs_assign] at hq; exact absurd hq List.not_mem_nil

open Classical in
/-- **A level assigns no scalar of a depth below its own.** -/
theorem belowVar_notMem_wvars_driverAux (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {y : String}, BelowVar d y →
      y ∉ (driverAux q_top cap mb 0 ℓ φ f d).wvars := by
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
      · exact belowVar_notMem_wvars_orderCom d h hq
      rcases mem_wvars_seq hq with hq | hq
      · exact belowVar_notMem_wvars_coverPhase cap d h hq
      rcases mem_wvars_seq hq with hq | hq
      · -- the dead-row sweep (rebase B8): the base case's own text, which
        -- since R1.8-T4a is exactly this pass at the bottom depth
        refine belowVar_notMem_wvars_baseCom q_top cap mb d φ h ?_
        rw [show (baseCom q_top cap mb d φ).wvars
            = (sweepCom q_top cap mb d φ).wvars from rfl]
        exact hq
      rcases mem_wvars_seq hq with hq | hq
      · rw [wvars_assign] at hq
        exact belowVar_ne h (le_refl d) (by tauto) (List.eq_of_mem_singleton hq)
      rw [wvars_while] at hq
      rcases mem_wvars_seq hq with hq | hq
      · rw [wvars_assign] at hq
        exact belowVar_ne h (le_refl d) (by tauto) (List.eq_of_mem_singleton hq)
      rcases mem_wvars_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases mem_wvars_seq hq with hr | hr
        · exact belowVar_notMem_wvars_descendCom cap d h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_enumBatch (batName d) (cluName d) mb h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_colourCom cap mb d h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_killCom q_top cap mb d φ h hr
        rcases mem_wvars_seq hr with hr | hr
        · -- the kill list (wave R1.8-T3-flip): its count is this depth's own,
          -- and its four scratch scalars carry no digit
          exact belowVar_notMem_wvars_killListCom mb d h hr
        rcases mem_wvars_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases mem_wvars_seq hr with hr | hr
        · exact belowVar_notMem_wvars_scatterFold q_top cap mb d φ h hr
        · exact belowVar_notMem_wvars_readbackCom q_top cap mb d φ h hr
      · rw [wvars_assign] at hq
        exact belowVar_ne h (le_refl d) (by tauto) (List.eq_of_mem_singleton hq)

/-- **The driver at a depth writes no array of a depth below it.** -/
theorem belowArr_notMem_warrs_driverAt {q_top cap mb ℓ d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {a : String} (h : BelowArr d a) : a ∉ (driverAt q_top cap mb 0 ℓ φ d).warrs := by
  rw [driverAt]
  exact belowArr_notMem_warrs_driverAux q_top cap mb ℓ φ (ℓ - d) d h

/-- **Nor does it assign a scalar of one.** -/
theorem belowVar_notMem_wvars_driverAt {q_top cap mb ℓ d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {y : String} (h : BelowVar d y) : y ∉ (driverAt q_top cap mb 0 ℓ φ d).wvars := by
  rw [driverAt]
  exact belowVar_notMem_wvars_driverAux q_top cap mb ℓ φ (ℓ - d) d h

/-! ### The three names the compacted loop header owns

**Rebase B3.** The centre loop reads the compacted centre list
`cpsName j`, its length `cnumName j` and its own index `cixName j`
*between* turns, so the turn — the nested call included — must leave all
three alone. None of the six phases writes them: the five that are not
the nested call write fixed scratch names, the depth's own cluster
arrays, the next depth's palette and the depth's tables, and the nested
call is a level at depth `j + 1`, which
`belowArr_notMem_warrs_driverAt` already covers. -/

open Classical in
/-- **The compacted list survives a turn.** -/
theorem cpsName_notMem_warrs_clusterCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {inner : Com} (hin : cpsName d ∉ inner.warrs) :
    cpsName d ∉ (clusterCom q_top cap mb φ d inner).warrs := by
  rw [clusterCom]
  intro hq
  rcases mem_warrs_seq hq with hr | hr
  · rcases hasDigit_warrs_descendCom cap d hr (hasDigit_cpsName d) with
      hc | hc | hc | hc | hc | hc | hc | hc <;>
      exact absurd hc (by simp [cpsName, cluName, resName, balName, balAltName, batName,
        alvName, gamName, memName, String.ext_iff])
  rcases mem_warrs_seq hr with hr | hr
  · rw [RamDriverFrames.warrs_enumBatch] at hr
    exact notHasDigit_mem (by decide) hr (hasDigit_cpsName d)
  rcases mem_warrs_seq hr with hr | hr
  · obtain ⟨c, hc⟩ := RamDriverFrames.mem_warrs_colourCom cap mb d hr
    exact absurd hc (by simp [cpsName, colName, String.ext_iff])
  rcases mem_warrs_seq hr with hr | hr
  · -- the kill pass writes the child's tables and the evaluator's scratch
    have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β :=
      fun β hβ => (tableRank_of_mem_tablesAt (d + 1) β hβ).1
    rcases warrs_killCom hlocal _ hr with ⟨i, hc⟩ | hc
    · exact absurd hc (by simp [cpsName, tabName, String.ext_iff])
    · exact absurd hc (by rw [cpsName]; exact not_ext_bb_append (by decide) (by decide) _)
  rcases mem_warrs_seq hr with hr | hr
  · -- the kill list writes the depth's own list, and nothing else
    exact absurd (warrs_killListCom mb d hr)
      (by simp [cpsName, klName, String.ext_iff])
  rcases mem_warrs_seq hr with hr | hr
  · exact hin hr
  rcases mem_warrs_seq hr with hr | hr
  · exact (by decide : ∀ q ∈ scratchArrs, ¬ HasDigit q) _
      (RamDriverFrames.warrs_scatterFold q_top cap mb φ d _ 0 _ hr) (hasDigit_cpsName d)
  · obtain ⟨i, hi⟩ := RamDriverBase.mem_warrs_readbackCom hr
    exact absurd hi (by simp [cpsName, tabName, String.ext_iff])

open Classical in
/-- **A per-depth scalar of the depth's own loop header survives a
turn**, given that it is not the depth's connector — which is the one
per-depth scalar the descent assigns.

**Wave R1.8-T3-flip (a2)** adds `hykk`, and it is not bookkeeping: the
kill list's count `kkName d` is a *per-depth* scalar, so unlike the kill
pass's `"kk"`/`"kv"` it carries a digit and `hy` alone cannot rule it
out. The two callers below discharge it by the numeral's prefix, the
same character arithmetic as `hyctr` and `hymm`. -/
theorem perDepthVar_notMem_wvars_clusterCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {inner : Com} {y : String} (hy : HasDigit y) (hyctr : y ≠ ctrName d)
    (hymm : y ≠ mnumName (d + 1)) (hykk : y ≠ kkName d) (hyus : '_' ∉ y.toList)
    (hyenv : ∀ i, y ≠ envName i) (hybb : ¬ RamDriverBot.Ext "bb" y)
    (hin : y ∉ inner.wvars) :
    y ∉ (clusterCom q_top cap mb φ d inner).wvars := by
  rw [clusterCom]
  intro hq
  rcases mem_wvars_seq hq with hr | hr
  · exact (hasDigit_wvars_descendCom cap d hr hy).elim hyctr hymm
  rcases mem_wvars_seq hr with hr | hr
  · rw [wvars_enumBatch_eq] at hr
    exact notHasDigit_mem (l := (enumBatch "" "" 0).wvars) (by decide) hr hy
  rcases mem_wvars_seq hr with hr | hr
  · exact notHasDigit_wvars_colourCom cap mb d y hr hy
  rcases mem_wvars_seq hr with hr | hr
  · -- the kill pass: its own two scalars carry no digit, and the rest is the
    -- evaluator's own
    have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (d + 1), IsLocal β :=
      fun β hβ => (tableRank_of_mem_tablesAt (d + 1) β hβ).1
    rcases wvars_killCom hlocal y hr with hc | hc | ⟨i, hc⟩ | hc
    · exact absurd (hc ▸ hy) (by decide)
    · exact absurd (hc ▸ hy) (by decide)
    · exact hyenv i hc
    · exact hybb hc
  rcases mem_wvars_seq hr with hr | hr
  · -- the kill list: its count is the depth's own scalar `hykk` excludes, and
    -- its four scratch scalars carry no digit
    rcases wvars_killListCom mb d hr with hc | hc | hc | hc | hc
    · exact hykk hc
    · exact absurd (hc ▸ hy) (by decide)
    · exact absurd (hc ▸ hy) (by decide)
    · exact absurd (hc ▸ hy) (by decide)
    · exact absurd (hc ▸ hy) (by decide)
  rcases mem_wvars_seq hr with hr | hr
  · exact hin hr
  rcases mem_wvars_seq hr with hr | hr
  · have hy2 : y ≠ "i" := fun hq' => (by decide : ¬ HasDigit "i") (hq' ▸ hy)
    have hy3 : y ∉ (RamScatter.scatterCom 0 0).wvars := fun hq' =>
      (by decide : ∀ q ∈ (RamScatter.scatterCom 0 0).wvars, ¬ HasDigit q) _ hq' hy
    obtain ⟨i, β, -, hm'⟩ := mem_wvars_foldIdx _ _ 0 hr
    rw [RamDriverFrames.scatterCom_eq] at hm'
    obtain ⟨k, σs, -, hm''⟩ := mem_wvars_foldIdx _ _ 0 hm'
    exact RamDriverFrames.notMem_wvars_atomCom hyus hy2 hy3 hm''
  · exact RamDriverBase.not_mem_wvars_readbackCom
      (fun hq' => (by decide : ¬ HasDigit "z") (hq' ▸ hy)) hr

open Classical in
theorem cnumName_notMem_wvars_clusterCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {inner : Com} (hin : cnumName d ∉ inner.wvars) :
    cnumName d ∉ (clusterCom q_top cap mb φ d inner).wvars :=
  perDepthVar_notMem_wvars_clusterCom q_top cap mb d φ (hasDigit_cnumName d)
    (by simp [cnumName, ctrName, String.ext_iff])
    (by simp [cnumName, mnumName, String.ext_iff])
    (by simp [cnumName, kkName, String.ext_iff])
    (by rw [cnumName]; exact underscore_notMem_prefixed (by decide) d)
    (fun i => RamDriverBot.lit_ne_envName (q := cnumName d) (c := 'c')
      ⟨_, by rw [cnumName, String.toList_append]; rfl⟩ (by decide) i)
    (by rw [cnumName]; exact not_ext_bb_append (by decide) (by decide) _) hin

open Classical in
theorem cixName_notMem_wvars_clusterCom (q_top cap mb d : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {inner : Com} (hin : cixName d ∉ inner.wvars) :
    cixName d ∉ (clusterCom q_top cap mb φ d inner).wvars :=
  perDepthVar_notMem_wvars_clusterCom q_top cap mb d φ (hasDigit_cixName d)
    (by simp [cixName, ctrName, String.ext_iff])
    (by simp [cixName, mnumName, String.ext_iff])
    (by simp [cixName, kkName, String.ext_iff])
    (by rw [cixName]; exact underscore_notMem_prefixed (by decide) d)
    (fun i => RamDriverBot.lit_ne_envName (q := cixName d) (c := 'c')
      ⟨_, by rw [cixName, String.toList_append]; rfl⟩ (by decide) i)
    (by rw [cixName]; exact not_ext_bb_append (by decide) (by decide) _) hin

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
    (h : d < ℓ) : "wa" ∈ (driverAt q_top cap mb 0 ℓ φ d).warrs := by
  rw [driverAt_succ q_top cap mb 0 ℓ φ h]
  refine mem_warrs_seq_right (mem_warrs_seq_right (mem_warrs_seq_right (mem_warrs_seq_right
    (mem_warrs_while_body (mem_warrs_seq_right (mem_warrs_seq_left ?_))))))
  rw [clusterCom]
  refine mem_warrs_seq_right (mem_warrs_seq_left ?_)
  rw [RamDriverFrames.warrs_enumBatch]
  exact List.mem_cons_self

open Classical in
/-- **And the elimination's accumulator.** -/
theorem elm_mem_warrs_driverAt {q_top cap mb ℓ d : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (h : d < ℓ) : "elm" ∈ (driverAt q_top cap mb 0 ℓ φ d).warrs := by
  rw [driverAt_succ q_top cap mb 0 ℓ φ h]
  refine mem_warrs_seq_left ?_
  rw [warrs_orderCom_split]
  exact List.mem_append_left _ (by decide)

end Lax3Proofs.RamDriverWrites
