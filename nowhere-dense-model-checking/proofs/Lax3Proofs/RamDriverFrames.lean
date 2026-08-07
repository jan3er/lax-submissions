import Lax3Proofs.RamDriverBase
import Lax3Proofs.RamDriverIO

/-!
The scatter phase of a cluster, and the two frames of a turn.

Three of `Lax3Proofs.RamDriverCluster`'s obligations are discharged here:
`RamDriverCluster.ScatterStep`, the fold of `RamScatter.scatterCom` over
the depth's table; and the two frame conditions `InnerFrames` and
`ClusterFrames`, which no syntax can supply because both commands
contain the nested driver, which is a program *variable*.

# The scatter phase

`atomCom` is one atom: the two copies the calling convention asks for —
the depth-`(j+1)` mask into `alv`, the atom's own depth-`(j+1)` table row
into `tab` — the pass, and the atom's flag. `atom_spec` is what one is
worth, `atoms_spec` folds it over one formula's atoms and `blocks_spec`
folds *that* over the depth's table; `scatterStep` is the obligation.

`ScatPre` is what the phase carries — the obligation's own precondition,
named once — and `ScatPre.run` is that a call of the phase preserves it:
the pass and the copies write `alv`, `tab` and the search's three scratch
arrays, and none of those is an array the turn pins, since the per-depth
names are prefixed and the fixed ones are elsewhere.

# The frames

`innerFrames` reduces `InnerFrames` to two syntactic questions about
`inner` — that it writes none of `TurnFrozen`'s arrays and assigns none
of four scalars — plus a run of it, which a `Spec` needs and which no
frame can produce.

`clusterFrames` runs the six phases and reads the two clauses off their
postconditions: `RamDriverCluster.CoverHeld` crosses the turn because
every one of the five obligations carries `RamDriverCluster.TurnPre`,
and the table clause is the readback's own, moved back to the turn's
entry by `tabName_notMem_warrs_turn` — that the descent, the padding,
the colouring and the scatter phase write no table.

# What the driver used to owe

The three conjuncts this file once carried as hypotheses are now in the
surface, and all three theorems consume them from it.

* `hcolread` is gone from `scatterStep` and from
  `RamDriverBase.readbackStep`: `RamDriverCluster.ScatterStep` and
  `ReadbackStep` carry the palette equation — and the bit clause beside
  it — in their own preconditions, which is where
  `RamDriverCluster.ColourStep` leaves them.
* `hplay` is gone from `clusterFrames`: `RamDriverCluster.ClusterFrames`
  now takes the same hypothesis about `inner` that
  `RamDriver.ClusterStepImplements` takes, and `RamDriver.PlayRec` — the
  recorded play — is a conjunct of `RamDriverCluster.TurnPre`, so the
  turn can run the nested call and hand the record back.
* `hA`, `hV` in `innerFrames` and `hinnerTab` in `clusterFrames` are now
  *true* of `RamDriver.driverAt … (j + 1)`. The clash they recorded is
  repaired at the program: the ordering pass writes `ordName j`, the
  cover's answers are copied into `xofName j`, `xmmName j`, `asgName j`
  and `xpName j` by `RamDriver.coverSave`, and the centre cursor is
  `curName j`. A nested level touches none of them, so `TurnFrozen` and
  the four scalar side conditions are frame conditions of the recursion
  and not obstructions to it.
-/

namespace Lax3Proofs.RamDriverFrames

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (TurnPre CoverHeld ClusterData BatchData ScatVal
  ScatterStep DescendStep EnumStep ColourStep ReadbackStep eq_of_arrOf_eq masked_alv_eq)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### The generated names

Every per-depth name of the driver is a literal prefix followed by a
decimal numeral, and the flags carry two. What a walk over the scatter
phase needs of them is that they are none of the five arrays the phase
writes, and that the flags are addressed injectively — the first because
the separator does not occur in a decimal representation, the second
because the representation is injective. Both come off
`RamDriverBase`'s kit. -/

/-- The arrays the calling convention and the scatter pass write. -/
def scratchArrs : List String := ["alv", "tab", "exc", "dist", "q"]

theorem notMem_scratchArrs_of_underscore {a : String} (h : '_' ∈ a.toList) :
    a ∉ scratchArrs := by
  simp only [scratchArrs, List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl | rfl | rfl) <;> simp at h

theorem underscore_notMem_prefixed {p : String} (hp : '_' ∉ p.toList) (k : ℕ) :
    '_' ∉ (p ++ toString k).toList := by
  simp only [String.toList_append, List.mem_append, not_or]
  exact ⟨hp, by simp⟩

theorem alvName_notMem_scratchArrs (j : ℕ) : alvName j ∉ scratchArrs := by
  simp [scratchArrs, alvName, String.ext_iff]

theorem memName_notMem_scratchArrs (j : ℕ) : memName j ∉ scratchArrs := by
  simp [scratchArrs, memName, String.ext_iff]

theorem gamName_notMem_scratchArrs (j : ℕ) : gamName j ∉ scratchArrs := by
  simp [scratchArrs, gamName, String.ext_iff]

theorem cluName_notMem_scratchArrs (j : ℕ) : cluName j ∉ scratchArrs := by
  simp [scratchArrs, cluName, String.ext_iff]

theorem resName_notMem_scratchArrs (j : ℕ) : resName j ∉ scratchArrs := by
  simp [scratchArrs, resName, String.ext_iff]

theorem batName_notMem_scratchArrs (j : ℕ) : batName j ∉ scratchArrs := by
  simp [scratchArrs, batName, String.ext_iff]

theorem underscore_mem_colName (j c : ℕ) : '_' ∈ (colName j c).toList := by
  rw [colName]
  simp only [String.toList_append, List.mem_append]
  exact _root_.Or.inl (_root_.Or.inr (by simp))

theorem colName_notMem_scratchArrs (j c : ℕ) : colName j c ∉ scratchArrs :=
  notMem_scratchArrs_of_underscore (underscore_mem_colName j c)

theorem tabName_notMem_scratchArrs (j i : ℕ) : tabName j i ∉ scratchArrs :=
  notMem_scratchArrs_of_underscore (RamDriverBase.underscore_mem_tabName j i)

theorem underscore_mem_flgName (j i k : ℕ) : '_' ∈ (flgName j i k).toList := by
  rw [flgName]
  simp only [String.toList_append, List.mem_append]
  exact _root_.Or.inl (_root_.Or.inr (by simp))

theorem flgName_ne_lit (j i k : ℕ) {q : String} (h : '_' ∉ q.toList) : flgName j i k ≠ q :=
  fun he => h (he ▸ underscore_mem_flgName j i k)

/-- **The scatter flags are addressed injectively.** -/
theorem flgName_inj {j i k j' i' k' : ℕ} (h : flgName j i k = flgName j' i' k') :
    j = j' ∧ i = i' ∧ k = k' := by
  simp only [flgName, String.ext_iff] at h
  simp at h
  obtain ⟨h1, h2⟩ := RamDriverBase.append_cons_inj
    (RamDriverBase.underscore_not_mem_toDigits j)
    (RamDriverBase.underscore_not_mem_toDigits j') h
  obtain ⟨h3, h4⟩ := RamDriverBase.append_cons_inj
    (RamDriverBase.underscore_not_mem_toDigits i)
    (RamDriverBase.underscore_not_mem_toDigits i') h2
  exact ⟨RamDriverBase.toDigits_injective h1, RamDriverBase.toDigits_injective h3,
    RamDriverBase.toDigits_injective h4⟩

/-! ### What the scatter phase carries -/

variable {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
  {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
  {Alv' Gam' : ℕ → ℕ} {C' : ℕ → ℕ → ℕ}

/-- `RamDriverCluster.ScatterStep`'s precondition, named once: the
turn's own state, the cluster's data, and the next depth's palette and
tables. The fold over the atoms carries it from one call to the next. -/
def ScatPre (B q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n)) (w : Fin mb → Fin n)
    (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
    ClusterData n mb j B G M X W w Alv' Gam' σ ∧
    (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
    (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
    colRead n C' (sigL cap mb (j + 1)) =
      stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
    TableInv q_top cap mb φ G (j + 1) Alv' C' σ

/-- **The state the scatter phase carries survives every call it
makes.** The pass and the two copies that precede it write `alv`, `tab`
and the search's three scratch arrays and nothing else, and none of
those is an array this clause pins — the per-depth names are prefixed
and the fixed ones are elsewhere. The three scalars are the carrier, the
slot count and the cover's cursor, which no sub-program of the phase
assigns. -/
theorem ScatPre.run {c : Com} {σ σ' : Env} {K : ℕ}
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ)
    (hrun : Run B c σ σ' K) (hA : ∀ a ∈ c.warrs, a ∈ scratchArrs)
    (hV : ∀ y ∈ ["n", "m", "lw"], y ∉ c.wvars)
    (hVctr : ∀ a : ℕ, ctrName a ∉ c.wvars) (hVxp : xpName j ∉ c.wvars)
    (hVmm : ∀ a : ℕ, mnumName a ∉ c.wvars) :
    ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ' := by
  have hfa : ∀ a : String, a ∉ scratchArrs → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (fun hmem => ha (hA a hmem))
  have hfv : ∀ y : String, y ∉ c.wvars → σ'.vars y = σ.vars y :=
    fun y hy => hrun.frame_var y hy
  obtain ⟨⟨⟨hn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCB, hlmem, hdep, hmvar,
    ⟨hnsW, hlwv, hosz, helm, hbh, hooff, hnoff, hstf, hsta, hstd, hste, hitg, hntg⟩,
    hpad0, hTB, Mem, mmj, hmemA, hmemV, hmemE, hmemBd⟩, hplayrec,
    hord, hxoff, hxmem, hasg, hxp, hmn, hordlt, hcout⟩,
    ⟨⟨⟨Xa, hXa, hXaS, hXaB⟩, ⟨Wa, hWa, hWaS, hWaB⟩, ⟨Ra, hRa, hRaS, hRaB⟩, halv', hAlvB, hmask,
      hmaskpt, hgam', hGamB, Mem', mm', hmemA', hmemV', hmemE', hmemBd'⟩, hwrange⟩,
    hcol', hcolbit', hcolread', htab'⟩ := h
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hMB, hGmB, hCB, levelMem_run hrun hlmem,
      hdep.run hrun, ?_,
      ⟨hnsW, by rw [hrun.frame_var "lw" (hV "lw" (by simp))]; exact hlwv,
        hosz.run hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        run_mem_arrs_lt hrun "itg" hitg, run_mem_arrs_lt hrun "ntg" hntg⟩, hpad0, hTB,
      Mem, mmj, (by rw [hfa _ (memName_notMem_scratchArrs j)]; exact hmemA),
      (by rw [hfv _ (hVmm j)]; exact hmemV), hmemE, hmemBd⟩,
    hplayrec.congr (fun a _ => hfv (ctrName a) (hVctr a))
      (fun a _ => hfa (gamName a) (gamName_notMem_scratchArrs a)),
    ?_, ?_, ?_, ?_, ?_, hmn, hordlt, hcout⟩,
    ⟨⟨⟨Xa, ?_, hXaS, hXaB⟩, ⟨Wa, ?_, hWaS, hWaB⟩, ⟨Ra, ?_, hRaS, hRaB⟩, ?_, hAlvB, hmask,
      hmaskpt, ?_, hGamB, Mem', mm',
      (by rw [hfa _ (memName_notMem_scratchArrs (j + 1))]; exact hmemA'),
      (by rw [hfv _ (hVmm (j + 1))]; exact hmemV'), hmemE', hmemBd'⟩, hwrange⟩,
    ?_, hcolbit', hcolread', ?_⟩
  · rw [hrun.frame_var "n" (hV "n" (by simp))]; exact hn
  · rw [hfa "off" (by decide)]; exact hoff
  · rw [hfa "tgt" (by decide)]; exact htgt
  · rw [hfa _ (alvName_notMem_scratchArrs j)]; exact halvj
  · rw [hfa _ (gamName_notMem_scratchArrs j)]; exact hgamj
  · intro cc hcc; rw [hfa _ (colName_notMem_scratchArrs j cc)]; exact hcolj cc hcc
  · rw [hrun.frame_var "m" (hV "m" (by simp))]; exact hmvar
  · rw [hfa "elm" (by decide)]; exact helm
  · rw [hfa "bh" (by decide)]; exact hbh
  · rw [hfa "ooff" (by decide)]; exact hooff
  · rw [hfa "noff" (by decide)]; exact hnoff
  · rw [hfa "stf" (by decide)]; exact hstf
  · rw [hfa "sta" (by decide)]; exact hsta
  · rw [hfa "std" (by decide)]; exact hstd
  · rw [hfa "ste" (by decide)]; exact hste
  · rw [hfa _ (by simp [ordName, scratchArrs, String.ext_iff])]; exact hord
  · rw [hfa _ (by simp [xofName, scratchArrs, String.ext_iff])]; exact hxoff
  · rw [hfa _ (by simp [xmmName, scratchArrs, String.ext_iff])]; exact hxmem
  · rw [hfa _ (by simp [asgName, scratchArrs, String.ext_iff])]; exact hasg
  · rw [hfv _ hVxp]; exact hxp
  · rw [hfa _ (cluName_notMem_scratchArrs j)]; exact hXa
  · rw [hfa _ (batName_notMem_scratchArrs j)]; exact hWa
  · rw [hfa _ (resName_notMem_scratchArrs j)]; exact hRa
  · rw [hfa _ (alvName_notMem_scratchArrs (j + 1))]; exact halv'
  · rw [hfa _ (gamName_notMem_scratchArrs (j + 1))]; exact hgam'
  · intro cc hcc; rw [hfa _ (colName_notMem_scratchArrs (j + 1) cc)]; exact hcol' cc hcc
  · intro i hi
    obtain ⟨Tb, hTb, hTb1, hTbS⟩ := htab' i hi
    exact ⟨Tb, by rw [hfa _ (tabName_notMem_scratchArrs (j + 1) i)]; exact hTb, hTb1, hTbS⟩

/-! ### One scatter atom -/

theorem alvName_ne_alv (j : ℕ) : alvName j ≠ "alv" := by simp [alvName, String.ext_iff]

open Classical in
/-- One scatter atom of one tabled formula: the two copies the calling
convention asks for, the pass, and the atom's flag. -/
noncomputable def atomCom (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i k : ℕ)
    (σs : ScatterSentence (sigL cap mb (j + 1))) : Com :=
  .seq (copyCom (alvName (j + 1)) "alv")
    (.seq (copyCom (tabName (j + 1) (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))) "tab")
      (.seq (RamScatter.scatterCom σs.r σs.t) (.assign (flgName j i k) (.var "flag"))))

open Classical in
/-- The driver's per-formula scatter block is the fold of `atomCom` over
the formula's scatter atoms. -/
theorem scatterCom_eq (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i : ℕ)
    (β : DistFO (sigL cap mb j) 1) :
    RamDriver.scatterCom q_top cap mb φ j i β =
      foldIdx (fun k σs => atomCom q_top cap mb φ j i k σs) 0
        (bcAtomsOf q_top (stepFml cap mb j β)).2 := rfl

open Classical in
theorem warrs_atomCom (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i k : ℕ)
    (σs : ScatterSentence (sigL cap mb (j + 1))) :
    (atomCom q_top cap mb φ j i k σs).warrs =
      ["alv"] ++ (["tab"] ++ ((RamScatter.scatterCom 0 0).warrs ++ [])) := by
  rw [atomCom]
  simp only [Com.warrs, RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom,
    RamDriverIO.warrs_scatterCom]

open Classical in
theorem warrs_atomCom_sub (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i k : ℕ)
    (σs : ScatterSentence (sigL cap mb (j + 1))) :
    ∀ a ∈ (atomCom q_top cap mb φ j i k σs).warrs, a ∈ scratchArrs := by
  rw [warrs_atomCom]
  decide

open Classical in
theorem wvars_atomCom (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i k : ℕ)
    (σs : ScatterSentence (sigL cap mb (j + 1))) :
    (atomCom q_top cap mb φ j i k σs).wvars =
      ["i", "i"] ++ (["i", "i"] ++ ((RamScatter.scatterCom 0 0).wvars ++ [flgName j i k])) := by
  rw [atomCom]
  simp only [Com.wvars, RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom,
    RamDriverIO.wvars_scatterCom]

/-- No scalar of the scatter pass carries the separator, which is why a
flag is none of them. -/
theorem underscore_notMem_scatter_wvars :
    ∀ y ∈ (RamScatter.scatterCom 0 0).wvars, '_' ∉ y.toList := by decide

open Classical in
/-- A fixed name the phase does not assign is none of an atom's
scalars: it is not one of the pass's own, and it carries no separator,
so it is not the flag either. -/
theorem notMem_wvars_atomCom {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} {j i k : ℕ}
    {σs : ScatterSentence (sigL cap mb (j + 1))} {y : String} (hy : '_' ∉ y.toList)
    (hy2 : y ≠ "i") (hy3 : y ∉ (RamScatter.scatterCom 0 0).wvars) :
    y ∉ (atomCom q_top cap mb φ j i k σs).wvars := by
  rw [wvars_atomCom]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro ((h | h) | ((h | h) | (h | h)))
  exacts [hy2 h, hy2 h, hy2 h, hy2 h, hy3 h, hy (h ▸ underscore_mem_flgName j i k)]

open Classical in
/-- Every other flag survives an atom's call: the pass assigns none of
them, and the flags are addressed injectively. -/
theorem flgName_notMem_wvars_atomCom {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {j i k i' k' : ℕ} {σs : ScatterSentence (sigL cap mb (j + 1))}
    (h : ¬(i' = i ∧ k' = k)) :
    flgName j i' k' ∉ (atomCom q_top cap mb φ j i k σs).wvars := by
  rw [wvars_atomCom]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro ((hc | hc) | ((hc | hc) | (hc | hc)))
  exacts [flgName_ne_lit (q := "i") j i' k' (by decide) hc,
    flgName_ne_lit (q := "i") j i' k' (by decide) hc,
    flgName_ne_lit (q := "i") j i' k' (by decide) hc,
    flgName_ne_lit (q := "i") j i' k' (by decide) hc,
    underscore_notMem_scatter_wvars _ hc (underscore_mem_flgName j i' k'),
    h (by obtain ⟨-, hi, hk⟩ := flgName_inj hc; exact ⟨hi, hk⟩)]

/-! The two frames of the calling convention's copy. -/

theorem notMem_warrs_copy {a src dst : String} (h : a ≠ dst) : a ∉ (copyCom src dst).warrs := by
  simp only [RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom, List.mem_singleton]
  exact h

theorem notMem_wvars_copy {y src dst : String} (h : y ≠ "i") : y ∉ (copyCom src dst).wvars := by
  simp only [RamDriverIO.copyCom_eq, RamDriverIO.wvars_fillCom, List.mem_cons,
    List.not_mem_nil, or_false]
  tauto

/-! The four readings of `ScatPre` the walk of one atom needs. -/

variable {σ : Env}

theorem ScatPre.n_eq
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : σ.vars "n" = n := h.1.1.1

theorem ScatPre.off
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : σ.arrs "off" = arrOf (n + 1) O := h.1.1.2.1

theorem ScatPre.tgt
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : σ.arrs "tgt" = arrOf Ws T := h.1.1.2.2.1

theorem ScatPre.mem
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : LevelMem B n cap mb σ := h.1.1.2.2.2.2.2.2.2.2.2.1

/-- **The block structure sits in a prefix of the level's target array**
(rebase F-c-4): `RamDriver.OrderMem`'s first conjunct, read off the
level's surface. It is what lets the scatter pass enter through
`RamScatter.scatter_specW` at the allocation width. -/
theorem ScatPre.nsW
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : ns ≤ Ws := h.1.1.2.2.2.2.2.2.2.2.2.2.2.2.1.1

theorem ScatPre.alvA
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : σ.arrs (alvName (j + 1)) = arrOf n Alv' := h.2.1.1.2.2.2.1

theorem ScatPre.alvB
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : ∀ z, z < n → Alv' z < B := h.2.1.1.2.2.2.2.1

theorem ScatPre.tab
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : TableInv q_top cap mb φ G (j + 1) Alv' C' σ := h.2.2.2.2.2

theorem ScatPre.data
    (h : ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ) : ClusterData n mb j B G M X W w Alv' Gam' σ := h.2.1

open Classical in
/-- **One scatter atom, discharged.** The mask of the next depth and the
atom's own table row are copied into the names the pass addresses, the
pass runs, and its answer is kept in the atom's flag.

What the flag is worth is `RamScatter.scatter_spec` read through two
identifications: the arena the next depth's mask cuts out is the cluster
step's, which is `RamDriverCluster.masked_alv_eq`, and the palette the
colour arrays hold is the cluster step's, which is `hcolread` — the
equation `RamDriverCluster.ColourStep` produces and which
`RamDriverCluster.ScatterStep` does not carry. Everything the phase
holds is given back, and every other flag is where it was. -/
theorem atom_spec (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B) (h1B : 1 < B)
    (hcolread : colRead n C' (sigL cap mb (j + 1)) =
      stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w)
    (i k : ℕ) {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hrB : σs.r + 1 < B) (htB : σs.t < B)
    {Kb : ℕ} (hKb : RamDriverIO.atomCost n ns σs.t ≤ Kb) :
    Spec B (ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
        Alv' Gam' C')
      (atomCom q_top cap mb φ j i k σs)
      (fun σ σ' => ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m
          X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', ¬(i' = i ∧ k' = k) →
          σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars (flgName j i k) ≤ 1 ∧
        (σ'.vars (flgName j i k) ≠ 0 ↔
          ScatVal (stepArenaP (masked G M) X w)
            (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs)) Kb := by
  classical
  refine Spec.of_exists fun σ hpre => ?_
  obtain ⟨hp, hpβ⟩ := getElem_posOf hβ
  obtain ⟨Tb, hTbA, hTb1, hTbS⟩ := hpre.tab _ hp
  have hTbB : ∀ z, z < n → Tb z < B := fun z hz => lt_of_le_of_lt (hTb1 z hz) h1B
  have hlmem := hpre.mem
  -- the mask of the next depth, into the name the pass reads
  obtain ⟨σ₁, r₁, hn₁, -, halv₁⟩ :=
    (RamDriverIO.copy_spec (B := B) (n := n) (src := alvName (j + 1)) (dst := "alv")
      (alvName_ne_alv (j + 1)) Alv' hnB (fun z hz => hpre.alvB z hz)).run (σ := σ)
      ⟨hpre.n_eq, hpre.alvA, hlmem.1.length (p := ("alv", n)) (by simp)⟩
  have hlmem₁ : LevelMem B n cap mb σ₁ := levelMem_run r₁ hlmem
  -- the atom's own table row, into the name the pass reads
  obtain ⟨σ₂, r₂, hn₂, -, htab₂⟩ :=
    (RamDriverIO.copy_spec (B := B) (n := n)
      (src := tabName (j + 1) (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))) (dst := "tab")
      (RamDriverBase.tabName_ne_lit _ _ (by decide)) Tb hnB hTbB).run (σ := σ₁)
      ⟨hn₁, by rw [r₁.frame_arr _ (notMem_warrs_copy
          (RamDriverBase.tabName_ne_lit _ _ (by decide)))]; exact hTbA,
        hlmem₁.1.length (p := ("tab", n)) (by simp)⟩
  have hlmem₂ : LevelMem B n cap mb σ₂ := levelMem_run r₂ hlmem₁
  -- the pass
  obtain ⟨σ₃, r₃, hflag₃, hle₃⟩ :=
    (RamScatter.scatter_specW (G := G) (M := Alv') (Tab := Tb) (O := O) (T := T)
      (ns := ns) (nt := Ws) (r := σs.r) (t := σs.t)
      (X := {a | Sat (masked G Alv') (colRead n C' (sigL cap mb (j + 1))) (fun _ => a) σs.β})
      hcsr hnB hnsB hpre.nsW hrB htB (fun z hz => hpre.alvB z hz) hTbB
      (fun v => by rw [hTbS v, hpβ]; exact Iff.rfl)).run (σ := σ₂)
      ⟨hn₂,
        by rw [r₂.frame_arr _ (notMem_warrs_copy (by decide)),
          r₁.frame_arr _ (notMem_warrs_copy (by decide))]; exact hpre.off,
        by rw [r₂.frame_arr _ (notMem_warrs_copy (by decide)),
          r₁.frame_arr _ (notMem_warrs_copy (by decide))]; exact hpre.tgt,
        by rw [r₂.frame_arr _ (notMem_warrs_copy (by decide))]; exact halv₁,
        htab₂, (hlmem₂.words).1, (hlmem₂.words).2,
        exists_arrOf (hlmem₂.1.length (p := ("exc", n)) (by simp))⟩
  have hflagB : σ₃.vars "flag" < B := lt_of_le_of_lt hle₃ h1B
  have r₄ : Run B (.assign (flgName j i k) (.var "flag")) σ₃
      (σ₃.setVar (flgName j i k) (σ₃.vars "flag")) (1 + (Expr.var "flag").size) :=
    Run.assign (v := σ₃.vars "flag") (evalB_var hflagB)
  have rall : Run B (atomCom q_top cap mb φ j i k σs) σ
      (σ₃.setVar (flgName j i k) (σ₃.vars "flag"))
      ((12 * n + 6) + ((12 * n + 6) +
        (RamScatter.scatterCost n ns σs.t + (1 + (Expr.var "flag").size)))) :=
    r₁.seq (r₂.seq (r₃.seq r₄))
  refine ⟨_, _, rall, by rw [RamDriverIO.atomCost] at hKb; simp only [Expr.size]; omega,
    hpre.run rall (warrs_atomCom_sub q_top cap mb φ j i k σs) ?_ ?_ ?_ ?_,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;>
      exact notMem_wvars_atomCom (by decide) (by decide) (by decide)
  · intro a
    exact notMem_wvars_atomCom (by rw [ctrName]; exact underscore_notMem_prefixed (by decide) a)
      (by simp [ctrName, String.ext_iff])
      (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
  · exact notMem_wvars_atomCom (by rw [xpName]; exact underscore_notMem_prefixed (by decide) j)
      (by simp [xpName, String.ext_iff])
      (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide))
  · intro a
    exact notMem_wvars_atomCom
      (by rw [mnumName]; exact underscore_notMem_prefixed (by decide) a)
      (by simp [mnumName, String.ext_iff])
      (RamDriverIO.notMem_of_append (p := "mm") (s := toString a) (by decide))
  · rw [out_setVar, r₃.out_eq (RamDriverIO.noWrite_scatterCom ..),
      r₂.out_eq (by rw [RamDriverIO.copyCom_eq]; exact RamDriverIO.noWrite_fillCom ..),
      r₁.out_eq (by rw [RamDriverIO.copyCom_eq]; exact RamDriverIO.noWrite_fillCom ..)]
  · exact rall.frame_var _ (notMem_wvars_atomCom
      (by rw [curName]; exact underscore_notMem_prefixed (by decide) j)
      (by simp [curName, String.ext_iff])
      (RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide)))
  · exact fun i' k' hik => rall.frame_var _ (flgName_notMem_wvars_atomCom hik)
  · rw [vars_setVar, if_pos rfl]; exact hle₃
  · rw [vars_setVar, if_pos rfl]
    have hb : σ₃.vars "flag" ≠ 0 ↔ σ₃.vars "flag" = 1 := by omega
    rw [hb, hflag₃, masked_alv_eq hpre.data, hcolread]
    exact Iff.rfl

/-! ### The atoms of one tabled formula -/

open Classical in
/-- **The scatter block of one tabled formula**, over any list of atoms
starting at any position: each atom's flag holds the atom's value, and
every flag the list does not name is where it was. The induction is the
list's. -/
theorem atoms_spec (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B) (h1B : 1 < B)
    (hcolread : colRead n C' (sigL cap mb (j + 1)) =
      stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w)
    (i : ℕ) {Kb : ℕ} :
    ∀ (l : List (ScatterSentence (sigL cap mb (j + 1)))) (k₀ : ℕ),
      (∀ σs ∈ l, σs.β ∈ tablesAt q_top cap mb φ (j + 1) ∧ σs.r + 1 < B ∧ σs.t < B ∧
        RamDriverIO.atomCost n ns σs.t ≤ Kb) →
      Spec B (ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
          Alv' Gam' C')
        (foldIdx (fun k σs => atomCom q_top cap mb φ j i k σs) k₀ l)
        (fun σ σ' => ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m
            X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (i' ≠ i ∨ ∀ p < l.length, k' ≠ k₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ _ : p < l.length,
            σ'.vars (flgName j i (k₀ + p)) ≤ 1 ∧
            (σ'.vars (flgName j i (k₀ + p)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G M) X w)
                (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) l[p]))
        (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro k₀ _
      refine (Spec.skip (B := B) (P := ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord
        Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro k₀ hall
      obtain ⟨hxβ, hxr, hxt, hxK⟩ := hall x (by simp)
      refine ((atom_spec hcsr hnB hnsB h1B hcolread i k₀ hxβ hxr hxt hxK).seq
        (ih (k₀ + 1) (fun s hs => hall s (by simp [hs]))) (fun _ _ _ hq => hq.1) ?_).mono
        (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hle', hval'⟩ ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' ?_, hfl' i' k' ?_]
        · rcases hik with h | h
          · exact fun hc => h hc.1
          · exact fun hc => h 0 (by simp) (by omega)
        · rcases hik with h | h
          · exact _root_.Or.inl h
          · exact _root_.Or.inr fun p hp => by
              have := h (p + 1) (by simp only [List.length_cons]; omega); omega
      · intro p hp
        match p with
        | 0 =>
            rw [Nat.add_zero, hfl'' i k₀ (_root_.Or.inr fun p _ => by omega)]
            exact ⟨hle', hval'⟩
        | q + 1 =>
            rw [show k₀ + (q + 1) = k₀ + 1 + q from by omega]
            simpa using hval'' q (by simpa using hp)

/-! ### The whole depth's table -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The scatter phase of a depth**, over any list of tabled formulas
starting at any position. One `atoms_spec` per formula, and the
positions the flags are addressed by are `RamDriver.posOf` of the atom
in the formula's own atom list. -/
theorem blocks_spec (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B) (h1B : 1 < B)
    (hcolread : colRead n C' (sigL cap mb (j + 1)) =
      stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w)
    {Kb Ki : ℕ} :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ),
      (∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) →
      (∀ β ∈ l, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb) →
      (∀ β ∈ l, Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki) →
      Spec B (ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
          Alv' Gam' C')
        (foldIdx (fun i β => RamDriver.scatterCom q_top cap mb φ j i β) i₀ l)
        (fun σ σ' => ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m
            X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (∀ p < l.length, i' ≠ i₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ hp : p < l.length,
            ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j l[p])).2,
              σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≤ 1 ∧
              (σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≠ 0 ↔
                ScatVal (stepArenaP (masked G M) X w)
                  (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
        (Ki * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro i₀ _ _ _
      refine (Spec.skip (B := B) (P := ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord
        Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro i₀ hmem hbnd hcost
      have hx : x ∈ tablesAt q_top cap mb φ j := hmem x (by simp)
      refine (((atoms_spec hcsr hnB hnsB h1B hcolread i₀
          (bcAtomsOf q_top (stepFml cap mb j x)).2 0
          (fun s hs => ⟨mem_tablesAt_succ_of_mem_bcAtomsOf_right hx hs,
            (hbnd x (by simp) s hs).1, (hbnd x (by simp) s hs).2.1,
            (hbnd x (by simp) s hs).2.2⟩)).mono (hcost x (by simp))).seq
        (ih (i₀ + 1) (fun β hβ => hmem β (by simp [hβ]))
          (fun β hβ => hbnd β (by simp [hβ])) (fun β hβ => hcost β (by simp [hβ])))
        (fun _ _ _ hq => hq.1) ?_).mono (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hval'⟩ ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' (fun p hp => by
            have := hik (p + 1) (by simp only [List.length_cons]; omega); omega),
          hfl' i' k' (_root_.Or.inl (by have := hik 0 (by simp); omega))]
      · intro p hp
        match p with
        | 0 =>
            intro σs hσs
            simp only [List.getElem_cons_zero] at hσs ⊢
            obtain ⟨hlt, hget⟩ := getElem_posOf hσs
            have hb := hval' (posOf σs (bcAtomsOf q_top (stepFml cap mb j x)).2) hlt
            rw [Nat.zero_add, hget] at hb
            rw [Nat.add_zero, hfl'' i₀ _ (fun p _ => by omega)]
            exact hb
        | q + 1 =>
            intro σs hσs
            rw [show i₀ + (q + 1) = i₀ + 1 + q from by omega]
            exact hval'' q (by simpa using hp) σs (by simpa using hσs)

/-! ### The obligation

`RamDriverCluster.ScatterStep` as it stands, plus one hypothesis it does
not carry. The postcondition reads every flag in the *cluster step's*
arena and palette, and the precondition pins the palette only as the
family `C'` the colour arrays hold; the equation between the two is
`RamDriverCluster.ColourStep`'s last clause, which
`RamDriverCluster.clusterStepImplements` obtains and then drops. It
enters here as `hcolread`, exactly as it does in
`RamDriverBase.readbackStep`, which owes it for the same reason. -/

open Classical in
/-- **The scatter atoms of one cluster, discharged.** One
`RamScatter.scatter_spec` per scatter atom of every tabled formula, at
the depth-`(j+1)` table row of the atom's own formula — which
`RamDriver.TableInv` says is the set the atom speaks about — preceded by
the two copies the calling convention asks for and followed by the
atom's flag. -/
theorem scatterStep {Kb Ki K : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
      σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ K) :
    ScatterStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' K := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩ := hσ
  obtain ⟨σ', hrun, hpre', hout, hc, -, hval⟩ :=
    (blocks_spec hcsr hB.n_lt hB.ns_lt hB.one_lt hcolread
      (tablesAt q_top cap mb φ j) 0 (fun _ hβ => hβ) hbnd hcost).run
      ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩
  exact ⟨σ', _, hrun, hK, hpre'.1, hpre'.2.1,
    hpre'.2.2.1, hpre'.2.2.2.2.2, hout, hc,
    fun i hi σs hσs => by simpa using hval i hi σs hσs⟩

/-! ### The scatter phase's own frame

What the whole phase writes, read off its syntax: the two names the
calling convention copies into and the search's three scratch arrays,
and nothing else. This is the scatter phase's contribution to
`RamDriverCluster.ClusterFrames` — that a turn leaves the depth-`j`
tables of the vertices it is not writing alone — and it is the only one
of the turn's six phases whose contribution is a frame and not a
walk. -/

open Classical in
theorem warrs_foldAtoms (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i : ℕ) :
    ∀ (l : List (ScatterSentence (sigL cap mb (j + 1)))) (k₀ : ℕ),
      ∀ a ∈ (foldIdx (fun k σs => atomCom q_top cap mb φ j i k σs) k₀ l).warrs,
        a ∈ scratchArrs := by
  intro l
  induction l with
  | nil => intro k₀ a ha; exact absurd ha (by rw [foldIdx]; simp [Com.warrs])
  | cons x xs ih =>
      intro k₀ a ha
      rw [foldIdx, Com.warrs, List.mem_append] at ha
      rcases ha with h | h
      · exact warrs_atomCom_sub q_top cap mb φ j i k₀ x a h
      · exact ih (k₀ + 1) a h

open Classical in
/-- **The scatter phase writes five arrays.** -/
theorem warrs_scatterFold (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ),
      ∀ a ∈ (foldIdx (fun i β => RamDriver.scatterCom q_top cap mb φ j i β) i₀ l).warrs,
        a ∈ scratchArrs := by
  intro l
  induction l with
  | nil => intro i₀ a ha; exact absurd ha (by rw [foldIdx]; simp [Com.warrs])
  | cons x xs ih =>
      intro i₀ a ha
      rw [foldIdx, Com.warrs, List.mem_append] at ha
      rcases ha with h | h
      · exact warrs_foldAtoms q_top cap mb φ j i₀ _ 0 a (by rwa [← scatterCom_eq])
      · exact ih (i₀ + 1) a h

open Classical in
/-- **The scatter phase leaves every table of every depth alone**, since
a table name carries the separator and none of the five does. -/
theorem tabName_notMem_warrs_scatterFold (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (j d i : ℕ) (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ) :
    tabName d i ∉ (foldIdx (fun i β => RamDriver.scatterCom q_top cap mb φ j i β) i₀ l).warrs :=
  fun hm => tabName_notMem_scratchArrs d i (warrs_scatterFold q_top cap mb φ j l i₀ _ hm)

/-! ### The frames of the turn's other four phases

`RamDriverCluster.ClusterFrames` asks, on top of the cover's answers,
that a turn leave the depth-`j` table cells of the vertices it is *not*
writing alone. The readback's own obligation says that of the readback;
what is owed here is that the four phases before it write no table at
all. Their write sets are folds — the expansion chain, the ancestor
loop, the three slot families — so each is one induction over the fold
plus the pieces' own syntax, and the conclusion is read off the names: a
table name carries the separator, and every array the descent, the
padding and the scatter phase write is a literal or a prefixed name
without one, while every array the colouring writes is a colour name,
whose prefix is not a table's. -/

theorem tabName_ne_colName (d i e c : ℕ) : tabName d i ≠ colName e c := by
  simp [tabName, colName, String.ext_iff]

/-- The write set of a `foldr` of commands is the union of the pieces'. -/
theorem mem_warrs_foldr {X : Type*} (f : X → Com) :
    ∀ (l : List X) {a : String},
      a ∈ (l.foldr (fun x c => Com.seq (f x) c) .skip).warrs → ∃ x ∈ l, a ∈ (f x).warrs := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons x xs ih =>
      intro a ha
      simp only [List.foldr_cons, Com.warrs, List.mem_append] at ha
      rcases ha with h | h
      · exact ⟨x, by simp, h⟩
      · obtain ⟨y, hy, hm⟩ := ih h
        exact ⟨y, by simp [hy], hm⟩

theorem mem_warrs_foldRange (f : ℕ → Com) (mm : ℕ) {a : String}
    (h : a ∈ (foldRange f mm).warrs) : ∃ b < mm, a ∈ (f b).warrs := by
  obtain ⟨b, hb, hm⟩ := mem_warrs_foldr f (List.range mm) h
  exact ⟨b, List.mem_range.mp hb, hm⟩

theorem warrs_expandCom (msk src dst : String) : (expandCom msk src dst).warrs = [dst] := rfl

theorem mem_warrs_chainCom (msk : String) (nm : ℕ → String) (r : ℕ) {a : String}
    (h : a ∈ (chainCom msk nm r).warrs) : ∃ b < r, a = nm (b + 1) := by
  obtain ⟨b, hb, hm⟩ := mem_warrs_foldRange _ r h
  rw [warrs_expandCom] at hm
  exact ⟨b, hb, List.eq_of_mem_singleton hm⟩

theorem warrs_andCom (a b dst : String) : (andCom a b dst).warrs = [dst] := rfl

theorem warrs_subCom (a b dst : String) : (subCom a b dst).warrs = [dst] := rfl

theorem warrs_clusterLoad (j : ℕ) :
    (clusterLoad j).warrs = [cluName j, cluName j, memName (j + 1)] := rfl

/-- The child's filter writes the child's own member array. -/
theorem warrs_memFilterCom (j : ℕ) : (memFilterCom j).warrs = [memName j] := rfl

theorem wvars_memFilterCom (j : ℕ) :
    (memFilterCom j).wvars = ["mk", mnumName j, "mv", mnumName j, "mk"] := rfl

theorem warrs_markPath (bat : String) : (markPath bat).warrs = [bat] := rfl

theorem warrs_bfsPathCom (r : ℕ) :
    (RamBfsPaths.bfsPathCom r).warrs = (RamBfsPaths.bfsPathCom 0).warrs := rfl

theorem underscore_notMem_bfsPath :
    ∀ a ∈ (RamBfsPaths.bfsPathCom 0).warrs, '_' ∉ a.toList := by decide

theorem warrs_bfsParCom (r : ℕ) :
    (RamBfsPaths.bfsParCom r).warrs = (RamBfsPaths.bfsParCom 0).warrs := rfl

theorem underscore_notMem_bfsPar :
    ∀ a ∈ (RamBfsPaths.bfsParCom 0).warrs, '_' ∉ a.toList := by decide

theorem underscore_notMem_extractPath :
    ∀ a ∈ RamBfsPaths.extractPathCom.warrs, '_' ∉ a.toList := by decide

/-- Every array the descent writes is a literal or a prefixed name, and
neither carries the separator. -/
theorem underscore_notMem_warrs_descendCom (cap j : ℕ) :
    ∀ a ∈ (descendCom cap j).warrs, '_' ∉ a.toList := by
  have hclu : '_' ∉ (cluName j).toList := by
    rw [cluName]; exact underscore_notMem_prefixed (by decide) j
  have hres : '_' ∉ (resName j).toList := by
    rw [resName]; exact underscore_notMem_prefixed (by decide) j
  have hbal : '_' ∉ (balName j).toList := by
    rw [balName]; exact underscore_notMem_prefixed (by decide) j
  have hblt : '_' ∉ (balAltName j).toList := by
    rw [balAltName]; exact underscore_notMem_prefixed (by decide) j
  have hbat : '_' ∉ (batName j).toList := by
    rw [batName]; exact underscore_notMem_prefixed (by decide) j
  have halv : ∀ d : ℕ, '_' ∉ (alvName d).toList := fun d => by
    rw [alvName]; exact underscore_notMem_prefixed (by decide) d
  have hgam : ∀ d : ℕ, '_' ∉ (gamName d).toList := fun d => by
    rw [gamName]; exact underscore_notMem_prefixed (by decide) d
  have hmem : ∀ d : ℕ, '_' ∉ (memName d).toList := fun d => by
    rw [memName]; exact underscore_notMem_prefixed (by decide) d
  have hstage : ∀ b : ℕ, '_' ∉ (ballStage j b).toList := by
    intro b
    rw [ballStage]
    split <;> assumption
  have hanc : ∀ a' : ℕ, ∀ a ∈ (ancestorStep cap j a').warrs, '_' ∉ a.toList := by
    intro a' a ha
    simp only [ancestorStep, Com.warrs, List.mem_append, List.nil_append,
      RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom, List.mem_cons,
      List.not_mem_nil, or_false, warrs_markPath] at ha
    rcases ha with rfl | h | h
    · decide
    · rw [warrs_bfsParCom] at h; exact underscore_notMem_bfsPar _ h
    · rcases h with h | rfl
      · exact underscore_notMem_extractPath _ h
      · exact hbat
  have hbatch : ∀ a ∈ (batchCom cap j).warrs, '_' ∉ a.toList := by
    intro a ha
    simp only [batchCom, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, RamDriverIO.warrs_fillCom, warrs_andCom] at ha
    rcases ha with rfl | rfl | h | rfl
    · exact hbat
    · exact hbat
    · obtain ⟨b, -, hm⟩ := mem_warrs_foldRange _ j h; exact hanc b a hm
    · exact hbat
  intro a ha
  simp only [descendCom, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or, warrs_clusterLoad, warrs_andCom, warrs_subCom,
    warrs_memFilterCom, RamDriverIO.warrs_fillCom] at ha
  rcases ha with (rfl | rfl | rfl) | rfl | (rfl | rfl | h) | h | rfl | rfl | rfl | rfl
  · exact hclu
  · exact hclu
  · exact hmem (j + 1)
  · exact hres
  · exact hbal
  · exact hbal
  · obtain ⟨b, -, rfl⟩ := mem_warrs_chainCom _ _ _ h; exact hstage (b + 1)
  · exact hbatch a h
  · exact halv (j + 1)
  · exact hgam (j + 1)
  · exact hgam (j + 1)
  · exact hmem (j + 1)

/-- The padding writes one array. -/
theorem warrs_enumBatch (bat clu : String) (mb : ℕ) :
    (enumBatch bat clu mb).warrs = ["wa", "wa"] := rfl

/-- Every array the colouring writes is a colour of the next depth. -/
theorem mem_warrs_colourCom (cap mb j : ℕ) {a : String}
    (h : a ∈ (colourCom cap mb j).warrs) : ∃ c, a = colName (j + 1) c := by
  simp only [colourCom, Com.warrs, List.mem_append] at h
  rcases h with h | h | h
  · simp only [oldCom, Com.warrs, List.mem_append, RamDriverIO.copyCom_eq,
      RamDriverIO.warrs_fillCom, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | rfl
    · obtain ⟨b, -, hm⟩ := mem_warrs_foldRange _ _ h
      rw [warrs_andCom] at hm
      exact ⟨oldIdx cap mb j b, List.eq_of_mem_singleton hm⟩
    · exact ⟨oldIdx cap mb j (sigL cap mb j), rfl⟩
  · obtain ⟨i, -, hm⟩ := mem_warrs_foldr _ (List.finRange mb) h
    simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      RamDriverIO.warrs_fillCom] at hm
    rcases hm with rfl | rfl | hm
    · exact ⟨pdIdx cap mb j i 0, rfl⟩
    · exact ⟨pdIdx cap mb j i 0, rfl⟩
    · obtain ⟨b, -, rfl⟩ := mem_warrs_chainCom _ _ _ hm
      exact ⟨pdIdx cap mb j i (b + 1), rfl⟩
  · obtain ⟨c, -, hm⟩ := mem_warrs_foldRange _ _ h
    simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      RamDriverIO.copyCom_eq, RamDriverIO.warrs_fillCom] at hm
    rcases hm with rfl | hm
    · exact ⟨puIdx cap mb j c 0, rfl⟩
    · obtain ⟨b, -, rfl⟩ := mem_warrs_chainCom _ _ _ hm
      exact ⟨puIdx cap mb j c (b + 1), rfl⟩

/-- **The colouring does not touch the padding buffer** (wave R1.8-T2).
The `ClusterWa` seam now has a third consumer — the kill pass, which
walks the buffer at the *child* palette, so it must run after the
colouring — and this is why the clause crosses it: the colouring writes
the child palette's arrays and nothing else. -/
theorem wa_notMem_warrs_colourCom (cap mb j : ℕ) : "wa" ∉ (colourCom cap mb j).warrs := by
  intro h
  obtain ⟨c, hc⟩ := mem_warrs_colourCom cap mb j h
  exact absurd hc (by simp [colName, String.ext_iff])

/-- **No phase of the turn but the readback writes a table.** -/
theorem tabName_notMem_warrs_turn (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j d i : ℕ) :
    tabName d i ∉ (descendCom cap j).warrs ∧
      tabName d i ∉ (enumBatch (batName j) (cluName j) mb).warrs ∧
      tabName d i ∉ (colourCom cap mb j).warrs ∧
      tabName d i ∉ (foldIdx (fun i β => RamDriver.scatterCom q_top cap mb φ j i β) 0
        (tablesAt q_top cap mb φ j)).warrs := by
  refine ⟨fun hm => underscore_notMem_warrs_descendCom cap j _ hm
      (RamDriverBase.underscore_mem_tabName d i), ?_, ?_,
    tabName_notMem_warrs_scatterFold q_top cap mb φ j d i _ 0⟩
  · rw [warrs_enumBatch]
    intro hm
    refine RamDriverBase.tabName_ne_lit d i (q := "wa") (by decide) ?_
    rcases List.mem_cons.mp hm with h | h
    · exact h
    · exact List.eq_of_mem_singleton h
  · intro hm
    obtain ⟨c, hc⟩ := mem_warrs_colourCom cap mb j hm
    exact tabName_ne_colName d i (j + 1) c hc

/-! ### What the nested call must leave alone

`RamDriverCluster.InnerFrames` is a specification of `inner`, and `inner`
is a program *variable*: nothing whatever follows about it from the
obligation's own text. Two things have to be handed in.

*The call itself.* A `Spec` is total correctness, so the frame cannot be
proved without a run of `inner`; `hinner` is the nested level's own
specification — `RamDriverCluster.InnerAvail`, which is exactly the
antecedent `RamDriver.ClusterStepImplements` and
`RamDriverCluster.ClusterFrames` carry. It is used twice: for the run,
and for its *postcondition*, which is `RamDriver.LevelPost` at depth
`j + 1` and therefore hands back everything a level owns —
the block structure, the two scalars, `RamDriver.LevelMem`,
`RamDriver.DepthMem`, `RamDriver.OrderMem` with its eight zeroed
accumulators, and the depth-`(j+1)` masks and palette. **Wave E2**: that
is why those are no longer frame conditions. They cannot be: the nested
level runs `RamDriver.orderCom`, which writes every one of the eight,
and `RamDriverBot.Ext`-fresh names besides, so `TurnFrozen` asking for
them was refutable at `RamDriver.driverAt (j+1)`.

The bit clause `InnerAvail` needs of the palette is the ninth conjunct
of `RamDriver.LevelPre` at depth `j + 1`, which `InnerFrames`'s own
precondition carries — so nothing has to be handed in for it, and the
whole family `hinner` can be applied under the obligation's `intro`.

*The frame itself.* `TurnFrozen` is what is left: the arrays of the
enclosing turn's *own* depth (and the game masks of the depths below,
for the recorded play), which a level at depth `j + 1` does not write
because its per-depth names are all at depth `j + 1` or above. That is
`Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_driverAt`, and the
three scalars are its scalar half. -/

/-- The arrays the enclosing turn is still holding while the nested
driver runs: the cover's three answers and the depth's order array, the
two masks and the palette of the depth, the cluster's own three, and the
game masks of the depths below — every one of them a name of a depth at
or below `j`, hence one the level at depth `j + 1` does not write. -/
def TurnFrozen (j : ℕ) (a : String) : Prop :=
  a ∈ [alvName j, cluName j, resName j, batName j,
      ordName j, xofName j, xmmName j, asgName j, memName j] ∨
    (∃ c, a = colName j c) ∨ (∃ b ≤ j, a = gamName b)

/-- **The frame of the nested driver, discharged from its syntax.** -/
theorem innerFrames {ℓ : ℕ} {wA : (ℕ → ℕ) → ℕ} {inner : Com} {Kin : ℕ → ℕ}
    (hinner : RamDriverCluster.InnerAvail B q_top cap mb ns Ws ℓ j φ G O T wA inner Kin)
    (hA : ∀ a : String, TurnFrozen j a → a ∉ inner.warrs)
    (hVctr : ∀ a ≤ j, ctrName a ∉ inner.wvars) (hVxp : xpName j ∉ inner.wvars)
    (hVcur : curName j ∉ inner.wvars) (hVmm : ∀ a ≤ j, mnumName a ∉ inner.wvars) :
    RamDriverCluster.InnerFrames B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg m X W w Alv' Gam' C' inner (Kin (wA Alv')) := by
  intro σ hσ
  obtain ⟨σ', hrun, ⟨hlevin, -, -⟩, -⟩ :=
    (hinner Alv' Gam' C' hσ.1.2.2.2.2.2.2.2.2.1).run
      ⟨hσ.1, hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2⟩
  have hfa : ∀ a : String, TurnFrozen j a → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (hA a ha)
  have hfv : ∀ y : String, y ∉ inner.wvars → σ'.vars y = σ.vars y :=
    fun y hy => hrun.frame_var y hy
  obtain ⟨hn', hoff', htgt', halv'', hgam'', hcol'', hAlvB', hGamB', hCB', hlmem', hdep',
    hmvar', hordmem', hpad0', hTB', Mem'', mm'', hmemA'', hmemV'', hmemE'', hmemBd''⟩ := hlevin
  obtain ⟨-,
    ⟨⟨-, -, -, halvj, hgamj, hcolj, hMB, hGmB, hCB, -, -, -, -, -, -,
        Mem, mmj, hmemA, hmemV, hmemE, hmemBd⟩, hplayrec,
      hord, hxoff, hxmem, hasg, hxp, hmn, hordlt, hcout⟩,
    ⟨⟨⟨Xa, hXa, hXaS, hXaB⟩, ⟨Wa, hWa, hWaS, hWaB⟩, ⟨Ra, hRa, hRaS, hRaB⟩, -, hAlvB, hmask,
      hmaskpt, -, hGamB, -⟩, hwrange⟩, -, -⟩ := hσ
  refine ⟨σ', hrun, ⟨⟨hn', hoff', htgt', ?_, ?_, ?_, hMB, hGmB, hCB, hlmem', hdep', hmvar',
      hordmem', hpad0', hTB',
      Mem, mmj, (by rw [hfa _ (_root_.Or.inl (by simp [TurnFrozen]))]; exact hmemA),
      (by rw [hfv _ (hVmm j le_rfl)]; exact hmemV), hmemE, hmemBd⟩,
    hplayrec.congr (fun a ha => hfv (ctrName a) (hVctr a (by omega)))
      (fun a ha => hfa (gamName a) (_root_.Or.inr (_root_.Or.inr ⟨a, by omega, rfl⟩))),
    ?_, ?_, ?_, ?_, ?_, hmn, hordlt, hcout⟩,
    ⟨⟨⟨Xa, ?_, hXaS, hXaB⟩, ⟨Wa, ?_, hWaS, hWaB⟩, ⟨Ra, ?_, hRaS, hRaB⟩, halv'', hAlvB, hmask,
      hmaskpt, hgam'', hGamB, Mem'', mm'', hmemA'', hmemV'', hmemE'',
      hmemBd''⟩, hwrange⟩, hcol'', ?_⟩
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact halvj
  · rw [hfa _ (_root_.Or.inr (_root_.Or.inr ⟨j, le_rfl, rfl⟩))]; exact hgamj
  · intro cc hcc
    rw [hfa _ (_root_.Or.inr (_root_.Or.inl ⟨cc, rfl⟩))]
    exact hcolj cc hcc
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hord
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hxoff
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hxmem
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hasg
  · rw [hfv _ hVxp]; exact hxp
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hXa
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hWa
  · rw [hfa _ (_root_.Or.inl (by simp))]; exact hRa
  · exact hfv _ hVcur

/-! ### What one turn leaves alone

`RamDriverCluster.ClusterFrames` is not a frame of the turn's syntax:
`inner` is a variable, and the second clause is about what the *readback*
wrote. So it is discharged the way the turn's own obligation is —
by running the six phases — with three things added.

*The cover's answers* need no frame at all: every one of the five
obligations carries `RamDriverCluster.TurnPre` in its postcondition, and
so does `RamDriverCluster.InnerFrames`, so `RamDriverCluster.CoverHeld`
crosses the turn by itself.

*The tables* need the four phases before the readback to write none, and
that is `tabName_notMem_warrs_turn` above together with `hinnerTab` — the
one clause the nested call cannot be asked for by `InnerFrames`, whose
postcondition says nothing about the depth's tables.

*The nested call's frame* is built here rather than handed in
(**wave E2**): `RamDriverCluster.InnerFrames` is a `Spec` of the nested
driver, so producing it needs that driver's termination, which is
exactly the `hinner` this obligation carries as an *antecedent*. A
caller doing the downward induction has `hinner` at every depth and
cannot have `InnerFrames` before it, so the hypothesis has to sit under
the `intro` — and it does: what is taken here is `innerFrames`'
syntactic side, and the semantic side comes from `hinner`. -/

open Classical in
/-- **What one cluster leaves alone, discharged.** -/
theorem clusterFrames {ℓ k : ℕ} {wA : (ℕ → ℕ) → ℕ} {wBk : ℕ} {inner : Com} {Kin : ℕ → ℕ}
    {Kd Ke Kc Kk Kkl Ks Kr K : ℕ}
    (hcsr : CsrGraph G ns O T)
    {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hdes : DescendStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m Kd)
    (henum : ∀ X W Alv' Gam',
      EnumStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W Alv' Gam' Ke)
    (hcol : ∀ X W w Alv' Gam',
      ColourStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W w Alv' Gam' Kc)
    (hkill : ∀ X W w Alv' Gam' C',
      RamDriverCluster.KillStep B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
        X W w Alv' Gam' C' Kk)
    (hkilltab : ∀ i, tabName j i ∉ (killCom q_top cap mb j φ).warrs)
    (hwakfr : "wa" ∉ (killCom q_top cap mb j φ).warrs)
    (hklisttab : ∀ i, tabName j i ∉ (killListCom mb j).warrs)
    (hklist : ∀ X W w Alv' Gam' C',
      RamDriverCluster.KillListStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m
        X W w Alv' Gam' C' Kkl)
    (hA : ∀ a : String, TurnFrozen j a → a ∉ inner.warrs)
    (hVctr : ∀ a ≤ j, ctrName a ∉ inner.wvars) (hVxp : xpName j ∉ inner.wvars)
    (hVcur : curName j ∉ inner.wvars) (hVmm : ∀ a ≤ j, mnumName a ∉ inner.wvars)
    (hscat : ∀ X W w Alv' Gam' C',
      ScatterStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
        Alv' Gam' C' Ks)
    (hread : ∀ X W w Alv' Gam' C',
      ReadbackStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
        Alv' Gam' C' Kr)
    (hinnerTab : ∀ i, tabName j i ∉ inner.warrs)
    (hmono : Monotone Kin)
    (hwAB : ∀ Alv' : ℕ → ℕ, k < n →
      RamCover.CoverOut G M π ord cap m Xoff Xmem asg →
      (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 →
        v ∈ Refine.MassMath.clusterAt G M π ord cap k) →
      wA Alv' ≤ wBk)
    (hK : Kd + (Ke + (Kc + (Kk + (Kkl + (Kin wBk + (Ks + Kr)))))) ≤ K) :
    RamDriverCluster.ClusterFrames B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg m k wA inner Kin K := by
  classical
  intro hkn hinner
  have hfr : ∀ X W w Alv' Gam' C',
      RamDriverCluster.InnerFrames B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord
        Xoff Xmem asg m X W w Alv' Gam' C' inner (Kin (wA Alv')) :=
    fun _ _ _ _ _ _ => innerFrames hinner hA hVctr hVxp hVcur hVmm
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htsz, hbarr, hplay, hcov, hcn⟩ := hσ
  have hcnlt : σ.vars (curName j) < n := by rw [hcn]; exact hkn
  have hturn : TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ :=
    ⟨hlev, hplay, hcov⟩
  obtain ⟨σ₁, hr₁, hturn₁, hout₁, hc₁, hwa₁, X, W, Alv', Gam', hball, hWne, hWcard,
      hsub₁, hbat₁, hplay₁⟩ := (hdes hcsr hB).run ⟨hturn, hcnlt⟩
  rw [hcn] at hsub₁
  have hinsize : Kin (wA Alv') ≤ Kin wBk :=
    hmono (hwAB Alv' hkn hcov.2.2.2.2.2.2.2.2 hsub₁)
  obtain ⟨σ₂, hr₂, hturn₂, hplay₂, hout₂, hc₂, w, hdat₂, hwa₂⟩ :=
    (henum X W Alv' Gam').run ⟨hturn₁, hbat₁, hplay₁, hWne, hWcard, hwa₁⟩
  obtain ⟨σ₃, hr₃, hturn₃, hdat₃, hplay₃, hout₃, hc₃, C', hcolarr₃, hcolbit₃, hcolread₃⟩ :=
    (hcol X W w Alv' Gam' hcsr hB).run ⟨hturn₂, hdat₂, hwa₂, hplay₂⟩
  have htsz₃ : TablesSized q_top cap mb φ n σ₃ := (htsz.run hr₁).run hr₂ |>.run hr₃
  have hbarr₃ : BaseArrs B q_top cap mb ℓ φ σ₃ := ((hbarr.run hr₁).run hr₂).run hr₃
  -- the kill pass (wave R1.8-T2), on the buffer the colouring left alone
  have hwa₃ : RamDriverCluster.ClusterWa mb w σ₃ := by
    show σ₃.arrs "wa" = _
    rw [hr₃.frame_arr "wa" (wa_notMem_warrs_colourCom cap mb j)]; exact hwa₂
  obtain ⟨σₖ, hrₖ, hturnₖ, hdatₖ, hcolarrₖ, hplayₖ, houtₖ, hcₖ, hkillₖ⟩ :=
    (hkill X W w Alv' Gam' C' hB).run (σ := σ₃)
      ⟨hturn₃, hdat₃, hwa₃, hcolarr₃, hcolbit₃, hcolread₃, hplay₃, htsz₃, hbarr₃⟩
  have htszₖ : TablesSized q_top cap mb φ n σₖ := htsz₃.run hrₖ
  have hbarrₖ : BaseArrs B q_top cap mb ℓ φ σₖ := hbarr₃.run hrₖ
  -- the kill list (wave R1.8-T3-flip), on the buffer the kill pass left alone
  have hwaₖ : RamDriverCluster.ClusterWa mb w σₖ := by
    show σₖ.arrs "wa" = _
    rw [hrₖ.frame_arr "wa" hwakfr]; exact hwa₃
  obtain ⟨σₗ, hrₗ, hturnₗ, hdatₗ, hcolarrₗ, hplayₗ, houtₗ, hcₗ, -, -⟩ :=
    (hklist X W w Alv' Gam' C' hB).run (σ := σₖ)
      ⟨hturnₖ, hdatₖ, hwaₖ, hcolarrₖ, hplayₖ, htszₖ, hkillₖ⟩
  have hlevin : LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σₗ := by
    -- the depth-`j` member conjunct is NOT passed through: the clause is
    -- depth-indexed through `memName`, exactly like the two mask clauses, and the
    -- child's list is the one the descent filtered (rebase E-mem)
    obtain ⟨hn₃, hoff₃, htgt₃, -, -, -, -, -, -, hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, -⟩ :=
      hturnₗ.1
    obtain ⟨-, -, -, halv₃, hAlvB, -, -, hgam₃, hGamB, hmemin₃⟩ := hdatₗ.1
    exact ⟨hn₃, hoff₃, htgt₃, halv₃, hgam₃, hcolarrₗ, hAlvB, hGamB, hcolbit₃,
      hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, hmemin₃⟩
  have htszₗ : TablesSized q_top cap mb φ n σₗ := htszₖ.run hrₗ
  have hbarrₗ : BaseArrs B q_top cap mb ℓ φ σₗ := hbarrₖ.run hrₗ
  obtain ⟨σ₄, hr₄, ⟨⟨-, -, htab₄⟩, hout₄⟩, hturn₄, hdat₄, hcolarr₄, hc₄⟩ :=
    (RamDriverCluster.spec_conj ((hinner Alv' Gam' C' hcolbit₃).pre
        (fun _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩))
      (hfr X W w Alv' Gam' C')).run (σ := σₗ)
      ⟨hlevin, hturnₗ, hdatₗ, htszₗ, hbarrₗ, hplayₗ⟩
  have htsz₄ : TablesSized q_top cap mb φ n σ₄ := htszₗ.run hr₄
  obtain ⟨σ₅, hr₅, hturn₅, hdat₅, hcolarr₅, htab₅, hout₅, hc₅, hflag₅⟩ :=
    (hscat X W w Alv' Gam' C').run (σ := σ₄)
      ⟨hturn₄, hdat₄, hcolarr₄, hcolbit₃, hcolread₃, htab₄⟩
  have htsz₅ : TablesSized q_top cap mb φ n σ₅ := htsz₄.run hr₅
  have hc₅₀ : σ₅.vars (curName j) = σ.vars (curName j) := by
    rw [hc₅, hc₄, hcₗ, hcₖ, hc₃, hc₂, hc₁]
  obtain ⟨σ₆, hr₆, hturn₆, hout₆, hc₆, hrb₆⟩ :=
    (hread X W w Alv' Gam' C').run (σ := σ₅)
      ⟨hturn₅, hdat₅, hcolarr₅, hcolbit₃, hcolread₃, htab₅, htsz₅,
        by rw [hc₅₀]; exact hcnlt, hflag₅⟩
  refine ⟨σ₆, _,
    hr₁.seq (hr₂.seq (hr₃.seq (hrₖ.seq (hrₗ.seq (hr₄.seq (hr₅.seq hr₆)))))), by omega,
    hturn₆.2.2, fun i hi Tb Tb₀ harr harr₀ v hv => ?_⟩
  obtain ⟨hfd, hfe, hfc, hfs⟩ := tabName_notMem_warrs_turn q_top cap mb φ j j i
  have hframe : σ₅.arrs (tabName j i) = σ.arrs (tabName j i) := by
    rw [hr₅.frame_arr _ hfs, hr₄.frame_arr _ (hinnerTab i), hrₗ.frame_arr _ (hklisttab i),
      hrₖ.frame_arr _ (hkilltab i),
      hr₃.frame_arr _ hfc, hr₂.frame_arr _ hfe, hr₁.frame_arr _ hfd]
  obtain ⟨Tb', Tb₀', harr', harr₀', hunch, -⟩ := hrb₆ i hi
  have h₁ : Tb (v : ℕ) = Tb' (v : ℕ) := eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
  have h₂ : Tb₀' (v : ℕ) = Tb₀ (v : ℕ) :=
    eq_of_arrOf_eq ((harr₀'.symm.trans hframe).trans harr₀) v.isLt
  rw [h₁, hunch v (by rw [hc₅₀]; exact hv), h₂]

end Lax3Proofs.RamDriverFrames
