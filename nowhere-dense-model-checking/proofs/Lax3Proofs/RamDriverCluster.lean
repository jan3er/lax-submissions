import Lax3Proofs.RamDriver
import Lax3Proofs.Refine.ArenaBlock
import Lax3Proofs.Refine.SigmaLoop

/-!
The cluster step and the level of `Lax3Proofs.RamDriver`, discharged.

This file is stage two of the driver: the two largest of the driver's
obligations — `RamDriver.ClusterStepImplements`, the turn of the loop
over the centres, and `RamDriver.LevelImplements`, the loop itself —
proved from the flat passes this file walks and from the semantic glue
`Lax3Proofs.RamDriver` already carries.

# The flat passes

`RamDriver.fillUpto` is the kit's array pass with a cell expression, so
a pass over the carrier is one application of `Fill.loop_spec` — except
that the driver's passes *read* arrays (`copyCom` reads the source,
`andCom` and `subCom` read two masks) and the kit's phase says nothing
about arrays it does not write. `fill_spec` is that gap closed once: the
same pass, with a list of arrays the caller declares frozen, which the
pass may read in its cell expression and which come back unchanged.
`fillCom_spec`, `copyCom_spec`, `andCom_spec` and `subCom_spec` are the
driver's four passes as instances of it, and `masked_mul` is what the
third of them is worth — the `andCom` half of `RamDriver.masked_step`.

# Neighbourhood expansion

The driver measures a distance profile by expanding a set `cap` times
rather than by searching. `nbhd` is one step of that and `ballOf` is the
result of `r` of them; `ballOf_zero` and `nbhd_ballOf` are the two
equations a chain of expansions is proved by, and `ballOf_singleton` is
the form `Evaluator.isoColoring_slotPd` reads a ball in.

`RamDriver.expandCom`'s own walk is two nested loops, and this file
carries its mathematics and its two invariants without closing the walk:
`expandVal` is the cell one step writes, `markSet_expandVal` is that the
mask it leaves marks exactly `nbhd` of what the source marks,
`ExpandInv` and `ScanHit` are what the outer and the inner loop carry,
and `hit_eq_expandVal` is the inner loop's exit reading — that a block
fully scanned decides the outer loop's cell. What is left is the
symbolic execution between them.

# What enters as a hypothesis, and why

The driver's own obligation `ClusterStepImplements` is a single `Prop`
about a program with six phases, of which one — the nested driver — is
the obligation's own hypothesis. The other five enter as named `Prop`s
of this file — `DescendStep`, `EnumStep`, `ColourStep`, `ScatterStep`
and `ReadbackStep` — in the manner of the driver's own obligations: each
is a self-contained Hoare triple over the program text, and each names
in its docstring the specification that discharges it.

`clusterStepImplements` composes them with the driver's `masked_step`,
`stepArenaP_eq`, `exists_pad_enum` and `sat_iff_eval_step`, and *all* of
the mathematics of the cluster step is here: what the five are left
owing is what their arrays hold, never what it means. `ReadbackStep` is
`RamDriver.ReadbackImplements` with its valuation indexed by the vertex
the readback stands on, which that obligation's is not — a local atom's
truth varies from vertex to vertex, and the driver's version evaluates
it at whatever the scalar `z` held before the loop started.

Two frames are needed that no syntax can supply, because both commands
contain the nested driver, which is a variable. `InnerFrames` says the
nested call leaves the depth it was called from alone; `ClusterFrames`
says a turn of the centre loop leaves the other clusters' table cells —
and the cover's three answers — alone, which
`RamDriver.ClusterStepImplements`'s postcondition does not. Each is
stated as a second specification of the same command at the same
precondition, and `spec_conj` merges it with the driver's obligation
into one: the semantics is deterministic, so two specifications of one
command speak about one final state.
-/

namespace Lax3Proofs.RamDriverCluster

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.Horizon Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance
open Lax3Proofs.FormulaTables Lax3Proofs.SplitterWin Lax3Proofs.SplitterWinRec
open Lax3Proofs.RamBfs (masked masked_adj CsrGraph MAdj WD)
open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.MassMath (blockSize clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### Two specifications of one command

`Spec` is an existential over the final state, so two specifications of
the same command from the same precondition name two states — and the
semantics is deterministic, so they are the same state. That is what
lets a caller take a phase's meaning from one lemma and its frame from
another without walking the program twice. -/

/-- **Two specifications of one command are one specification.** -/
theorem spec_conj {B : ℕ} {P : Env → Prop} {c : Com} {Q Q' : Env → Env → Prop} {K K' : ℕ}
    (h : Spec B P c Q K) (h' : Spec B P c Q' K') :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Q' σ σ') K := by
  intro σ hσ
  obtain ⟨σ₁, hr₁, hq₁⟩ := h σ hσ
  obtain ⟨σ₂, hr₂, hq₂⟩ := h' σ hσ
  obtain ⟨k₁, -, hb₁⟩ := hr₁.bigStep
  obtain ⟨k₂, -, hb₂⟩ := hr₂.bigStep
  obtain ⟨rfl, -⟩ := hb₁.unique hb₂
  exact ⟨σ₁, hr₁, hq₁, hq₂⟩

/-! ### The flat passes

`RamDriver.fillUpto a (.var m) e` is the kit's array pass, and
`Fill.loop_spec` is its whole content — for a cell expression that reads
nothing. The driver's passes read: `copyCom` reads its source, `andCom`
and `subCom` read two masks apiece. So the pass is restated with a list
of arrays the caller declares frozen; they may occur in the cell
expression, they are not written, and they come back. -/

/-- The arrays a pass reads and does not write, with their lengths and
their cell functions. -/
def Frozen (l : List (String × ℕ × (ℕ → ℕ))) (σ : Env) : Prop :=
  ∀ p ∈ l, σ.arrs p.1 = arrOf p.2.1 p.2.2

theorem Frozen.get {l : List (String × ℕ × (ℕ → ℕ))} {σ : Env}
    (h : Frozen l σ) {p : String × ℕ × (ℕ → ℕ)} (hp : p ∈ l) :
    σ.arrs p.1 = arrOf p.2.1 p.2.2 := h p hp

/-- **A flat pass with frozen readers.** `x := 0; while x < m do (a[x]
:= e; x := x + 1)` at the counter name the driver uses, with a family of
arrays the pass may read. What is asked of the cell expression is what
`Fill.loop_spec` asks — that it evaluates to what `F` says about the
cell the counter names — but now in the presence of the frozen family,
which is what makes a copy or a mask operation expressible. -/
theorem fill_spec (B N : ℕ) (a m : String) (e : Expr) (F : ℕ → ℕ)
    (l : List (String × ℕ × (ℕ → ℕ))) (him : "i" ≠ m) (ha : ∀ p ∈ l, p.1 ≠ a) (hNB : N < B)
    (he : ∀ σ, Frozen l σ → σ.vars m = N → σ.vars "i" < N →
      e.evalB B σ = some (F (σ.vars "i"))) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf N g) ∧ σ.vars m = N ∧ Frozen l σ)
      (fillUpto a (.var m) e)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf N g ∧ ∀ j, j < N → g j = F j) ∧
        σ'.vars "i" = N ∧ σ'.vars m = N ∧ Frozen l σ')
      ((10 + e.size) * N + 6) := by
  have hbody : Spec B
      (fun σ => (Fill.Below a "i" N F σ ∧ σ.vars m = N ∧ Frozen l σ) ∧ σ.vars "i" < N)
      (Fill.put a "i" e)
      (fun σ σ' => (Fill.Below a "i" N F σ' ∧ σ'.vars m = N ∧ Frozen l σ') ∧
        σ'.vars "i" = σ.vars "i" + 1)
      (6 + e.size) :=
    ((Fill.put_spec B N a "i" e F _ (fun _ hσ => ⟨hσ.1.1, hσ.2⟩) hNB
      (fun _ hσ => he _ hσ.1.2.2 hσ.1.2.1 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1, by rw [hq.2.1 m (by simp [Ne.symm him])]; exact hσ.1.2.1,
        fun p hp => by rw [hq.2.2.1 p.1 (by simp [ha p hp])]; exact hσ.1.2.2 p hp⟩, hq.1.2⟩)
  refine ((Spec.forRangeZero "i" m
    (fun σ => Fill.Below a "i" N F σ ∧ σ.vars m = N ∧ Frozen l σ) N (6 + e.size) hNB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2.1) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g, harr⟩, hm, hfr⟩
    exact ⟨Fill.below_zero (by rw [arrs_setVar]; exact harr) (by simp),
      by simp [Ne.symm him, hm], fun p hp => by rw [arrs_setVar]; exact hfr p hp⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2, hq.2, hq.1.2.1, hq.1.2.2⟩

/-- **A constant fill over the carrier**: `RamDriver.fillCom` at a
literal, which is what opens every indicator the driver writes. -/
theorem fillCom_spec (B N : ℕ) (a : String) (v : ℕ) (hNB : N < B) (hvB : v < B) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf N g) ∧ σ.vars "n" = N)
      (fillCom a (.lit v))
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf N g ∧ ∀ j, j < N → g j = v) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N)
      (11 * N + 6) :=
  ((fill_spec B N a "n" (.lit v) (fun _ => v) [] (by decide) (by simp) hNB
    (fun _ _ _ _ => evalB_lit hvB)).pre (fun _ hσ => ⟨hσ.1, hσ.2, by simp [Frozen]⟩)).post
    (fun _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.1⟩)

/-- **A copy over the carrier**: `RamDriver.copyCom`, the driver's whole
calling convention, since every sub-program addresses fixed array
names. -/
theorem copyCom_spec (B N Ns : ℕ) (src dst : String) (g : ℕ → ℕ)
    (hsd : src ≠ dst) (hNB : N < B) (hNs : N ≤ Ns) (hgB : ∀ k, k < N → g k < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf N h) ∧ σ.vars "n" = N ∧
        σ.arrs src = arrOf Ns g)
      (copyCom src dst)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ j, j < N → h j = g j) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧ σ'.arrs src = arrOf Ns g)
      (12 * N + 6) := by
  refine ((fill_spec B N dst "n" (.get src (.var "i")) g [(src, Ns, g)] (by decide)
    (by simpa using hsd) hNB ?_).pre ?_).post ?_
  · intro σ hfr hn hlt
    have hs : σ.arrs src = arrOf Ns g := hfr (src, Ns, g) (by simp)
    exact evalB_get (evalB_var (by omega))
      (by rw [hs, getElem?_arrOf g (by omega)]) (hgB _ hlt)
  · rintro σ ⟨hd, hn, hs⟩
    exact ⟨hd, hn, by rintro p hp; rcases List.mem_singleton.mp hp with rfl; exact hs⟩
  · rintro σ σ' - ⟨hd, hi, hn, hfr⟩
    exact ⟨hd, hi, hn, hfr (src, Ns, g) (by simp)⟩

/-- **The pointwise conjunction of two masks**: `RamDriver.andCom`,
which is what cuts an arena down to an indicator. -/
theorem andCom_spec (B N : ℕ) (a b dst : String) (ga gb : ℕ → ℕ)
    (had : a ≠ dst) (hbd : b ≠ dst) (hNB : N < B) (haB : ∀ k, k < N → ga k < B)
    (hbB : ∀ k, k < N → gb k < B) (habB : ∀ k, k < N → ga k * gb k < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf N h) ∧ σ.vars "n" = N ∧
        σ.arrs a = arrOf N ga ∧ σ.arrs b = arrOf N gb)
      (andCom a b dst)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ j, j < N → h j = ga j * gb j) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧
        σ'.arrs a = arrOf N ga ∧ σ'.arrs b = arrOf N gb)
      (15 * N + 6) := by
  refine ((fill_spec B N dst "n" (.mul (.get a (.var "i")) (.get b (.var "i")))
    (fun k => ga k * gb k) [(a, N, ga), (b, N, gb)] (by decide) ?_ hNB ?_).pre ?_).post ?_
  · rintro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact had
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hbd
      · exact absurd hp'' (by simp)
  · intro σ hfr hn hlt
    have hA : σ.arrs a = arrOf N ga := hfr (a, N, ga) (by simp)
    have hBb : σ.arrs b = arrOf N gb := hfr (b, N, gb) (by simp)
    exact evalB_bin
      (evalB_get (evalB_var (by omega)) (by rw [hA, getElem?_arrOf ga hlt]) (haB _ hlt))
      (evalB_get (evalB_var (by omega)) (by rw [hBb, getElem?_arrOf gb hlt]) (hbB _ hlt))
      (by simpa using habB _ hlt)
  · rintro σ ⟨hd, hn, hA, hBb⟩
    refine ⟨hd, hn, ?_⟩
    rintro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hA
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hBb
      · exact absurd hp'' (by simp)
  · rintro σ σ' - ⟨hd, hi, hn, hfr⟩
    exact ⟨hd, hi, hn, hfr (a, N, ga) (by simp), hfr (b, N, gb) (by simp)⟩

/-- **The first mask with the second's marks killed**:
`RamDriver.subCom`, the isolation half of a cluster step's mask
arithmetic, whose meaning is `RamDriver.masked_step`. -/
theorem subCom_spec (B N : ℕ) (a b dst : String) (ga gb : ℕ → ℕ)
    (had : a ≠ dst) (hbd : b ≠ dst) (hNB : N < B) (haB : ∀ k, k < N → ga k < B)
    (hbB : ∀ k, k < N → gb k < B) (hB : 1 < B)
    (habB : ∀ k, k < N → ga k * (1 - gb k) < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf N h) ∧ σ.vars "n" = N ∧
        σ.arrs a = arrOf N ga ∧ σ.arrs b = arrOf N gb)
      (subCom a b dst)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ j, j < N → h j = ga j * (1 - gb j)) ∧
        σ'.vars "i" = N ∧ σ'.vars "n" = N ∧
        σ'.arrs a = arrOf N ga ∧ σ'.arrs b = arrOf N gb)
      (17 * N + 6) := by
  refine ((fill_spec B N dst "n" (.mul (.get a (.var "i")) (.sub (.lit 1) (.get b (.var "i"))))
    (fun k => ga k * (1 - gb k)) [(a, N, ga), (b, N, gb)] (by decide) ?_ hNB ?_).pre ?_).post ?_
  · rintro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact had
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hbd
      · exact absurd hp'' (by simp)
  · intro σ hfr hn hlt
    have hA : σ.arrs a = arrOf N ga := hfr (a, N, ga) (by simp)
    have hBb : σ.arrs b = arrOf N gb := hfr (b, N, gb) (by simp)
    exact evalB_bin
      (evalB_get (evalB_var (by omega)) (by rw [hA, getElem?_arrOf ga hlt]) (haB _ hlt))
      (evalB_bin (evalB_lit hB)
        (evalB_get (evalB_var (by omega)) (by rw [hBb, getElem?_arrOf gb hlt]) (hbB _ hlt))
        (by simp; omega))
      (by simpa using habB _ hlt)
  · rintro σ ⟨hd, hn, hA, hBb⟩
    refine ⟨hd, hn, ?_⟩
    rintro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hA
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hBb
      · exact absurd hp'' (by simp)
  · rintro σ σ' - ⟨hd, hi, hn, hfr⟩
    exact ⟨hd, hi, hn, hfr (a, N, ga) (by simp), hfr (b, N, gb) (by simp)⟩

/-! ### Reading an array back

Two readings the whole file runs on: an array of the carrier's length is
determined below the carrier by the list it is, and the set a mask marks
is the set of vertices whose cell is nonzero. -/

variable {n : ℕ}

/-- Two cell functions that give the same array agree on the carrier. -/
theorem eq_of_arrOf_eq {N : ℕ} {f g : ℕ → ℕ} (h : arrOf N f = arrOf N g) {k : ℕ} (hk : k < N) :
    f k = g k := by
  have h' : (arrOf N f).getD k 0 = (arrOf N g).getD k 0 := by rw [h]
  rwa [getD_arrOf f hk, getD_arrOf g hk] at h'

/-- The set a mask array marks. -/
def markSet (n : ℕ) (A : ℕ → ℕ) : Set (Fin n) := {v | A (v : ℕ) ≠ 0}

theorem mem_markSet {A : ℕ → ℕ} {v : Fin n} : v ∈ markSet n A ↔ A (v : ℕ) ≠ 0 := Iff.rfl

/-- **The size of an arena is its mark set, counted.** `RamDriver.arenaSize`
is stated with the set written out, because the obligation `Prop`s of
that file read it and `markSet` is defined here; the two are the same
term. This is the `rfl` `Refine.MassMath.mass_le_of_alive` is stated
against, so the mass bound instantiates at a driver mask without a
rewrite. -/
theorem arenaSize_eq_markSet (n : ℕ) (M : ℕ → ℕ) :
    arenaSize n M = (markSet n M).ncard := rfl

/-- The arena is a function of the mask on the carrier alone. -/
theorem masked_congr {G : SimpleGraph (Fin n)} {M M' : ℕ → ℕ} (h : ∀ k, k < n → M k = M' k) :
    masked G M = masked G M' := by
  ext u v
  rw [masked_adj, masked_adj, h (u : ℕ) u.isLt, h (v : ℕ) v.isLt]

/-- **The arena of a pointwise product of masks.** Multiplying a mask by
an indicator isolates the indicator's complement: this is the `andCom`
half of `RamDriver.masked_step`, which the driver states for the two
mask operations together. -/
theorem masked_mul {G : SimpleGraph (Fin n)} (M Xa : ℕ → ℕ) {X : Set (Fin n)}
    (hX : ∀ v : Fin n, v ∈ X ↔ Xa (v : ℕ) ≠ 0) :
    masked G (fun a => M a * Xa a) = deleteVerts (masked G M) Xᶜ := by
  ext u v
  rw [masked_adj, SplitterBasics.deleteVerts_adj, masked_adj, Set.mem_compl_iff,
    Set.mem_compl_iff, not_not, not_not, hX u, hX v]
  constructor
  · rintro ⟨hadj, hu, hv⟩
    exact ⟨⟨hadj, fun h => hu (by rw [h]; ring), fun h => hv (by rw [h]; ring)⟩,
      fun h => hu (by rw [h]; ring), fun h => hv (by rw [h]; ring)⟩
  · rintro ⟨⟨hadj, hu, hv⟩, hu', hv'⟩
    exact ⟨hadj, Nat.mul_ne_zero hu hu', Nat.mul_ne_zero hv hv'⟩

/-! ### Neighbourhood expansion, as mathematics

The driver measures every distance profile of a cluster step by
expanding a set one step at a time, `cap` times, rather than by
searching: the radius is a construction-time constant and one step is a
flat pass over the block structure. What the pass computes is `nbhd`,
and what the chain of them computes is `ballOf` — the metric statement
`Evaluator.isoColoring`'s slot equations are phrased in. -/

/-- One step of neighbourhood expansion in an arena: a set together with
its neighbours. -/
def nbhd (A : SimpleGraph (Fin n)) (S : Set (Fin n)) : Set (Fin n) :=
  S ∪ {x | ∃ y ∈ S, A.Adj x y}

/-- The `r`-neighbourhood of a set: everything within `r` of a member.
At a singleton this is a ball, and at a colour class it is the second
profile family of the isolation step. -/
def ballOf (A : SimpleGraph (Fin n)) (r : ℕ) (S : Set (Fin n)) : Set (Fin n) :=
  {x | ∃ y ∈ S, WithinDist A r x y}

/-- **The chain starts at the set itself**: distance zero is equality. -/
theorem ballOf_zero (A : SimpleGraph (Fin n)) (S : Set (Fin n)) : ballOf A 0 S = S := by
  ext x
  constructor
  · rintro ⟨y, hy, p, hp⟩
    cases p with
    | nil => exact hy
    | cons _ q => simp at hp
  · exact fun hx => ⟨x, hx, withinDist_refl A 0 x⟩

/-- **And one expansion is one unit of radius.** The step lemma of the
chain: a vertex within `r + 1` of the set is within `r` of it or a
neighbour of something that is. -/
theorem nbhd_ballOf (A : SimpleGraph (Fin n)) (r : ℕ) (S : Set (Fin n)) :
    nbhd A (ballOf A r S) = ballOf A (r + 1) S := by
  ext x
  simp only [nbhd, ballOf, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨y, hy, hw⟩ | ⟨u, ⟨y, hy, hw⟩, hadj⟩)
    · exact ⟨y, hy, withinDist_mono_radius (by omega) hw⟩
    · refine ⟨y, hy, ?_⟩
      have h := withinDist_trans (withinDist_of_adj hadj) hw
      rwa [Nat.add_comm] at h
  · rintro ⟨y, hy, hw⟩
    rcases RamBfs.withinDist_head hw with rfl | ⟨c, hadj, hc⟩
    · exact Or.inl ⟨x, hy, withinDist_refl A r x⟩
    · exact Or.inr ⟨c, ⟨y, hy, hc⟩, hadj⟩

/-- A ball is the `r`-neighbourhood of the centre's singleton, which is
the form `Evaluator.isoColoring_slotPd` reads it in. -/
theorem ballOf_singleton (A : SimpleGraph (Fin n)) (r : ℕ) (u : Fin n) :
    ballOf A r {u} = {x | WithinDist A r x u} := by
  ext x
  simp only [ballOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun ⟨y, hy, hw⟩ => hy ▸ hw, fun hw => ⟨u, rfl, hw⟩⟩

open Classical in
/-- **The cell one expansion step writes.** The source's own cell,
raised to one when some live neighbour of the vertex is marked — which
is what `RamDriver.expandStep` computes, the initial `hit := src[z]`
being why a marked vertex stays marked. -/
noncomputable def expandVal (G : SimpleGraph (Fin n)) (Msk Src : ℕ → ℕ) (z : ℕ) : ℕ :=
  if ∃ y : ℕ, MAdj G Msk z y ∧ Src y ≠ 0 then 1 else Src z

/-- The cell it writes is one of the two values it can be, which is the
whole of the bound a chain of expansions needs. -/
theorem expandVal_eq_or (G : SimpleGraph (Fin n)) (Msk Src : ℕ → ℕ) (z : ℕ) :
    expandVal G Msk Src z = 1 ∨ expandVal G Msk Src z = Src z := by
  classical
  unfold expandVal
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **What one expansion step is worth.** The set the destination marks
is one neighbourhood step of the set the source marks, taken in the
arena the first mask cuts out. -/
theorem markSet_expandVal (G : SimpleGraph (Fin n)) (Msk Src : ℕ → ℕ) :
    markSet n (expandVal G Msk Src) = nbhd (masked G Msk) (markSet n Src) := by
  classical
  ext v
  simp only [markSet, nbhd, Set.mem_union, Set.mem_setOf_eq, expandVal]
  split
  · rename_i h
    obtain ⟨y, hy, hsy⟩ := h
    exact ⟨fun _ => Or.inr ⟨⟨y, hy.lt_right⟩, hsy, hy.2.2⟩, fun _ => one_ne_zero⟩
  · rename_i h
    refine ⟨Or.inl, ?_⟩
    rintro (hs | ⟨u, hsu, hadj⟩)
    · exact hs
    · exact absurd ⟨(u : ℕ), ⟨v.isLt, u.isLt, hadj⟩, hsu⟩ h

/-! ### One step of neighbourhood expansion, as a walk

`RamDriver.expandCom` is two nested loops: a flat pass over the carrier,
and inside it, for a live vertex, a scan of its block. The outer one is
a fill of the destination mask with `expandVal`, so `Spec.forRangeZero`
owns it and `Fill.Below` is what it carries; the inner one is
`Csr.rowScan_spec`, and what *it* carries is that the hit flag records
whether a live marked neighbour has been seen among the slots passed so
far. -/

/-- The state one pass of the expansion carries: the destination filled
up to the counter, and everything it reads.

**The target array is the level's allocation width** (rebase F-c-4):
`nt` is the physical width, `ns` the block structure's own slot count,
and `ns ≤ nt` the clause that makes every row's read in range. The scan
below runs against `CsrWide.CsrW`, which is where the two numbers were
separated. -/
def ExpandInv (n ns nt : ℕ) (G : SimpleGraph (Fin n)) (O T Msk Src : ℕ → ℕ)
    (msk src dst : String) (σ : Env) : Prop :=
  Fill.Below dst "z" n (expandVal G Msk Src) σ ∧ σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
    σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src

open Classical in
/-- The state the scan of one block carries: the pass's own, the two row
bounds, and the hit flag, which is one exactly when a slot already
passed named a live marked vertex. -/
def ScanHit (n ns nt : ℕ) (G : SimpleGraph (Fin n)) (O T Msk Src : ℕ → ℕ)
    (msk src dst : String) (z : ℕ) (σ : Env) : Prop :=
  ExpandInv n ns nt G O T Msk Src msk src dst σ ∧ σ.vars "z" = z ∧
    σ.vars "jend" = O (z + 1) ∧ O z ≤ σ.vars "j" ∧ σ.vars "j" ≤ O (z + 1) ∧
    σ.vars "hit" =
      (if ∃ p, O z ≤ p ∧ p < σ.vars "j" ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0 then 1 else Src z)

open Classical in
/-- **What a full block scan leaves.** With the whole block passed, the
hit flag is `RamDriver.expandVal`: the slots of the block name exactly
the neighbours of the vertex, so "some slot passed named a live marked
vertex" is "some neighbour in the arena is marked". -/
theorem hit_eq_expandVal {ns z : ℕ} {G : SimpleGraph (Fin n)} {O T Msk Src : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) (hzn : z < n) (hmz : Msk z ≠ 0) :
    (if ∃ p, O z ≤ p ∧ p < O (z + 1) ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0 then 1 else Src z) =
      expandVal G Msk Src z := by
  classical
  unfold expandVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨p, h₁, h₂, hm, hs⟩
    exact ⟨T p, hcsr.madj_of_slot hzn h₁ h₂ hmz hm, hs⟩
  · rintro ⟨y, hy, hs⟩
    obtain ⟨p, h₁, h₂, rfl⟩ := hcsr.slot_of_madj hy
    exact ⟨p, h₁, h₂, hy.alive_right, hs⟩

/-! ### The three answers of the cover, as the turn of the loop reads them

`RamCover.CoverPost` is an existential over the arrays it left; a loop
whose turns all read the same answers wants them named once, and that is
what `CoverHeld` is. `coverPost_of_held` puts them back into the form
the driver's obligations ask for. -/

/-- The cover's three answers, named — at the *depth's own* names, which
`RamDriver.coverSave` copied them into. A nested level takes a cover of
its own, so the fixed names `xoff`, `xmem`, `asg` and `xp` hold another
level's answers by the time the enclosing turn's readback runs; these do
not. -/
abbrev CoverHeld (B n j : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord : ℕ → ℕ) (cap : ℕ) (Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (σ : Env) : Prop :=
  RamDriver.CoverHeldAt B n j G M π ord cap Xoff Xmem asg m σ

/-- Everything a turn of the centre loop reads and hands on: the depth's
own state, the play it has recorded, and the cover's answers. -/
def TurnPre (B n cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ) (Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (σ : Env) : Prop :=
  LevelPre B n cap mb ns Ws O T j M Gm C σ ∧ PlayRec B cap G j M Gm σ ∧
    CoverHeld B n j G M π ord cap Xoff Xmem asg m σ

/-! ### The valuation of one tabled formula's atoms

`RamDriver.sat_iff_eval_step` reads a tabled formula as a boolean
combination over two kinds of atom, evaluated in the cluster step's
arena and colouring. Naming that valuation is what lets the readback's
obligation state what its input is worth without restating the
`Sum.elim` each time. -/

/-- The greedy value of one scatter atom in an arena. -/
def ScatVal {L : ℕ} (A : SimpleGraph (Fin n)) (col : Coloring n L)
    (σs : ScatterSentence L) : Prop :=
  σs.t ≤ (greedySet A σs.r {a | Sat A col (fun _ => a) σs.β}).ncard

/-- The valuation of the atoms of a step formula at one vertex: a local
atom is its own truth in the cluster step's arena, a scatter atom is the
greedy value there. This is exactly the valuation
`RamDriver.sat_iff_eval_step` evaluates the boolean combination over. -/
def atomVal {L : ℕ} (A : SimpleGraph (Fin n)) (col : Coloring n L) (v : Fin n) :
    DistFO L 1 ⊕ ScatterSentence L → Prop :=
  Sum.elim (fun γ => Sat A col (fun _ => v) γ) (ScatVal A col)

/-! ### The five sub-walks of one cluster

`RamDriver.ClusterStepImplements`'s docstring splits the turn into six
passes, of which one — the nested driver — is the obligation's own
hypothesis. The other five are the `Prop`s of this section, each a
self-contained Hoare triple over the program text and each naming, in
its docstring, what discharges it. Nothing of the *mathematics* of the
cluster step is in them: what they say their arrays hold is stated in
the terms `RamDriver.masked_step`, `RamDriver.stepArenaP_eq`,
`RamDriver.exists_pad_enum` and `Evaluator.isoColoring`'s three slot
equations put those arrays in, and turning that into satisfaction is
`clusterStepImplements`'s business below. -/

section Cluster

/-- What the descent leaves: the cluster, the batch, the
cluster-restricted mask and the two masks of the next depth, each named
with what it is worth.

**The mask of the next depth is pinned pointwise** (wave R1.8-T1, design
§2.4). The graph equation `masked G Alv' = deleteVerts (deleteVerts _ Xᶜ) W`
is blind to the mask *value* at a vertex with no edges — that is finding
B8/1 (`Refine.DeadRow.descent_mask_not_pointwise_monotone`) — so the
clause after it says which cells the stored array holds nonzero: exactly
the alive vertices of the cluster outside the batch. It is not a new
obligation on the program but a reading of what it already computes: the
array is the cell function `Alv' k = M k * Xa k * (1 - Wa k)` of
`RamDriver.masked_step`, whose proof derives this very equivalence on the
way to the graph equation (`RamDriverDescend.mask_cell_ne_zero` names it,
and `RamDriverDescend.descendStep` exports it for the array it stored).
Two consumers need the *set* and not the graph: the kill pass's
postcondition, which writes a row for every vertex of `X ∩ alive ∩ Wᶜ`
that the child mask kills, and the level induction's no-resurrection step
(a vertex dead at depth `j` is dead at depth `j + 1`, which follows by
`M v = 0` refuting the left conjunct). -/
def BatchData (n j B : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ) (σ : Env) : Prop :=
  (∃ Xa, σ.arrs (cluName j) = arrOf n Xa ∧ markSet n Xa = X ∧ ∀ k, k < n → Xa k ≤ 1) ∧
    (∃ Wa, σ.arrs (batName j) = arrOf n Wa ∧ markSet n Wa = W ∧ ∀ k, k < n → Wa k < B) ∧
    (∃ Ra, σ.arrs (resName j) = arrOf n Ra ∧
      masked G Ra = deleteVerts (masked G M) Xᶜ ∧ ∀ k, k < n → Ra k < B) ∧
    σ.arrs (alvName (j + 1)) = arrOf n Alv' ∧ (∀ k, k < n → Alv' k < B) ∧
    masked G Alv' = deleteVerts (deleteVerts (masked G M) Xᶜ) W ∧
    (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔ (M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∉ W)) ∧
    σ.arrs (gamName (j + 1)) = arrOf n Gam' ∧ (∀ k, k < n → Gam' k < B) ∧
    (∃ (Mem' : ℕ → ℕ) (mm' : ℕ), σ.arrs (memName (j + 1)) = arrOf n Mem' ∧
      σ.vars (mnumName (j + 1)) = mm' ∧ MemEnum n mm' Mem' Alv' ∧ ∀ z < mm', Mem' z < B)

/-- The same with the padded enumeration the batch was read into.

**The buffer is not here** (wave E2). `RamDriver.enumBatch` writes the
padded enumeration into the *fixed* name `"wa"`, and a nested level runs
a padding of its own, so no clause about `"wa"` can cross the nested
call: `ClusterFrames` would have to ask the driver at depth `j + 1` not
to write it, and the driver does. The buffer is live between the padding
and the colouring and nowhere else — the scatter phase and the readback
read the depth-`(j+1)` tables and the cluster's masks, never the
enumeration — so it is `ClusterWa` below, a conjunct of `EnumStep`'s
postcondition and of `ColourStep`'s precondition, and of nothing that
straddles the recursion. -/
def ClusterData (n mb j B : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (σ : Env) : Prop :=
  BatchData n j B G M X W Alv' Gam' σ ∧ Set.range w = W

/-- **The padded enumeration, in the fixed buffer the colouring reads
it from.** -/
def ClusterWa {n : ℕ} (mb : ℕ) (w : Fin mb → Fin n) (σ : Env) : Prop :=
  σ.arrs "wa" = arrOf mb (fun k => if h : k < mb then (w ⟨k, h⟩ : ℕ) else 0)

/-- **The arena the next depth's mask cuts out is the cluster step's.**
The join point of the descent and the padding: the descent knows the
batch as a set and `RamDriver.sat_iff_eval_step` wants it as an
enumeration, and `RamDriver.stepArenaP_eq` is what identifies the two. -/
theorem masked_alv_eq {mb j B : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ} {σ : Env}
    (h : ClusterData n mb j B G M X W w Alv' Gam' σ) :
    masked G Alv' = stepArenaP (masked G M) X w := by
  rw [stepArenaP_eq (masked G M) X w h.2]
  exact h.1.2.2.2.2.2.1

/-- **The descent.** That `RamDriver.descendCom` writes the cluster
indicator, the ball, the batch and the two masks of the next depth.

Its content is the two mask equations of the driver's docstring. The
work mask is `RamDriver.masked_step` at the cluster's indicator and the
batch's, which is why the postcondition below names the arena the mask
cuts out as `deleteVerts (deleteVerts _ Xᶜ) W` and not as an array; the
cluster-restricted mask `resName j` is the same lemma with the batch
dropped, which is `masked_mul` above. That the cluster holds the
`cap`-ball of every vertex it was assigned is
`RamCover.CoverOut.asg_cover` read through `RamCover.CoverOut.block`,
which is what `clusterLoad` materializes. The batch's two size facts —
that it is nonempty and has at most `mb` vertices — are the program's
own: it contains the connector because `batchCom` stores a `1` there
before anything else, and it has at most one connector plus one walk
buffer of `2·cap + 1` cells per earlier round, which is `mb` because
`mb` is `ℓ · (2·cap + 1)`. The expansion chain that builds the ball is
`RamDriver.expandCom` iterated `2·cap` times.

**The last clause is the splitter game's.** The pass is the only one of
the six that moves the *game* arena — `gamName j` to `gamName (j + 1)`,
by the ball of the round and the batch — so it is the only one that can
say the play went on: at a node whose recorded rounds reach a game arena
the connector still has an edge in, the round extends by the batch the
program marked; at one where it does not, the round leaves nothing and
so does the cluster step. That disjunction is `RamDriver.playRec_succ`,
and what the walk owes it is four things about the batch and no equation
with any other set: that the ball its chain built is the ball of the
*game* arena — which is why `descendCom` expands `gamName j` and not
`alvName j` — that the batch stays inside that ball, that it holds the
connector, and that for every earlier round the state records and the
search reaches it holds the support of the walk the search found, where
the ball keeps it.

**Rebase B2 (§5.3): the size clause — restated at the inclusion it
came from (rebase G2/E6).** The postcondition carries one more line:
every vertex the next depth's arena marks lies in the *cluster* of the
centre this turn is processing. B2 carried only its cardinality
consequence `arenaSize n Alv' ≤ blockSize Xoff (σ.vars (curName j))`;
the G2 interface reads budgets at arena *weights*, and the weighted
consequence (`Refine.MassWeight.arenaWeight_le_blockWeight`) needs the
inclusion itself, which is what the descent's own walk proves anyway:
`clusterLoad` marks exactly the turn's cluster, and the next-depth mask
is that indicator with two more masks multiplied in. The old reading is
recovered by `Refine.ArenaBlock.arenaSize_le_ncard` +
`ncard_clusterAt_le_blockSize`; without some such clause the nested
driver's budget — a function of the arena it is handed — cannot be
turned into a number the turn's cost condition may mention, since
`Alv'` is existentially quantified here. -/
def DescendStep (B cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m K : ℕ) : Prop :=
  CsrGraph G ns O T → ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      σ.vars (curName j) < n)
    (descendCom cap j)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧ (∃ g, σ'.arrs "wa" = arrOf mb g) ∧
      ∃ (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ),
        (∀ v : Fin n, asg (v : ℕ) = σ.vars (curName j) → ball (masked G M) cap v ⊆ X) ∧
        W.Nonempty ∧ W.ncard ≤ mb ∧
        (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 →
          v ∈ clusterAt G M π ord cap (σ.vars (curName j))) ∧
        BatchData n j B G M X W Alv' Gam' σ' ∧
        PlayRec B cap G (j + 1) Alv' Gam' σ') K

/-- **The padding.** That `RamDriver.enumBatch` leaves in `wa` an
enumeration of the batch by exactly `mb` entries.

One walk over two loops: the first collects the marked vertices in
vertex order, the second repeats the first entry to the fixed width.
What the result is worth is `RamDriver.exists_pad_enum`, proved in the
driver — a nonempty set of at most `mb` elements is the range of a map
from `Fin mb` — and `FormulaTables.range_comp_of_surjective` is why the
repetition costs the isolation rewrite nothing. The pass writes `wa` and
three counters and nothing else, which is why everything it is handed
comes back. -/
def EnumStep (B cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      BatchData n j B G M X W Alv' Gam' σ ∧ PlayRec B cap G (j + 1) Alv' Gam' σ ∧
      W.Nonempty ∧ W.ncard ≤ mb ∧ (∃ g, σ.arrs "wa" = arrOf mb g))
    (enumBatch (batName j) mb)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
        ClusterWa mb w σ') K

/-- **The colouring of the next depth.** That `RamDriver.colourCom`
writes the whole depth-`(j+1)` palette.

Three walks, one per slot family, and each is an expansion chain in the
*cluster-restricted* arena `resName j`: `oldCom` for
`Evaluator.isoColoring_slotOld`, `pdCom` for `isoColoring_slotPd` and
`puCom` for `isoColoring_slotPu`. The chains are `RamDriver.chainCom`,
whose content is `RamDriver.expandCom` iterated, and the packing
arithmetic is `RamDriver.oldIdx`, `pdIdx` and `puIdx` — the numeric
values of `FormulaTables.oldSlots`, `pdSlots` and `puSlots`, so no
packing appears in the program text. The postcondition is stated as the
one equation those three walks add up to: the colouring the arrays hold
is `RamDriver.stepColoringP`.

`CsrGraph G ns O T` and `WordBoundK B n d ns cap mb` prefix the obligation
for the reason they prefix `DescendStep`: the expansion chains of the
three slot families read the block structure, and nothing in the
precondition ties `O` and `T` to `G`. Without them the obligation is
**refutable** — its postcondition speaks about `masked G M`, the program
has been told only about `O` and `T`, and any `G` disagreeing with the
block structure refutes it. -/
def ColourStep (B cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  CsrGraph G ns O T → ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧ ClusterWa mb w σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ)
    (colourCom cap mb j)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ C' : ℕ → ℕ → ℕ,
        (∀ c < sigL cap mb (j + 1), σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
        (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
        colRead n C' (sigL cap mb (j + 1)) =
          stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) K

/-- **The kill rows of one turn** (wave R1.8-T2, design §2.3): the table
rows the turn owes at the vertices *it* killed.

The kill set is `X ∩ {alive at j} ∩ W` — in the cluster, alive at the
parent depth, in the batch — and by `BatchData`'s pointwise clause (wave
R1.8-T1) that is exactly the half of the child depth's dead set this
turn is responsible for: there `Alv' v = 0`, so the row's content is the
*edgeless* reading (`Refine.DeadRow.sat_bot_of_dead₁`), and the clause
below states it in the child arena, which is the form
`RamDriver.TableInv` at depth `j + 1` reads. The other half of the child
depth's dead set is the outside class, which no per-vertex pass can
afford (`Refine.DeadRowProbe.no_coeff_pays_outsideRows`) and none needs
(`stepColoringP_subset`: it carries one row, the empty one).

Note the domain is stated at the *turn's own* data — the parent mask, the
cluster and the batch — and not at `Alv'`: the kill set is what this
pass can see, and the child mask alone cannot tell a kill from a vertex
that was dead already. -/
def KillRowsAt (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (M Alv' : ℕ → ℕ) (X W : Set (Fin n)) (C' : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ (j + 1)).length) (Tb : ℕ → ℕ),
    σ.arrs (tabName (j + 1) i) = arrOf n Tb →
    ∀ v : Fin n, M (v : ℕ) ≠ 0 → v ∈ X → v ∈ W →
      Tb (v : ℕ) ≤ 1 ∧
      (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G Alv') (colRead n C' (sigL cap mb (j + 1)))
        (fun _ => v) (tablesAt q_top cap mb φ (j + 1))[i])

/-- **The kill pass.** That `RamDriver.killCom` writes the child-depth
row of every vertex this turn killed, and nothing else of what the turn
holds.

The walk is the padded batch buffer, `mb` entries, so the precondition
carries `ClusterWa` — the pass is the third and last consumer of the
seam, and it still stands strictly before the nested call. The row body
is the depth-`(j+1)` straight line of `RamDriver.botCom` fragments, so
the precondition also carries the child palette (the arrays, their bit
clause and the equation `ColourStep` left), the depth's table lengths
`RamDriver.TablesSized` and the evaluator's scratch
`RamDriver.BaseArrs`. What discharges it is
`Refine.KillPass.killStep`; the mathematics is one rewrite, the edgeless
reading into the child arena's at a killed vertex
(`Refine.DeadRow.sat_bot_of_dead₁`), and everything else is names. -/
def KillStep (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n)) (w : Fin mb → Fin n)
    (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧ ClusterWa mb w σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ TablesSized q_top cap mb φ n σ ∧
      BaseArrs B q_top cap mb ℓ φ σ)
    (killCom q_top cap mb j φ)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1), σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      KillRowsAt q_top cap mb j φ G M Alv' X W C' σ') K

/-- **The scatter atoms.** That the fold of `RamDriver.scatterCom` over
the depth's table decides every scatter atom of every tabled formula.

One call of `RamScatter.scatterCom` per atom, preceded by the two copies
that are the driver's calling convention: the depth-`(j+1)` mask into
`alv` and the depth-`(j+1)` table row of the atom's own formula into
`tab`. `RamScatter.scatter_spec` is the call, and its hypothesis
`hTab` — that the table row is the indicator of the set the atom speaks
about — is `TableInv` at depth `j + 1`, read at the position
`RamDriver.posOf` names, which is a position of the entry by
`RamDriver.getElem_posOf` and
`FormulaTables.mem_tablesAt_succ_of_mem_bcAtomsOf_right`. -/
def ScatterStep (B q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n)) (w : Fin mb → Fin n)
    (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      TableInv q_top cap mb φ G (j + 1) Alv' C' σ)
    (foldIdx (fun i β => scatterCom q_top cap mb φ j i β) 0 (tablesAt q_top cap mb φ j))
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1), σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      TableInv q_top cap mb φ G (j + 1) Alv' C' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2,
          σ'.vars (flgName j i
              (posOf σs (bcAtomsOf q_top
                (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
            (σ'.vars (flgName j i
              (posOf σs (bcAtomsOf q_top
                (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G M) X w)
                (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs)) K

/-- **The readback.** That `RamDriver.readbackCom` writes, at every
vertex the cluster was assigned, the value of every tabled formula's own
boolean combination, and leaves every other vertex's cell alone.

This is the driver's readback obligation, repaired. The version
`Lax3Proofs.RamDriver` used to carry handed the atoms' valuation as a
function of the *entering* state, so a local atom — whose truth varies
from vertex to vertex — was evaluated at whatever the scalar `z`
happened to hold before the loop started; the valuation has to be
indexed by the vertex the readback stands on, and here it is. The walk itself is the one that obligation describes: one
loop, a conditional, a straight line of stores, and the arithmetic of
the bits — that `RamDriver.bcExpr` of a valuation into `{0, 1}` is again
in `{0, 1}` and is nonzero exactly when `BC.eval` holds, an induction on
the combination. What the value *means* is not asked here. -/
def ReadbackStep (B q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n)) (w : Fin mb → Fin n)
    (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      TableInv q_top cap mb φ G (j + 1) Alv' C' σ ∧
      TablesSized q_top cap mb φ n σ ∧ σ.vars (curName j) < n ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2,
          σ.vars (flgName j i
              (posOf σs (bcAtomsOf q_top
                (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
            (σ.vars (flgName j i
              (posOf σs (bcAtomsOf q_top
                (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G M) X w)
                (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
    (readbackCom q_top cap mb φ j)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length), ∃ Tb Tb₀ : ℕ → ℕ,
        σ'.arrs (tabName j i) = arrOf n Tb ∧ σ.arrs (tabName j i) = arrOf n Tb₀ ∧
        (∀ v : Fin n, asg (v : ℕ) ≠ σ.vars (curName j) → Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
        ∀ v : Fin n, asg (v : ℕ) = σ.vars (curName j) →
          Tb (v : ℕ) ≤ 1 ∧
          (Tb (v : ℕ) ≠ 0 ↔
            ∃ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
                DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i]),
              (bcOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i]) h).eval
                (atomVal (stepArenaP (masked G M) X w)
                  (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) v))) K

/-- **The nested driver, as the enclosing turn is handed it.** This is
the antecedent `RamDriver.ClusterStepImplements` and `ClusterFrames`
both carry, named so that the frame of the nested call can be asked for
*under* it — see `clusterStepImplements`'s `hfr`.

It is definitionally the antecedent as those two write it out, so
`intro`ing them gives a term of this type.

**Rebase B2 (§5.2), reading abstracted at G2/E6.** `Kin` is a
*function of the arena's measure*, applied at `wA M'` — the nested
driver on a small sub-arena is cheap, which is the whole content of the
Σ interface. `wA := arenaSize n` is the landed size reading;
`Refine.MassWeight.arenaWeight` is the G2 one (it lives above this file
in the import order, which is why the reading is a parameter). -/
def InnerAvail (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ) (wA : (ℕ → ℕ) → ℕ)
    (inner : Com) (Kin : ℕ → ℕ) : Prop :=
  ∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ), (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
    Spec B (fun σ => LevelPre B n cap mb ns Ws O T (j + 1) M' Gm' C' σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
        PlayRec B cap G (j + 1) M' Gm' σ) inner
      (fun σ σ' => LevelPost B q_top cap mb φ G ns Ws O T (j + 1) M' Gm' C' σ σ' ∧
        σ'.out = σ.out) (Kin (wA M'))

/-- **What the nested driver leaves alone.** The driver's obligation
hands the nested call in as a `Spec` about the depth-`(j+1)` state and
says nothing about the depth-`j` state the enclosing turn is still
holding — and `inner` is a variable, so no frame condition can be read
off its syntax. This is that frame, stated at the same command so that
`spec_conj` merges the two into one specification.

It is not a new obligation on the driver: `RamDriver.driverAt` writes
only the arrays of the depths at or **above** its own and the fixed
names its sub-programs address, so every clause below is a frame
condition of the recursion, discharged the same way at every level —
`Lax3Proofs.RamDriverWrites` is that reading of the program text. -/
def InnerFrames (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ)
    (inner : Com) (Kin : ℕ) : Prop :=
  Spec B (fun σ => LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σ ∧
      TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ)
    inner
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1), σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      σ'.vars (curName j) = σ.vars (curName j)) Kin

/-! ### One cluster

The composition. Every step of it is one of the five specifications
above or the obligation's own hypothesis; the one thing that is not
composition is the last line, where the boolean combination the readback
wrote turns into satisfaction at the depth's own arena by
`RamDriver.sat_iff_eval_step`, at the cluster the cover produced and the
batch the searches produced. -/

open Classical in
/-- **One cluster, discharged.** The turn of the loop over the centres
leaves the table of every vertex the centre was assigned correct.

The five walks compose into a run of `RamDriver.clusterCom`, and what
the run leaves is turned into the obligation's postcondition by
`RamDriver.sat_iff_eval_step` — a tabled formula holds at a vertex of
the depth's arena exactly when its own boolean combination evaluates to
true over the depth-`(j+1)` tables and the scatter values of the cluster
step's arena, which is what the readback wrote there. The hypothesis
that lemma needs of the cluster — that it contains the `cap`-ball of the
vertex — is the descent's postcondition, which is
`RamCover.CoverOut.asg_cover` at the centre being processed; the batch
is the program's own and nothing is asked of it. -/
theorem clusterStepImplements {B q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asgf : ℕ → ℕ} {mm k : ℕ} {wA : (ℕ → ℕ) → ℕ} {wBk : ℕ}
    {inner : Com} {Kin : ℕ → ℕ}
    {Kd Ke Kc Kk Ks Kr K : ℕ}
    (hcap : cap = rhoMinus 0 q_top)
    (hdes : DescendStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asgf mm Kd)
    (henum : ∀ X W Alv' Gam',
      EnumStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asgf mm X W Alv' Gam' Ke)
    (hcol : ∀ X W w Alv' Gam',
      ColourStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asgf mm X W w Alv' Gam' Kc)
    (hwafr : "wa" ∉ (colourCom cap mb j).warrs)
    (hkill : ∀ X W w Alv' Gam' C',
      KillStep B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asgf mm X W w
        Alv' Gam' C' Kk)
    (hfr : InnerAvail B q_top cap mb ns Ws ℓ j φ G O T wA inner Kin → ∀ X W w Alv' Gam' C',
      InnerFrames B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asgf mm X W w
        Alv' Gam' C' inner (Kin (wA Alv')))
    (hscat : ∀ X W w Alv' Gam' C',
      ScatterStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asgf mm X W w
        Alv' Gam' C' Ks)
    (hread : ∀ X W w Alv' Gam' C',
      ReadbackStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asgf mm X W w
        Alv' Gam' C' Kr)
    (hmono : Monotone Kin)
    (hwAB : ∀ Alv' : ℕ → ℕ, k < n →
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asgf →
      (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π ord cap k) →
      wA Alv' ≤ wBk)
    (hK : Kd + (Ke + (Kc + (Kk + (Kin wBk + (Ks + Kr))))) ≤ K) :
    ClusterStepImplements B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asgf mm k
      wA inner Kin K := by
  classical
  intro d hB hcsr hkn _ hinner
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htsz, hbarr, hplay, hheld, hcn⟩ := hσ
  have hcnlt : σ.vars (curName j) < n := by rw [hcn]; exact hkn
  have hturn : TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asgf mm σ :=
    ⟨hlev, hplay, hheld⟩
  -- the descent: the cluster, the batch, the two masks of the next depth, and the round
  obtain ⟨σ₁, hr₁, hturn₁, hout₁, hc₁, hwa₁, X, W, Alv', Gam', hball, hWne, hWcard,
      hsub₁, hbat₁, hplay₁⟩ :=
    (hdes hcsr hB).run ⟨hturn, hcnlt⟩
  -- **the descend clause**: the nested arena is inside this turn's cluster, so any
  -- monotone measure of it — a number the turn's cost condition may mention — is
  -- bounded by the turn's own block reading
  rw [hcn] at hsub₁
  have hinsize : Kin (wA Alv') ≤ Kin wBk :=
    hmono (hwAB Alv' hkn hheld.2.2.2.2.2.2.2.2 hsub₁)
  -- the padding
  obtain ⟨σ₂, hr₂, hturn₂, hplay₂, hout₂, hc₂, w, hdat₂, hwa₂⟩ :=
    (henum X W Alv' Gam').run ⟨hturn₁, hbat₁, hplay₁, hWne, hWcard, hwa₁⟩
  -- the colouring of the next depth
  obtain ⟨σ₃, hr₃, hturn₃, hdat₃, hplay₃, hout₃, hc₃, C', hcolarr₃, hcolbit₃, hcolread₃⟩ :=
    (hcol X W w Alv' Gam' hcsr hB).run ⟨hturn₂, hdat₂, hwa₂, hplay₂⟩
  have htsz₃ : TablesSized q_top cap mb φ n σ₃ := (htsz.run hr₁).run hr₂ |>.run hr₃
  have hbarr₃ : BaseArrs B q_top cap mb ℓ φ σ₃ := ((hbarr.run hr₁).run hr₂).run hr₃
  -- **the kill pass** (wave R1.8-T2). The padded buffer is still live: the
  -- colouring reads it and writes only the child palette, which is the last link
  -- of the `ClusterWa` seam — the nested call is where it ends
  have hwa₃ : ClusterWa mb w σ₃ := by
    show σ₃.arrs "wa" = _
    rw [hr₃.frame_arr "wa" hwafr]; exact hwa₂
  obtain ⟨σₖ, hrₖ, hturnₖ, hdatₖ, hcolarrₖ, hplayₖ, houtₖ, hcₖ, hkillₖ⟩ :=
    (hkill X W w Alv' Gam' C' hB).run (σ := σ₃)
      ⟨hturn₃, hdat₃, hwa₃, hcolarr₃, hcolbit₃, hcolread₃, hplay₃, htsz₃, hbarr₃⟩
  have hlevin : LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σₖ := by
    -- the depth-`j` member conjunct is NOT passed through: the clause is
    -- depth-indexed through `memName`, exactly like the two mask clauses, and the
    -- child's list is the one the descent filtered (rebase E-mem)
    obtain ⟨hn₃, hoff₃, htgt₃, -, -, -, -, -, -, hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, -⟩ :=
      hturnₖ.1
    obtain ⟨-, -, -, halv₃, hAlvB, -, -, hgam₃, hGamB, hmemin₃⟩ := hdatₖ.1
    exact ⟨hn₃, hoff₃, htgt₃, halv₃, hgam₃, hcolarrₖ,
      fun z hz => hAlvB z hz, fun z hz => hGamB z hz, hcolbit₃,
      hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, hmemin₃⟩
  have htszₖ : TablesSized q_top cap mb φ n σₖ := htsz₃.run hrₖ
  have hbarrₖ : BaseArrs B q_top cap mb ℓ φ σₖ := hbarr₃.run hrₖ
  -- the nested driver, with the frame of the depth it was called from
  obtain ⟨σ₄, hr₄, ⟨⟨-, -, htab₄⟩, hout₄⟩, hturn₄, hdat₄, hcolarr₄, hc₄⟩ :=
    (spec_conj ((hinner Alv' Gam' C' hcolbit₃).pre
        (fun _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩))
      (hfr hinner X W w Alv' Gam' C')).run
      (σ := σₖ) ⟨hlevin, hturnₖ, hdatₖ, htszₖ, hbarrₖ, hplayₖ⟩
  have htsz₄ : TablesSized q_top cap mb φ n σ₄ := htszₖ.run hr₄
  -- the scatter atoms
  obtain ⟨σ₅, hr₅, hturn₅, hdat₅, hcolarr₅, htab₅, hout₅, hc₅, hflag₅⟩ :=
    (hscat X W w Alv' Gam' C').run (σ := σ₄)
      ⟨hturn₄, hdat₄, hcolarr₄, hcolbit₃, hcolread₃, htab₄⟩
  have htsz₅ : TablesSized q_top cap mb φ n σ₅ := htsz₄.run hr₅
  have hc₅₀ : σ₅.vars (curName j) = σ.vars (curName j) := by
    rw [hc₅, hc₄, hcₖ, hc₃, hc₂, hc₁]
  -- the readback
  obtain ⟨σ₆, hr₆, hturn₆, hout₆, hc₆, hrb₆⟩ :=
    (hread X W w Alv' Gam' C').run (σ := σ₅)
      ⟨hturn₅, hdat₅, hcolarr₅, hcolbit₃, hcolread₃, htab₅, htsz₅,
        by rw [hc₅₀]; exact hcnlt, hflag₅⟩
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq (hrₖ.seq (hr₄.seq (hr₅.seq hr₆)))))
  refine ⟨σ₆, _, hrun, by omega, hturn₆.1, htsz₅.run hr₆, hbarrₖ.run (hr₄.seq (hr₅.seq hr₆)),
    hturn₆.2.1,
    by rw [hout₆, hout₅, hout₄, houtₖ, hout₃, hout₂, hout₁],
    by rw [hc₆, hc₅, hc₄, hcₖ, hc₃, hc₂, hc₁], fun i hi => ?_⟩
  obtain ⟨Tb, Tb₀, harr, -, -, hval⟩ := hrb₆ i hi
  refine ⟨Tb, harr, fun v hasgv => ?_⟩
  -- the assignment array is the cover's, so the vertex is one of this centre's
  have hasgf : asgf (v : ℕ) = σ₅.vars (curName j) := by rw [hc₅₀]; exact hasgv
  obtain ⟨hbit, hval'⟩ := hval v hasgf
  refine ⟨hbit, ?_⟩
  rw [hval']
  -- and what the readback wrote there is what the formula is worth
  have hβ : TableRank q_top (tablesAt q_top cap mb φ j)[i] :=
    tableRank_of_mem_tablesAt j _ (List.getElem_mem hi)
  have hballv : ball (masked G M) cap v ⊆ X := hball v (by rw [hasgf]; exact hc₅₀)
  have hglue := sat_iff_eval_step (mb := mb) (j := j) hcap (A := masked G M)
    (col := colRead n C (sigL cap mb j)) w v hβ hballv
  exact ⟨fun h => hglue.mpr h.2, fun hs => ⟨hasRank_stepFml hβ, hglue.mp hs⟩⟩

end Cluster

/-! ### The level

`RamDriver.driverAt … j` is the ordering pass, the cover pass, and the
loop over the centres the cover produced. The first two enter through
the driver's own obligations; the loop is `Spec.forRangeZero`, its body
`RamDriver.ClusterStepImplements`, and what it leaves is the table
invariant of the depth — because the turns partition the carrier, which
is `RamCover.CoverOut.asg_lt`. -/

section Level

/-- **Re-associating a sequence.** The driver's obligations are stated
over `.seq c d` where the program text is `.seq c (.seq d e)`: the cover
pass owns the copy that precedes it, and the copy is not a node of the
level's block. Splitting the one run and rebuilding it the other way is
the whole of the difference. -/
theorem run_seq_assoc {B : ℕ} {c d e : Com} {σ τ ρ : Env} {K K' : ℕ}
    (h : Run B (.seq c d) σ τ K) (h' : Run B e τ ρ K') :
    Run B (.seq c (.seq d e)) σ ρ (K + K') := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨k', hk', hb'⟩ := h'
  cases hb with
  | seq hb₁ hb₂ => exact ⟨_, by omega, .seq hb₁ (.seq hb₂ hb')⟩

variable {B cap mb ns Ws j : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {σ : Env}

/-- The depth's state does not see the cursor: no clause of it is about
a scalar other than the carrier's size, the edge count, the live width
and the depth's own member count. -/
theorem levelPre_setVar (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (x : String)
    (hxn : x ≠ "n") (hxm : x ≠ "m") (hxlw : x ≠ "lw") (hxmm : x ≠ mnumName j) (k : ℕ) :
    LevelPre B n cap mb ns Ws O T j M Gm C (σ.setVar x k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨hsz, hd, hq⟩, hdep, hm, hle, hosz, hz,
    Mem, mmj, hma, hmv, hme, hmB⟩ := h
  have _ := hxlw
  refine ⟨?_, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6, h7, h8, h9,
    ⟨fun p hp => by simpa using hsz p hp, by simpa using hd, by simpa using hq⟩,
    fun a => ⟨fun p hp => by simpa using (hdep a).1 p hp,
      fun c hc => by simpa using (hdep a).2 c hc⟩,
    ?_, hle.setVar x hxlw k, fun p hp => by simpa using hosz p hp, hz,
    Mem, mmj, by simpa using hma, ?_, hme, hmB⟩
  · rw [vars_setVar, if_neg (Ne.symm hxn)]; exact h1
  · rw [vars_setVar, if_neg (Ne.symm hxm)]; exact hm
  · rw [vars_setVar, if_neg (Ne.symm hxmm)]; exact hmv

theorem levelPre_setVar_c (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (k : ℕ) :
    LevelPre B n cap mb ns Ws O T j M Gm C (σ.setVar (curName j) k) :=
  levelPre_setVar h _ (curName_ne_n j) (curName_ne_m j) (curName_ne_lw j)
    (by simp [curName, mnumName, String.ext_iff]) k

theorem levelPre_setVar_ci (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (k : ℕ) :
    LevelPre B n cap mb ns Ws O T j M Gm C (σ.setVar (cixName j) k) :=
  levelPre_setVar h _ (cixName_ne_n j) (cixName_ne_m j) (cixName_ne_lw j)
    (by simp [cixName, mnumName, String.ext_iff]) k

/-- Nor does the table clause. -/
theorem tablesSized_setVar_c {q_top : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (h : TablesSized q_top cap mb φ n σ) (x : String) (k : ℕ) :
    TablesSized q_top cap mb φ n (σ.setVar x k) :=
  fun j p hp => by simpa using h j p hp

/-- Nor the arrays of the bottom. -/
theorem baseArrs_setVar_c {q_top ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (h : BaseArrs B q_top cap mb ℓ φ σ) (x : String) (k : ℕ) :
    BaseArrs B q_top cap mb ℓ φ (σ.setVar x k) :=
  ⟨fun p hp => by simpa using h.1 p hp,
    fun jd i hi => botMem_of_length (fun a => by rw [arrs_setVar]) _ "bb" (h.2 jd i hi)⟩

/-- Nor the recorded play, whose scalars are the earlier connectors. -/
theorem playRec_setVar {G : SimpleGraph (Fin n)}
    (h : PlayRec B cap G j M Gm σ) (x : String) (hx : ∀ a : ℕ, x ≠ ctrName a) (k : ℕ) :
    PlayRec B cap G j M Gm (σ.setVar x k) :=
  h.congr (fun a _ => by rw [vars_setVar, if_neg (Ne.symm (hx a))])
    (fun a _ => by rw [arrs_setVar])

theorem playRec_setVar_c {G : SimpleGraph (Fin n)}
    (h : PlayRec B cap G j M Gm σ) (k : ℕ) :
    PlayRec B cap G j M Gm (σ.setVar (curName j) k) :=
  playRec_setVar h _ (curName_ne_ctrName j) k

theorem playRec_setVar_ci {G : SimpleGraph (Fin n)}
    (h : PlayRec B cap G j M Gm σ) (k : ℕ) :
    PlayRec B cap G j M Gm (σ.setVar (cixName j) k) :=
  playRec_setVar h _ (cixName_ne_ctrName j) k

/-- Nor do the cover's answers. -/
theorem coverHeld_setVar {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    (h : CoverHeld B n j G M π ord cap Xoff Xmem asg m σ) (x : String)
    (hx : x ≠ xpName j) (k : ℕ) :
    CoverHeld B n j G M π ord cap Xoff Xmem asg m (σ.setVar x k) :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2.1,
    by simpa using h.2.2.2.1,
    by rw [vars_setVar, if_neg (Ne.symm hx)]; exact h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem coverHeld_setVar_c {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    (h : CoverHeld B n j G M π ord cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeld B n j G M π ord cap Xoff Xmem asg m (σ.setVar (curName j) k) :=
  coverHeld_setVar h _ (curName_ne_xpName j j) k

theorem coverHeld_setVar_ci {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    (h : CoverHeld B n j G M π ord cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeld B n j G M π ord cap Xoff Xmem asg m (σ.setVar (cixName j) k) :=
  coverHeld_setVar h _ (cixName_ne_xpName j j) k

/-- **What one cluster leaves alone.** `RamDriver.ClusterStepImplements`
says what the turn wrote at the vertices of the centre it was
processing; the loop needs, on top of that, that it wrote nothing at the
vertices of the centres already processed, and that the cover's three
answers are still there for the next turn. Neither is a frame condition
that can be read off the syntax — the turn contains the nested driver,
which is a variable — so both are stated here, at the same precondition,
and `spec_conj` merges them with the driver's obligation into one
specification of one command. -/
def ClusterFrames (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m k : ℕ) (wA : (ℕ → ℕ) → ℕ)
    (inner : Com) (Kin : ℕ → ℕ) (K : ℕ) : Prop :=
  k < n →
  (∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ), (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
      Spec B (fun σ => LevelPre B n cap mb ns Ws O T (j + 1) M' Gm' C' σ ∧
          TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
          PlayRec B cap G (j + 1) M' Gm' σ) inner
        (fun σ σ' => LevelPost B q_top cap mb φ G ns Ws O T (j + 1) M' Gm' C' σ σ' ∧
          σ'.out = σ.out) (Kin (wA M'))) →
    Spec B (fun σ => LevelPre B n cap mb ns Ws O T j M Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
        PlayRec B cap G j M Gm σ ∧
        CoverHeld B n j G M π ord cap Xoff Xmem asg m σ ∧ σ.vars (curName j) = k)
      (clusterCom q_top cap mb φ j inner)
      (fun σ σ' => CoverHeld B n j G M π ord cap Xoff Xmem asg m σ' ∧
        ∀ (i : ℕ), i < (tablesAt q_top cap mb φ j).length → ∀ Tb Tb₀ : ℕ → ℕ,
          σ'.arrs (tabName j i) = arrOf n Tb → σ.arrs (tabName j i) = arrOf n Tb₀ →
          ∀ v : Fin n, asg (v : ℕ) ≠ σ.vars (curName j) → Tb (v : ℕ) = Tb₀ (v : ℕ)) K

/-- **What the centre loop carries.** The depth's state, its table
arrays, the cover's answers, the compacted centre list, the output tape
as it was, and the tables of the vertices whose centre has already been
processed. The last clause is stated over *any* cell function the array
happens to have, since a turn hands its own back.

**Rebase B3.** The loop counter is `cixName j`, an index into the
compacted list `cps`, and "already processed" is therefore
`∃ k < cix, asg v = cps k` rather than `asg v < cur`: the turns still
partition the carrier, but they enumerate the *listed* positions and no
longer the carrier. `Compacted.covers` at the exit is what says every
vertex has had its turn — its assigned position holds it, so its block
is nonempty, so the compaction listed it. -/
def LevelInv (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg cps : ℕ → ℕ) (m cnum : ℕ) (outs : List ℕ) (σ : Env) : Prop :=
  LevelPre B n cap mb ns Ws O T j M Gm C σ ∧ TablesSized q_top cap mb φ n σ ∧
    BaseArrs B q_top cap mb ℓ φ σ ∧ PlayRec B cap G j M Gm σ ∧
    CoverHeld B n j G M π ord cap Xoff Xmem asg m σ ∧
    σ.arrs (cpsName j) = arrOf n cps ∧ σ.vars (cnumName j) = cnum ∧
    σ.out = outs ∧ σ.vars (cixName j) ≤ cnum ∧
    ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length) (Tb : ℕ → ℕ),
      σ.arrs (tabName j i) = arrOf n Tb →
      ∀ v : Fin n, (M (v : ℕ) = 0 ∨ ∃ k < σ.vars (cixName j), asg (v : ℕ) = cps k) →
        Tb (v : ℕ) ≤ 1 ∧
        (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
          (tablesAt q_top cap mb φ j)[i])

open Classical in
/-- **One level, discharged.** `RamDriver.driverAt … j` establishes the
table invariant of its depth, for every depth at or above the bottom.

Downward induction on the budget still to spend. At `j = ℓ` it is the
base case's hypothesis. Below `ℓ` it is the ordering pass, the cover
pass, and `Refine.SigmaLoop.forRangeZeroSum` over the centres with
`RamDriver.ClusterStepImplements` as its body — the nested driver
entering that body as the induction hypothesis at `j + 1`. What the loop
leaves is the table invariant of the whole carrier, because the turns
partition it: `RamCover.CoverOut.asg_lt` assigns every vertex to a
centre, so at the exit every vertex has had its own turn, and
`ClusterFrames` is why no later turn undid it.

**Rebase B2: the Σ/size interface** (`integration-design.md` §5.6).
Every cost is read at a **measure of the arena** — since rebase G2/E6
an abstract one: a level costs `Kl j (wA M)`, a turn
`Ks j (wB Xoff Xmem k)` on its own block, and the loop pays the **sum**
of its turns rather than `n` times the worst one —
`Refine.SigmaLoop.forRangeZeroSum` in place of `Spec.forRangeZero`. The
readings `wA`/`wB` are parameters because the G2 instantiation
(`Refine.MassWeight.arenaWeight`/`blockWeight`, the arena weight at the
level's fixed graph) lives above this file in the import order;
`wA := arenaSize n`, `wB := fun Xoff _ => blockSize Xoff` is the landed
size reading, and `RamDriverRoot.levelAt` instantiates the weights. Two
hypotheses carry the arithmetic that makes the sum affordable, and
neither is about the program:

* `hmass`, the mass mathematics — that the compacted loop takes at most
  `wA M` turns, and that the turns' blocks sum to at most
  `Kmass · (wA M + 1)` (at the weight reading this is
  `Refine.MassWeight.mass_of_alive_compaction_weight`, same hypotheses,
  same coefficient). **Rebase F-c-3:** it is handed the
  ordering-property slot `P π ord` beside `RamCover.OrdersBy`, because
  the coefficient `Kmass` *is* the cover's degree and a cover's degree
  is a property of the ordering the phase built, not of every ordering.
  At `R = 0`, `P` is `fun _ _ => True` and the clause costs its supplier
  nothing; at `R = R*` it is `CoverDegree.AugChainData`, and
  `RamDriverRoot.wreachDeg_of_orderP` is the step from the slot to the
  degree. Before this the phase's `P` witness was destructured away one
  line after it arrived (`horder`'s postcondition), which left the
  root's `hdeg` slot asking for a bound at *every* permutation — a
  hypothesis with no possible producer. `Refine.ArenaBlock.mass_of_alive_compaction`
  is that pair, compiled, from wave B4's `Refine.MassAlive.aliveMass_le`
  plus **one clause `RamDriver.compactCom` does not yet establish**: that
  the listed centres are alive. It is threaded parametrically here
  because supplying it means filtering the compaction, and an
  alive-filtered compaction leaves the *dead* vertices without a turn —
  `Refine.ArenaBlock.dead_vertex_has_no_alive_turn` compiles that, and
  the partition step below is what it contradicts. That is the campaign's
  open item; nothing in this theorem's shape depends on how it is
  resolved.
* `hK`, the level's cost side condition in the Σ shape —
  `CostRecurrence.exists_driverCostsSigma` discharges it in one call, up
  to the three-unit shift the compacted loop's `cps` read costs
  (`RamDriverRoot.levelCost_of_sigma`).

`Refine.ArenaBlock.sum_blockSize_compacted_le` is what connects them:
the turns' blocks are distinct blocks of the one arena, so their sizes
sum to at most its mass. **No semantic clause of the induction moved**:
the partition argument, the frames and the table invariant are B3's,
untouched.

The carrier is no longer asked to be nonempty: `RamDriver.TablesSized`
is the depth's table arrays at the carrier's length, carried by the
level's own precondition, so the loop no longer has to *produce* that
fact from a turn having been taken.

The block structure is asked for in the *simple* form
`RamElim.CsrSimple` — `RamBfs.CsrGraph` with no row naming a vertex
twice — because that is what the ordering phase's two eliminations need
and what `RamDriver.OrderImplements` therefore takes; the cover phase
and the cluster step take the weaker `CsrGraph`, and get it from
`hcsr.csr`. Nothing between the root and here can bridge the two, so the
clause is data of the input encoding.

**The value bound, and the two arena slots** (rebase E-mem/W2). `hB` is
`RamDriver.WordBoundK` at a degree parameter `d` the induction never
looks at: every phase but one reads only the five projections, so the
level is uniform in `d` and hands its own `hB` down unchanged. The
exception is the cover phase, whose two values are addresses *into* the
cluster arena — the emission scan's running pointer and the pass's exit
pointer — and those are `hptr` and `hexit`, quantified here over the
mask and the ordering because the ordering is produced inside the loop
and the mask changes with the depth. Both have a carrier reading
(`RamDriver.ptrWords_of_square`, `massWords_of_square`, off the retired
`WordBound.cover`) and a mass reading
(`Refine.ArenaPointer.ptrWords_of_mass`, `massWords_of_mass`, off
`WordBoundK` at the cover's degree); this theorem is indifferent to
which, and that is the whole point of their being slots.

Both slots carry `RamCover.OrdersBy n π ord` as a hypothesis (W3). The
mass readings need it — the double count of `Refine.MassMath` is over
the ordering's own fibres — and the loop has it in hand at the one
point either slot is used, since the ordering phase produced `π` and
`ord` together with it. The carrier readings ignore it, so this costs
the landed instantiation nothing. -/
theorem levelImplements {B q_top cap mb R ℓ W ns : ℕ} {N : ℕ → ℕ} {s : ℕ}
    {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {P : Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop}
    {wA : (ℕ → ℕ) → ℕ} {wB : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ}
    {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ} {Kmass : ℕ}
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) (hWB : n + W + 1 < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (helim : ElimAvail B n) (haug : AugAvail B n) (hcovav : CoverAvail B cap ns G O T)
    (hptr : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.PtrWords B G M π ord cap)
    (hexit : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.MassWords B G M π ord cap)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hℓ : ℓ = N (2 * s + 2))
    (hbase : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ), masked G M = ⊥ →
      LevelImplements B q_top cap mb R ℓ W ns ℓ φ G O T M Gm C (Kl ℓ (wA M)))
    (horder : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplements B n R W cap mb ns j G O T M Gm C P (Ko j (wA M)))
    (hcover : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      CoverImplements B cap mb ns W j G O T M Gm C π ord (Kc j (wA M)))
    (hstep : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm k : ℕ),
      ClusterStepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm k
        wA (driverAt q_top cap mb R ℓ φ (j + 1)) (Kl (j + 1)) (Ks j (wB Xoff Xmem k)))
    (hframe : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm k : ℕ),
      ClusterFrames B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm k
        wA (driverAt q_top cap mb R ℓ φ (j + 1)) (Kl (j + 1)) (Ks j (wB Xoff Xmem k)))
    (hloopfr : ∀ (j : ℕ), j < ℓ →
      cpsName j ∉ (clusterCom q_top cap mb φ j
          (driverAt q_top cap mb R ℓ φ (j + 1))).warrs ∧
        cnumName j ∉ (clusterCom q_top cap mb φ j
          (driverAt q_top cap mb R ℓ φ (j + 1))).wvars ∧
        cixName j ∉ (clusterCom q_top cap mb φ j
          (driverAt q_top cap mb R ℓ φ (j + 1))).wvars)
    (hsweep : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      SweepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C (Kd j (wA M)))
    (hmass : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg cps : ℕ → ℕ)
        (mm cnum : ℕ), RamCover.OrdersBy n π ord → P π ord →
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Compacted n cnum mm M ord Xoff cps →
      cnum ≤ wA M ∧
        (∑ k ∈ Finset.range cnum, wB Xoff Xmem (cps k)) ≤ Kmass * (wA M + 1))
    (hK : ∀ (j : ℕ), j < ℓ → ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    ∀ (j : ℕ), j ≤ ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb R ℓ W ns j φ G O T M Gm C (Kl j (wA M)) := by
  classical
  have key : ∀ (f j : ℕ), ℓ - j = f → j ≤ ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb R ℓ W ns j φ G O T M Gm C (Kl j (wA M)) := by
    intro f
    induction f with
    | zero =>
      intro j hf hj M Gm C hbit
      have hje : j = ℓ := by omega
      subst hje
      intro σ hσ
      -- the budget is spent, so the play cannot have got this far: the arena is edgeless
      have hbot : masked G M = ⊥ :=
        eq_bot_of_playOk_full hQ (by rw [← hℓ]; exact playOk_of_playRec hσ.2.2.2)
      exact hbase M Gm C hbot hbit σ hσ
    | succ f ih =>
      intro j hf hj M Gm C hbit
      have hjl : j < ℓ := by omega
      have hinner : ∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ),
          (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
          Spec B (fun σ => LevelPre B n cap mb ns W O T (j + 1) M' Gm' C' σ ∧
              TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
              PlayRec B cap G (j + 1) M' Gm' σ)
            (driverAt q_top cap mb R ℓ φ (j + 1))
            (fun σ σ' => LevelPost B q_top cap mb φ G ns W O T (j + 1) M' Gm' C' σ σ' ∧
              σ'.out = σ.out) (Kl (j + 1) (wA M')) :=
        fun M' Gm' C' hb' => ih (j + 1) (by omega) (by omega) M' Gm' C' hb'
      refine Spec.of_exists fun σ hσ => ?_
      rw [driverAt_succ q_top cap mb R ℓ φ hjl]
      -- the ordering pass
      obtain ⟨σ₁, hr₁, hlev₁, hout₁, hctr₁, hgam₁, π, ord, hord₁, hordby, hordP⟩ :=
        (horder j hjl M Gm C hB hcsr hWB helim haug).run hσ.1
      have htsz₁ : TablesSized q_top cap mb φ n σ₁ := hσ.2.1.run hr₁
      have hbarr₁ : BaseArrs B q_top cap mb ℓ φ σ₁ := hσ.2.2.1.run hr₁
      have hplay₁ : PlayRec B cap G j M Gm σ₁ :=
        hσ.2.2.2.congr (fun a _ => hctr₁ a) (fun a _ => hgam₁ a)
      -- the cover pass, and the compaction that ends it
      obtain ⟨σ₂, hr₂, hlev₂, hout₂, hctr₂, hgam₂, Xoff, Xmem, asg, cps, mm, cnum,
          hheld₂, hcps₂, hcnum₂, hcomp₂⟩ :=
        (hcover j hjl M Gm C π ord hB hcsr.csr (hptr M π ord hordby) (hexit M π ord hordby)
            hcovav hordby).run
          ⟨hlev₁, hord₁, fun z hz => hordby.lt hz⟩
      have htsz₂ : TablesSized q_top cap mb φ n σ₂ := htsz₁.run hr₂
      have hbarr₂ : BaseArrs B q_top cap mb ℓ φ σ₂ := hbarr₁.run hr₂
      have hplay₂ : PlayRec B cap G j M Gm σ₂ :=
        hplay₁.congr (fun a _ => hctr₂ a) (fun a _ => hgam₂ a)
      have hcnB : cnum < B := lt_of_le_of_lt hcomp₂.le_carrier hB.n_lt
      -- **the dead-row sweep** (rebase B8): the rows of the vertices the mask has
      -- killed, written once, before any turn — so the compacted loop may skip them
      obtain ⟨σ₃, hr₃, hlev₃, hout₃, hctr₃, hgam₃, hodr₃, hxof₃, hxmm₃, hasg₃, hxp₃,
          hcpsf₃, hcnumf₃, hdead₃⟩ :=
        (hsweep j hjl M Gm C).run (σ := σ₂) ⟨hlev₂, htsz₂, hbarr₂⟩
      have htsz₃ : TablesSized q_top cap mb φ n σ₃ := htsz₂.run hr₃
      have hbarr₃ : BaseArrs B q_top cap mb ℓ φ σ₃ := hbarr₂.run hr₃
      have hplay₃ : PlayRec B cap G j M Gm σ₃ :=
        hplay₂.congr (fun a _ => hctr₃ a) (fun a _ => hgam₃ a)
      have hheld₃ : CoverHeld B n j G M π ord cap Xoff Xmem asg mm σ₃ :=
        ⟨by rw [hodr₃ j]; exact hheld₂.1, by rw [hxof₃ j]; exact hheld₂.2.1,
          by rw [hxmm₃ j]; exact hheld₂.2.2.1, by rw [hasg₃ j]; exact hheld₂.2.2.2.1,
          by rw [hxp₃ j]; exact hheld₂.2.2.2.2.1, hheld₂.2.2.2.2.2.1,
          hheld₂.2.2.2.2.2.2.1, hheld₂.2.2.2.2.2.2.2.1, hheld₂.2.2.2.2.2.2.2.2⟩
      have hcps₃ : σ₃.arrs (cpsName j) = arrOf n cps := by rw [hcpsf₃ j]; exact hcps₂
      have hcnum₃ : σ₃.vars (cnumName j) = cnum := by rw [hcnumf₃ j]; exact hcnum₂
      -- **the partition, split** (rebase B8). An *alive* vertex's assigned position is
      -- alive too — clusters are alive-homogeneous — so its block is not empty and the
      -- compaction listed it. A dead vertex's position is not listed, and does not need
      -- to be: the sweep has already written its row.
      have hasgcps : ∀ v < n, M v ≠ 0 → ∃ k < cnum, asg v = cps k := by
        intro v hv hal
        have hout := hheld₂.2.2.2.2.2.2.2.2
        have hlt : asg v < n := hout.asg_lt v hv
        have hself : RamCover.InCluster (masked G M) π cap (ord (asg v)) v :=
          hout.asg_cover v hv (mem_ball_self _ _ _)
        obtain ⟨p, hp₁, hp₂, -⟩ := (hout.block (asg v) hlt v).mpr hself
        obtain ⟨k, hk, hkc⟩ := hcomp₂.covers (asg v) hlt (by omega)
          ((Refine.MassAlive.inCluster_alive_iff hself).mp hal)
        exact ⟨k, hk, hkc.symm⟩
      -- and a dead vertex's own centre is dead, so no turn of the loop is its turn
      have hdeadne : ∀ v : Fin n, M (v : ℕ) = 0 → ∀ k < cnum, asg (v : ℕ) ≠ cps k := by
        intro v hdv k hk he
        refine hcomp₂.alive k hk ?_
        rw [← he]
        exact Refine.ArenaBlock.dead_vertex_has_no_alive_turn hheld₂.2.2.2.2.2.2.2.2 v.isLt hdv
      obtain ⟨hfrA, hfrQ, hfrI⟩ := hloopfr j hjl
      -- one turn of the loop over the *listed* centres, **at its own block**: the
      -- obligation, its frame, and the syntactic frame of the three loop-header names
      have hbody : ∀ kk : ℕ, kk < cnum → Spec B
          (fun τ =>
            LevelInv B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg cps mm cnum
              σ₃.out τ ∧ τ.vars (cixName j) = kk)
          (.seq (.assign (curName j) (.get (cpsName j) (.var (cixName j))))
            (.seq (clusterCom q_top cap mb φ j (driverAt q_top cap mb R ℓ φ (j + 1)))
              (.assign (cixName j) (.add (.var (cixName j)) (.lit 1)))))
          (fun _ τ' =>
            LevelInv B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg cps mm cnum
              σ₃.out τ' ∧
            τ'.vars (cixName j) = kk + 1) (Ks j (wB Xoff Xmem (cps kk)) + 7) := by
        intro kk hkk
        have hpos : cps kk < n := hcomp₂.lt _ hkk
        have hcl : Spec B (fun τ => LevelPre B n cap mb ns W O T j M Gm C τ ∧
              TablesSized q_top cap mb φ n τ ∧ BaseArrs B q_top cap mb ℓ φ τ ∧
              PlayRec B cap G j M Gm τ ∧
              CoverHeld B n j G M π ord cap Xoff Xmem asg mm τ ∧ τ.vars (curName j) = cps kk)
            (clusterCom q_top cap mb φ j (driverAt q_top cap mb R ℓ φ (j + 1))) _
            (Ks j (wB Xoff Xmem (cps kk))) :=
          spec_conj
            (hstep j hjl M Gm C π ord Xoff Xmem asg mm (cps kk) hB hcsr.csr hpos hbit hinner)
            (hframe j hjl M Gm C π ord Xoff Xmem asg mm (cps kk) hpos hinner)
        refine Spec.of_exists fun τ hτ => ?_
        obtain ⟨⟨hlevτ, htszτ, hbarrτ, hplayτ, hheldτ, hcpsτ, hcnumτ, houtτ, -, htabτ⟩,
          hcix⟩ := hτ
        have hcixlt : τ.vars (cixName j) < cnum := by rw [hcix]; exact hkk
        have hcixB : τ.vars (cixName j) < B := by omega
        have hposτ : cps (τ.vars (cixName j)) < n := by rw [hcix]; exact hpos
        -- the turn's position is read out of the compacted list
        have hread : Run B (.assign (curName j) (.get (cpsName j) (.var (cixName j)))) τ
            (τ.setVar (curName j) (cps (τ.vars (cixName j)))) 3 := by
          have h := Run.assign (B := B) (σ := τ) (x := curName j)
            (e := .get (cpsName j) (.var (cixName j)))
            (evalB_get (evalB_var hcixB)
              (by rw [hcpsτ]; exact getElem?_arrOf cps (lt_of_lt_of_le hcixlt hcomp₂.le_carrier))
              (lt_trans hposτ hB.n_lt))
          simpa using h
        set τ₁ := τ.setVar (curName j) (cps (τ.vars (cixName j))) with hτ₁
        have hcur₁ : τ₁.vars (curName j) = cps (τ.vars (cixName j)) := by
          rw [hτ₁, vars_setVar, if_pos rfl]
        obtain ⟨τ₂, hr, ⟨⟨hlev', htsz', hbarr', hplay', hout', hc', htab'⟩, hheld', hfr'⟩,
            hfv, hfa, -, -⟩ :=
          (hcl.frame).run (σ := τ₁)
            ⟨levelPre_setVar_c hlevτ _, tablesSized_setVar_c htszτ _ _,
              baseArrs_setVar_c hbarrτ _ _, playRec_setVar_c hplayτ _,
              coverHeld_setVar_c hheldτ _, by rw [hcur₁, hcix]⟩
        have hcix₂ : τ₂.vars (cixName j) = τ.vars (cixName j) := by
          rw [hfv _ hfrI, hτ₁, vars_setVar, if_neg (cixName_ne_curName j j)]
        have hbump : Run B (.assign (cixName j) (.add (.var (cixName j)) (.lit 1))) τ₂
            (τ₂.setVar (cixName j) (τ.vars (cixName j) + 1)) 4 := by
          have h := Run.assign (B := B) (σ := τ₂) (x := cixName j)
            (e := .add (.var (cixName j)) (.lit 1))
            (evalB_bin (evalB_var (by rw [hcix₂]; exact hcixB)) (evalB_lit (by omega))
              (by simp only [Bop.apply_add, hcix₂]; omega))
          rw [Bop.apply_add, hcix₂] at h
          simpa using h
        refine ⟨τ₂.setVar (cixName j) (τ.vars (cixName j) + 1), _,
          hread.seq (hr.seq hbump), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact levelPre_setVar_ci hlev' _
        · exact tablesSized_setVar_c htsz' _ _
        · exact baseArrs_setVar_c hbarr' _ _
        · exact playRec_setVar_ci hplay' _
        · exact coverHeld_setVar_ci hheld' _
        · rw [arrs_setVar, hfa _ hfrA, hτ₁, arrs_setVar]; exact hcpsτ
        · rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j)), hfv _ hfrQ, hτ₁,
            vars_setVar, if_neg (cnumName_ne_curName j j)]
          exact hcnumτ
        · rw [out_setVar, hout', hτ₁, out_setVar]; exact houtτ
        · rw [vars_setVar, if_pos rfl]; omega
        · -- the tables: this turn's vertices, the dead ones, and the earlier turns' left
          -- alone
          intro i hi Tb harr v hv
          rw [vars_setVar, if_pos rfl] at hv
          rw [arrs_setVar] at harr
          obtain ⟨Tb', harr', hcorr'⟩ := htab' i hi
          have hTb : Tb (v : ℕ) = Tb' (v : ℕ) :=
            eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
          rcases hv with hdv | ⟨k, hk, hkv⟩
          · -- a dead vertex: the sweep wrote its row, and this turn's centre is alive
            obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
            have hne : asg (v : ℕ) ≠ τ₁.vars (curName j) := by
              rw [hcur₁]; exact hdeadne v hdv _ hcixlt
            have := hfr' i hi Tb' Tb₀ harr' (by rw [hτ₁, arrs_setVar]; exact harr₀) v hne
            rw [hTb, this]
            exact htabτ i hi Tb₀ harr₀ v (Or.inl hdv)
          · rcases Nat.lt_or_ge k (τ.vars (cixName j)) with hlt | hge
            · -- an earlier listed centre: the turn left its cell alone
              obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
              have hne : asg (v : ℕ) ≠ τ₁.vars (curName j) := by
                rw [hcur₁, hkv]
                exact fun hq => absurd (hcomp₂.inj (by omega) hcixlt hq) (by omega)
              have := hfr' i hi Tb' Tb₀ harr' (by rw [hτ₁, arrs_setVar]; exact harr₀) v hne
              rw [hTb, this]
              exact htabτ i hi Tb₀ harr₀ v (Or.inr ⟨k, hlt, hkv⟩)
            · -- this turn's own vertex
              have hkeq : k = τ.vars (cixName j) := by omega
              rw [hTb]
              exact hcorr' v (by rw [hcur₁, hkv, hkeq])
        · rw [vars_setVar, if_pos rfl]; omega
      -- the loop, over the compacted list, **paying the sum of its turns**
      obtain ⟨σ₄, hr₄, hI₄, hcn₄⟩ :=
        (Refine.SigmaLoop.forRangeZeroSum (cixName j) (cnumName j)
          (LevelInv B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg cps mm cnum
            σ₃.out) cnum
          (fun kk => Ks j (wB Xoff Xmem (cps kk)) + 7) hcnB
          (fun _ hτ => hτ.2.2.2.2.2.2.2.2.1) (fun _ hτ => hτ.2.2.2.2.2.2.1)
          hbody).run
          (σ := σ₃) ⟨levelPre_setVar_ci hlev₃ 0, tablesSized_setVar_c htsz₃ _ 0,
            baseArrs_setVar_c hbarr₃ _ 0, playRec_setVar_ci hplay₃ 0,
            coverHeld_setVar_ci hheld₃ 0, by simpa using hcps₃,
            by rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j))]; exact hcnum₃,
            by simp,
            by simp,
            by intro i hi Tb harr v hv
               rw [arrs_setVar] at harr
               rcases hv with hdv | ⟨k, hk, -⟩
               · exact hdead₃ i hi Tb harr v hdv
               · rw [vars_setVar, if_pos rfl] at hk; omega⟩
      -- the exit: the alive vertices by their turn, the dead ones by the sweep
      have htabinv : TableInv q_top cap mb φ G j M C σ₄ := by
        intro i hi
        obtain ⟨Tb, harr⟩ := hI₄.2.1.get j hi
        have hrow : ∀ v : Fin n, Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
              (tablesAt q_top cap mb φ j)[i]) := by
          intro v
          by_cases hdv : M (v : ℕ) = 0
          · exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v (Or.inl hdv)
          · obtain ⟨k, hk, hkv⟩ := hasgcps (v : ℕ) v.isLt hdv
            exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v
              (Or.inr ⟨k, by rw [hcn₄]; exact hk, hkv⟩)
        exact ⟨Tb, harr, fun v hv => (hrow ⟨v, hv⟩).1, fun v => (hrow v).2⟩
      -- **the cost, in the Σ shape.** The turns' blocks are distinct blocks of the one
      -- cluster arena, so their sizes sum to at most its mass; the mass mathematics
      -- turns that into the coefficient the level condition consumes.
      obtain ⟨hturns, hbs⟩ :=
        hmass M π ord Xoff Xmem asg cps mm cnum hordby hordP hheld₂.2.2.2.2.2.2.2.2 hcomp₂
      have hsum : (∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 7 + 4)) =
          ∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 11) :=
        Finset.sum_congr rfl fun _ _ => by omega
      have hcost := hK j hjl (wA M) cnum hturns
        (fun c => wB Xoff Xmem (cps c)) hbs
      refine ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ?_,
        ⟨hI₄.1, hI₄.2.1, htabinv⟩,
        by rw [hI₄.2.2.2.2.2.2.2.1, hout₃, hout₂, hout₁]⟩
      rw [hsum]
      omega
  exact fun j hj => key (ℓ - j) j rfl hj

end Level


end Lax3Proofs.RamDriverCluster
