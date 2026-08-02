import Lax13Proofs.Refine.Iicf.Impl.AbsHeap
import Lax13Proofs.Refine.Iicf.Impl.ArrayList

/-!
# Array-list implementation of priority heaps

Port of the generic `IICF_Impl_Heap.thy` from
`maxhaslbeck/Sepreftime@c1c987b45ec886d289ba215768182ac87b82f20d`,
cross-checked against the executable specialization in
`lammich/isabelle_llvm_time@42dd7f59998d76047bb4b6bce76d8f67b53a08b6`.

The executable source globally instantiates its generic locale with natural
elements, identity priority, signed-natural indices, and an array list. This
file keeps that specialization. The logical heap motions are exactly those
of `AbsHeap`: one-based update/value/exchange, parent swim, optimized smaller-
child sink (left on ties), append-then-swim insertion, and exchange/butlast/
sink deletion.

The source can allocate its initial array and grow by allocation.  This
repository's array list is caller-owned, so executable insertion is exposed
only from the existing ready relation and empty remains a semantic model with
no executable rule.  Reads and in-place motions preserve the caller's buffer;
pop uses the caller-owned logical-capacity shrink supplied by `ArrayList`.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## Composed representation -/

def implHeapRel : Set (ArrayList × Multiset ℕ) :=
  relComp arrayListRel (absHeapRel id)

def implHeapReadyRel : Set (ArrayList × Multiset ℕ) :=
  relComp arrayListReadyRel (absHeapRel id)

def implHeapAssn : Multiset ℕ → String × String × String → Assn :=
  hrComp arrayListAssn (absHeapRel id)

def implHeapReadyAssn : Multiset ℕ → String × String × String → Assn :=
  hrComp arrayListReadyAssn (absHeapRel id)

@[intf_of_assn] theorem implHeapAssn_intf :
    intfOfAssn implHeapAssn (MultisetI ℕ) := trivial

@[intf_of_assn] theorem implHeapReadyAssn_intf :
    intfOfAssn implHeapReadyAssn (MultisetI ℕ) := trivial

@[simp] theorem mem_implHeapRel_iff {s : ArrayList} {m : Multiset ℕ} :
    (s, m) ∈ implHeapRel ↔
      ∃ h : AbsHeap ℕ, (s, h) ∈ arrayListRel ∧
        heapInvariant id h ∧ (h : Multiset ℕ) = m := by
  simp [implHeapRel, mem_relComp, mem_absHeapRel_iff]

@[simp] theorem mem_implHeapReadyRel_iff {s : ArrayList} {m : Multiset ℕ} :
    (s, m) ∈ implHeapReadyRel ↔
      ∃ h : AbsHeap ℕ, (s, h) ∈ arrayListReadyRel ∧
        heapInvariant id h ∧ (h : Multiset ℕ) = m := by
  simp [implHeapReadyRel, mem_relComp, mem_absHeapRel_iff]

theorem implHeapRel_singleValued : SingleValued implHeapRel := by
  intro s m n hm hn
  obtain ⟨h, hs, -, hmb⟩ := mem_implHeapRel_iff.mp hm
  obtain ⟨k, ht, -, hnb⟩ := mem_implHeapRel_iff.mp hn
  have hhk : h = k := arrayListRel_singleValued s h k hs ht
  subst k
  exact hmb.symm.trans hnb

/-! ## Exact array-list heap operations -/

def implHeapUpdate? (s : ArrayList) (i v : ℕ) : Option ArrayList :=
  arlSet? s (i - 1) v

def implHeapValue? (s : ArrayList) (i : ℕ) : Option ℕ :=
  arlGet? s (i - 1)

def implHeapExchange? (s : ArrayList) (i j : ℕ) : Option ArrayList :=
  arlSwap? s (i - 1) (j - 1)

noncomputable def implHeapValid (s : ArrayList) (i : ℕ) : Bool :=
  propBool (0 < i ∧ i ≤ s.length)

def implHeapPrio? (s : ArrayList) (i : ℕ) : Option ℕ :=
  implHeapValue? s i

def implHeapSwim (s : ArrayList) (i : ℕ) : ArrayList :=
  arlWithActive s (heapSwim id s.active i)

def implHeapSink (s : ArrayList) (i : ℕ) : ArrayList :=
  arlWithActive s (heapSink id s.active i)

def implHeapInsert? (x : ℕ) (s : ArrayList) : Option ArrayList := do
  let t ← arlAppend s x
  pure (implHeapSwim t t.length)

def implHeapPeekMin? (s : ArrayList) : Option ℕ := arlGet? s 0

def implHeapPopMin? (s : ArrayList) : Option (ℕ × ArrayList) := do
  let (x, h') ← heapPopMin? id s.active
  let t ← arlButlast? s
  pure (x, arlWithActive t h')

def implHeapEmptyModel : ArrayList := arlEmptyModel

def implHeapIsEmpty (s : ArrayList) : Bool := arlIsEmpty s

/-! ## Primitive and loop refinement seams -/

theorem implHeapUpdate?_refines {s t : ArrayList} {h : AbsHeap ℕ}
    {i v : ℕ} (hs : (s, h) ∈ arrayListRel)
    (ht : implHeapUpdate? s i v = some t) :
    (t, heapUpdate h i v) ∈ arrayListRel := by
  apply arlSet?_some_refines hs
  simpa [implHeapUpdate?, heapUpdate] using ht

theorem implHeapValue?_refines {s : ArrayList} {h : AbsHeap ℕ}
    {i : ℕ} (hs : (s, h) ∈ arrayListRel) (hi : heapValid h i) :
    implHeapValue? s i = some (heapValue h i) := by
  rw [implHeapValue?, arlGet?_refines hs]
  have hidx : i - 1 < h.length := by
    rcases hi with ⟨hi0, hilen⟩
    omega
  exact listAt?_eq_some_getD h (i - 1) default hidx

theorem implHeapExchange?_refines {s t : ArrayList} {h : AbsHeap ℕ}
    {i j : ℕ} (hs : (s, h) ∈ arrayListRel)
    (ht : implHeapExchange? s i j = some t) :
    (t, heapExchange h i j) ∈ arrayListRel := by
  apply arlSwap?_some_refines hs
  simpa [implHeapExchange?, heapExchange] using ht

@[simp] theorem implHeapValid_refines {s : ArrayList} {h : AbsHeap ℕ}
    (hs : (s, h) ∈ arrayListRel) (i : ℕ) :
    implHeapValid s i = propBool (heapValid h i) := by
  apply propBool_congr
  apply propext
  simp [heapValid, arrayListRel_length hs]

theorem implHeapPrio?_refines {s : ArrayList} {h : AbsHeap ℕ}
    {i : ℕ} (hs : (s, h) ∈ arrayListRel) (hi : heapValid h i) :
    implHeapPrio? s i = some (id (heapValue h i)) := by
  simpa [implHeapPrio?] using implHeapValue?_refines hs hi

theorem implHeapSwim_refines {s : ArrayList} {h : AbsHeap ℕ} {i : ℕ}
    (hs : (s, h) ∈ arrayListRel) (hinv : swimInvariant id h i) :
    (implHeapSwim s i, heapSwim id h i) ∈ arrayListRel := by
  change s.Wf ∧ s.active = h at hs
  have hc := heapSwim_correct id hinv
  have hlen : (heapSwim id s.active i).length = s.length := by
    rw [hs.2]
    exact hc.2.2.trans (arrayListRel_length ⟨hs.1, hs.2⟩).symm
  refine ⟨arlWithActive_wf hs.1 hlen, ?_⟩
  rw [implHeapSwim, arlWithActive_active hlen, hs.2]

theorem implHeapSink_refines {s : ArrayList} {h : AbsHeap ℕ} {i : ℕ}
    (hs : (s, h) ∈ arrayListRel) (hinv : sinkInvariant id h i) :
    (implHeapSink s i, heapSink id h i) ∈ arrayListRel := by
  change s.Wf ∧ s.active = h at hs
  have hc := heapSink_correct id hinv
  have hlen : (heapSink id s.active i).length = s.length := by
    rw [hs.2]
    exact hc.2.2.trans (arrayListRel_length ⟨hs.1, hs.2⟩).symm
  refine ⟨arlWithActive_wf hs.1 hlen, ?_⟩
  rw [implHeapSink, arlWithActive_active hlen, hs.2]

theorem implHeapInsert?_refines {s t : ArrayList} {h : AbsHeap ℕ}
    {x : ℕ} (hs : (s, h) ∈ arrayListReadyRel)
    (hinv : heapInvariant id h) (ht : implHeapInsert? x s = some t) :
    (t, heapInsert id x h) ∈ arrayListRel := by
  simp only [implHeapInsert?] at ht
  cases ha : arlAppend s x with
  | none => simp [ha] at ht
  | some u =>
      simp only [ha, Option.bind_eq_bind, Option.bind_some] at ht
      have ht' : implHeapSwim u u.length = t := by simpa using ht
      subst t
      have hu : (u, heapAppend h x) ∈ arrayListRel :=
        arlAppend_some_refines hs.1 ha
      have hulen : u.length = h.length + 1 := by
        simpa [heapAppend] using arrayListRel_length hu
      have hw := implHeapSwim_refines hu
        (swimInvariant_append id hinv x)
      simpa [heapInsert, hulen] using hw

@[simp] theorem implHeapIsEmpty_refines {s : ArrayList} {h : AbsHeap ℕ}
    (hs : (s, h) ∈ arrayListRel) :
    implHeapIsEmpty s = propBool (h = []) := by
  simpa [implHeapIsEmpty] using arlIsEmpty_refines hs

theorem implHeapPeekMin?_refines {s : ArrayList} {h : AbsHeap ℕ}
    (hs : (s, h) ∈ arrayListRel) :
    implHeapPeekMin? s = heapPeekMin? h := by
  change arlGet? s 0 = h.head?
  rw [arlGet?_refines hs]
  cases h <;> rfl

theorem implHeapPopMin?_refines {s : ArrayList} {h : AbsHeap ℕ}
    (hs : (s, h) ∈ arrayListRel) (hinv : heapInvariant id h)
    (hne : h ≠ []) :
    ∃ x h' t, implHeapPopMin? s = some (x, t) ∧
      heapPopMin? id h = some (x, h') ∧ (t, h') ∈ arrayListRel := by
  classical
  obtain ⟨x, h', hpop, h'inv, hx, hbag, hmin⟩ :=
    heapPopMin?_correct id hinv hne
  have hslen : s.length = h.length := arrayListRel_length hs
  have hsne : s.length ≠ 0 := by
    rw [hslen]
    simpa using hne
  obtain ⟨u, hu⟩ : ∃ u, arlButlast? s = some u := by
    simp [arlButlast?, hsne]
  have hurel : (u, listButlast h) ∈ arrayListRel :=
    arlButlast?_some_refines hs hu
  have hxmem : x ∈ (h : Multiset ℕ) := hx
  have hh'len : h'.length = h.length - 1 := by
    change Multiset.card (h' : Multiset ℕ) =
      Multiset.card (h : Multiset ℕ) - 1
    rw [hbag]
    simpa [msetErase] using
      (@Multiset.card_erase_of_mem ℕ (Classical.decEq ℕ)
        x (h : Multiset ℕ) hxmem)
  have hulen : h'.length = u.length := by
    rw [hh'len, arrayListRel_length hurel]
    simp [listButlast]
  let t := arlWithActive u h'
  have ht : (t, h') ∈ arrayListRel := by
    exact ⟨arlWithActive_wf hurel.1 hulen,
      arlWithActive_active hulen⟩
  refine ⟨x, h', t, ?_, hpop, ht⟩
  simp [implHeapPopMin?, hs.2, hpop, hu, t]

/-! ## Synthesized primitive IR seams

These are the source locale's `update_impl`, `val_of_impl`, `exch_impl`,
`valid_impl`, and identity-priority `prio_of_impl`.  The metadata cells are
returned unchanged by destructive operations.  Each budget is obtained by
expanding the monadic primitive sequence that synthesis turns into the pinned
command immediately below it. -/

noncomputable def implHeapUpdateRaw (buffer : List ℕ) (n cap i v : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopBinop .sub i 1) fun k => arlSetRaw buffer n cap k v

noncomputable def implHeapValueRaw (buffer : List ℕ) (i : ℕ) :
    NRest ℕ ECost :=
  NRest.bindT (mopBinop .sub i 1) fun k => arlGetRaw buffer k

noncomputable def implHeapExchangeRaw (buffer : List ℕ) (n cap i j : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopBinop .sub i 1) fun k =>
  NRest.bindT (mopBinop .sub j 1) fun l => arlSwapRaw buffer n cap k l

noncomputable def implHeapValidRaw (n i : ℕ) : NRest ℕ ECost :=
  irIf (decide (0 < i))
    (irIf (decide (n < i)) (mopConstN 0) (mopConstN 1))
    (mopConstN 0)

noncomputable def implHeapPrioRaw (buffer : List ℕ) (i : ℕ) :
    NRest ℕ ECost := implHeapValueRaw buffer i

noncomputable def implHeapUpdateCost : ECost :=
  irUnit Currency.sub + arlSetCost

noncomputable def implHeapValueCost : ECost :=
  irUnit Currency.sub + arlGetCost

noncomputable def implHeapExchangeCost : ECost :=
  2 • irUnit Currency.sub + arlSwapCost

noncomputable def implHeapValidCost (i : ℕ) : ECost :=
  (if 0 < i then 2 else 1) • irUnit Currency.ite + irUnit Currency.const

noncomputable def implHeapUpdateExecSpec (buffer : List ℕ) (n cap i v : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer.set (i - 1) v, (n, cap)))
    implHeapUpdateCost

noncomputable def implHeapValueExecSpec (buffer : List ℕ) (i : ℕ) :
    NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[i - 1]!) implHeapValueCost

noncomputable def implHeapExchangeExecSpec (buffer : List ℕ)
    (n cap i j : ℕ) : NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume
    (NRest.returnT
      ((buffer.set (i - 1) buffer[j - 1]!).set (j - 1) buffer[i - 1]!,
        (n, cap))) implHeapExchangeCost

noncomputable def implHeapValidExecSpec (n i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (if 0 < i ∧ i ≤ n then 1 else 0))
    (implHeapValidCost i)

theorem implHeapUpdateRaw_eq (buffer : List ℕ) (n cap i v : ℕ)
    (hi : i - 1 < buffer.length) :
    implHeapUpdateRaw buffer n cap i v =
      implHeapUpdateExecSpec buffer n cap i v := by
  simp [implHeapUpdateRaw, implHeapUpdateExecSpec, implHeapUpdateCost,
    mopBinop_def, arlSetRaw_eq buffer n cap (i - 1) v hi,
    NRest.consume_consume, bindT_unit]

theorem implHeapValueRaw_eq (buffer : List ℕ) (i : ℕ)
    (hi : i - 1 < buffer.length) :
    implHeapValueRaw buffer i = implHeapValueExecSpec buffer i := by
  simp [implHeapValueRaw, implHeapValueExecSpec, implHeapValueCost,
    mopBinop_def, arlGetRaw_eq buffer (i - 1) hi,
    NRest.consume_consume, bindT_unit]

theorem implHeapExchangeRaw_eq (buffer : List ℕ) (n cap i j : ℕ)
    (hi : i - 1 < buffer.length) (hj : j - 1 < buffer.length) :
    implHeapExchangeRaw buffer n cap i j =
      implHeapExchangeExecSpec buffer n cap i j := by
  simp [implHeapExchangeRaw, implHeapExchangeExecSpec, implHeapExchangeCost,
    mopBinop_def, arlSwapRaw_eq buffer n cap (i - 1) (j - 1) hi hj,
    NRest.consume_consume, bindT_unit, two_smul, add_assoc]

theorem implHeapValidRaw_eq (n i : ℕ) :
    implHeapValidRaw n i = implHeapValidExecSpec n i := by
  by_cases hi0 : 0 < i
  · by_cases hin : n < i
    · have hnle : ¬ i ≤ n := by omega
      simp [implHeapValidRaw, implHeapValidExecSpec, implHeapValidCost,
        hi0, hin, hnle, irIf_true, mopConstN, NRest.consume_consume,
        two_smul, add_assoc]
    · have hle : i ≤ n := by omega
      simp [implHeapValidRaw, implHeapValidExecSpec, implHeapValidCost,
        hi0, hin, hle, irIf_true, irIf_false, mopConstN,
        NRest.consume_consume, two_smul, add_assoc]
  · simp [implHeapValidRaw, implHeapValidExecSpec, implHeapValidCost,
      hi0, irIf_false, mopConstN, NRest.consume_consume]

sepref_synth implHeapUpdateSynth
    (A len cap idx value one k : String) (buffer : List ℕ) (n c i v : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn v value ∗ hnCtxt natAssn 1 one ∗ junkCell k)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapUpdateRaw buffer n c i v)

sepref_synth implHeapValueSynth
    (A idx one k out : String) (buffer : List ℕ) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 1 one ∗ junkCell k ∗ junkCell out)
    _ _ out natAssn (implHeapValueRaw buffer i)

sepref_synth implHeapExchangeSynth
    (A len cap I J one K L XI XJ : String)
    (buffer : List ℕ) (n c i j : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
      hnCtxt natAssn 1 one ∗ junkCell K ∗ junkCell L ∗
      junkCell XI ∗ junkCell XJ)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapExchangeRaw buffer n c i j)

sepref_synth implHeapValidSynth (len idx out : String) (n i : ℕ) :
  hnRefine (hnCtxt natAssn n len ∗ hnCtxt natAssn i idx ∗ junkCell out)
    _ _ out natAssn (implHeapValidRaw n i)

def implHeapUpdateCom (A idx value one k : String) : Com :=
  .seq (.binop .sub k idx one) (arlSetCom A "len" "cap" k value)

def implHeapValueCom (A idx one k out : String) : Com :=
  .seq (.binop .sub k idx one) (.aget out A k)

def implHeapExchangeCom (A I J one K L XI XJ : String) : Com :=
  .seq (.binop .sub K I one)
    (.seq (.binop .sub L J one) (arlSwapCom A "len" "cap" K L XI XJ))

def implHeapValidCom (len idx out : String) : Com :=
  .ite (.lt (.lit 0) (.cell idx))
    (.ite (.lt (.cell len) (.cell idx)) (.const out 0) (.const out 1))
    (.const out 0)

@[sepref_fr_rules] theorem implHeapUpdate_exec_hnr
    (A len cap idx value one k : String) (buffer : List ℕ) (n c i v : ℕ)
    (hi : i - 1 < buffer.length) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn v value ∗ hnCtxt natAssn 1 one ∗ junkCell k)
    (implHeapUpdateCom A idx value one k)
      (junkCell k ∗ hnCtxt natAssn v value ∗ hnCtxt natAssn i idx ∗
        hnCtxt natAssn 1 one)
      (A, (len, cap))
      (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (implHeapUpdateExecSpec buffer n c i v) := by
  rw [← implHeapUpdateRaw_eq buffer n c i v hi]
  simpa [implHeapUpdateCom, arlSetCom] using
    implHeapUpdateSynth A len cap idx value one k buffer n c i v

@[sepref_fr_rules] theorem implHeapValue_exec_hnr
    (A idx one k out : String) (buffer : List ℕ) (i : ℕ)
    (hi : i - 1 < buffer.length) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 1 one ∗ junkCell k ∗ junkCell out)
    (implHeapValueCom A idx one k out)
      (hnCtxt arrayAssn buffer A ∗ junkCell k ∗ hnCtxt natAssn i idx ∗
        hnCtxt natAssn 1 one)
      out natAssn
      (implHeapValueExecSpec buffer i) := by
  rw [← implHeapValueRaw_eq buffer i hi]
  simpa [implHeapValueCom] using
    implHeapValueSynth A idx one k out buffer i

@[sepref_fr_rules] theorem implHeapExchange_exec_hnr
    (A len cap I J one K L XI XJ : String)
    (buffer : List ℕ) (n c i j : ℕ)
    (hi : i - 1 < buffer.length) (hj : j - 1 < buffer.length) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
      hnCtxt natAssn 1 one ∗ junkCell K ∗ junkCell L ∗
      junkCell XI ∗ junkCell XJ)
    (implHeapExchangeCom A I J one K L XI XJ)
      (junkCell L ∗ junkCell XI ∗ junkCell K ∗ junkCell XJ ∗
        hnCtxt natAssn j J ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn i I)
      (A, (len, cap))
      (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (implHeapExchangeExecSpec buffer n c i j) := by
  rw [← implHeapExchangeRaw_eq buffer n c i j hi hj]
  simpa [implHeapExchangeCom, arlSwapCom] using
    implHeapExchangeSynth A len cap I J one K L XI XJ buffer n c i j

@[sepref_fr_rules] theorem implHeapValid_exec_hnr
    (len idx out : String) (n i : ℕ) :
  hnRefine (hnCtxt natAssn n len ∗ hnCtxt natAssn i idx ∗ junkCell out)
    (implHeapValidCom len idx out)
      ((□ : Assn) ∗ hnCtxt natAssn n len ∗ hnCtxt natAssn i idx)
      out natAssn (implHeapValidExecSpec n i) := by
  rw [← implHeapValidRaw_eq n i]
  simpa [implHeapValidCom] using
    implHeapValidSynth len idx out n i

theorem implHeapPrioRaw_eq (buffer : List ℕ) (i : ℕ) :
    implHeapPrioRaw buffer i = implHeapValueRaw buffer i := rfl

@[sepref_fr_rules] theorem implHeapPrio_exec_hnr
    (A idx one k out : String) (buffer : List ℕ) (i : ℕ)
    (hi : i - 1 < buffer.length) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 1 one ∗ junkCell k ∗ junkCell out)
    (implHeapValueCom A idx one k out)
    (hnCtxt arrayAssn buffer A ∗ junkCell k ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 1 one)
    out natAssn (implHeapValueExecSpec buffer i) :=
  implHeapValue_exec_hnr A idx one k out buffer i hi

/-! ## Source-shaped swim and sink IR loops -/

structure ImplSwimStats where
  swaps : ℕ
  stoppedOnOrder : Bool
  deriving DecidableEq, Repr

def implSwimStatsFuel : ℕ → AbsHeap ℕ → ℕ → ImplSwimStats
  | 0, _, _ => ⟨0, false⟩
  | fuel + 1, h, i =>
      if 0 < heapParent i ∧ heapParent i ≤ h.length then
        if heapValue h (heapParent i) ≤ heapValue h i then ⟨0, true⟩
        else
          let r := implSwimStatsFuel fuel
            (heapExchange h i (heapParent i)) (heapParent i)
          ⟨r.swaps + 1, r.stoppedOnOrder⟩
      else ⟨0, false⟩

def implSwimStats (h : AbsHeap ℕ) (i : ℕ) : ImplSwimStats :=
  implSwimStatsFuel i h i

structure ImplSinkStats where
  swaps : ℕ
  rightChildren : ℕ
  stoppedOnOrder : Bool
  deriving DecidableEq, Repr

def implSinkStatsFuel : ℕ → AbsHeap ℕ → ℕ → ImplSinkStats
  | 0, _, _ => ⟨0, 0, false⟩
  | fuel + 1, h, i =>
      match heapSinkChild? id h i with
      | none => ⟨0, 0, false⟩
      | some j =>
          let hasRight :=
            if 0 < heapRight i ∧ heapRight i ≤ h.length then 1 else 0
          if heapValue h j < heapValue h i then
            let r := implSinkStatsFuel fuel (heapExchange h i j) j
            ⟨r.swaps + 1, r.rightChildren + hasRight, r.stoppedOnOrder⟩
          else ⟨0, hasRight, true⟩

def implSinkStats (h : AbsHeap ℕ) (i : ℕ) : ImplSinkStats :=
  implSinkStatsFuel (h.length + 1) h i

noncomputable def implHeapSwimCost (h : AbsHeap ℕ) (i : ℕ) : ECost :=
  let s := implSwimStats h i
  let stops := if s.stoppedOnOrder then 1 else 0
  let iterations := s.swaps + stops
  irUnit Currency.div +
    (iterations + 1) • irUnit Currency.«while» +
    iterations • (2 • irUnit Currency.sub + 2 • irUnit Currency.aget +
      irUnit Currency.ite) +
    s.swaps • (2 • irUnit Currency.aset + 2 • irUnit Currency.div) +
    stops • irUnit Currency.mul

noncomputable def implHeapSinkCost (h : AbsHeap ℕ) (i : ℕ) : ECost :=
  let s := implSinkStats h i
  let stops := if s.stoppedOnOrder then 1 else 0
  let iterations := s.swaps + stops
  irUnit Currency.div + 2 • irUnit Currency.add +
    (iterations + 1) • irUnit Currency.«while» +
    iterations • (irUnit Currency.mul + irUnit Currency.add +
      2 • irUnit Currency.ite + irUnit Currency.copy +
      2 • irUnit Currency.sub + 2 • irUnit Currency.aget) +
    s.rightChildren • (2 • irUnit Currency.sub +
      2 • irUnit Currency.aget + irUnit Currency.ite) +
    s.swaps • (2 • irUnit Currency.aset + irUnit Currency.mul +
      irUnit Currency.add) +
    stops • (irUnit Currency.mul + irUnit Currency.add)

/-- The generated shape of source `swim_impl`: `parent := i/2`, then one
guard evaluation per recursive level.  `parent := 0` represents the source
RECT return without changing the heap. -/
def implHeapSwimSourceCom (A idx parent two one I P XI XP : String) : Com :=
  .seq (.binop .div parent idx two)
    (.while (.lt (.lit 0) (.cell parent))
      (.seq (.binop .sub I idx one)
        (.seq (.binop .sub P parent one)
          (.seq (.aget XI A I)
            (.seq (.aget XP A P)
              (.ite (.lt (.cell XI) (.cell XP))
                (.seq (.aset A I XP)
                  (.seq (.aset A P XI)
                    (.seq (.copy idx parent)
                      (.binop .div parent idx two))))
                (.const parent 0)))))))

/-- The generated shape of optimized source `sink_impl`.  `bound = n/2`
makes the guard overflow-safe; the right child is chosen only when strictly
smaller, so ties go left exactly as in the Isabelle equation. -/
def implHeapSinkSourceCom (A len idx bound bound1 len1 two one left right child
    L R C I XL XR XC XI : String) : Com :=
  .seq (.binop .div bound len two)
    (.seq (.binop .add bound1 bound one)
      (.seq (.binop .add len1 len one)
        (.while (.lt (.cell idx) (.cell bound1))
          (.seq (.binop .mul left idx two)
            (.seq (.binop .add right left one)
              (.seq
                (.ite (.lt (.cell right) (.cell len1))
                  (.seq (.binop .sub L left one)
                    (.seq (.binop .sub R right one)
                      (.seq (.aget XL A L)
                        (.seq (.aget XR A R)
                          (.ite (.lt (.cell XR) (.cell XL))
                            (.copy child right) (.copy child left))))))
                  (.copy child left))
                (.seq (.binop .sub C child one)
                  (.seq (.binop .sub I idx one)
                    (.seq (.aget XC A C)
                      (.seq (.aget XI A I)
                        (.ite (.lt (.cell XC) (.cell XI))
                          (.seq (.aset A I XC)
                            (.seq (.aset A C XI) (.copy idx child)))
                          (.copy idx bound1))))))))))))

/-! The executable specifications below are deliberately the operational
`irWhileIT` programs themselves.  Thus the registered `hnRefine` rules prove
the command's actual branch-sensitive execution and price; the closed forms
`implHeapSwimCost` and `implHeapSinkCost` above remain useful semantic
accounting functions, but are not silently substituted for an unproved loop
execution theorem. -/

abbrev ImplSwimLoopState := List ℕ × ℕ × ℕ

def implHeapSwimLoopInv (_ : ImplSwimLoopState) : Prop := True

def implHeapSwimLoopGuard (s : ImplSwimLoopState) : Bool := decide (0 < s.2.2)

noncomputable def implHeapSwimMove (buffer : List ℕ)
    (I P XI XP idx parent : ℕ) : NRest ImplSwimLoopState ECost :=
  NRest.bindT (mopAset buffer I XP) fun h1 =>
  NRest.bindT (mopAset h1 P XI) fun h2 =>
  NRest.bindT (mopBinop .div idx 2) fun idx' =>
  NRest.bindT (mopBinop .div parent 2) fun parent' =>
  NRest.bindT (mopPair idx' parent') fun q => mopPair h2 q

set_option maxHeartbeats 500000 in
sepref_synth implHeapSwimMoveExec
    (A I P XI XP idx parent two : String)
    (buffer : List ℕ) (ii pp xi xp ix par : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn ii I ∗
      hnCtxt natAssn pp P ∗ hnCtxt natAssn xi XI ∗ hnCtxt natAssn xp XP ∗
      hnCtxt natAssn ix idx ∗ hnCtxt natAssn par parent ∗
      hnCtxt natAssn 2 two)
    _ _ (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimMove buffer ii pp xi xp ix par)

attribute [sepref_fr_rules] implHeapSwimMoveExec

noncomputable def implHeapSwimStop (buffer : List ℕ) (idx parent : ℕ) :
    NRest ImplSwimLoopState ECost :=
  NRest.bindT (mopBinop .mul parent 0) fun parent' =>
  NRest.bindT (mopPair idx parent') fun q => mopPair buffer q

set_option maxHeartbeats 300000 in
sepref_synth implHeapSwimStopExec
    (A idx parent zero : String) (buffer : List ℕ) (i p : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn p parent ∗ hnCtxt natAssn 0 zero)
    _ _ (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimStop buffer i p)

attribute [sepref_fr_rules] implHeapSwimStopExec

def implHeapSwimMoveCom (A I P XI XP idx parent two : String) : Com :=
  .seq (.aset A I XP)
    (.seq (.aset A P XI)
      (.seq (.binop .div idx idx two)
        (.seq (.binop .div parent parent two) (.seq .skip .skip))))

set_option linter.unusedVariables false in
def implHeapSwimStopCom (A idx parent zero : String) : Com :=
  .seq (.binop .mul parent parent zero) (.seq .skip .skip)

noncomputable def implHeapSwimLoopBody
    (s : ImplSwimLoopState) : NRest ImplSwimLoopState ECost :=
  NRest.bindT (mopBinop .sub s.2.1 1) fun I =>
  NRest.bindT (mopBinop .sub s.2.2 1) fun P =>
  NRest.bindT (mopAget s.1 I) fun XI =>
  NRest.bindT (mopAget s.1 P) fun XP =>
  irIf (decide (XI < XP))
    (implHeapSwimMove s.1 I P XI XP s.2.1 s.2.2)
    (implHeapSwimStop s.1 s.2.1 s.2.2)

noncomputable def implHeapSwimLoopSpec (buffer : List ℕ) (i parent : ℕ) :
    NRest ImplSwimLoopState ECost :=
  irWhileIT implHeapSwimLoopInv implHeapSwimLoopGuard
    implHeapSwimLoopBody (buffer, i, parent)

set_option maxHeartbeats 500000 in
set_option linter.unusedVariables false in
sepref_synth implHeapSwimBodyExec
    (A idx parent two one zero I P XI XP : String)
    (buffer : List ℕ) (i p : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (buffer, i, p) (A, idx, parent) ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero ∗
      junkCell I ∗ junkCell P ∗ junkCell XI ∗ junkCell XP)
    _ _ (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimLoopBody (buffer, i, p))

def implHeapSwimBodyCom (A idx parent two one zero I P XI XP : String) : Com :=
  .seq (.binop .sub I idx one)
    (.seq (.binop .sub P parent one)
      (.seq (.aget XI A I)
        (.seq (.aget XP A P)
          (.ite (.lt (.cell XI) (.cell XP))
            (implHeapSwimMoveCom A I P XI XP idx parent two)
            (implHeapSwimStopCom A idx parent zero)))))

theorem implHeapSwimBody_exec_hnr
    (A idx parent two one zero I P XI XP : String)
    (buffer : List ℕ) (i p : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (buffer, i, p) (A, idx, parent) ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero ∗ junkCell I ∗ junkCell P ∗
      junkCell XI ∗ junkCell XP)
    (implHeapSwimBodyCom A idx parent two one zero I P XI XP)
    (hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
      junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero)
    (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimLoopBody (buffer, i, p)) := by
  simpa only [implHeapSwimBodyCom, implHeapSwimMoveCom,
    implHeapSwimStopCom] using
    implHeapSwimBodyExec A idx parent two one zero I P XI XP buffer i p

def implHeapSwimLoopCom (A idx parent two one zero I P XI XP : String) : Com :=
  .while (.lt (.lit 0) (.cell parent))
    (implHeapSwimBodyCom A idx parent two one zero I P XI XP)

@[sepref_fr_rules] theorem implHeapSwimLoop_exec_hnr
    (A idx parent two one zero I P XI XP : String)
    (buffer : List ℕ) (i p : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn p parent ∗ hnCtxt natAssn 2 two ∗ junkCell P ∗
      junkCell XI ∗ junkCell I ∗ junkCell XP ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero)
    (implHeapSwimLoopCom A idx parent two one zero I P XI XP)
    (hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
      junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero)
    (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimLoopSpec buffer i p) := by
  unfold implHeapSwimLoopCom implHeapSwimLoopSpec
  apply hnRefine_pre_perm
    (P := hnCtxt (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (buffer, i, p) (A, idx, parent) ∗
      (hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
        junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
        hnCtxt natAssn 0 zero)) (by
    simp only [hnCtxt_def, prodAssn]
    ac_rfl)
  apply hnr_while
  · rintro ⟨buf, ii, pp⟩ _
    simp only [implHeapSwimLoopGuard]
    have h := condRefine_lt_lit_cell 0 pp parent
    have e :
        (hnCtxt (arrayAssn ×ₐ natAssn ×ₐ natAssn)
            (buf, ii, pp) (A, idx, parent) ∗
          (hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
            junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
            hnCtxt natAssn 0 zero)) =
        hnCtxt natAssn pp parent ∗
          (hnCtxt arrayAssn buf A ∗ hnCtxt natAssn ii idx ∗
            hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
            junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
            hnCtxt natAssn 0 zero) := by
      simp only [hnCtxt_def, prodAssn]
      ac_rfl
    rw [e]
    exact h.frame
  · rintro ⟨buf, ii, pp⟩ _ _
    exact hnRefine_pre_perm (by ac_rfl)
      (implHeapSwimBody_exec_hnr A idx parent two one zero I P XI XP
        buf ii pp)

noncomputable def implHeapSwimExecSpec (s : ArrayList) (i : ℕ) :
    NRest ImplSwimLoopState ECost :=
  NRest.bindT (mopBinop .div i 2) fun parent =>
    implHeapSwimLoopSpec s.buffer i parent

def implHeapSwimInitCom (idx parent two : String) : Com :=
  .binop .div parent idx two

theorem implHeapSwimInit_exec_hnr
    (A idx parent two one zero I P XI XP : String)
    (s : ArrayList) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero ∗ junkCell parent ∗
      junkCell I ∗ junkCell P ∗ junkCell XI ∗ junkCell XP)
    (implHeapSwimInitCom idx parent two)
    ((hnCtxt natAssn i idx ∗ hnCtxt natAssn 2 two) ∗
      (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn 1 one ∗
        hnCtxt natAssn 0 zero ∗ junkCell I ∗ junkCell P ∗
        junkCell XI ∗ junkCell XP))
    parent natAssn (mopBinop .div i 2) := by
  apply hnRefine_frame_perm
    (P := junkCell parent ∗ hnCtxt natAssn i idx ∗ hnCtxt natAssn 2 two)
    (F := hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero ∗ junkCell I ∗ junkCell P ∗
      junkCell XI ∗ junkCell XP)
  · ac_rfl
  · simpa only [implHeapSwimInitCom] using
      hnr_mop_binop .div parent idx two i 2

def implHeapSwimCom (A idx parent two one zero I P XI XP : String) : Com :=
  .seq (implHeapSwimInitCom idx parent two)
    (implHeapSwimLoopCom A idx parent two one zero I P XI XP)

@[sepref_fr_rules] theorem implHeapSwim_exec_hnr
    (A idx parent two one zero I P XI XP : String)
    (s : ArrayList) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero ∗ junkCell parent ∗ junkCell I ∗
      junkCell P ∗ junkCell XI ∗ junkCell XP)
    (implHeapSwimCom A idx parent two one zero I P XI XP)
    (hnCtxt natAssn 2 two ∗ junkCell P ∗ junkCell XI ∗
      junkCell I ∗ junkCell XP ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero)
    (A, idx, parent) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapSwimExecSpec s i) := by
  unfold implHeapSwimExecSpec implHeapSwimCom
  apply hnr_seq
    (implHeapSwimInit_exec_hnr A idx parent two one zero I P XI XP s i)
  intro p _
  exact hnRefine_pre_perm (by ac_rfl)
    (implHeapSwimLoop_exec_hnr A idx parent two one zero I P XI XP
      s.buffer i p)

abbrev ImplSinkLoopState := List ℕ × ℕ

def implHeapSinkLoopInv (_ : ImplSinkLoopState) : Prop := True

def implHeapSinkLoopGuard (bound1 : ℕ) (s : ImplSinkLoopState) : Bool :=
  decide (s.2 < bound1)

noncomputable def implHeapSinkChooseChild
    (buffer : List ℕ) (left right len1 : ℕ) : NRest ℕ ECost :=
  irIf (decide (right < len1))
    (NRest.bindT (mopBinop .sub left 1) fun L =>
     NRest.bindT (mopBinop .sub right 1) fun R =>
     NRest.bindT (mopAget buffer L) fun XL =>
     NRest.bindT (mopAget buffer R) fun XR =>
     irIf (decide (XR < XL)) (mopCopy right) (mopCopy left))
    (mopCopy left)

set_option maxHeartbeats 1000000 in
sepref_synth implHeapSinkChooseExec
    (A left right len1 one child L R XL XR : String)
    (buffer : List ℕ) (l r l1 : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn l left ∗
      hnCtxt natAssn r right ∗ hnCtxt natAssn l1 len1 ∗
      hnCtxt natAssn 1 one ∗ junkCell child ∗ junkCell L ∗ junkCell R ∗
      junkCell XL ∗ junkCell XR)
    _ _ child natAssn (implHeapSinkChooseChild buffer l r l1)

attribute [sepref_fr_rules] implHeapSinkChooseExec

noncomputable def implHeapSinkMove (buffer : List ℕ)
    (I C XI XC idx child : ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mopAset buffer I XC) fun h1 =>
  NRest.bindT (mopAset h1 C XI) fun h2 =>
  NRest.bindT (mopBinop .mul idx 0) fun idx0 =>
  NRest.bindT (mopBinop .add idx0 child) fun idx' => mopPair h2 idx'

set_option maxHeartbeats 500000 in
sepref_synth implHeapSinkMoveExec
    (A I C XI XC idx child zero : String)
    (buffer : List ℕ) (ii cc xi xc ix ch : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn ii I ∗
      hnCtxt natAssn cc C ∗ hnCtxt natAssn xi XI ∗ hnCtxt natAssn xc XC ∗
      hnCtxt natAssn ix idx ∗ hnCtxt natAssn ch child ∗
      hnCtxt natAssn 0 zero)
    _ _ (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkMove buffer ii cc xi xc ix ch)

attribute [sepref_fr_rules] implHeapSinkMoveExec

noncomputable def implHeapSinkStop (buffer : List ℕ) (idx bound1 : ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mopBinop .mul idx 0) fun idx0 =>
  NRest.bindT (mopBinop .add idx0 bound1) fun idx' => mopPair buffer idx'

set_option maxHeartbeats 300000 in
sepref_synth implHeapSinkStopExec
    (A idx bound1 zero : String) (buffer : List ℕ) (i b1 : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn b1 bound1 ∗ hnCtxt natAssn 0 zero)
    _ _ (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkStop buffer i b1)

attribute [sepref_fr_rules] implHeapSinkStopExec

noncomputable def implHeapSinkRepair (buffer : List ℕ)
    (idx child bound1 : ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mopBinop .sub child 1) fun C =>
  NRest.bindT (mopBinop .sub idx 1) fun I =>
  NRest.bindT (mopAget buffer C) fun XC =>
  NRest.bindT (mopAget buffer I) fun XI =>
  irIf (decide (XC < XI))
    (implHeapSinkMove buffer I C XI XC idx child)
    (implHeapSinkStop buffer idx bound1)

set_option maxHeartbeats 1000000 in
sepref_synth implHeapSinkRepairExec
    (A idx child bound1 one zero C I XC XI : String)
    (buffer : List ℕ) (i ch b1 : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      hnCtxt natAssn ch child ∗ hnCtxt natAssn b1 bound1 ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero ∗ junkCell C ∗ junkCell I ∗ junkCell XC ∗
      junkCell XI)
    _ _ (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkRepair buffer i ch b1)

attribute [sepref_fr_rules] implHeapSinkRepairExec

noncomputable def implHeapSinkLoopBody
    (bound1 len1 : ℕ) (s : ImplSinkLoopState) : NRest ImplSinkLoopState ECost :=
  NRest.bindT (mopBinop .mul s.2 2) fun left =>
  NRest.bindT (mopBinop .add left 1) fun right =>
  NRest.bindT (implHeapSinkChooseChild s.1 left right len1) fun child =>
  implHeapSinkRepair s.1 s.2 child bound1

noncomputable def implHeapSinkLoopSpec (buffer : List ℕ)
    (i bound1 len1 : ℕ) : NRest ImplSinkLoopState ECost :=
  irWhileIT implHeapSinkLoopInv (implHeapSinkLoopGuard bound1)
    (implHeapSinkLoopBody bound1 len1) (buffer, i)

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth implHeapSinkBodyExec
    (A idx bound1 len1 two one zero left right child
      L R C I XL XR XC XI : String)
    (buffer : List ℕ) (i b1 l1 : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (buffer, i) (A, idx) ∗
      hnCtxt natAssn b1 bound1 ∗ hnCtxt natAssn l1 len1 ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero ∗ junkCell left ∗ junkCell right ∗
      junkCell child ∗ junkCell L ∗ junkCell R ∗ junkCell C ∗
      junkCell I ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗ junkCell XI)
    _ _ (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkLoopBody b1 l1 (buffer, i))

set_option linter.unusedVariables false in
def implHeapSinkBodyCom (A idx bound1 len1 two one zero left right child
    L R C I XL XR XC XI : String) : Com :=
  .seq (.binop .mul left idx two)
    (.seq (.binop .add right left one)
      (.seq
        (.ite (.lt (.cell right) (.cell len1))
          (.seq (.binop .sub child left one)
            (.seq (.binop .sub L right one)
              (.seq (.aget R A child)
                (.seq (.aget C A L)
                  (.ite (.lt (.cell C) (.cell R))
                    (.copy I right) (.copy I left))))))
          (.copy I left))
        (.seq (.binop .sub C I one)
          (.seq (.binop .sub L idx one)
            (.seq (.aget R A C)
              (.seq (.aget child A L)
                (.ite (.lt (.cell R) (.cell child))
                  (.seq (.aset A L R)
                    (.seq (.aset A C child)
                      (.seq (.binop .mul idx idx zero)
                        (.seq (.binop .add idx idx I) .skip))))
                  (.seq (.binop .mul idx idx zero)
                    (.seq (.binop .add idx idx bound1) .skip)))))))))

def implHeapSinkLoopCom (A idx bound1 len1 two one zero left right child
    L R C I XL XR XC XI : String) : Com :=
  .while (.lt (.cell idx) (.cell bound1))
    (implHeapSinkBodyCom A idx bound1 len1 two one zero left right
      child L R C I XL XR XC XI)

@[sepref_fr_rules] theorem implHeapSinkLoop_exec_hnr
    (A idx bound1 len1 two one zero left right child
      L R C I XL XR XC XI : String)
    (buffer : List ℕ) (i b1 l1 : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗
      junkCell I ∗ hnCtxt natAssn 0 zero ∗ junkCell C ∗ junkCell child ∗
      junkCell L ∗ junkCell R ∗ hnCtxt natAssn 1 one ∗ junkCell right ∗
      junkCell left ∗ hnCtxt natAssn 2 two ∗ hnCtxt natAssn b1 bound1 ∗
      hnCtxt natAssn l1 len1 ∗ junkCell XL ∗ junkCell XR ∗
      junkCell XC ∗ junkCell XI)
    (implHeapSinkLoopCom A idx bound1 len1 two one zero left right
      child L R C I XL XR XC XI)
    (junkCell I ∗ hnCtxt natAssn 0 zero ∗ junkCell C ∗ junkCell child ∗
      junkCell L ∗ junkCell R ∗ hnCtxt natAssn 1 one ∗ junkCell right ∗
      junkCell left ∗ hnCtxt natAssn 2 two ∗ hnCtxt natAssn b1 bound1 ∗
      hnCtxt natAssn l1 len1 ∗ junkCell XL ∗ junkCell XR ∗
      junkCell XC ∗ junkCell XI)
    (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkLoopSpec buffer i b1 l1) := by
  unfold implHeapSinkLoopCom implHeapSinkLoopSpec
  apply hnRefine_pre_perm
    (P := hnCtxt (arrayAssn ×ₐ natAssn) (buffer, i) (A, idx) ∗
      (junkCell I ∗ hnCtxt natAssn 0 zero ∗ junkCell C ∗ junkCell child ∗
        junkCell L ∗ junkCell R ∗ hnCtxt natAssn 1 one ∗ junkCell right ∗
        junkCell left ∗ hnCtxt natAssn 2 two ∗ hnCtxt natAssn b1 bound1 ∗
        hnCtxt natAssn l1 len1 ∗ junkCell XL ∗ junkCell XR ∗
        junkCell XC ∗ junkCell XI))
    (by simp only [hnCtxt_def, prodAssn]; ac_rfl)
  apply hnr_while
  · rintro ⟨buf, ii⟩ _
    have h := condRefine_lt_cells ii b1 idx bound1
    have e :
        (hnCtxt (arrayAssn ×ₐ natAssn) (buf, ii) (A, idx) ∗
          (junkCell I ∗ hnCtxt natAssn 0 zero ∗ junkCell C ∗ junkCell child ∗
            junkCell L ∗ junkCell R ∗ hnCtxt natAssn 1 one ∗ junkCell right ∗
            junkCell left ∗ hnCtxt natAssn 2 two ∗ hnCtxt natAssn b1 bound1 ∗
            hnCtxt natAssn l1 len1 ∗ junkCell XL ∗ junkCell XR ∗
            junkCell XC ∗ junkCell XI)) =
        (hnCtxt natAssn ii idx ∗ hnCtxt natAssn b1 bound1) ∗
          (hnCtxt arrayAssn buf A ∗ hnCtxt natAssn l1 len1 ∗
            hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗
            hnCtxt natAssn 0 zero ∗ junkCell left ∗ junkCell right ∗
            junkCell child ∗ junkCell L ∗ junkCell R ∗ junkCell C ∗
            junkCell I ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗ junkCell XI) := by
      simp only [hnCtxt_def, prodAssn]
      ac_rfl
    rw [e]
    exact h.frame
  · rintro ⟨buf, ii⟩ _ _
    exact hnRefine_pre_perm
      (P := hnCtxt (arrayAssn ×ₐ natAssn) (buf, ii) (A, idx) ∗
        hnCtxt natAssn b1 bound1 ∗ hnCtxt natAssn l1 len1 ∗
        hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗
        hnCtxt natAssn 0 zero ∗ junkCell left ∗ junkCell right ∗
        junkCell child ∗ junkCell L ∗ junkCell R ∗ junkCell C ∗
        junkCell I ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗
        junkCell XI)
      (by simp only [hnCtxt_def, prodAssn]; ac_rfl)
      (by simpa only [implHeapSinkBodyCom] using
        (implHeapSinkBodyExec A idx bound1 len1 two one zero left right child
          L R C I XL XR XC XI buf ii b1 l1))

noncomputable def implHeapSinkExecSpec (s : ArrayList) (i : ℕ) :
    NRest ImplSinkLoopState ECost :=
  NRest.bindT (mopBinop .div s.length 2) fun bound =>
  NRest.bindT (mopBinop .add bound 1) fun bound1 =>
  NRest.bindT (mopBinop .add s.length 1) fun len1 =>
    implHeapSinkLoopSpec s.buffer i bound1 len1

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
sepref_synth implHeapSinkExec
    (A len idx bound bound1 len1 two one zero left right child
      L R C I XL XR XC XI : String)
    (s : ArrayList) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn i idx ∗ hnCtxt natAssn 2 two ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero ∗
      junkCell bound ∗ junkCell bound1 ∗ junkCell len1 ∗ junkCell left ∗
      junkCell right ∗ junkCell child ∗ junkCell L ∗ junkCell R ∗
      junkCell C ∗ junkCell I ∗ junkCell XL ∗ junkCell XR ∗
      junkCell XC ∗ junkCell XI)
    _ _ (A, idx) (arrayAssn ×ₐ natAssn)
    (implHeapSinkExecSpec s i)

def implHeapSinkCom (A len idx bound bound1 len1 two one zero left right child
    L R C I XL XR XC XI : String) : Com :=
  .seq (.binop .div bound len two)
    (.seq (.binop .add bound1 bound one)
      (.seq (.binop .add len1 len one)
        (implHeapSinkLoopCom A idx bound1 len1 two one zero I C child
          L R right left XL XR XC XI)))

@[sepref_fr_rules] theorem implHeapSink_exec_hnr
    (A len idx bound bound1 len1 two one zero left right child
      L R C I XL XR XC XI : String) (s : ArrayList) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn i idx ∗ hnCtxt natAssn 2 two ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 0 zero ∗ junkCell bound ∗
      junkCell bound1 ∗ junkCell len1 ∗ junkCell left ∗ junkCell right ∗
      junkCell child ∗ junkCell L ∗ junkCell R ∗ junkCell C ∗
      junkCell I ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗ junkCell XI)
    (implHeapSinkCom A len idx bound bound1 len1 two one zero left right
      child L R C I XL XR XC XI)
    (junkCell left ∗ hnCtxt natAssn 0 zero ∗ junkCell right ∗
      junkCell child ∗ junkCell L ∗ junkCell R ∗
      hnCtxt natAssn 1 one ∗ junkCell C ∗ junkCell I ∗
      hnCtxt natAssn 2 two ∗ junkCell bound1 ∗ junkCell len1 ∗
      junkCell XL ∗ junkCell XR ∗ junkCell XC ∗ junkCell XI ∗
      hnCtxt natAssn s.length len ∗ junkCell bound)
    (A, idx) (arrayAssn ×ₐ natAssn) (implHeapSinkExecSpec s i) := by
  simpa only [implHeapSinkCom] using
    implHeapSinkExec A len idx bound bound1 len1 two one zero left right
      child L R C I XL XR XC XI s i

/-! ## Public command shapes and executable boundaries -/

def implHeapIsEmptyCom (len out : String) : Com := arlIsEmptyCom len out

def implHeapPeekMinCom (A one idx out : String) : Com :=
  implHeapValueCom A one one idx out

set_option linter.unusedVariables false in
def implHeapInsertCom
    (A len cap phys value one two zero outLen outCap ok doubled
      idx parent I P XI XP : String) : Com :=
  .seq (boundedExecCom A len cap phys value one two outLen outCap ok doubled)
    (.seq (.copy doubled outLen)
      (.seq (implHeapSwimCom A doubled idx two one zero P parent I XI)
        (.seq .skip .skip)))

set_option linter.unusedVariables false in
def implHeapPopMinCom
    (A len cap lastIdx one oneIdx two four zero root I J XI XJ outCap
      fourN twoN bound bound1 len1 left right child L R C XL XR XC
      sinkIdx : String) : Com :=
  .seq (arlLastCom A one oneIdx I root)
    (.seq (implHeapExchangeCom A one lastIdx oneIdx I J XI XJ)
      (.seq (arlButlastCom A len cap oneIdx four two J XI I)
        (.seq
          (.seq (.binop .div J len two)
            (.seq (.binop .add XI J oneIdx)
              (.seq (.binop .add XJ len oneIdx)
                (implHeapSinkLoopCom A oneIdx XI XJ two one zero left len1
                  twoN bound bound1 fourN outCap right child L R))))
          (.seq .skip (.seq .skip .skip)))))

noncomputable def implHeapIsEmptyExecSpec (s : ArrayList) : NRest ℕ ECost :=
  arlIsEmptyExecSpec s.length

noncomputable def implHeapPeekMinExecSpec (s : ArrayList) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT s.buffer[0]!) implHeapValueCost

noncomputable def implHeapInsertCost? (x : ℕ) (s : ArrayList) : Option ECost := do
  let t ← boundedPush s x
  let c ← boundedPushCostN s
  pure (c.toECost + implHeapSwimCost t.active t.length)

noncomputable def implHeapInsertExecSpec (x : ℕ) (s : ArrayList) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (boundedExecSpec s x) fun raw =>
  let t : ArrayList :=
    ⟨raw.2.1, raw.2.2.1, raw.2.2.2.1⟩
  NRest.bindT (mopCopy t.length) fun idx =>
  NRest.bindT (implHeapSwimExecSpec t idx) fun moved =>
  NRest.bindT (mopPair t.length t.capacity) fun md =>
    mopPair moved.1 md

noncomputable def implHeapPopMinCost (s : ArrayList) : ECost :=
  let exchanged := heapExchange s.active 1 s.length
  let moved := heapButlast exchanged
  implHeapValueCost + implHeapExchangeCost +
    arlButlastCost s.length s.capacity + implHeapSinkCost moved 1

noncomputable def implHeapPopMinExecSpec (s : ArrayList) :
    NRest (ℕ × (List ℕ × (ℕ × ℕ))) ECost :=
  NRest.bindT (implHeapValueExecSpec s.buffer 1) fun root =>
  NRest.bindT
      (implHeapExchangeExecSpec s.buffer s.length s.capacity 1 s.length)
      fun exchanged =>
  NRest.bindT
      (arlButlastExecSpec exchanged.1 exchanged.2.1 exchanged.2.2)
      fun shrunk =>
  let t : ArrayList := ⟨shrunk.1, shrunk.2.1, shrunk.2.2⟩
  NRest.bindT (implHeapSinkExecSpec t 1) fun moved =>
  NRest.bindT (mopPair t.length t.capacity) fun md =>
  NRest.bindT (mopPair moved.1 md) fun heap =>
    mopPair root heap

attribute [-sepref_fr_rules] arlAppend_exec_hnr

@[sepref_fr_rules] theorem implHeapAppendRaw_exec_hnr
    (s : ArrayList) (x : ℕ) (hwf : s.Wf)
    (A len cap phys value one two outLen outCap ok doubled : String) :
  hnRefine
    (junkCell outLen ∗ junkCell outCap ∗ junkCell ok ∗ junkCell doubled ∗
      hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗
      hnCtxt natAssn s.buffer.length phys ∗ hnCtxt natAssn x value ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 2 two)
    (boundedExecCom A len cap phys value one two outLen outCap ok doubled)
    (junkCell doubled ∗ hnCtxt natAssn s.capacity cap ∗
      hnCtxt natAssn s.length len ∗ hnCtxt natAssn x value ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 2 two)
    (ok, (A, (outLen, (outCap, phys))))
      (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ (natAssn ×ₐ natAssn))))
    (boundedExecSpec s x) := by
  simpa only [boundedExecPre, boundedExecPost] using
    arlAppend_exec_hnr s x hwf A len cap phys value one two outLen outCap ok doubled

set_option maxHeartbeats 3000000 in
set_option linter.unusedVariables false in
sepref_synth implHeapInsertExec
    (A len cap phys value one two zero outLen outCap ok doubled idx parent
      I P XI XP : String) (s : ArrayList) (x : ℕ) (hwf : s.Wf) :
  hnRefine
    (junkCell outLen ∗ junkCell outCap ∗ junkCell ok ∗ junkCell doubled ∗
      hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗
      hnCtxt natAssn s.buffer.length phys ∗ hnCtxt natAssn x value ∗
      hnCtxt natAssn 1 one ∗ hnCtxt natAssn 2 two ∗ junkCell idx ∗
      hnCtxt natAssn 0 zero ∗ junkCell parent ∗ junkCell I ∗
      junkCell P ∗ junkCell XI ∗ junkCell XP)
    _ _ (A, outLen, outCap) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapInsertExecSpec x s)

@[sepref_fr_rules] theorem implHeapInsert_exec_hnr
    (A len cap phys value one two zero outLen outCap ok doubled idx parent
      I P XI XP : String) (s : ArrayList) (x : ℕ) (hwf : s.Wf)
    (_hready : boundedPush s 0 ≠ none) :
  hnRefine
    (junkCell outLen ∗ junkCell outCap ∗ junkCell ok ∗ junkCell doubled ∗
      hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗ hnCtxt natAssn s.buffer.length phys ∗
      hnCtxt natAssn x value ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 2 two ∗ junkCell idx ∗ hnCtxt natAssn 0 zero ∗
      junkCell parent ∗ junkCell I ∗ junkCell P ∗ junkCell XI ∗
      junkCell XP)
    (implHeapInsertCom A len cap phys value one two zero outLen outCap ok
      doubled idx parent I P XI XP)
    (hnCtxt natAssn 2 two ∗ junkCell parent ∗ junkCell I ∗
      junkCell P ∗ junkCell XI ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn 0 zero ∗ junkCell ok ∗ junkCell phys ∗
      hnCtxt natAssn s.capacity cap ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn x value ∗ junkCell XP ∗ junkCell doubled ∗
      junkCell idx)
    (A, outLen, outCap) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (implHeapInsertExecSpec x s) := by
  simpa only [implHeapInsertCom, implHeapSwimCom, implHeapSwimInitCom] using
    implHeapInsertExec A len cap phys value one two zero outLen outCap ok
      doubled idx parent I P XI XP s x hwf

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
set_option linter.unusedVariables false in
sepref_synth implHeapPopMinExec
    (A len cap lastIdx one oneIdx two four zero root I J XI XJ outCap fourN twoN
      bound bound1 len1 left right child L R C XL XR XC sinkIdx : String)
    (s : ArrayList) (hwf : s.Wf)
    (hget : 1 - 1 < s.buffer.length)
    (hlast : s.length - 1 < s.buffer.length) :
  hnRefine
    (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn s.length lastIdx ∗ hnCtxt natAssn 1 oneIdx ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 0 zero ∗ junkCell I ∗ junkCell root ∗
      junkCell J ∗ junkCell XI ∗ junkCell XJ ∗ junkCell outCap ∗
      junkCell fourN ∗ junkCell twoN ∗ junkCell bound ∗
      junkCell bound1 ∗ junkCell len1 ∗ junkCell left ∗
      junkCell right ∗ junkCell child ∗ junkCell L ∗ junkCell R ∗
      junkCell C ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗
      junkCell sinkIdx)
    _ _ (root, (A, (len, I)))
      (natAssn ×ₐ (arrayAssn ×ₐ natAssn ×ₐ natAssn))
    (implHeapPopMinExecSpec s)

set_option linter.unusedVariables false in
@[sepref_fr_rules] theorem implHeapPopMin_exec_hnr
    (A len cap lastIdx one oneIdx two four zero root I J XI XJ outCap
      fourN twoN bound bound1 len1 left right child L R C XL XR XC
      sinkIdx : String) (s : ArrayList) (hwf : s.Wf)
    (hne : s.length ≠ 0) :
  hnRefine
    (hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn s.length lastIdx ∗ hnCtxt natAssn 1 oneIdx ∗
      hnCtxt natAssn 2 two ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 0 zero ∗ junkCell I ∗ junkCell root ∗
      junkCell J ∗ junkCell XI ∗ junkCell XJ ∗ junkCell outCap ∗
      junkCell fourN ∗ junkCell twoN ∗ junkCell bound ∗
      junkCell bound1 ∗ junkCell len1 ∗ junkCell left ∗
      junkCell right ∗ junkCell child ∗ junkCell L ∗ junkCell R ∗
      junkCell C ∗ junkCell XL ∗ junkCell XR ∗ junkCell XC ∗
      junkCell sinkIdx)
    (implHeapPopMinCom A len cap lastIdx one oneIdx two four zero root I J
      XI XJ outCap fourN twoN bound bound1 len1 left right child L R C XL
      XR XC sinkIdx)
    (junkCell outCap ∗ hnCtxt natAssn 0 zero ∗ junkCell fourN ∗
      junkCell twoN ∗ junkCell bound ∗ junkCell bound1 ∗
      hnCtxt natAssn 1 one ∗ junkCell len1 ∗ junkCell left ∗
      hnCtxt natAssn 2 two ∗ junkCell XI ∗ junkCell XJ ∗
      junkCell right ∗ junkCell child ∗ junkCell L ∗ junkCell R ∗
      junkCell J ∗ junkCell cap ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn s.length lastIdx ∗ junkCell C ∗ junkCell XL ∗
      junkCell XR ∗ junkCell XC ∗ junkCell sinkIdx ∗ junkCell oneIdx)
    (root, (A, (len, I)))
      (natAssn ×ₐ (arrayAssn ×ₐ natAssn ×ₐ natAssn))
    (implHeapPopMinExecSpec s) := by
  have hget : 1 - 1 < s.buffer.length := by
    rcases hwf with ⟨_, hlen, hcap⟩
    omega
  have hlast : s.length - 1 < s.buffer.length := by
    rcases hwf with ⟨_, hlen, hcap⟩
    omega
  simpa only [implHeapPopMinCom] using
    implHeapPopMinExec A len cap lastIdx one oneIdx two four zero root I J
      XI XJ outCap fourN twoN bound bound1 len1 left right child L R C XL
      XR XC sinkIdx s hwf hget hlast

@[sepref_fr_rules] theorem implHeapIsEmpty_exec_hnr
    (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (implHeapIsEmptyCom len out) ((□ : Assn) ∗ hnCtxt natAssn n len)
      out natAssn (arlIsEmptyExecSpec n) := by
  simpa [implHeapIsEmptyCom] using arlIsEmpty_exec_hnr len out n

def implHeapPeekRawCom (A zero out : String) : Com := .aget out A zero

@[sepref_fr_rules] theorem implHeapPeek_exec_hnr
    (A zero out : String) (buffer : List ℕ) (hbuf : buffer ≠ []) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn 0 zero ∗ junkCell out)
      (implHeapPeekRawCom A zero out)
      (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn 0 zero)
      out natAssn
      (NRest.consume (NRest.returnT buffer[0]!) arlGetCost) := by
  have hzero : 0 < buffer.length := by
    cases buffer with
    | nil => contradiction
    | cons x xs => simp
  simpa [implHeapPeekRawCom, arlGetCom, arlGetExecSpec] using
    arlGet_exec_hnr A zero out buffer 0 hzero

/-! `implHeapEmptyModel` has no command/spec pair: source `empty_impl`
allocates an array.  Insert has an executable command only together with the
existing branch-sensitive `boundedExecSpec`; it is not assigned a fake
constant price.  Pop similarly composes `arlButlastCost` with the exact sink
trace, so its price is state/path dependent. -/

/-! ## Public semantic operations -/

noncomputable def implHeapEmptyOp : NRest ArrayList ECost :=
  NRest.returnT implHeapEmptyModel

noncomputable def implHeapIsEmptyOp (s : ArrayList) : NRest Bool ECost :=
  NRest.returnT (implHeapIsEmpty s)

noncomputable def implHeapInsertOp (x : ℕ) (s : ArrayList) : NRest ArrayList ECost :=
  match implHeapInsert? x s with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def implHeapPeekMinOp (s : ArrayList) : NRest ℕ ECost :=
  match implHeapPeekMin? s with
  | some x => NRest.returnT x
  | none => NRest.fail

noncomputable def implHeapPopMinOp (s : ArrayList) : NRest (ℕ × ArrayList) ECost :=
  match implHeapPopMin? s with
  | some p => NRest.returnT p
  | none => NRest.fail

private theorem returnT_le_spec_zero {α : Type} {x : α} {P : α → Prop}
    (hP : P x) :
    (NRest.returnT x : NRest α ECost) ≤ NRest.spec P (fun _ => 0) := by
  rw [NRest.returnT, NRest.spec]
  refine NRest.rest_le_rest_iff.mpr fun y => ?_
  by_cases hy : y = x
  · subst y
    simp [hP]
  · simp [NRest.single_of_ne hy]

theorem implHeapEmptyOp_refines :
    (implHeapEmptyOp, op_mset_empty ℕ) ∈ NRest.nrestRel implHeapRel := by
  apply NRest.param_returnT
  apply mem_implHeapRel_iff.mpr
  exact ⟨[], arlEmptyModel_refines, heapInvariant_nil id, rfl⟩

@[sepref_fref_thms] theorem implHeapIsEmptyOp_refines :
    (implHeapIsEmptyOp, op_mset_is_empty ℕ) ∈
      fref (fun _ : Multiset ℕ => True) implHeapRel
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) := by
  intro s m _ hsm
  obtain ⟨h, hs, hinv, hm⟩ := mem_implHeapRel_iff.mp hsm
  unfold implHeapIsEmptyOp op_mset_is_empty
  apply NRest.param_returnT
  change implHeapIsEmpty s = propBool (msetIsEmpty m)
  rw [implHeapIsEmpty_refines hs]
  apply propBool_congr
  apply propext
  change h = [] ↔ m = 0
  rw [← hm]
  simp

@[sepref_fref_thms] theorem implHeapInsertOp_refines :
    (implHeapInsertOp, op_mset_insert ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => fref (fun _ : Multiset ℕ => True) implHeapReadyRel
          (fun _ => NRest.nrestRel implHeapRel)) := by
  intro x y _ hxy s m _ hsm
  change x = y at hxy
  subst y
  obtain ⟨h, hs, hinv, hm⟩ := mem_implHeapReadyRel_iff.mp hsm
  have hsome : ∃ t, implHeapInsert? x s = some t := by
    have hready : arlAppend s x ≠ none := by
      intro hnone
      have hf := (arlAppend_failure_iff hs.1.1).mp hnone
      have hzero : arlAppend s 0 = none :=
        (arlAppend_failure_iff hs.1.1).mpr hf
      exact hs.2 hzero
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hready
    exact ⟨implHeapSwim u u.length, by simp [implHeapInsert?, hu]⟩
  obtain ⟨t, ht⟩ := hsome
  simp [implHeapInsertOp, ht, op_mset_insert]
  apply NRest.param_returnT
  apply mem_implHeapRel_iff.mpr
  refine ⟨heapInsert id x h, implHeapInsert?_refines hs hinv ht,
    heapInsert_invariant id x h hinv, ?_⟩
  rw [heapInsert_bag id x h hinv, hm]

@[sepref_fref_thms] theorem implHeapPeekMinOp_refines :
    (implHeapPeekMinOp, op_prio_peek_min ℕ ℕ id) ∈
      fref (fun _ : Multiset ℕ => True) implHeapRel
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s m _ hsm
  obtain ⟨h, hs, hinv, hm⟩ := mem_implHeapRel_iff.mp hsm
  cases h with
  | nil =>
      have hm0 : m = 0 := by simpa using hm.symm
      rw [fold_op_prio_peek_min]
      simp [implHeapPeekMinOp, implHeapPeekMin?, arlGet?_refines hs,
        prioPeekMin, hm0]
  | cons x xs =>
      have hmne : m ≠ 0 := by rw [← hm]; simp
      have hpeek : implHeapPeekMin? s = some x := by
        rw [implHeapPeekMin?_refines hs]
        rfl
      have hpost : x ∈ m ∧ ∀ y ∈ m, id x ≤ id y := by
        constructor
        · rw [← hm]
          simp
        · intro y hy
          have hy' : y ∈ (x :: xs) := by
            rw [← hm] at hy
            simpa using hy
          simpa [heapValue] using heap_min_mem id hinv hy'
      rw [fold_op_prio_peek_min]
      unfold implHeapPeekMinOp
      simp only [hpeek]
      apply NRest.nrestRel_of_le
      refine (NRest.returnT_refine (R := Set.diagonal ℕ) rfl).trans ?_
      apply NRest.concFun_mono
      simp only [prioPeekMin, NRest.assert_pos hmne, NRest.returnT_bindT]
      exact returnT_le_spec_zero hpost

@[sepref_fref_thms] theorem implHeapPopMinOp_refines :
    (implHeapPopMinOp, op_prio_pop_min ℕ ℕ id) ∈
      fref (fun _ : Multiset ℕ => True) implHeapRel
        (fun _ => NRest.nrestRel (Set.diagonal ℕ ×ᵣ implHeapRel)) := by
  intro s m _ hsm
  obtain ⟨h, hs, hinv, hm⟩ := mem_implHeapRel_iff.mp hsm
  cases h with
  | nil =>
      have hm0 : m = 0 := by simpa using hm.symm
      have hsactive : s.active = [] := hs.2
      rw [fold_op_prio_pop_min]
      simp [implHeapPopMinOp, implHeapPopMin?, hsactive, prioPopMin, hm0]
  | cons x xs =>
      have hne : x :: xs ≠ [] := by simp
      obtain ⟨y, h', t, hpopImpl, hpop, ht⟩ :=
        implHeapPopMin?_refines hs hinv hne
      have hxx : y = x := by
        have hp := Option.some.inj hpop
        exact (congrArg Prod.fst hp).symm
      subst y
      obtain ⟨z, k, hzk, hkinv, hzmem, hkbag, hzmin⟩ :=
        heapPopMin?_correct id hinv hne
      have hzx : z = x := by
        have hp := Option.some.inj (hpop.symm.trans hzk)
        exact (congrArg Prod.fst hp).symm
      subst z
      have hkh' : k = h' := by
        have hp := Option.some.inj (hpop.symm.trans hzk)
        exact (congrArg Prod.snd hp).symm
      subst k
      have hmne : m ≠ 0 := by rw [← hm]; simp
      have htrel : (t, msetErase m x) ∈ implHeapRel := by
        apply mem_implHeapRel_iff.mpr
        exact ⟨h', ht, hkinv, by simpa [hm] using hkbag⟩
      have hpost : x ∈ m ∧ msetErase m x = msetErase m x ∧
          ∀ y ∈ m, id x ≤ id y := by
        refine ⟨by simpa [hm] using hzmem, rfl, ?_⟩
        intro y hy
        apply hzmin y
        simpa [hm] using hy
      rw [fold_op_prio_pop_min]
      unfold implHeapPopMinOp
      simp only [hpopImpl]
      apply NRest.nrestRel_of_le
      refine (NRest.returnT_refine
        (R := Set.diagonal ℕ ×ᵣ implHeapRel)
        (show ((x, t), (x, msetErase m x)) ∈
          Set.diagonal ℕ ×ᵣ implHeapRel from ⟨rfl, htrel⟩)).trans ?_
      apply NRest.concFun_mono
      simp only [prioPopMin, NRest.assert_pos hmne, NRest.returnT_bindT]
      exact returnT_le_spec_zero hpost

/-! ## Regression, accounting, and registration gates -/

#guard (implHeapSwim
    ⟨[1, 2, 3, 0, 9, 9, 9, 9], 4, 8⟩ 4).active = [0, 1, 3, 2]
#guard (implHeapSink
    ⟨[8, 2, 3, 4, 5, 9, 9, 9], 5, 8⟩ 1).active = [2, 4, 3, 8, 5]
#guard implSwimStats [1, 2, 3, 0] 4 = ⟨2, false⟩
#guard implSwimStats [1, 2, 3, 4] 4 = ⟨0, true⟩
#guard implSinkStats [8, 2, 3, 4, 5] 1 = ⟨2, 2, false⟩
#guard implSinkStats [1, 2, 3] 1 = ⟨0, 1, true⟩

#guard implHeapUpdateCom "A" "idx" "value" "one" "k" =
  (Com.binop .sub "k" "idx" "one").seq
    ((Com.aset "A" "k" "value").seq (Com.skip.seq Com.skip))
#guard implHeapValueCom "A" "idx" "one" "k" "out" =
  (Com.binop .sub "k" "idx" "one").seq (Com.aget "out" "A" "k")
#guard implHeapExchangeCom "A" "I" "J" "one" "K" "L" "XI" "XJ" =
  (Com.binop .sub "K" "I" "one").seq
    ((Com.binop .sub "L" "J" "one").seq
      ((Com.aget "XI" "A" "K").seq
        ((Com.aget "XJ" "A" "L").seq
          ((Com.aset "A" "K" "XJ").seq
            ((Com.aset "A" "L" "XI").seq (Com.skip.seq Com.skip))))))
#guard implHeapValidCom "len" "idx" "out" =
  Com.ite (Cond.lt (.lit 0) (.cell "idx"))
    (Com.ite (Cond.lt (.cell "len") (.cell "idx"))
      (Com.const "out" 0) (Com.const "out" 1))
    (Com.const "out" 0)

theorem implHeapSwimCost_while :
    (implHeapSwimCost [1, 2, 3, 0] 4).toFun Currency.«while» = 3 := by
  decide +kernel

theorem implHeapSwimCost_aset :
    (implHeapSwimCost [1, 2, 3, 0] 4).toFun Currency.aset = 4 := by
  decide +kernel

theorem implHeapSwimCost_div :
    (implHeapSwimCost [1, 2, 3, 0] 4).toFun Currency.div = 5 := by
  decide +kernel

theorem implHeapSinkCost_while :
    (implHeapSinkCost [8, 2, 3, 4, 5] 1).toFun Currency.«while» = 3 := by
  decide +kernel

theorem implHeapSinkCost_ite :
    (implHeapSinkCost [8, 2, 3, 4, 5] 1).toFun Currency.ite = 6 := by
  decide +kernel

theorem implHeapSinkCost_aget :
    (implHeapSinkCost [8, 2, 3, 4, 5] 1).toFun Currency.aget = 8 := by
  decide +kernel

theorem implHeapSinkCost_add :
    (implHeapSinkCost [8, 2, 3, 4, 5] 1).toFun Currency.add = 6 := by
  decide +kernel

run_cmd do
  let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
  for n in #[``implHeapRel, ``implHeapAssn, ``implHeapUpdate?,
      ``implHeapValue?, ``implHeapExchange?, ``implHeapValid,
      ``implHeapPrio?, ``implHeapSwim, ``implHeapSink,
      ``implHeapEmptyOp_refines, ``implHeapIsEmptyOp_refines,
      ``implHeapInsertOp_refines, ``implHeapPopMinOp_refines,
      ``implHeapPeekMinOp_refines, ``implHeapUpdate_exec_hnr,
      ``implHeapValue_exec_hnr, ``implHeapExchange_exec_hnr,
      ``implHeapValid_exec_hnr, ``implHeapPrio_exec_hnr,
      ``implHeapSwimCom, ``implHeapSwim_exec_hnr,
      ``implHeapSinkCom, ``implHeapSink_exec_hnr,
      ``implHeapInsertCom, ``implHeapInsert_exec_hnr,
      ``implHeapPopMinCom, ``implHeapPopMin_exec_hnr] do
    unless env.contains n do
      throwError "impl-heap source gate: missing declaration {n}"

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``implHeapIsEmptyOp_refines, ``implHeapInsertOp_refines,
      ``implHeapPopMinOp_refines, ``implHeapPeekMinOp_refines] do
    unless frefs.contains n do
      throwError "impl-heap fref gate: missing rule {n}"
  let frs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``implHeapUpdate_exec_hnr, ``implHeapValue_exec_hnr,
      ``implHeapExchange_exec_hnr, ``implHeapValid_exec_hnr,
      ``implHeapPrio_exec_hnr, ``implHeapIsEmpty_exec_hnr,
      ``implHeapPeek_exec_hnr, ``implHeapSwim_exec_hnr,
      ``implHeapSink_exec_hnr, ``implHeapInsert_exec_hnr,
      ``implHeapPopMin_exec_hnr] do
    unless frs.contains n do
      throwError "impl-heap executable gate: missing rule {n}"

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapInsertOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapInsertOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapUpdate_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapUpdate_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapSwim_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapSwim_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapSink_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapSink_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapInsert_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapInsert_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapPopMin_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapPopMin_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.implHeapPopMinOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implHeapPopMinOp_refines

end Lax13Proofs.Refine.Sepref.Iicf
