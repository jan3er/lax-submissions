import Lax3Proofs.Refine.ScatterSynth
import Lax3Proofs.Refine.AugmentSynth

/-!
# T1 acceptance — 2A gap 3 (the `fri` bound-tuple split), on the real
engine composition

The 2A satellite's probe 2: bind the search leaf (`mopBfs`, the whole
synthesized BFS as one `sepref_fr_rules` operation), then run the
marking sweep over the DISTANCE ARRAY THE SEARCH PRODUCED — the sweep's
frame and body want `arrayAssn st.1 "dist"` as its own conjunct while
the leaf's postcondition owns the whole four-tuple
`hnCtxt (arrayAssn ×ₐ …) st ("dist","q","head","tl")`.

Before T1/D-b the loop-exit entailment stalled in `fri` ("no premise
conjunct matches the target conjunct"); with the pair equations in
`fri_prepare_simps` both spellings normalize and the composition
synthesizes. The loop is written as an explicit `irWhileIT` (not behind
`markLoop`'s def) because a *named* wrapper is an operator-phase
question — R2A/D-f — not a frame-layer one; this file is the
frame-layer acceptance.
-/

namespace Lax3Proofs.Refine.T1FriProbe

open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine NRest Ir
open Lax3Proofs.Refine.ScatterSynth

set_option maxHeartbeats 2000000 in
sepref_synth bfsThenSweep (n d src rp1 : ℕ) (off tgt alv dist₀ q₀ exc₀ : List ℕ) :
  hnRefine
    (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (exc₀, 0) ("exc", "sw") ∗
      hnCtxt natAssn rp1 "mkr" ∗
      junkCell "mke" ∗ junkCell "mkd" ∗ junkCell "mka" ∗ junkCell "mkb" ∗
      junkCell "mkc" ∗ junkCell "mkp" ∗ junkCell "mkm")
    _ _ ("exc", "sw") (arrayAssn ×ₐ natAssn)
    (NRest.bindT (mopBfs n d src off tgt alv dist₀ q₀) fun st =>
      irWhileIT (fun s => markBf n s = true → markP n st.1 s) (markBf n)
        (markF rp1 st.1) (exc₀, 0))

#print axioms bfsThenSweep

/-! ## The 2C minimal instance (coordinator's F2): two ordinary loops,
no engine leaf — `cntPass`, then the prefix pass over the array the
count produced. The 2C satellite's spelling
`prefLoop n (r.1, ofl₀, 0)` writes the start state as a LITERAL tuple,
which no conjunct owns — the sanctioned idiom is the pack (`packOF`,
the `mopPair` chain), after which the loop rule sees its state whole.
With T1's fixes the composition synthesizes; the literal-tuple
spelling remains unsupported by design (a loop state is a resource and
must be assembled — that is P4/D-m's linearity, not a gap). -/

set_option maxHeartbeats 2000000 in
sepref_synth cntThenPref (n : ℕ) (doff dtg ooff₀ ofl₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (ooff₀, 0) ("ooff", "agi") ∗
      hnCtxt arrayAssn doff "doff" ∗ hnCtxt arrayAssn dtg "dtg" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "agjo" ∗ junkCell "agip" ∗ junkCell "agend" ∗
      junkCell "agu" ∗ junkCell "agup" ∗ junkCell "agc" ∗
      hnCtxt arrayAssn ofl₀ "ofl" ∗ hnCtxt natAssn 0 "pfi" ∗
      junkCell "pfip" ∗ junkCell "pfb" ∗ junkCell "pfa" ∗ junkCell "pft")
    _ _ ("ooff", ("ofl", "pfi")) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (NRest.bindT (AugmentSynth.cntPass n doff dtg (ooff₀, 0)) fun r =>
      NRest.bindT (AugmentSynth.packOF r.1 ofl₀ 0) fun z =>
        AugmentSynth.prefLoop n z)

#print axioms cntThenPref

end Lax3Proofs.Refine.T1FriProbe
