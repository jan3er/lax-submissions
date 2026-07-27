import Lax14.MulticolorRamsey
import Lax14Proofs.PairRamsey

/-!
The multicolour Ramsey theorem for pairs, in the submitted form: the ported
list-indexed statement of `Lax14Proofs.PairRamsey`, specialized to a constant
list of sizes and transported from `Finset`/`Fintype.card` to `Set.ncard` over
the canonical carriers `Fin n`.
-/

namespace Lax14Proofs.MulticolorRamsey

/--
---
conclusion: Lax14.MulticolorRamsey.exists_monochromatic_set
---
Every colouring of the unordered pairs of a large enough finite set with `k`
colours admits a monochromatic subset of size `s`: the multicolour Ramsey
theorem for pairs, over the canonical carriers `Fin n` and with no hypothesis
on the number of colours.

# Proof strategy

The mathematical content is the ported `Lax14Proofs.PairRamsey.multicolor_ramsey`,
which asks for a *list* of requested sizes, one per colour, and produces a
`Finset` monochromatic in the colour whose entry it meets.  That statement is
proved by induction on the list of colours from the two-colour graph form
`Lax14Proofs.PairRamsey.ramsey` (Erdős–Szekeres neighbourhood splitting): the
first colour is turned into a graph, a clique in it is monochromatic of the
first colour, and an independent set carries a colouring by the remaining
colours to which the induction hypothesis applies.

The bridge to the submitted statement instantiates the list as
`List.replicate k s`, so that all colours request the same size `s`, and
transports along `List.length_replicate : (List.replicate k s).length = k`,
precomposing the given colouring with `Fin.cast` in one direction and casting
the returned colour index back in the other.  The carrier is `Fin n`, whose
`Fintype.card` is `n`, and the returned `Finset` is coerced to a `Set`, its
cardinality translated by `Set.ncard_coe_finset`.

The submitted statement carries no positivity hypothesis on the number of
colours, whereas the ported one needs a nonempty list.  The case `k = 0` is
therefore split off first and closed outright: with `N := 1` the carrier
`Fin n` is nonempty, so the assumed colouring produces an element of `Fin 0`,
which is absurd.

# Attribution

The proof is ported from the proof package of the submission
*Monadic dependence and neighborhood complexity* (`Lax5Proofs/Ramsey.lean`),
where it appears as Theorems 3.7 and 3.8 of the source lecture notes.  The
theorem is due to Ramsey, *On a problem of formal logic* (Proc. London Math.
Soc. 1930); the two-colour induction used here is the Erdős–Szekeres argument.
-/
theorem exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun n c hn => ?_⟩
    exact ((c s(⟨0, hn⟩, ⟨0, hn⟩)).elim0)
  · obtain ⟨N, hN⟩ := PairRamsey.multicolor_ramsey (List.replicate k s) (by
      simp [List.replicate_eq_nil_iff, hk.ne'])
    have hlen : (List.replicate k s).length = k := List.length_replicate
    refine ⟨N, fun n c hn => ?_⟩
    have hcard : N ≤ Fintype.card (Fin n) := by simpa using hn
    obtain ⟨i, S, hsize, hpair⟩ :=
      hN (V := Fin n) hcard (fun e => Fin.cast hlen.symm (c e))
    refine ⟨Fin.cast hlen i, (↑S : Set (Fin n)), ?_, ?_⟩
    · rw [Set.ncard_coe_finset]
      calc s = (List.replicate k s).get i := by simp
        _ ≤ S.card := hsize
    · intro u hu v hv huv
      have h := hpair hu hv huv
      simp only at h
      exact congrArg (Fin.cast hlen) h

end Lax14Proofs.MulticolorRamsey
