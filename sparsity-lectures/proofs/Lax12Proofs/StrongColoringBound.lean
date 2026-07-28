import Lax12.StrongColoringBound
import Lax12Proofs.OrderBridge
import Lax12Proofs.ScolByAdm

/-!
Lemma 2.5 of Chapter 2 of the notes, transported to the submitted
concepts: the strong coloring number is bounded by a power of the
admissibility.
-/

namespace Lax12Proofs.StrongColoringBound

open Lax12.Admissibility Lax12.ColoringNumbers
open Lax12Proofs.OrderBridge

/--
---
conclusion: Lax12.StrongColoringBound.scol_le_of_adm
---
The strong `r`-coloring number of a graph is at most
`1 + (adm_r - 1) ^ r`, where `adm_r` is its `r`-admissibility.

# Proof strategy

The ported development proves the inequality for a fixed linear order.
The submitted parameters are minima over vertex permutations, so it is
enough to run the ported bound under one well-chosen order: take a
permutation witnessing `adm G r`, order the vertices by their positions
under it, and observe two inclusions.  First, every admissible family of
paths in the ported sense is an admissible family of walks in the
submitted sense, so the ported admissibility under that order is at most
`adm G r`.  Second, every vertex strongly reachable in the submitted
sense is strongly reachable in the ported sense — a walk bypasses to a
path with a smaller support — so the submitted `scol`, being the minimum
over permutations, is at most the ported one.  The right-hand side is
monotone in the admissibility, which closes the chain.

# Attribution

The statement is Lemma 2.5 of Chapter 2 of the sparsity lecture notes of
Pilipczuk and Siebertz (numbering of the 2019/20 edition).  The proof is
a port of the formalization accompanying those notes, whose per-order
version is `Lax12Proofs.ScolByAdm.scol_le_one_add_adm_sub_one_pow`.
-/
theorem scol_le_of_adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    scol G r ≤ 1 + (adm G r - 1) ^ r := by
  classical
  obtain ⟨π, hπ⟩ : HasAdmAtMost G r (adm G r) :=
    Nat.sInf_mem (exists_adm_bound G r)
  letI := orderOfPerm π
  have h1 : Lax12Proofs.OrderedParameters.adm G r ≤ adm G r :=
    catalog_adm_le G r (adm G r) hπ
  have h2 : scol G r ≤ Lax12Proofs.OrderedParameters.scol G r :=
    scol_le_catalog (orderOfPerm π) G r
  have h3 : Lax12Proofs.OrderedParameters.scol G r ≤
      1 + (Lax12Proofs.OrderedParameters.adm G r - 1) ^ r :=
    Lax12Proofs.ScolByAdm.scol_le_one_add_adm_sub_one_pow G r
  have h4 : (Lax12Proofs.OrderedParameters.adm G r - 1) ^ r ≤ (adm G r - 1) ^ r :=
    Nat.pow_le_pow_left (Nat.sub_le_sub_right h1 1) r
  omega

end Lax12Proofs.StrongColoringBound
