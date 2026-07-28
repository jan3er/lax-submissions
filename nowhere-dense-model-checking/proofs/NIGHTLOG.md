
## ND-MC P2 session 1 — 2026-07-28
Gate cleared in-session: Jan endorsed the full Lax3 surface on the
orchestrator's review package; statements frozen at 514cc4c. P2
(locality engine) ran as three parallel Opus tracks over a
supervisor-written Horizon prelude (eq. (1), exact ρ⁺ = 9^k·ρ⁻,
monotonicity both ways and antidiagonal, strict chain). Landed,
sorry-free, kernel axioms propext/choice/Quot.sound only:
(a) SemLocal — Lem 5 as a strengthened agreement (Sat ↔ SatWithin D
for every D containing the ρ⁻-balls), arity-independent primed forms,
the source's k ≥ 1 dropped (sound under the frozen exL semantics,
argued in the module docstring); (b) Clusters + ScatterCore — Vitali/
Cor 10 packaged as a ClusterSystem structure with the exact scale
R = r·9^t, t < k (the finite radius range farQuant's case split
needs), and Lem 11 verbatim with the Maximal hypothesis in
ScatterChoice.spec's shape; the source's last-paragraph counting gap
closed via proper subset + ncard_lt_ncard, recorded in the module;
(c) SyntaxLemmas — Sat ↔ SatWithin univ, DRank mono_left/mono_right/
antidiagonal (Obs 4), scatter Obs 6, UsesOnly + congruence, rename
soundness. Headline finding of (c): unconditional rename and
environment-congruence are FALSE — the frozen exL guard reads the
whole context — proved as in-module counterexample theorems; the
repaired lemmas carry range-of-environment / guard-agreement
hypotheses. This is the source's silent guarded↔unrestricted
rewriting made explicit; the separation-lemma session must write out
the guards it means (exU + binary atoms), not lean on rename.
Process learnings: the lax namespace audit rejects proofs-side
declarations in concept namespaces AND concept definition names
passed to simp/rw (match splitters get recorded in the proofs
module); lake build alone does not catch either — always gate on lax
build. SyntaxLemmas' Unfolding section (rfl clause lemmas, local
simp) is the sanctioned way to take Sat/SatWithin/rename/IsLocal
apart. EnterWorktree based the worktree on a stale ref — reset to
main before seeding. Remaining P2: separate (Lem 8), farQuant
(Lem 12), locality + normalForm assembly, then the locality axiom
discharge.
