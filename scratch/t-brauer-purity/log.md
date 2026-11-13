# t-brauer-purity results log

Start 2026-11-12 22:54 PST, fresh run (no earlier log). Base 01267822.

## Environment facts (VERIFIED by grep)
- Mathlib v4.35 has `IsRegularLocalRing` (RingTheory/RegularLocalRing/Defs.lean), `Algebra.QuasiFiniteAt`
  (RingTheory/QuasiFinite/Basic.lean:368), `Algebra.IsEtaleAt` (= FormallyEtale R S_q, Etale/Locus.lean:35),
  `Algebra.IsUnramifiedAt` (Unramified/Locus.lean:47), `Ideal.ramificationIdx` (length of S_q/pS_q,
  RingTheory/RamificationInertia/Ramification.lean:53).
- Mathlib v4.35 has no purity of the branch locus, no Abhyankar lemma, no tame-ramification notion,
  no Brauer group of a local or global field beyond the definition, no comparison of
  `continuousCohomology` with cochains (grep for abhyankar/purity/tamely: no hits in RingTheory).
- No Tau Ceti or Stacks-formalization sources on this host (searched ~/*, ~/*/*), and no network:
  no bridge from those libraries can be compiled here.
- `ZMod N` carries the discrete topology (Topology/Instances/ZMod.lean:24), so `IsCocycle2`'s
  continuity is the genuine condition (local constancy).
- Glue use of T15: `leafLocalTwo_of_T15` (ZInQKernel/HDecomp/Descent/WP3.lean:231) uses only
  `(hC.1 p).2` (the finite-place uniqueness half); the real half and existence are unused.

## Lean
- `LocalH2Real.lean` (Mathlib only, definitions copied verbatim from I6Base): COMPILES, no sorry,
  axioms [propext, Classical.choice, Quot.sound]. `h2TwoClasses_of_card_two` (any discrete group of
  order 2), `card_absoluteGaloisGroup_real : Nat.card G_ℝ = 2`, `h2TwoClasses_real`.
- `LocalH2RealKernel.lean` (imports ZInQKernel.HDecomp.Conductor.I6Base; kernel definitions, nothing
  copied): COMPILES, standard axioms. `TBrauerPurityK.h2TwoClasses_real :
  PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℝ)`, `TBrauerPurityK.localH2CardC_iff :
  PkgI6.LocalH2CardC ↔ ∀ p [Fact p.Prime], PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])`.
- `KummerEtale.lean` (Mathlib only): COMPILES, standard axioms.
  `etale_adjoinRoot_X_pow_sub_C : 0 < e → IsUnit (e : A) → IsUnit u → Algebra.Etale A (AdjoinRoot (X^e - C u))`
  (standard étale pair (Xᵉ-u, 1)); an ingredient of Abhyankar (T2), not T2 itself.
