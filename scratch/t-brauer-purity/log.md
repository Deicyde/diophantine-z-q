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
- `AbhyankarBricks.lean` (Mathlib only, the instance context of `PkgI2.AbhyankarDVR` verbatim):
  COMPILES, standard axioms. `dvd_ramificationIdx_of_pow_eq` (general: DVR `R`, uniformizer `π`,
  Dedekind `S`, `tⁿ = π` in `S`, `𝔪S ≠ ⊥` ⇒ `n ∣ Q.ramificationIdx R` for `Q` over `𝔪`);
  `abhyankar_isScalarTower_RLM`, `abhyankar_finiteDimensional`, `abhyankar_isSeparable`,
  `abhyankar_isDedekindDomain` (M/K finite separable, `integralClosure R M` Dedekind);
  `abhyankar_dvd_ramificationIdx`: in the leaf's setting, `n ∣ e(Q|𝔪)` for every prime `Q` of
  `integralClosure R M` over `𝔪` (lower half of the conclusion; tameness hypothesis unused).
- `AbhyankarBricks.lean` extended: COMPILES, standard axioms.
  `finrank_le_of_pow_eq` ([K(t):K] ≤ m); `ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq`
  (DVR `R`, uniformizer `π`, `m` invertible, `M = K(t)`, `tᵐ = π` ⇒ every prime of
  `integralClosure R M` over `𝔪` has e = m, f = 1; via Mathlib's
  `Ideal.sum_ramification_inertia_eq_finrank` and `IsIntegralClosure.rank`);
  `abhyankarDVR_conclusion_of_L_eq_K`: the exact conclusion of `PkgI2.AbhyankarDVR` (e = n and
  separable residue extension, with the leaf's quotient-algebra instance) when `L = K`.
- `KummerUnramified.lean` (Mathlib only): COMPILES, standard axioms.
  `isUnramifiedAt_of_pow_eq`: `A` Dedekind with fraction field `K`, `L/K` finite separable, `B`
  Dedekind integral closure of `A` in `L` (finite, torsion-free), `w ∈ B` with `wᵉ = u ∈ A`,
  `e ≥ 1` invertible in `A`, `K[w] = L`: `A → B` is unramified at every prime `P` with `u ∉ P`
  (via `dvd_differentIdeal_iff`, `aeval_derivative_mem_differentIdeal`,
  `minpoly.isIntegrallyClosed_dvd`); `ramificationIdx_eq_one_of_pow_eq` (e(P) = 1).
  Step (b) of the T2 plan, in global Dedekind form.
- **`T2Full.lean` (Mathlib only; `PkgI2.AbhyankarDVR` copied verbatim from Leaves.lean): COMPILES,
  no sorry, axioms [propext, Classical.choice, Quot.sound]. `TBrauerPurity.abhyankarDVR :
  PkgI2.AbhyankarDVR.{u}` — leaf T2 PROVED.** Assembly `abhyankarDVR_main`: step (a)
  `exists_pow_mul_eq` (CRT-free: ϖ ∈ Q∖Q², (ϖ) = Q·J₂, b ∈ J₂ᵉ∖Q, b·π = ϖᵉ·a with a ∉ Q);
  `w = b tᵐ/ϖ`, `wᵉ = bᵉ⁻¹a`; `L₁ = L(w)`, `A₂ = integralClosure A₁ L₁`; `A₁ → A₂` unramified at
  `P = Q'∩A₂` (`isUnramifiedAt_of_pow_eq`); `e(Q'|P)·f(Q'|P) ≤ [M:L₁] ≤ m` (deprecated
  `Ideal.sum_ramification_inertia`); `n ∣ e(Q'|𝔪) = e·e(Q'|P)` (`Ideal.ramificationIdx_tower`
  twice, `ramificationIdx_eq_one`); residue separability via `dvd_differentIdeal_of_not_isSeparable`,
  f = 1, and transitivity.
- `T2Kernel.lean` (imports `ZInQKernel.HDecomp.Objects`; nothing copied but the proof):
  COMPILES, standard axioms. `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` (the
  kernel's definition) and `TBrauerPurityT2K.abhyankarDVR_objBridge : ObjBridge.AbhyankarDVR`.
