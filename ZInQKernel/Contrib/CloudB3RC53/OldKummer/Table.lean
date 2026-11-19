import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Two

/-!
# Old Kummer, part 6: the RC6 table function at the actual Kummer conditions

Manuscript `diophantine_zq.tex`, tex 4544–4573 (the table of local condition dimensions), with the
old-Kummer row taken from the actual Kummer condition (tex 3413–3438).

RC6's table function at the genuine objects is `GenuineInst.genCondDimFun2 K S cond kd` with the
old-Kummer dimension `kd = kummerDimOfCurves K Ew (kd2OfCurves K Ew)` (Mattuck's
`kummerResidualDim` of the local integral models `E_w` at every place). Here:

* `kummerDimOfCurves_kd2OfCurves`: this is `kummerResidualDim w (E_w)` at every place `w`;
* **`two_pow_kummerDimOfCurves_eq_actual`**: if `E_v` is a model of the actual local twist at
  `v ∈ S` with `E_v(K_v)/2` finite, `2^(kummerDimOfCurves … v) = |H⁰(U_v)| · |H¹(U_v)|` for RC29's
  actual Kummer condition `U_v` at `i = 1`;
* **`two_pow_genCondDimFun2_eq_actual`**: the same for the table entry
  `genCondDimFun2 K S cond kd v` at a place with `cond v = .oldKummer`;
* `two_pow_kummerDimOfCurves_eq_actual_odd`: at odd places with full rational `2`-torsion of
  `E_v`, without the finiteness hypothesis.

Non-vacuity: `kummerDimOfCurves_actual_nonvacuous` (over `ℚ` at `v₃`, models `E_w = W0`).

Scope: the table function itself is unchanged (`kd` is still a number); these lemmas identify
it, place by place, with the order of the actual condition's cohomology. They need the model
identification `hC` at each old-Kummer place — RC6's wiring takes the models `E_w` as arbitrary
and does not impose it — and they are at the residual level `i = 1` (see part 2, `Actual.lean`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

omit hEw in
open scoped Classical in
/-- At every place, `kummerDimOfCurves K Ew (kd2OfCurves K Ew)` is Mattuck's
`kummerResidualDim w (E_w)`. PROVED. -/
theorem kummerDimOfCurves_kd2OfCurves (w : HeightOneSpectrum (𝓞 K)) :
    kummerDimOfCurves K Ew (kd2OfCurves K Ew) w.asIdeal = kummerResidualDim w (Ew w) := by
  have h : w.asIdeal.IsPrime ∧ w.asIdeal ≠ ⊥ := ⟨w.isPrime, w.ne_bot⟩
  unfold kummerDimOfCurves
  rw [dite_eq_left_of_eq_true (eq_true h)]
  split_ifs
  · unfold kd2OfCurves
    rw [dite_eq_left_of_eq_true (eq_true h)]
  · rfl

variable {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef 1)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S W (2 ^ 1))

open scoped Classical in
/-- **The RC6 old-Kummer dimension is the dimension of the actual Kummer condition**: if `E_v` is
a model of the actual local twist at `v ∈ S` and `E_v(K_v)/2` is finite, then
`2^(kummerDimOfCurves K Ew (kd2OfCurves K Ew) v) = |H⁰(U_v)| · |H¹(U_v)|`. PROVED. -/
theorem two_pow_kummerDimOfCurves_eq_actual (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    (hC : (Ew v.1).baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    [Finite (ModN ((Ew v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2)] :
    2 ^ kummerDimOfCurves K Ew (kd2OfCurves K Ew) v.1.asIdeal =
      Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) := by
  rw [kummerDimOfCurves_kd2OfCurves,
    genCondDim2_oldKummer_actual W s hs hs0 α hFull v hα (Ew v.1) hC]
  rfl

open scoped Classical in
/-- **The RC6 table entry at an old-Kummer place is the dimension of the actual Kummer
condition**: `2^(genCondDimFun2 K S cond kd v) = |H⁰(U_v)| · |H¹(U_v)|` for
`kd = kummerDimOfCurves K Ew (kd2OfCurves K Ew)` and `cond v = .oldKummer`. PROVED. -/
theorem two_pow_genCondDimFun2_eq_actual (cond : Ideal (𝓞 K) → LocalCondition) (v : Places K S)
    (hcond : cond v.1.asIdeal = .oldKummer)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    (hC : (Ew v.1).baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    [Finite (ModN ((Ew v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2)] :
    2 ^ GenuineInst.genCondDimFun2 K S cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))
        v.1.asIdeal =
      Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) := by
  have hP : v.1.asIdeal.IsPrime ∧ v.1.asIdeal ≠ ⊥ := ⟨v.1.isPrime, v.1.ne_bot⟩
  rw [← two_pow_kummerDimOfCurves_eq_actual Ew W s hs hs0 α hFull v hα hC]
  unfold GenuineInst.genCondDimFun2
  rw [dite_eq_left_of_eq_true (eq_true hP), hcond]
  rfl

open scoped Classical in
/-- At odd places with full rational `2`-torsion of `E_v` (no finiteness hypothesis):
`2^(kummerDimOfCurves … v) = |H⁰(U_v)| · |H¹(U_v)| = 2⁴`. PROVED. -/
theorem two_pow_kummerDimOfCurves_eq_actual_odd (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1) (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal)
    (hC : (Ew v.1).baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    (h4 : Nat.card
      (Submodule.torsionBy ℤ ((Ew v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2) = 4) :
    2 ^ kummerDimOfCurves K Ew (kd2OfCurves K Ew) v.1.asIdeal =
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
          Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) ∧
      Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
          Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
        2 ^ LocalCondition.dim .oldKummer 0 := by
  have := compactSpace_place K v.1
  have hcard := card_modN_two_eq_card_twoTorsion v.1 (Ew v.1) h2
  have : Finite (ModN ((Ew v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard, h4]; norm_num)
  exact ⟨two_pow_kummerDimOfCurves_eq_actual Ew W s hs hs0 α hFull v hα hC,
    genCondDim2_oldKummer_actual_odd W s hs hs0 α hFull v hα h2 (Ew v.1) hC h4⟩

/-! ### Non-vacuity -/

/-- The local integral models `E_w = W0` (`y² = x³ − x`) at every place of `ℚ`. -/
abbrev EwW0 : ∀ w : HeightOneSpectrum (𝓞 ℚ), WeierstrassCurve (w.adicCompletionIntegers ℚ) :=
  fun w => W0 (w.adicCompletionIntegers ℚ)

instance isElliptic_EwW0 (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((EwW0 w).baseChange (w.adicCompletion ℚ)).IsElliptic :=
  isElliptic_baseChange_W0 w

open scoped Classical in
/-- **Non-vacuity of `two_pow_kummerDimOfCurves_eq_actual_odd`**: over `ℚ` at `v₃`, with the
models `E_w = W0`, `E = y² = x³ − x`, `h = s = 1`, `α = alphaOne`. PROVED. -/
theorem kummerDimOfCurves_actual_nonvacuous :
    2 ^ kummerDimOfCurves ℚ EwW0 (kd2OfCurves ℚ EwW0) v3.asIdeal =
      2 ^ LocalCondition.dim .oldKummer 0 := by
  obtain ⟨h1, h2⟩ := two_pow_kummerDimOfCurves_eq_actual_odd EwW0 (W0 ℚ) 1 (one_sq_KS S3)
    one_ne_zero (alphaOne S3 1) (fullTorsion_W0 S3) pv3 (isLocallyQuadAt_alphaOne S3 1 v3)
    two_not_mem_v3 (baseChange_W0_eq_localTwist v3) (natCard_twoTorsion_baseChange_W0 v3)
  exact h1.trans h2

end ZInQ.Contrib.CloudB3RC53.OldKummer
