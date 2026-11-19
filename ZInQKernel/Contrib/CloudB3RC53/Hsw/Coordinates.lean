import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchDuality
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps

/-!
# RC53 `hsw`: the coordinate pairing identity from the residue pairing

The hypothesis `hsw` of `SwitchAdjunctionFromDuality` (and its specialisation `SwitchCoordinates`
for `GenuineSwitch`, and the field `DualityFromSelmer.hsw`) is tex L2816–2818:

  `tr((0, s, −ι u) ∪ (0, t, 0)) = ⟨e_R[g t], e_R[g u]⟩` "in the chosen coordinates".

## What is and is not provable

`hsw` is **not** provable for an arbitrary coordinate isomorphism `eR : H¹(W_rel) ≃ F ⊕ S`. The
structures `QuasiRelaxedLocalization` and `GenuineSwitch` carry `eR` as free data, and no other
hypothesis of `SwitchAdjunctionFromDuality` involves `eR`. So replacing `eR` by `c • eR` for a
scalar `c ≠ 0, ±1` multiplies the right-hand side by `c²` and leaves the left-hand side unchanged.
The tex says "in the chosen coordinates": `hsw` fixes the coordinates as well as computing the
cup product. `hsw_reScale` records this formally.

This file proves the coordinate half. Suppose the left-hand side is the value
`P(e_R[g t], e_R[g u])` of some bilinear form `P` on `F ⊕ S` (the *residue pairing* hypothesis
`ResiduePairing`). Suppose also that `P` has the local-duality shape of tex L4859–4890:

* the finite plane `F ⊕ 0` is isotropic;
* the singular plane `0 ⊕ S` is isotropic;
* `P` is `σ`-graded-symmetric;
* the cross pairing `F × S → k` is perfect.

Then, after a linear change of coordinates `A` on the singular plane only, `hsw` holds exactly
(`hsw_of_residuePairing`). The change `eR ↦ (id × A) ∘ eR` fixes the finite plane, so the relaxed
image is only moved by `id × A` (`reCoord_U`), and the detection condition `F ≤ U` is unchanged
(`finPlane_le_reCoord_U_iff`). The same holds for `GenuineSwitch.SwitchCoordinates`
(`switchCoordinates_of_residuePairing`). The full consequence `U = U^⊥` (for the re-coordinatised
relaxed image) is `localizationDualityInput_of_residuePairing`.

The reduction is no stronger than `hsw` itself. When `σ² = 1`, `switchPairing ε σ J` has all four
properties (`switchPairing_residueShape`), and `hsw` *is* `ResiduePairing` for `P = switchPairing`
(`residuePairing_of_hsw`). So any instance of `hsw` gives an instance of the hypotheses used here
(non-vacuity, relative non-vacuity).

## Remaining input (GLUE / local duality)

* The residue pairing identity itself: the left-hand side factors through the classes
  `[g t], [g u] ∈ H¹(W_rel)` as a bilinear form `P`.
* The local Tate duality properties of that `P` (the four bullets above).

These are the content of tex L2790–2818 together with local duality at the switched place. They
are not determined by the data of `QuasiRelaxedLocalization`, which carries no pairing on `W_rel`.
For the genuine switch the first is `genuine_exists_residuePairing` (`CupOneReverse.lean`), and
`Shape.lean` reduces the second to intrinsic local-duality properties (`hsw_of_localDuality`).

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-! ### Choosing coordinates on the singular plane -/

/-- **The coordinates on the singular plane can be chosen** (`PROVED`): a perfect pairing
`β' : F × S → k` is the cross pairing `ε e₂(x, J y)` after a linear change of coordinates on `S`. -/
theorem exists_coord_crossPairing {ε : k} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1) (β' : LinearMap.BilinForm k (Fin 2 → k)) (hβ' : β'.IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k), ∀ x y, β' x y = crossPairing ε J x (A y) := by
  have hcp := crossPairing_isPerfPair hε hJ2
  let eβ := LinearEquiv.ofBijective β'.flip (LinearMap.IsPerfPair.bijective_right β')
  let ecp := LinearEquiv.ofBijective (crossPairing ε J).flip
    (LinearMap.IsPerfPair.bijective_right (crossPairing ε J))
  refine ⟨eβ.trans ecp.symm, fun x y => ?_⟩
  have h := congrArg (fun f : Module.Dual k (Fin 2 → k) => f x) (ecp.apply_symm_apply (eβ y))
  change β' x y = (crossPairing ε J).flip (ecp.symm (eβ y)) x
  rw [show (crossPairing ε J).flip (ecp.symm (eβ y)) = ecp (ecp.symm (eβ y)) from rfl, h]
  rfl

/-- **A local-duality-shaped pairing is the switch pairing in suitable coordinates** (`PROVED`).
Let `P` be a bilinear form on `F ⊕ S` with both planes isotropic, `σ`-graded-symmetric, and with
perfect cross pairing. Then `P(a, b) = switchPairing ε σ J ((id × A) a) ((id × A) b)` for a linear
automorphism `A` of the singular plane. -/
theorem exists_coord_switchPairing {ε : k} (hε : ε ≠ 0) (σ : k) {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1) (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hS : ∀ y y', P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k), ∀ a b,
      P a b = switchPairing ε σ J (a.1, A a.2) (b.1, A b.2) := by
  obtain ⟨A, hA⟩ := exists_coord_crossPairing hε hJ2 _ hperf
  refine ⟨A, fun a b => ?_⟩
  rw [planePairing_eq_of_isotropic P σ hF hS hσ, planePairing_apply, planePairing_apply, hA, hA]

/-! ### Re-coordinatising the relaxed localization -/

/-- The coordinate change `id × A` on `F ⊕ S`. It fixes the finite plane pointwise. -/
abbrev coordChange (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) :=
  (LinearEquiv.refl k (Fin 2 → k)).prodCongr A

/-- The quasi relaxed localization with the singular-plane coordinates changed by `A`. All
cochain data is unchanged; only `eR` becomes `(id × A) ∘ eR`. -/
abbrev reCoord (R : QuasiRelaxedLocalization k) (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    QuasiRelaxedLocalization k :=
  { R with eR := R.eR.trans (coordChange A) }

/-- The relaxed image of the re-coordinatised localization is the image of the old one under
`id × A`. `PROVED`. -/
theorem reCoord_U (R : QuasiRelaxedLocalization k) (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    (reCoord R A).U = R.U.map (coordChange A).toLinearMap := by
  simp only [QuasiRelaxedLocalization.U, Submodule.map_comp, LinearEquiv.coe_trans]

/-- `id × A` maps the finite plane onto itself. `PROVED`. -/
theorem map_coordChange_finPlane (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    (finPlane k (Fin 2 → k) (Fin 2 → k)).map (coordChange A).toLinearMap =
      finPlane k (Fin 2 → k) (Fin 2 → k) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, hb, he⟩
    rw [SetLike.mem_coe, mem_finPlane] at hb
    have hb' : b = 0 := hb
    rw [mem_finPlane, ← he, hb']
    simp
  · intro hy
    rw [mem_finPlane] at hy
    refine ⟨(x, 0), mem_finPlane.2 rfl, ?_⟩
    simp [show y = 0 from hy]

/-- **Detection is unchanged by the coordinate choice**: `F ≤ U` for the re-coordinatised
localization iff `F ≤ U` for the original one. `PROVED`. -/
theorem finPlane_le_reCoord_U_iff (R : QuasiRelaxedLocalization k)
    (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    finPlane k (Fin 2 → k) (Fin 2 → k) ≤ (reCoord R A).U ↔
      finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U := by
  rw [reCoord_U]
  conv_lhs => rw [← map_coordChange_finPlane A]
  exact Submodule.map_le_map_iff_of_injective (coordChange A).injective _ _

/-! ### `hsw` from the residue pairing (`QuasiRelaxedLocalization` generality) -/

/-- **The residue pairing hypothesis**: the cone-trace of the cup product of tex L2816 is the value
of a bilinear form `P` on the `eR`-coordinates of the classes `[g t], [g u]`. This is `hsw` with
`switchPairing ε σ J` replaced by an arbitrary `P`. -/
def ResiduePairing (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) : Prop :=
  ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
    (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
    (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
    tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
      P (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu))

/-- **`hsw` in chosen coordinates** (tex L2816–2818), `PROVED`. Assume the residue pairing `P` has
the local-duality shape: both planes isotropic, `σ`-graded-symmetric, perfect cross pairing. Then
there is a coordinate change `A` on the singular plane such that the re-coordinatised localization
`reCoord R A` satisfies the hypothesis `hsw` of `SwitchAdjunctionFromDuality` verbatim. -/
theorem hsw_of_residuePairing (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) {ε : k} (hε : ε ≠ 0) (σ : k)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) (hP : ResiduePairing R Ustr f Q tr P)
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hS : ∀ y y', P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k),
      ∀ (t u : (reCoord R A).D.U.X 1) (s : Ustr.X 2) (_ht : (reCoord R A).D.U.d 1 2 rfl t = 0)
        (_hu : (reCoord R A).D.U.d 1 2 rfl u = f.f 2 2 rfl s)
        (ct cu : LinearMap.ker ((reCoord R A).Wrel.d 1 2 rfl))
        (_hct : ct.1 = (reCoord R A).gR.f 1 1 rfl t) (_hcu : cu.1 = (reCoord R A).gR.f 1 1 rfl u),
        tr (selCupFun Q 2 1 3 rfl ((0 : (reCoord R A).D.G.X 2), s,
            -((reCoord R A).D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : (reCoord R A).D.G.X 1), t, (0 : (reCoord R A).D.L.X (1 - 1)))) =
          switchPairing ε σ J ((reCoord R A).eR (cls1 (reCoord R A).Wrel ct))
            ((reCoord R A).eR (cls1 (reCoord R A).Wrel cu)) := by
  obtain ⟨A, hA⟩ := exists_coord_switchPairing hε σ hJ2 P hF hS hσ hperf
  exact ⟨A, fun t u s ht hu ct cu hct hcu => (hP t u s ht hu ct cu hct hcu).trans (hA _ _)⟩

/-- **The localization duality `U = U^⊥` from the residue pairing**, `PROVED`. These are the
hypotheses of the other team's `switchAdjunctionFromDuality_proof`, with `hsw` replaced by
`ResiduePairing` plus the local-duality shape of `P`. The conclusion holds for the relaxed image of
the re-coordinatised localization, which is `R.U` moved by `id × A` (`reCoord_U`) and contains `F`
iff `R.U` does (`finPlane_le_reCoord_U_iff`). -/
theorem localizationDualityInput_of_residuePairing (R : QuasiRelaxedLocalization k)
    (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ0 : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) (hP : ResiduePairing R Ustr f Q tr P)
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hS : ∀ y y', P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k),
      LocalizationDualityInput ε σ J hε hσ0 hJ2 (reCoord R A).U := by
  obtain ⟨A, hA⟩ := hsw_of_residuePairing R Ustr f Q tr hε σ hJ2 P hP hF hS hσ hperf
  exact ⟨A, localizationDualityInput_of_adjunction (reCoord R A) (restrictData R.D f) ε σ J hε hσ0
    hJ2 _ _ (switchAdjunctionFromDuality_proof k (reCoord R A) Ustr f hfg hf hg hex Q tr htr ε σ J
      hε hσ0 hJ2 hγ hA)⟩

/-- The `DualityFromSelmer` bundle (`SwitchInputs/GenuineSteps.lean`) for the re-coordinatised
localization, with its `hsw` field discharged by `hsw_of_residuePairing`. `PROVED`. -/
theorem exists_dualityFromSelmer_of_residuePairing (R : QuasiRelaxedLocalization k)
    (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ0 : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) (hP : ResiduePairing R Ustr f Q tr P)
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hS : ∀ y y', P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k), Nonempty (DualityFromSelmer (reCoord R A)) := by
  obtain ⟨A, hA⟩ := hsw_of_residuePairing R Ustr f Q tr hε σ hJ2 P hP hF hS hσ hperf
  exact ⟨A, ⟨⟨Ustr, f, hfg, hf, hg, hex, Q, tr, htr, ε, σ, J, hε, hσ0, hJ2, hγ, hA⟩⟩⟩

/-! ### `GenuineSwitch.SwitchCoordinates` from the residue pairing -/

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- The genuine switch with the singular-plane coordinates changed by `A`. -/
abbrev genuineReCoord (X : GenuineSwitch K S k M) (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    GenuineSwitch K S k M :=
  { X with eR := X.eR.trans (coordChange A) }

/-- **`SwitchCoordinates` in chosen coordinates** (tex L2816–2818), `PROVED`: for the genuine
switch, a residue pairing of local-duality shape gives `SwitchCoordinates` after a coordinate
change on the singular plane. -/
theorem switchCoordinates_of_residuePairing (X : GenuineSwitch K S k M)
    (Q : SelPairData X.Dstr X.toQuasi.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k) {ε : k} (hε : ε ≠ 0)
    (σ : k) {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)))
    (hP : ResiduePairing X.toQuasi (piCx X.US) (piMap X.φ) Q tr P)
    (hF : ∀ x x', P (x, 0) (x', 0) = 0) (hS : ∀ y y', P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b)
    (hperf : (P.compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair) :
    ∃ A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k), (genuineReCoord X A).SwitchCoordinates Q tr ε σ J := by
  obtain ⟨A, hA⟩ := hsw_of_residuePairing X.toQuasi (piCx X.US) (piMap X.φ) Q tr hε σ hJ2 P hP hF
    hS hσ hperf
  exact ⟨A, hA⟩

/-- The relaxed image of the re-coordinatised genuine switch is `X.toQuasi.U` moved by `id × A`.
`PROVED`. -/
theorem genuineReCoord_U (X : GenuineSwitch K S k M) (A : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)) :
    (genuineReCoord X A).toQuasi.U = X.toQuasi.U.map (coordChange A).toLinearMap :=
  reCoord_U X.toQuasi A

end Genuine


/-! ### `hsw` depends on the coordinates -/

/-- The quasi relaxed localization with coordinates rescaled by `c ≠ 0`. -/
abbrev reScale (R : QuasiRelaxedLocalization k) (c : k) (hc : c ≠ 0) :
    QuasiRelaxedLocalization k :=
  { R with eR := R.eR.trans (LinearEquiv.smulOfNeZero k _ c hc) }

/-- **`hsw` is a coordinate convention**, `PROVED`. If `hsw` holds for `R` and for `R` with `eR`
rescaled by `c`, then every right-hand side value is killed by `c² − 1`. The cochain data, and so
the left-hand side, is the same for both. So `hsw` cannot follow from hypotheses that do not
mention `eR`. -/
theorem hsw_reScale (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (ε σ : k)
    (J : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (h1 : ResiduePairing R Ustr f Q tr (switchPairing ε σ J))
    (h2 : ResiduePairing (reScale R c hc) Ustr f Q tr (switchPairing ε σ J))
    (t u : R.D.U.X 1) (s : Ustr.X 2) (ht : R.D.U.d 1 2 rfl t = 0)
    (hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
    (hct : ct.1 = R.gR.f 1 1 rfl t) (hcu : cu.1 = R.gR.f 1 1 rfl u) :
    (c * c - 1) * switchPairing ε σ J (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu)) = 0 := by
  have e := (h1 t u s ht hu ct cu hct hcu).symm.trans (h2 t u s ht hu ct cu hct hcu)
  change _ = switchPairing ε σ J (c • R.eR (cls1 R.Wrel ct)) (c • R.eR (cls1 R.Wrel cu)) at e
  rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul] at e
  linear_combination -e

/-! ### Relative non-vacuity -/

/-- **`switchPairing` has the local-duality shape** when `σ² = 1` (the manuscript's `σ = 1`
included). `PROVED`. -/
theorem switchPairing_residueShape {ε σ : k} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1) :
    (∀ x x', switchPairing ε σ J (x, 0) (x', 0) = 0) ∧
      (∀ y y', switchPairing ε σ J (0, y) (0, y') = 0) ∧
      (∀ a b, switchPairing ε σ J b a = σ * switchPairing ε σ J a b) ∧
      ((switchPairing ε σ J).compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _)).IsPerfPair := by
  refine ⟨fun x x' => by simp, fun y y' => by simp, fun a b => ?_, ?_⟩
  · simp only [planePairing_apply]
    linear_combination (crossPairing ε J b.1 a.2) * hσ.symm
  · have h : (switchPairing ε σ J).compl₁₂ (LinearMap.inl k _ _) (LinearMap.inr k _ _) =
        crossPairing ε J := by
      ext x y
      simp
    rw [h]
    exact crossPairing_isPerfPair hε hJ2

/-- **`hsw` is a residue pairing**: `hsw` is `ResiduePairing` for `P = switchPairing ε σ J`.
With `switchPairing_residueShape`, every instance of `hsw` (with `σ² = 1`) is an instance of the
hypotheses of `hsw_of_residuePairing` (with `A = id`), so the reduction asks for nothing beyond
`hsw`. `PROVED`. -/
theorem residuePairing_of_hsw (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hsw : ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
      (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
      (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
      tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
        switchPairing ε σ J (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu))) :
    ResiduePairing R Ustr f Q tr (switchPairing ε σ J) :=
  hsw

/-- The shape hypotheses are satisfiable over `ℚ` with the manuscript's normalisation
`ε = 1, σ = 1, J = 1`. `PROVED`. -/
example : (∀ x x', switchPairing (1 : ℚ) 1 1 (x, 0) (x', 0) = 0) ∧
    (∀ y y', switchPairing (1 : ℚ) 1 1 (0, y) (0, y') = 0) ∧
    (∀ a b, switchPairing (1 : ℚ) 1 1 b a = 1 * switchPairing (1 : ℚ) 1 1 a b) ∧
    ((switchPairing (1 : ℚ) 1 1).compl₁₂ (LinearMap.inl ℚ _ _)
      (LinearMap.inr ℚ _ _)).IsPerfPair :=
  switchPairing_residueShape one_ne_zero (mul_one 1) (mul_one 1)

end ZInQ.Contrib.CloudB3RC53.Hsw
