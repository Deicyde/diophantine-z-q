import ZInQKernel.Contrib.CloudB3RC53.CoordLink.Bridge47
import ZInQKernel.Contrib.CloudB3RC53.Torsion.Exists

/-!
# E1a, part 5: `RelIsKM` from the two-term core of the relaxed complex

How RC0/RC15 define `u_rel`: in the (4.7) data (`CommonCoordinateTrianglesN`, `NaturalStep`) the
relaxed coordinate `u_rel = u U` is the class-functional coordinate of a two-term relaxed model
(`IsCoordOn D_R z_R w_R u_rel`, RC15's identity `z ⊗ λ = u · adj D`), over `ℚ₂[[t]]`. So `u_rel`
is a two-term coordinate, and `RelIsKM` (`u_rel,x = kmCoord(C_x)`) is reduced here to cancelling
the pre-cancellation complex `C_x` down to its two-term core:

* `kmCoord_pre_block` (PROVED): cancelling the new-local block (`kmCoord_preCancel`) and then the
  three Smith blocks (lane ClearingComplex's `kmCoord_block`) gives
  `kmCoord(C_x) = −det B_x · δ₀ δ₁⁻¹ δ₂ · (α_x β_x if the remaining map vanishes, else 0)`;
* `isClassFunctionalCoord_transport` (PROVED): an integral two-term model over `Λ` whose
  `ℚ₂[[t]]`-image carries the coordinate `2^{-e} ιQ(g)` carries the coordinate `uK e g` over
  `Frac 𝒪` (RC15's identity transported through `Λ[1/2]`);
* `PreCoreLink` (the remaining identification, GLUE, stated at the level of the coordinate): the
  pre-cancellation complex `C_x` and the two-term core `[S^n --D_x--> S^n]` of the relaxed complex
  at `x` (with its class and functional) have the same Knudsen–Mumford coordinate — both are
  models of the relaxed Selmer complex at `x` in the retained bases (the genuine complex of lane
  RC26, `SelmerComplex.galoisSelData`); the cancellation of acyclic summands in compatible bases
  does not change the coordinate;
* **`relIsKM_of_core` (PROVED)**: from `PreCoreLink`, the exactness of the augmented core over
  `Frac 𝒪`, and the integral core whose `ℚ₂[[t]]`-image carries the (4.7) relaxed coordinate,
  `RelIsKM M (urelK …) z λ` holds — with the same `urelK` as `correctedIsEta_of_triangles`;
* `coordLink_of_triangles_core` (PROVED): E1a (`CoordLink`) from the (4.7) data, the integral core
  and `PreCoreLink` only.

**Classification.** PROVED (`PreCoreLink` is the named GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

variable {b dK hK cE tK : ℕ}

/-! ### The pre-cancellation coordinate after all cancellations -/

open Classical in
/-- **`kmCoord(C_x) = −det B · δ₀ δ₁⁻¹ δ₂ · (αβ or 0)`** (PROVED): the new-local cancellation
followed by the cancellation of the three Smith blocks. -/
theorem kmCoord_pre_block {K : Type} [Field K] (C : ClearingComplex.PreComplex K)
    (hB : IsUnit C.B.det) (z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → K)
    (lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → K) (hz : (PreComplex'.toFour C).d1 *ᵥ z = 0)
    (hlam : lam ᵥ* (PreComplex'.toFour C).d1 = 0) (hA0 : IsUnit (C.cancel hB).A0.det)
    (hA1 : IsUnit (C.cancel hB).A1.det) (hA2 : IsUnit (C.cancel hB).A2.det) :
    kmCoord (PreComplex'.toFour C) z lam hz hlam (σPre C.m0 C.m1 C.m2 C.N) =
      -(C.B.det * ((if (C.cancel hB).hRem = 0 then (C.cancel hB).alphaB z *
        (C.cancel hB).betaB (transportFun C lam) else 0) * (C.cancel hB).A0.det *
          ((C.cancel hB).A1.det)⁻¹ * (C.cancel hB).A2.det)) := by
  rw [kmCoord_preCancel hB]
  have hb := kmCoord_block (D := C.cancel hB) z (transportFun C lam) (hz_cancel C hB hz)
    (hμ_cancel C hB hlam) hA0 hA1 hA2
  refine (congrArg (C.B.det * ·) hb).trans ?_
  ring

/-! ### Transport of RC15's coordinate from `ℚ₂[[t]]` to `Frac 𝒪` -/

theorem adjugate_map_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) : (M.map f).adjugate i j = f (M.adjugate i j) := by
  have := RingHom.map_adjugate f M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
  rw [← this]; rfl

/-- `Λ → Frac 𝒪`. -/
abbrev ψO : Lam →+* FractionRing OO := (algebraMap OO (FractionRing OO)).comp (algebraMap Lam OO)

theorem two_pow_ne_zero_frac (n : ℕ) : (2 : FractionRing OO) ^ n ≠ 0 := by
  rw [show (2 : FractionRing OO) ^ n = algebraMap OO (FractionRing OO) ((2 : OO) ^ n) by
    rw [map_pow, map_ofNat]]
  exact (map_ne_zero_iff _ (IsFractionRing.injective OO (FractionRing OO))).mpr
    (Determinant.two_pow_ne_zero_OO n)

/-- **RC15's coordinate through `Λ[1/2]`** (PROVED): if the `ℚ₂[[t]]`-image of an integral
two-term model has coordinate `2^{-e} ιQ(g)`, its `Frac 𝒪`-image has coordinate `uK e g`. -/
theorem isClassFunctionalCoord_transport {n : ℕ} (DΛ : Matrix (Fin n) (Fin n) Lam)
    (zΛ wΛ : Fin n → Lam) (e : ℕ) (g : Lam)
    (h : Central.IsClassFunctionalCoord (DΛ.map ιQ) (ιQ ∘ zΛ) (ιQ ∘ wΛ)
      (PowerSeries.C ((2 : ℚ_[2]) ^ e)⁻¹ * ιQ g)) :
    Central.IsClassFunctionalCoord (DΛ.map ψO) (ψO ∘ zΛ) (ψO ∘ wΛ) (uK (O := OO) e g) := by
  unfold Central.IsClassFunctionalCoord at h ⊢
  -- the identity `2^e z ⊗ w = g · adj D` over `Λ`
  have hΛ : (2 : Lam) ^ e • vecMulVec zΛ wΛ = g • DΛ.adjugate := by
    refine Matrix.ext fun i j => ?_
    apply ιQ_injective
    have hij := congrFun (congrFun h i) j
    have hadj : (DΛ.map ιQ).adjugate i j = ιQ (DΛ.adjugate i j) := adjugate_map_apply _ _ _ _
    simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul, hadj] at hij
    simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, map_mul, map_pow, map_ofNat]
    have h2 : (2 : PowerSeries ℚ_[2]) ^ e * PowerSeries.C ((2 : ℚ_[2]) ^ e)⁻¹ = 1 := by
      rw [show (2 : PowerSeries ℚ_[2]) ^ e = PowerSeries.C ((2 : ℚ_[2]) ^ e) by
        rw [map_pow, map_ofNat], ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), map_one]
    rw [hij]
    linear_combination (ιQ g * ιQ (DΛ.adjugate i j)) * h2
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun hΛ i) j
  simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply] at hij
  have hψ := congrArg ψO hij
  simp only [map_mul, map_pow, map_ofNat] at hψ
  have hadj : (DΛ.map ψO).adjugate i j = ψO (DΛ.adjugate i j) := adjugate_map_apply _ _ _ _
  simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul, hadj]
  unfold Determinant.uK
  have h2 := two_pow_ne_zero_frac e
  field_simp
  change ψO (zΛ i) * ψO (wΛ j) * 2 ^ e = ψO g * ψO (DΛ.adjugate i j)
  linear_combination hψ

/-! ### The remaining identification and `RelIsKM` -/

/-- **GLUE: the pre-cancellation complex and the two-term core of the relaxed complex have the same
Knudsen–Mumford coordinate** (at `x`, where `Δ_x ≠ 0`): `C_x` with `(z, λ)` and the core
`[K^n --D--> K^n]` with its class and functional are models of the relaxed Selmer complex at `x` in
the retained bases. -/
def PreCoreLink (M : Identification2 b dK hK cE tK) (x : Addr b)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    {n : ℕ} (D : Matrix (Fin n) (Fin n) (FractionRing OO)) (zc wc : Fin n → FractionRing OO)
    (hzc : (twoTerm D).d1 *ᵥ zc = 0) (hwc : wc ᵥ* (twoTerm D).d1 = 0) : Prop :=
  kmCoord (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) (evK (sgnChar x) ∘ z)
      (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x)
      (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N) =
    kmCoord (twoTerm D) zc wc hzc hwc (σ₀ n)

/-- **The integral two-term core of the relaxed complex at `x`** (data): a two-term model over `Λ`
with an integral class and closed functional, whose augmented complex over `Frac 𝒪` is exact. -/
structure IntegralCore where
  n : ℕ
  D : Matrix (Fin n) (Fin n) Lam
  zc : Fin n → Lam
  wc : Fin n → Lam
  hz : (twoTerm (D.map ψO)).d1 *ᵥ (ψO ∘ zc) = 0
  hw : (ψO ∘ wc) ᵥ* (twoTerm (D.map ψO)).d1 = 0
  exact : ((twoTerm (D.map ψO)).aug (ψO ∘ zc) (ψO ∘ wc) hz hw).IsExact

/-- **`RelIsKM` from the two-term core** (PROVED): if the (4.7) relaxed coordinate at `x` is RC15's
coordinate of the `ℚ₂[[t]]`-image of the integral core, and `PreCoreLink` holds, then
`urelK x = kmCoord(C_x)`. -/
theorem relIsKM_of_core {ℓ : ℕ} (Dd : RCData ℓ) (F : Family) (M : Identification2 F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hcompat : ∀ x, (T x).chi (Central.eta (T x).Q (T x).v (T x).g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ))
    (core : Addr F.b → IntegralCore)
    (hcore : ∀ x, Central.IsClassFunctionalCoord ((core x).D.map ιQ) (ιQ ∘ (core x).zc)
      (ιQ ∘ (core x).wc) (T x).urel)
    (hlink : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      PreCoreLink M x z lam hz hlam ((core x).D.map ψO) (ψO ∘ (core x).zc) (ψO ∘ (core x).wc)
        (core x).hz (core x).hw) :
    RelIsKM M (urelK ηΛ hunit e₀ g₀) z lam hz hlam := by
  intro x hΔ
  rw [hlink x hΔ]
  have hu := hcore x
  rw [urel_eq_of_triangles ηΛ hunit h₀ x (T x) (hcompat x)] at hu
  have hK := isClassFunctionalCoord_transport (core x).D (core x).zc (core x).wc (e₀ x)
    ((hunit x).unit⁻¹ * g₀ x) hu
  obtain ⟨hc⟩ := exists_contraction _ (FourCx.isExact_toBased _ (core x).exact)
  exact (kmCoord_twoTerm _ _ _ _ _ _ hc hK).symm

/-- **E1a from the (4.7) data, the integral core and `PreCoreLink` only** (PROVED). -/
theorem coordLink_of_triangles_core {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2 F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hcompat : ∀ x, (T x).chi (Central.eta (T x).Q (T x).v (T x).g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ))
    (core : Addr F.b → IntegralCore)
    (hcore : ∀ x, Central.IsClassFunctionalCoord ((core x).D.map ιQ) (ιQ ∘ (core x).zc)
      (ιQ ∘ (core x).wc) (T x).urel)
    (hlink : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      PreCoreLink M x z lam hz hlam ((core x).D.map ψO) (ψO ∘ (core x).zc) (ψO ∘ (core x).wc)
        (core x).hz (core x).hw) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink M.toIdentification.B (kappaOf M) (φO F.b ηΛ) 0 e g
        (cOf M.D z (transportFun (M.C.map (φO F.b)) lam) hz
          (hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam)) :=
  coordLink_of_km Dd F M z lam hz hlam (φO F.b ηΛ) (urelK ηΛ hunit e₀ g₀)
    (correctedIsEta_of_triangles Dd F ηΛ hunit e₀ g₀ h₀)
    (relIsKM_of_core Dd F M z lam hz hlam ηΛ hunit e₀ g₀ h₀ T hcompat core hcore hlink)

end ZInQ.Contrib.CloudB3RC53.CoordLink
