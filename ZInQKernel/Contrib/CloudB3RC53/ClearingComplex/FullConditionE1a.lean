import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionIdentification
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCoord
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1a
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3

/-!
# E1a and the inputs of (5.9) for the full-condition identification

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
5509–5516 and 5605–5617, with the new singular summands in degrees one and two (tex 3479–3481).

* `Cev3 C x`: the sign-evaluated full-condition pre-cancellation complex over `Frac 𝒪`;
  `Dev3_toFour_eq`: the sign-evaluated remaining complex is the cancellation of `C_x`;
* `coordLink_core3` (PROVED): if `ũ_x = η_x u_{rel,x}` and `u_{rel,x}` is the Knudsen–Mumford
  coordinate of `[z] ⊗ [λ]` of `C_x` (orientation `σFull`) where `Δ_x ≠ 0`, then
  `ũ_x = η_x κ_x c_x` with **`κ = det(B)⁻¹`** (a unit of `𝒪[G]`; the disk in degrees one and
  two, `kmCoord_fullCancel`) and `c_x` the coordinate of the remaining complex at the restricted
  cycle `z ∘ inl` and functional `λ ∘ inl`;
* `OrigCoordLink3`, `ClearingInputsG3`: the coordinate identification and the inputs of (5.9)
  for `Identification3` (the analogues of `OrigCoordLink`, `ClearingInputsG`);
* `clearingInputsCx_of_G3`, `clearingTarget_of_G3` (PROVED): RC0's `ClearingInputsCx` and
  `ClearingTarget` from `ClearingInputsG3` (with height-one regularity for the latter).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)
open ZInQ.Contrib.CloudB3RC53.CoordLink (CorrectedIsEta kmCoord_congr FourCx.ext')

variable {b : ℕ}

section Generic

variable (C : FullPreComplex (MonoidAlgebra OO (SignGroup b))) (hB : IsUnit C.B.det)

/-- The sign-evaluated full-condition pre-cancellation complex `C_x` over `Frac 𝒪`. -/
abbrev Cev3 (x : Addr b) : FullPreComplex (FractionRing OO) := C.map (evK (sgnChar x))

include hB in
theorem isUnit_Bev3 (x : Addr b) : IsUnit (Cev3 C x).B.det := by
  have h := RingHom.map_det (evK (sgnChar x)) C.B
  rw [RingHom.mapMatrix_apply] at h
  change IsUnit (C.B.map (evK (sgnChar x))).det
  rw [← h]
  exact hB.map _

theorem det_Bev3 (x : Addr b) : (Cev3 C x).B.det = evK (sgnChar x) C.B.det := by
  have h := RingHom.map_det (evK (sgnChar x)) C.B
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

/-- **The sign-evaluated remaining complex is the cancellation of `C_x`.** -/
theorem Dev3_toFour_eq (x : Addr b) :
    (Dx (C.cancel hB) x).toFour = ((Cev3 C x).cancel (isUnit_Bev3 C hB x)).toFour := by
  refine FourCx.ext' rfl ?_ rfl
  change (C.P - C.Q * C.B⁻¹ * C.T).map (evK (sgnChar x)) =
    C.P.map (evK (sgnChar x)) - C.Q.map (evK (sgnChar x)) * (C.B.map (evK (sgnChar x)))⁻¹ *
      C.T.map (evK (sgnChar x))
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_inv_of_isUnit _ _ hB]

variable {C}

theorem hzev3 {z : C.D1 ⊕ C.N → MonoidAlgebra OO (SignGroup b)} (hz : C.toFour.d1 *ᵥ z = 0)
    (x : Addr b) : (Cev3 C x).toFour.d1 *ᵥ (evK (sgnChar x) ∘ z) = 0 := by
  change fromBlocks (C.P.map (evK (sgnChar x))) (C.Q.map (evK (sgnChar x)))
    (C.T.map (evK (sgnChar x))) (C.B.map (evK (sgnChar x))) *ᵥ (evK (sgnChar x) ∘ z) = 0
  rw [← fromBlocks_map]
  funext i
  rw [← RingHom.map_mulVec]
  change evK (sgnChar x) ((C.toFour.d1 *ᵥ z) i) = 0
  rw [hz]
  simp

theorem hlamev3 {lam : C.D2 ⊕ C.N → MonoidAlgebra OO (SignGroup b)}
    (hlam : lam ᵥ* C.toFour.d1 = 0) (x : Addr b) :
    (evK (sgnChar x) ∘ lam) ᵥ* (Cev3 C x).toFour.d1 = 0 := by
  change (evK (sgnChar x) ∘ lam) ᵥ* fromBlocks (C.P.map (evK (sgnChar x)))
    (C.Q.map (evK (sgnChar x))) (C.T.map (evK (sgnChar x))) (C.B.map (evK (sgnChar x))) = 0
  rw [← fromBlocks_map]
  funext i
  rw [← RingHom.map_vecMul]
  change evK (sgnChar x) ((lam ᵥ* C.toFour.d1) i) = 0
  rw [hlam]
  simp

/-- The comparison factor `κ = det(B)⁻¹ ∈ 𝒪[G]`. -/
def kappa3 : MonoidAlgebra OO (SignGroup b) := ↑(hB.unit⁻¹)

theorem evK_kappa3 (x : Addr b) : evK (sgnChar x) (kappa3 hB) = (evK (sgnChar x) C.B.det)⁻¹ := by
  have h0 : kappa3 hB * C.B.det = 1 := hB.val_inv_mul
  have h : evK (sgnChar x) (kappa3 hB) * evK (sgnChar x) C.B.det = 1 := by
    rw [← map_mul, h0, map_one]
  exact eq_inv_of_mul_eq_one_left h

/-- **E1a, generic core for the full-condition model** (PROVED): if `ũ_x = η_x u_{rel,x}` and
`u_{rel,x}` is the Knudsen–Mumford coordinate of `C_x` (orientation `σFull`) where `Δ_x ≠ 0`, then
`ũ_x = η_x κ_x c_x` with `κ = det(B)⁻¹` and `c_x = kmCoord(D_x, z ∘ inl, λ ∘ inl)`. -/
theorem coordLink_core3 {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (C : FullPreComplex (MonoidAlgebra OO (SignGroup F.b))) (hB : IsUnit C.B.det)
    (Bs : Determinant.SmithBlocks (MonoidAlgebra OO (SignGroup F.b)) OO)
    (z : C.D1 ⊕ C.N → MonoidAlgebra OO (SignGroup F.b))
    (lam : C.D2 ⊕ C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : C.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.toFour.d1 = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      ∀ x, uK (e x) (g x) = evK (sgnChar x) η * urel x)
    (hrel : ∀ x : Addr F.b, evK (sgnChar x) Bs.Δ ≠ 0 →
      urel x = kmCoord (Cev3 C x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam)
        (hzev3 hz x) (hlamev3 hlam x) (σFull C.m0 C.m1 C.m2 C.N)) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink Bs (kappa3 hB) η 0 e g
        (cOf (C.cancel hB) (z ∘ Sum.inl) (lam ∘ Sum.inl) (FullPreComplex.hz_full hB hz)
          (FullPreComplex.hlam_full hB hlam)) := by
  intro e g hrep x hΔ
  rw [hη e g hrep x, hrel x hΔ, pow_zero, inv_one, mul_one]
  have key := kmCoord_fullCancel (C := Cev3 C x) (isUnit_Bev3 C hB x)
    (z := evK (sgnChar x) ∘ z) (lam := evK (sgnChar x) ∘ lam) (hz := hzev3 hz x)
    (hlam := hlamev3 hlam x)
  refine (congrArg (evK (sgnChar x) η * ·) key).trans ?_
  rw [det_Bev3 C x, evK_kappa3 hB x, mul_assoc]
  congr 2
  unfold cOf
  exact (kmCoord_congr (Dev3_toFour_eq C hB x) rfl rfl _ _ _ _ _).symm

end Generic

/-! ### Against `Identification3` -/

section Coordinate

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {dK hK cE tK : ℕ}

/-- **Coordinate identification for the full-condition model** at every representation where
`Δ_x ≠ 0`: the corrected coordinate is `η_x` times the Knudsen–Mumford coordinate of `[z] ⊗ [λ]`
of the original (pre-cancellation, full-condition) complex `C_x` (tex 3877–3892, 4224,
5605–5615). As for `OrigCoordLink`, the existential interface does not supply the provenance of
`z`, `λ`, `η`. -/
def OrigCoordLink3 {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification3 K S S' hS F.b dK hK cE tK)
    (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) : Prop :=
  ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
    ∀ x : Addr F.b, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      uK (e x) (g x) = evK (sgnChar x) η *
        kmCoord (Cev3 (M.C.map (φO F.b)) x).toFour (evK (sgnChar x) ∘ z)
          (evK (sgnChar x) ∘ lam) (hzev3 hz x) (hlamev3 hlam x)
          (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N)

/-- **E1a for the full-condition identification** (PROVED): from `OrigCoordLink3`,
`ũ_x = η_x κ_x c_x` where `Δ_x ≠ 0`, with `κ = det(B)⁻¹` and `c` the coordinate of the remaining
complex at the restricted cycle and functional. -/
theorem coordLink_of_orig3 {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification3 K S S' hS F.b dK hK cE tK)
    (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (h : OrigCoordLink3 D F M z lam hz hlam η) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
      CoordLink M.toIdentification.B (kappa3 M.isUnit_B) η 0 e g
        (cOf M.D (z ∘ Sum.inl) (lam ∘ Sum.inl) (FullPreComplex.hz_full M.isUnit_B hz)
          (FullPreComplex.hlam_full M.isUnit_B hlam)) := by
    intro e g hrep x hΔ
    rw [h e g hrep x hΔ, pow_zero, inv_one, mul_one]
    have key := kmCoord_fullCancel (C := Cev3 (M.C.map (φO F.b)) x)
      (isUnit_Bev3 (M.C.map (φO F.b)) M.isUnit_B x)
      (z := evK (sgnChar x) ∘ z) (lam := evK (sgnChar x) ∘ lam) (hz := hzev3 hz x)
      (hlam := hlamev3 hlam x)
    refine (congrArg (evK (sgnChar x) η * ·) key).trans ?_
    rw [det_Bev3 (M.C.map (φO F.b)) x, evK_kappa3 M.isUnit_B x, mul_assoc]
    congr 2
    unfold cOf
    exact (kmCoord_congr (Dev3_toFour_eq (M.C.map (φO F.b)) M.isUnit_B x) rfl rfl
      _ _ _ _ _).symm

end Coordinate

/-- **The inputs of (5.9) over the full-condition identification** (ELLIOT: Proposition
`ex:limits-fixed-field-clearing` in the form of its proof, with E1a for an existential model;
`Identification3` is ELLIOT for its `FullCore` (tex 5394–5430, 5522–5543) and GLUE for its Galois
comparisons; tex 5234–5238, 5394–5463, 5509–5617). Caveats: the new places are not tied to the
family's primes (`S' = S` is admitted for every family); the family-Selmer clause (`Mf`, `Δf`,
`hfull`, `ψf`) is met by every complex once `S ≠ ∅`, and `M₀, Δ₀` are not related to `Mf, Δf`;
the deduction `clearingTarget_of_G3` uses only `FullCore`, the vacuous `SelmerIdentification` and
`OrigCoordLink3` (neither `ψ0, ψold, square, tame` nor the PRINT `NekovarProp788ii` is in its
closure); `OrigCoordLink3` does not supply the provenance of `z`, `λ`, `η`. -/
def ClearingInputsG3 {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification3 K S S' hS F.b dK hK cE tK)
        (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
        (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
        (η : MonoidAlgebra OO (SignGroup F.b)), OrigCoordLink3 D F M z lam hz hlam η

/-- **RC0's `ClearingInputsCx` from the full-condition inputs** (PROVED; `κ = det(B)⁻¹`). -/
theorem clearingInputsCx_of_G3 {ℓ : ℕ} (D : RCData ℓ) (h : ClearingInputsG3 D) :
    ClearingInputsCx D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  exact clearingInputsCx_of_km3 D K ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨S, S', hS, _, _, M, z, lam, hz, hlam, η, hlink⟩ := hF Co Ce F hFam
    exact ⟨S, S', hS, inferInstance, inferInstance, M, z ∘ Sum.inl, lam ∘ Sum.inl,
      FullPreComplex.hz_full M.isUnit_B hz, FullPreComplex.hlam_full M.isUnit_B hlam,
      kappa3 M.isUnit_B, η, coordLink_of_orig3 D F M z lam hz hlam η hlink⟩⟩

/-- **`RCSteps.clearing` from the full-condition inputs and height-one regularity** (PROVED). -/
theorem clearingTarget_of_G3 {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h : ClearingInputsG3 D) : ClearingTarget D :=
  clearingTarget_of_complex D h1 (clearingInputsCx_of_G3 D h)

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
