import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.TateLevel
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitTransport

/-!
# Conjugation on the realized derivative stages

The coefficient basis is a `ℤ₂`-basis of the Tate module over `K_S`. The compatible torsion-level
maps identify this module with `T_2E` over `ℚ̄`, as used in the finite coefficients
`M_i = (T_2E ⊗ A_i)(α_i)` (tex 2723–2727). The maps come from
`ZInQKernel/Contrib/OneProof/RC/KummerMaps/TateLevel.lean`.

`rhoK` transports the rational Tate action through this identification. `rhoKMatrix` writes it
in the coefficient basis; a change of Tate basis transports the Frobenius matrix with it
(tex 3268–3273). For actual complex conjugation, `rhoK_conj_pt` identifies the transported action
with the coordinate action at every torsion level. Its matrix `conjMatrixK` is `J = ρ_T(τ)`,
with `J² = 1` and `det J = -1` (tex 2798–2805; 3092–3096).

The fibre conjugation in `ZInQKernel/Contrib/OneProof/RC/FibreDuality/LimitTransport.lean` is the
same action. Its cross pairing uses this `J`, also after coefficient specialization
(tex 2762–2767; 5035–5043).

`realizedDerivativeK` writes the derivative stages of `Realization.lean` in this basis.
The retained congruences give the limiting local action `(J, -J)` (tex 5026–5032).
`ratSqFrob` is the restriction of the square of rational Frobenius, the finite Frobenius
at an inert derivative prime (tex 5026–5030). Its Tate congruence, together with the scalar
character congruence, gives trivial action on `𝕋 / I_i 𝕋` (tex 2723–2727; 3297–3309).

`FrobeniusMatchesLabel` is a GLUE input: it records the matching of a label's stage Frobenius
with this square, up to conjugation. The manuscript chooses a prime and a place realizing the
required finite representative (tex 4809–4816). `htriv_of_match` and
`realizedDerivativeK_of_match` use the matching and character hypotheses; they do not construct
those hypotheses. Every theorem below is proved from its displayed parameters.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open Filter Topology Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (TorsS KS ActualConj conjPt conjTors coe_conjTors FullTorsion)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar TateMod tateRep)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix tateMatrix_mul tateMatrix_one det_tateMatrix)
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped WeierstrassCurve PowerSeries.WithPiTopology

/-! ### The Tate module over `K_S` is the Tate module over `ℚ̄` -/

section TateIso

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- PROVED (tex 2723–2727). The torsion-level maps commute with the Tate transition maps. -/
theorem tateTorsMap_transition (n : ℕ) (P : Lev K S (E⁄K) (n + 1)) :
    TauCeti.tateModuleTransition 2 (E⁄Qbar).toAffine.Point n (tateTorsMap S E e (n + 1) P) =
      tateTorsMap S E e n (transLev K S (E⁄K) n P) := by
  apply Subtype.ext
  rw [TauCeti.tateModuleTransition_apply, coe_tateTorsMap, coe_tateTorsMap, coe_transLev]
  exact (map_nsmul (tatePointMap S E e) 2 _).symm

/-- definition (tex 2723–2727). The levelwise additive map from the Tate module over `K_S`
to the Tate module over `ℚ̄`. -/
def tateSMap : TateS K S (E⁄K) →+ TateMod E 2 where
  toFun P := TauCeti.TateModule.mk (fun n => tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n))
    fun n => by
      rw [tateTorsMap_transition]
      exact congrArg _ (P.2 n)
  map_zero' := TauCeti.TateModule.ext fun n => by
    rw [map_zero (TauCeti.TateModule.proj n)]
    exact map_zero (tateTorsMap S E e n)
  map_add' P Q := TauCeti.TateModule.ext fun n => by
    rw [map_add (TauCeti.TateModule.proj n)]
    exact map_add (tateTorsMap S E e n) ((P : ∀ n, Lev K S (E⁄K) n) n)
      ((Q : ∀ n, Lev K S (E⁄K) n) n)
/-- PROVED (tex 2723–2727). Projection of `tateSMap` is the torsion-level map. -/
theorem proj_tateSMap (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSMap S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl
/-- PROVED (tex 2723–2727). The levelwise Tate map respects multiplication by `ℤ₂`. -/
theorem tateSMap_smul (a : ℤ_[2]) (P : TateS K S (E⁄K)) :
    tateSMap S E e (a • P) = a • tateSMap S E e P := by
  apply TauCeti.TateModule.ext
  intro n
  rw [TauCeti.TateModule.proj_smul, proj_tateSMap, proj_tateSMap]
  apply Subtype.ext
  rw [TauCeti.TateModule.coe_zmod_smul]
  change ((tateTorsMap S E e n (resN n a • (P : ∀ n, Lev K S (E⁄K) n) n) : TateLevel E n) :
    (E⁄Qbar).toAffine.Point) = _
  rw [map_nsmul, AddSubgroup.coe_nsmul]
  rfl

/-- definition (tex 2723–2727). The levelwise Tate map as a `ℤ₂`-linear map. -/
def tateSLin : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateMod E 2 :=
  { tateSMap S E e with map_smul' := tateSMap_smul S E e }
/-- PROVED (tex 2723–2727). Projection of the linear Tate map is the torsion-level map. -/
theorem proj_tateSLin (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSLin S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl
/-- PROVED (tex 2723–2727). Injectivity at every torsion level makes the Tate map injective. -/
theorem tateSLin_injective : Function.Injective (tateSLin S E e) := by
  intro P Q h
  apply TateS.ext'
  intro n
  have h' := congrArg (TauCeti.TateModule.proj n) h
  rw [proj_tateSLin, proj_tateSLin] at h'
  exact congrArg Subtype.val (tateTorsMap_injective S E e n h')

variable [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
/-- PROVED (tex 2723–2727). Full two-power torsion over `K_S` makes the Tate map surjective. -/
theorem tateSLin_surjective : Function.Surjective (tateSLin S E e) := by
  intro y
  have hb : ∀ n, Function.Bijective (tateTorsMap S E e n) := fun n =>
    tateTorsMap_bijective S E e n (HasFullTwoTorsion.full n)
  choose P hP using fun n => (hb n).2 (TauCeti.TateModule.proj n y)
  refine ⟨⟨P, fun n => ?_⟩, ?_⟩
  · apply (hb n).1
    rw [← tateTorsMap_transition, hP, hP, TauCeti.TateModule.proj_succ]
  · apply TauCeti.TateModule.ext
    intro n
    exact hP n

/-- definition (tex 2723–2727). The levelwise `ℤ₂`-linear identification of the Tate module
of `E_K` over `K_S` with that of `E` over `ℚ̄`, under full two-power torsion over `K_S`. -/
def tateSEquiv : TateS K S (E⁄K) ≃ₗ[ℤ_[2]] TateMod E 2 :=
  LinearEquiv.ofBijective (tateSLin S E e) ⟨tateSLin_injective S E e, tateSLin_surjective S E e⟩
/-- PROVED (tex 2723–2727). The Tate equivalence has the prescribed torsion-level projections. -/
theorem proj_tateSEquiv (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSEquiv S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl

end TateIso

/-! ### The transported Galois action and its matrices in the coefficient basis -/

section Transport

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)]

/-- definition (tex 3268–3273). The coefficient basis of the Tate module over `K_S` used for
transporting the derivative Frobenius matrices. -/
abbrev basisK : Basis (Fin 2) ℤ_[2] (TateS K S (E⁄K)) :=
  ZInQ.Manuscript.RC.LambdaCoef.tateBasis (K := K) (S := S) (W := E⁄K)

/-- definition (tex 2723–2727). The rational Tate action of `g ∈ G_ℚ`, transported to the
Tate module over `K_S`. -/
def rhoK (g : GalQ) : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateS K S (E⁄K) :=
  (tateSEquiv S E e).symm.toLinearMap ∘ₗ tateRep E 2 g ∘ₗ (tateSEquiv S E e).toLinearMap
/-- PROVED (tex 2723–2727). The Tate equivalence intertwines `rhoK` with the rational action. -/
theorem tateSEquiv_rhoK (g : GalQ) (x : TateS K S (E⁄K)) :
    tateSEquiv S E e (rhoK S E e g x) = tateRep E 2 g (tateSEquiv S E e x) := by
  simp [rhoK]
/-- PROVED (tex 2723–2727). The transported Tate action respects multiplication in `G_ℚ`. -/
theorem rhoK_mul (g h : GalQ) : rhoK S E e (g * h) = rhoK S E e g ∘ₗ rhoK S E e h := by
  apply LinearMap.ext
  intro x
  apply (tateSEquiv S E e).injective
  simp only [LinearMap.comp_apply, tateSEquiv_rhoK, map_mul, Module.End.mul_apply]
/-- PROVED (tex 2723–2727). The identity Galois element acts as the identity on the Tate module. -/
theorem rhoK_one : rhoK S E e 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (tateSEquiv S E e).injective
  simp [tateSEquiv_rhoK]

/-- definition (tex 3268–3273). The matrix of the transported Tate action in the coefficient
basis. -/
def rhoKMatrix (g : GalQ) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  LinearMap.toMatrix (basisK S E) (basisK S E) (rhoK S E e g)

/-- definition (tex 3268–3273). The coefficient basis transported to the Tate module over `ℚ̄`. -/
abbrev basisQ : Basis (Fin 2) ℤ_[2] (TateMod E 2) := (basisK S E).map (tateSEquiv S E e)
/-- PROVED (tex 3268–3273). `rhoKMatrix` is the rational Tate matrix in the transported basis. -/
theorem rhoKMatrix_eq_toMatrix (g : GalQ) :
    rhoKMatrix S E e g = LinearMap.toMatrix (basisQ S E e) (basisQ S E e) (tateRep E 2 g) := by
  ext a b
  simp only [rhoKMatrix, rhoK, LinearMap.toMatrix_apply, Module.Basis.map_repr,
    Module.Basis.map_apply, LinearEquiv.trans_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

/-- PROVED (tex 3268–3273). Changing from the rational Tate basis to the transported basis
conjugates the matrix of `ρ_T(g)`. -/
theorem rhoKMatrix_eq (g : GalQ) :
    rhoKMatrix S E e g =
      (basisQ S E e).toMatrix (ZInQ.Manuscript.RC.PrintsArith.tateBasis E) * tateMatrix E g *
        (ZInQ.Manuscript.RC.PrintsArith.tateBasis E).toMatrix (basisQ S E e) := by
  rw [rhoKMatrix_eq_toMatrix, tateMatrix,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
/-- PROVED (tex 3268–3273). The coefficient-basis matrices respect Galois multiplication. -/
theorem rhoKMatrix_mul (g h : GalQ) :
    rhoKMatrix S E e (g * h) = rhoKMatrix S E e g * rhoKMatrix S E e h := by
  rw [rhoKMatrix, rhoK_mul, LinearMap.toMatrix_comp (basisK S E) (basisK S E) (basisK S E)]
  rfl
/-- PROVED (tex 3268–3273). The coefficient-basis matrix of the identity element is `1`. -/
theorem rhoKMatrix_one : rhoKMatrix S E e 1 = 1 := by
  rw [rhoKMatrix, rhoK_one, LinearMap.toMatrix_id]

/-- PROVED (tex 3092–3096; 3268–3273). Transporting the Tate action preserves its determinant. -/
theorem det_rhoKMatrix (g : GalQ) : (rhoKMatrix S E e g).det = (tateMatrix E g).det := by
  rw [rhoKMatrix, LinearMap.det_toMatrix, det_tateMatrix, rhoK]
  have h := LinearMap.det_conj (tateRep E 2 g) (tateSEquiv S E e).symm
  rw [LinearEquiv.symm_symm] at h
  exact h

/-- PROVED (tex 3090–3096; 3268–3273). Tate matrix congruences persist in the coefficient basis. -/
theorem rhoKMatrix_congr {i : ℕ} {g g' : GalQ}
    (h : (PadicInt.toZModPow i).mapMatrix (tateMatrix E g) =
      (PadicInt.toZModPow i).mapMatrix (tateMatrix E g')) :
    (PadicInt.toZModPow i).mapMatrix (rhoKMatrix S E e g) =
      (PadicInt.toZModPow i).mapMatrix (rhoKMatrix S E e g') := by
  rw [rhoKMatrix_eq, rhoKMatrix_eq, map_mul, map_mul, map_mul, map_mul, h]

end Transport

/-! ### The actual complex conjugation in the coefficient basis -/

section Conj

open ComplexConjugate

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)

/-- PROVED (tex 2778–2779; 2798–2805). At every torsion level, the transported action of
`e τ e⁻¹` is the coordinate action of the actual complex conjugation `τ`. -/
theorem rhoK_conj_pt (x : TateS K S (E⁄K)) (n : ℕ) :
    (rhoK S E e (tateConjQ e C) x).pt n =
      conjPt C (E⁄K) (tate_baseChange_map_kappa E C) (x.pt n) := by
  have h1 := congrArg (TauCeti.TateModule.proj n) (tateSEquiv_rhoK S E e (tateConjQ e C) x)
  rw [proj_tateSEquiv] at h1
  change _ = tateProj E n (tateRep E 2 (tateConjQ e C) (tateSEquiv S E e x)) at h1
  rw [tateProj_tateRep] at h1
  change _ = tateLevelAct E n (tateConjQ e C) (TauCeti.TateModule.proj n (tateSEquiv S E e x))
    at h1
  rw [proj_tateSEquiv, ← tateTorsMap_conjTors] at h1
  have h2 := tateTorsMap_injective S E e n h1
  have h3 := congrArg Subtype.val h2
  rw [coe_conjTors] at h3
  exact h3

/-- PROVED (tex 2778–2779; 2798–2805). An endomorphism with the coordinate action of `τ` at
all torsion levels is the transported conjugation. -/
theorem eq_rhoK_conj_of_pt (f : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateS K S (E⁄K))
    (hf : ∀ x n, (f x).pt n = conjPt C (E⁄K) (tate_baseChange_map_kappa E C) (x.pt n)) :
    f = rhoK S E e (tateConjQ e C) := by
  apply LinearMap.ext
  intro x
  apply TateS.ext'
  intro n
  rw [hf, rhoK_conj_pt]

/-- PROVED (tex 2778–2779; 2798–2805). The transported conjugation is independent of the
chosen isomorphism `K̄ ≃ ℚ̄`, since its torsion-level coordinate action is fixed. -/
theorem rhoK_conj_indep (e' : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    rhoK S E e (tateConjQ e C) = rhoK S E e' (tateConjQ e' C) :=
  (eq_rhoK_conj_of_pt E e' C _ fun x n => rhoK_conj_pt E e C x n)

/-- definition (tex 2798–2805). The matrix `J = ρ_T(τ)` of actual complex conjugation in the
coefficient basis of the Tate module over `K_S`. -/
def conjMatrixK : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  rhoKMatrix S E (tateAlgEquiv K) (tateConjQ (tateAlgEquiv K) C)

/-- PROVED (tex 2798–2805). Every isomorphism `K̄ ≃ ℚ̄` gives the same coefficient-basis
conjugation matrix. -/
theorem conjMatrixK_eq : conjMatrixK E C = rhoKMatrix S E e (tateConjQ e C) := by
  rw [conjMatrixK, rhoKMatrix, rhoKMatrix, rhoK_conj_indep E (tateAlgEquiv K) C e]

/-- PROVED (tex 2803–2804). The conjugation matrix satisfies `J² = 1`. -/
theorem conjMatrixK_sq : conjMatrixK E C * conjMatrixK E C = 1 := by
  rw [conjMatrixK, ← rhoKMatrix_mul, tateConjQ_mul_self, rhoKMatrix_one]

/-- PROVED (tex 2778–2779; 2803–2804). Actual complex conjugation acts on two-power roots of
unity by inversion, giving its cyclotomic action. -/
theorem tateConjQ_roots (M : ℕ) (ζ : Qbar) (hζ : ζ ^ (2 ^ M) = 1) :
    tateConjQ e C ζ = ζ ^ (2 ^ M - 1) := by
  have hinj : Function.Injective (fun y : Qbar => C.ι (e.symm y)) :=
    C.ι.injective.comp e.symm.injective
  apply hinj
  change C.ι (e.symm (tateConjQ e C ζ)) = C.ι (e.symm (ζ ^ (2 ^ M - 1)))
  rw [tateConjQ_complex]
  have hz : (C.ι (e.symm ζ)) ^ (2 ^ M) = 1 := by
    rw [← map_pow, ← map_pow, hζ, map_one, map_one]
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hz (pow_ne_zero _ two_ne_zero)
  rw [← Complex.inv_eq_conj hnorm, map_pow, map_pow]
  have hz0 : C.ι (e.symm ζ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero _ two_ne_zero)] at hz
    exact zero_ne_one hz
  rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hz]

/-- PROVED (tex 3095–3096). The conjugation matrix satisfies `det J = -1`. -/
theorem det_conjMatrixK : (conjMatrixK E C).det = -1 := by
  rw [conjMatrixK, det_rhoKMatrix, det_tateMatrix_conj E (tateConjQ_roots (tateAlgEquiv K) C)]

/-- PROVED (tex 2762–2767). After extending coefficients, the specialization of `conjMatrixK`
is the matrix of `id ⊗ ρ_T(τ)` in the base-changed coefficient basis. -/
theorem conjMatrixK_baseChange (A : Type) [CommRing A] [Algebra ℤ_[2] A] :
    LinearMap.toMatrix (Algebra.TensorProduct.basis A (basisK S E))
        (Algebra.TensorProduct.basis A (basisK S E))
        (LinearMap.baseChange A (rhoK S E e (tateConjQ e C))) =
      (conjMatrixK E C).map (algebraMap ℤ_[2] A) := by
  rw [LinearMap.toMatrix_baseChange, conjMatrixK_eq E e C]
  rfl

end Conj

/-! ### The conjugation matrix of the fibre duality -/

section FibreConj

open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)
  (hW : (E⁄K).map (C.κ : K →+* K) = E⁄K) (P : Ideal Lambda) [P.IsPrime]

/-- PROVED (tex 2762–2767; 2798–2805). The Tate conjugation used in fibre duality is the
transported action of the actual complex conjugation. -/
theorem conjTate_eq_rhoK (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    ZInQ.Manuscript.RC.FibreDuality.conjTate C (E⁄K) hW = rhoK S E e (tateConjQ e C) :=
  eq_rhoK_conj_of_pt E e C _ fun x n =>
    ZInQ.Manuscript.RC.FibreDuality.conjTate_pt C (E⁄K) hW x n
/-- PROVED (tex 2798–2805; 5035–5038). The fibre duality's matrix `conjMatrix` is the
coefficient specialization of `conjMatrixK`, the `J` in its cross pairing. -/
theorem conjMatrix_eq_conjMatrixK :
    ZInQ.Manuscript.RC.FibreDuality.conjMatrix C (E⁄K) hW P =
      (conjMatrixK E C).map (algebraMap ℤ_[2] (ResAt P)) := by
  rw [ZInQ.Manuscript.RC.FibreDuality.conjMatrix, conjTate_eq_rhoK E C hW (tateAlgEquiv K)]
  rfl

end FibreConj

/-! ### The realized derivative matrices in the coefficient basis -/

section RealizedK

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S) {α : GKS K S →* Lambdaˣ}
  (L : MovingLabel K S) {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
  {excl : ℕ → Finset ℕ} (D : DerivativePrimes E (tateConjQ e C) h F excl)
  (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i, h i x = x)
  (htriv : ∀ i (x : TLam K S (E⁄K) α), L.frob i • x - x ∈ tlamNbhd K S (E⁄K) α i)
  (U : Ultrafilter ℕ)

/-- definition (tex 3090–3096; 4809–4816; 5026–5032). The realized derivative stages with
rational Frobenius and `J = ρ_T(τ)` in the coefficient basis. The primes and the stage
Frobenius on `𝕋` are those of `realizedDerivative`, using the supplied derivative congruence. -/
def realizedDerivativeK : DerivativeMatrices (R := Lambda) stageIdeal U :=
  { realizedDerivative L D (tateConjQ_mul_self e C) (tateConjQ_roots e C) hh htriv U with
    rationalFrob := fun i => (rhoKMatrix S E e (D.frob i)).map (algebraMap ℤ_[2] Lambda)
    J := (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda)
    rational_congr := Eventually.of_forall fun i a b => by
      have hc := congrFun (congrFun (rhoKMatrix_congr S E e (D.tate_conj hh i)) a) b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hc
      have hz : PadicInt.toZModPow i (rhoKMatrix S E e (D.frob i) a b -
          rhoKMatrix S E e (tateConjQ e C) a b) = 0 := by
        rw [map_sub, hc, sub_self]
      have hm := algebraMap_mem_stageIdeal hz
      rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, conjMatrixK_eq E e C, ← map_sub]
      exact hm
    J_square := by
      rw [← Matrix.map_mul, conjMatrixK_sq, Matrix.map_one _ (map_zero _) (map_one _)] }

/-- PROVED (tex 3092–3093). The realized conjugation is `ρ_T(τ)` in the coefficient basis,
by the definition of `realizedDerivativeK`. -/
theorem realizedDerivativeK_J :
    (realizedDerivativeK E e C L D hh htriv U).J = (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) :=
  rfl

/-- PROVED (tex 3092–3093; 5028–5030). The realized rational Frobenius matrices are the
transported rational Tate actions. -/
theorem realizedDerivativeK_rationalFrob (i : ℕ) :
    (realizedDerivativeK E e C L D hh htriv U).rationalFrob i =
      (rhoKMatrix S E e (D.frob i)).map (algebraMap ℤ_[2] Lambda) :=
  rfl

/-- PROVED (tex 4809–4816). The realized residue characteristic is the selected rational prime. -/
theorem realizedDerivativeK_ell (i : ℕ) :
    (realizedDerivativeK E e C L D hh htriv U).ell i = ((D.ell i : ℕ) : Lambda) :=
  rfl

/-- PROVED (tex 3095–3096). The realized coefficient-basis conjugation has determinant `-1`. -/
theorem realizedDerivativeK_J_det : (realizedDerivativeK E e C L D hh htriv U).J.det = -1 := by
  rw [realizedDerivativeK_J, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_conjMatrixK,
    map_neg, map_one]

/-- PROVED (tex 4210–4213). The determinant of rational Frobenius is the selected prime,
hence agrees with the realized residue characteristic modulo the stage ideal. -/
theorem realizedDerivativeK_rationalFrob_det (i : ℕ) :
    ((realizedDerivativeK E e C L D hh htriv U).rationalFrob i).det -
      (realizedDerivativeK E e C L D hh htriv U).ell i ∈ stageIdeal i := by
  rw [realizedDerivativeK_rationalFrob, realizedDerivativeK_ell, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_rhoKMatrix, det_tateMatrix,
    ZInQ.Manuscript.RC.GlueSweep.Tate.det_tateRep_eq_of_isFrobAt E (D.odd i) (D.isFrob i),
    map_natCast, sub_self]
  exact Submodule.zero_mem _

/-- PROVED (tex 3092–3096; 3297–3309; 5026–5032). The derivative stages have inner limits
`ℓ = -1`, `q = 1`, `Φ = 1`, and rational Frobenius `J = ρ_T(τ)`, with `det J = -1`. -/
theorem realizedDerivativeK_limits (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (realizedDerivativeK E e C L D hh htriv U).ell = -1 ∧
      ulim U (fun i => (realizedDerivativeK E e C L D hh htriv U).ell i ^ 2) = 1 ∧
      ulimMat U (realizedDerivativeK E e C L D hh htriv U).phi = 1 ∧
      ulimMat U (realizedDerivativeK E e C L D hh htriv U).rationalFrob =
        (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) ∧
      (realizedDerivativeK E e C L D hh htriv U).J.det = -1 :=
  ⟨ell_limit stageIdeal_tendsToZero hU _, residueSize_limit stageIdeal_tendsToZero hU _,
    phi_limit stageIdeal_tendsToZero hU _, rationalFrob_limit stageIdeal_tendsToZero hU _,
    limitJ_det stageIdeal_tendsToZero hU _
      (Eventually.of_forall (realizedDerivativeK_rationalFrob_det E e C L D hh htriv U))⟩

/-- PROVED (tex 5026–5032). The limiting actions on the finite and singular planes are
`(J, -J)`, where `J = ρ_T(τ)` in the coefficient basis. -/
theorem realizedDerivativeK_localAction (hU : (U : Filter ℕ) ≤ cofinite) :
    (Matrix.toLin' (ulimMat U (realizedDerivativeK E e C L D hh htriv U).rationalFrob)).prodMap
      (Matrix.toLin' (ulimMat U (fun i => (realizedDerivativeK E e C L D hh htriv U).ellInv i •
        (realizedDerivativeK E e C L D hh htriv U).rationalFrob i))) =
      localLimitAction ((conjMatrixK E C).map (algebraMap ℤ_[2] Lambda)) :=
  localLimitAction_from_stages stageIdeal_tendsToZero hU _

/-- PROVED (tex 5010–5013; 5035–5038). At a coefficient fibre, the realized `J = ρ_T(τ)`
is exactly the fibre duality's `conjMatrix`. -/
theorem realizedDerivativeK_J_fibre (hW : (E⁄K).map (C.κ : K →+* K) = E⁄K)
    (P : Ideal Lambda) [P.IsPrime] :
    (realizedDerivativeK E e C L D hh htriv U).J.map
        (algebraMap Lambda (ZInQ.Manuscript.RC.Wiring.ResAt P)) =
      ZInQ.Manuscript.RC.FibreDuality.conjMatrix C (E⁄K) hW P := by
  rw [conjMatrix_eq_conjMatrixK E C hW P, realizedDerivativeK_J, Matrix.map_map]
  congr 1

end RealizedK

/-! ### Elements of `G_ℚ` fixing `K`, as elements of `G_{K,S}` -/

section Descend

open ZInQ.Manuscript.RC.SelmerComplex (resAbsCont)
open ZInQ.Manuscript.RC.CoefModules (inclS galS)

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- definition (tex 2786–2788). For `g ∈ G_ℚ` fixing the image of `K`, the conjugate
`e⁻¹ g e` as a `K`-automorphism of `K̄`, realizing the subgroup `G_K ⊂ G_ℚ`. -/
def galKOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  { (e.trans (g.trans e.symm)).toRingEquiv with
    commutes' := fun x => by
      change e.symm (g (e (algebraMap K (AlgebraicClosure K) x))) = _
      rw [hg, AlgEquiv.symm_apply_apply] }
/-- PROVED (tex 2786–2788). The descended `K`-automorphism acts by `x ↦ e⁻¹(g(e(x)))`. -/
theorem galKOfQ_apply (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (x : AlgebraicClosure K) :
    galKOfQ e g hg x = e.symm (g (e x)) :=
  rfl

/-- PROVED (tex 2786–2788). The inclusion `Gal(K̄/K) → G_ℚ` sends `galKOfQ e g` back to `g`. -/
theorem tateGalToQ_galKOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    tateGalToQ e (galKOfQ e g hg) = g := by
  ext y
  rw [tateGalToQ_apply, galKOfQ_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- definition (tex 2786–2788; 3458–3463). The restriction of `e⁻¹ g e` to `K_S`, as an
element of the coefficient Galois group `G_{K,S}`. -/
def gksOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) : GKS K S :=
  resAbsCont K S (galKOfQ e g hg)
/-- PROVED (tex 2786–2788; 3458–3463). The descended absolute automorphism lifts `gksOfQ`
along the inclusion `K_S ⊂ K̄`. -/
theorem gksOfQ_lift (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (x : KS K S) :
    galKOfQ e g hg (inclS K S x) = inclS K S (galS K S (gksOfQ S e g hg) x) :=
  (tate_isLift_iff (gksOfQ S e g hg) (galKOfQ e g hg)).mpr rfl x

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]

/-- PROVED (tex 2723–2727; 2786–2788). The Tate equivalence carries the action of the
restricted element `gksOfQ e g` to the rational Tate action `ρ_T(g)`. -/
theorem tateSEquiv_gksOfQ_smul (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (P : TateS K S (E⁄K)) :
    tateSEquiv S E e (gksOfQ S e g hg • P) = tateRep E 2 g (tateSEquiv S E e P) := by
  apply TauCeti.TateModule.ext
  intro n
  rw [proj_tateSEquiv]
  change tateTorsMap S E e n (gksOfQ S e g hg • (P : ∀ n, Lev K S (E⁄K) n) n) =
    tateProj E n (tateRep E 2 g (tateSEquiv S E e P))
  rw [tateTorsMap_smul S E e n (gksOfQ S e g hg) (galKOfQ e g hg) (gksOfQ_lift S e g hg),
    tateGalToQ_galKOfQ, tateProj_tateRep]
  rfl
/-- PROVED (tex 2723–2727; 2786–2788). Restriction to `K_S` acts on its Tate module as the
transported rational action `rhoK`. -/
theorem gksOfQ_smul_eq_rhoK (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (P : TateS K S (E⁄K)) :
    gksOfQ S e g hg • P = rhoK S E e g P := by
  apply (tateSEquiv S E e).injective
  rw [tateSEquiv_gksOfQ_smul, tateSEquiv_rhoK]

end Descend

/-! ### The square of the rational Frobenius -/

section RatSq

open ZInQ.Manuscript.RC.SelmerComplex (resAbsCont)
open ZInQ.Manuscript.RC.CoefModules (inclS galS)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)
  {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar} {excl : ℕ → Finset ℕ}
  (D : DerivativePrimes E (tateConjQ e C) h F excl)
  (hK : ∀ i (x : K), (D.frob i * D.frob i) (e (algebraMap K (AlgebraicClosure K) x)) =
    e (algebraMap K (AlgebraicClosure K) x))

/-- definition (tex 5026–5030). The square of the selected rational Frobenius, restricted
from `e⁻¹ Fr_i² e` to `K_S`, using the hypothesis that this square fixes `K`. -/
def ratSqFrob (i : ℕ) : GKS K S :=
  gksOfQ S e (D.frob i * D.frob i) (hK i)

omit [E.IsElliptic] in
/-- PROVED (tex 3090–3093). A Tate matrix congruent to `1` modulo `2^i` differs from `1`
by `2^i` times a matrix over `ℤ₂`. -/
theorem exists_sub_one_eq_two_pow_smul {i : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hM : (PadicInt.toZModPow i).mapMatrix M = 1) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℤ_[2], M - 1 = (2 : ℤ_[2]) ^ i • N := by
  have hmem : ∀ a b, (M - 1) a b ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ i} := by
    intro a b
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply, map_sub]
    have h1 := congrFun (congrFun hM a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose N hN using fun a b => Ideal.mem_span_singleton'.mp (hmem a b)
  refine ⟨Matrix.of fun a b => N a b, ?_⟩
  ext a b
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hN a b, Nat.cast_ofNat, mul_comm]

omit [HasFullTwoTorsion K S (E⁄K)] in
/-- PROVED (tex 3092–3093). Squaring the retained congruence `ρ_T(Fr_i) ≡ J`, with `J² = 1`,
makes the Tate matrix of `Fr_i²` the identity modulo `2^i`. -/
theorem tateMatrix_frob_sq_mod (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ) :
    (PadicInt.toZModPow i).mapMatrix (tateMatrix E (D.frob i * D.frob i)) = 1 := by
  rw [tateMatrix_mul, map_mul, D.tate_conj hh i, ← map_mul, ← tateMatrix_mul,
    tateConjQ_mul_self, tateMatrix_one, map_one]

/-- PROVED (tex 3092–3093; 5028–5030). The restricted rational Frobenius square acts
trivially on `T_2E / 2^i T_2E`, expressed by divisibility of its action minus the identity. -/
theorem ratSqFrob_smul_sub (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ) (P : TateS K S (E⁄K)) :
    ∃ Q : TateS K S (E⁄K), (2 : ℤ_[2]) ^ i • Q = ratSqFrob E e C D hK i • P - P := by
  obtain ⟨N, hN⟩ := exists_sub_one_eq_two_pow_smul (tateMatrix_frob_sq_mod E e C D hh i)
  let b := ZInQ.Manuscript.RC.PrintsArith.tateBasis E
  have hf : LinearMap.toMatrix b b
      (tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) =
      (2 : ℤ_[2]) ^ i • N := by
    rw [map_sub, LinearMap.toMatrix_id, ← hN]
    rfl
  have hy : ∀ y : TateMod E 2,
      ((tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) y) =
      (2 : ℤ_[2]) ^ i • Matrix.toLin b b N y := by
    intro y
    rw [← Matrix.toLin_toMatrix b b
      (tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2), hf,
      map_smul, LinearMap.smul_apply]
  refine ⟨(tateSEquiv S E e).symm (Matrix.toLin b b N (tateSEquiv S E e P)), ?_⟩
  apply (tateSEquiv S E e).injective
  rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, map_sub, ratSqFrob, tateSEquiv_gksOfQ_smul]
  rfl

variable {α : GKS K S →* Lambdaˣ}

/-- PROVED (tex 2723–2727; 3297–3309). Under the character congruence
`α(ratSqFrob D i) ≡ 1` modulo the stage ideal, the rational Frobenius square acts trivially
on the twisted quotient `𝕋 / I_i 𝕋`. -/
theorem twisted_congr_ratSqFrob (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ)
    (hα : ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (x : TLam K S (E⁄K) α) :
    ratSqFrob E e C D hK i • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  induction x using TLam.induction with
  | zero => rw [smul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul l P => exact smul_tmul_sub_mem _ i l P hα (ratSqFrob_smul_sub E e C D hK hh i P)
  | add x y hx hy =>
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy

omit [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)] in
/-- PROVED (tex 3268–3273). Trivial action on the twisted quotient `𝕋 / I_i 𝕋` is preserved
when the Frobenius element is conjugated in `G_{K,S}`. -/
theorem twisted_congr_of_conj {i : ℕ} {σ : GKS K S}
    (hσ : ∀ x : TLam K S (E⁄K) α, σ • x - x ∈ tlamNbhd K S (E⁄K) α i) (g : GKS K S)
    (x : TLam K S (E⁄K) α) : (g * σ * g⁻¹) • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  have e1 : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e1]
  exact act_mem_tlamNbhd g i (hσ (g⁻¹ • x))

/-- GLUE (tex 4809–4816; 5026–5030). The input matching each label's stage Frobenius in
`G_{K,S}` with a conjugate of the restriction of `e⁻¹ Fr_i² e`. The matching is assumed
by `htriv_of_match` and `realizedDerivativeK_of_match`, not constructed by them; for inert primes
of a quadratic field it is supplied by `frobeniusMatchesLabel_of_inert`
(`ZInQKernel/Contrib/RC53Assist/FrobeniusMatch/Arithmetic.lean`). -/
def FrobeniusMatchesLabel (L : MovingLabel K S) : Prop :=
  ∀ i, ∃ g : GKS K S, L.frob i = g * ratSqFrob E e C D hK i * g⁻¹

/-- PROVED (tex 3297–3309; 4809–4816; 5028–5030). A Frobenius match and the character
congruence imply that the label's stage Frobenius acts trivially on `𝕋 / I_i 𝕋`. -/
theorem htriv_of_match (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) :
    ∀ i (x : TLam K S (E⁄K) α), L.frob i • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  intro i x
  obtain ⟨g, hg⟩ := hL i
  rw [hg]
  exact twisted_congr_of_conj E (twisted_congr_ratSqFrob E e C D hK hh i (hα i)) g x

/-- definition (tex 3090–3096; 3297–3309; 4809–4816). The coefficient-basis derivative
stages constructed from the actual primes and the supplied Frobenius match and character
congruence. Their derivative congruence is proved by `htriv_of_match`. -/
def realizedDerivativeK_of_match (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) (U : Ultrafilter ℕ) :
    DerivativeMatrices (R := Lambda) stageIdeal U :=
  realizedDerivativeK E e C (α := α) L D hh (htriv_of_match E e C D hK hh hα L hL) U

/-- PROVED (tex 3092–3093). The stages built from a Frobenius match have conjugation
`J = ρ_T(τ)` in the coefficient basis. -/
theorem realizedDerivativeK_of_match_J (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) (U : Ultrafilter ℕ) :
    (realizedDerivativeK_of_match E e C D hK hh hα L hL U).J =
      (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) :=
  rfl

end RatSq

end ZInQ.Contrib.RC53Assist.InnerLimitArith
