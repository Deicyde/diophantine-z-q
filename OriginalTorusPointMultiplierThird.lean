import NativeSpecialPointPowersSecond
import CommonNativeModelDataFirst

/-!
# Reflecting the actual torus Frobenius multiplier to original points

The actual reduction and the actual special-fibre pullback preserve powers.
For integral prime-power torsion, equality of the two genuine reductions
reflects upstairs by the derived henselian torsion uniqueness theorem.
The torus multiplier is first derived on the intrinsic presented torus,
then transported to the ORIGINAL generic abelian point action. No desired
generic multiplier, injectivity or lifting premise is supplied.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.OriginalTorusPointMultiplier

open SemistableGeometry.IntegralGalois
open SemistableGeometry.IntegralResidueActions
open SemistableGeometry.SpecialPointBinding
open SemistableGeometry.NativeSpecialPointPowers
open SemistableGeometry.ActualTorusMultiplier
open RaynaudWild.FrobDescent

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- The ORIGINAL generic-point map preserves powers through its actual group isomorphism. -/
theorem originalPoint_pow {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (a : valuationDomain w hw ⟶ N) (q : ℕ) :
    originalPoint N gen w hw (a ^ q) = originalPoint N gen w hw a ^ q :=
  map_pow (NeronInvariantTorsion.genericFibreHom O w hw gen hgen) a q

/-- Native special-fibre reduction preserves every actual integral point power. -/
theorem reduction_special_pow (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    (a : valuationDomain w hw ⟶ N) (q : ℕ) :
    letI : GrpObj (specialFibre N) := Functor.grpObjObj
    specialPoint hw N (reductionArrow w hw ≫ a ^ q) =
      specialPoint hw N (reductionArrow w hw ≫ a) ^ q := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  rw [MonObj.comp_pow, specialPoint_pow]

/-- Equality between the twisted reduction and a power reflects to the ORIGINAL generic point. -/
theorem original_twisted_power_of_reduction {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom] [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : O)) (n : ℕ)
    (ψ : Ω ≃ₐ[K] Ω) (hD : ψ ∈ w.decompositionSubgroup K) (q : ℕ)
    (a : valuationDomain w hw ⟶ N) (ha : a ^ (ℓ ^ n) = 1)
    (hred : letI : GrpObj (specialFibre N) := Functor.grpObjObj
      specialActionArrow hw ψ hD ≫ specialPoint hw N (reductionArrow w hw ≫ a) =
        specialPoint hw N (reductionArrow w hw ≫ a) ^ q) :
    A.galAct ψ (originalPoint N gen w hw a) = originalPoint N gen w hw a ^ q := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hact : (valuationActionArrow w hw ψ hD ≫ a) ^ (ℓ ^ n) = 1 := by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  have hpow : (a ^ q) ^ (ℓ ^ n) = 1 := by
    rw [← pow_mul, mul_comm q (ℓ ^ n), pow_mul, ha, one_pow]
  have hsact : specialPoint hw N (reductionArrow w hw ≫ (valuationActionArrow w hw ψ hD ≫ a)) =
      specialActionArrow hw ψ hD ≫ specialPoint hw N (reductionArrow w hw ≫ a) := by
    rw [← Category.assoc, ← reductionArrow_covariance, Category.assoc]
    exact (specialPoint_covariance hw N ψ hD (reductionArrow w hw ≫ a)).symm
  have hres : reductionArrow w hw ≫ (valuationActionArrow w hw ψ hD ≫ a) =
      reductionArrow w hw ≫ a ^ q := by
    apply specialPoint_injective hw N
    exact hsact.trans (hred.trans (reduction_special_pow w hw N a q).symm)
  have hu : IsUnit ((ℓ ^ n : ℕ) : O) := by
    rw [Nat.cast_pow]
    exact hℓ.pow n
  have heq := HenselDivision.valuation_point_torsion_eq_of_reduction w hw N
    (ℓ ^ n) (ℓ ^ n) hu hu (reductionArrow w hw) rfl
    (valuationActionArrow w hw ψ hD ≫ a) (a ^ q) hact hpow hres
  rw [← originalPoint_covariance N gen w hw ψ hD a, heq, originalPoint_pow N gen hgen]

/-- Postcomposition by an intrinsic group homomorphism preserves actual point powers. -/
theorem point_pow_comp {k : Type} [Field k]
    (D U V : Over (Spec (CommRingCat.of k))) [GrpObj U] [GrpObj V]
    (inc : U ⟶ V) [IsMonHom inc] (a : D ⟶ U) (q : ℕ) :
    (a ^ q) ≫ inc = (a ≫ inc) ^ q := by
  induction q with
  | zero => simpa only [pow_zero] using MonObj.one_comp inc
  | succ q ih => rw [pow_succ, MonObj.mul_comp, ih, pow_succ]

/-- A derived common torus period gives the multiplier on ORIGINAL generic torsion points reducing into that torus. -/
theorem exists_period_original_torus_multiplier {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom] [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : O))
    (U : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj U]
    (inc : U ⟶ specialFibre N)
    (hinc : letI : GrpObj (specialFibre N) := Functor.grpObjObj; IsMonHom inc)
    [IsOpenImmersion inc.left] (rk : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      letI := algK' (φbar' (IsLocalRing.ResidueField O)) R
      (Fin rk → Rˣ) →* (algPt' (IsLocalRing.ResidueField O) R ⟶ U))
    (he : ResTTorusNat (IsLocalRing.ResidueField O) U rk e)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) :
    ∃ p : ℕ, 0 < p ∧ ∀ r : ℕ, 0 < r → ∀ n : ℕ, ∀ a : valuationDomain w hw ⟶ N,
      a ^ (ℓ ^ n) = 1 →
      (∃ t : Fin rk → (IsLocalRing.ResidueField w)ˣ,
        specialPoint hw N (reductionArrow w hw ≫ a) = actualTorusPoint hw U rk e t ≫ inc) →
      A.galAct (σ ^ (p * r)) (originalPoint N gen w hw a) =
        originalPoint N gen w hw a ^ (Nat.card (IsLocalRing.ResidueField O) ^ (p * r)) := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  letI : IsMonHom inc := hinc
  letI : LocallyOfFinitePresentation (specialFibre N).hom := lfp_baseChange_of_smooth N
  letI : LocallyOfFinitePresentation U.hom := lfp_of_openImmersion inc
  obtain ⟨m, hm⟩ := actual_torus_frobenius_multiplier hw U rk e he σ hD hcong
  refine ⟨m.factorial, Nat.factorial_pos m, ?_⟩
  intro r hr n a ha ht
  obtain ⟨t, ht⟩ := ht
  apply original_twisted_power_of_reduction N gen hgen hN w hw ℓ hℓ n
    (σ ^ (m.factorial * r)) (pow_mem hD _) _ a ha
  rw [ht, ← Category.assoc, hm r t]
  exact point_pow_comp _ U (specialFibre N) inc (actualTorusPoint hw U rk e t) _

end SemistableGeometry.OriginalTorusPointMultiplier
