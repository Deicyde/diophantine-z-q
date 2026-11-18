import ActualResidueTorusThird
import IntegralResidueActionsSecond

/-!
# Actual residue torus points and one native Frobenius multiplier

The torus naturality witness is the intrinsic semistability presentation,
not an eigenaction hypothesis. The verified spread-out theorem fixes one
period; the actual residue Frobenius of the same original arithmetic lift
then acts by q^r on torus points for every common multiple. The point-domain
comparison is an actual identity-underlying over-isomorphism, whose scalar
map was proved equal to the original residue base map.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SemistableGeometry.ActualTorusMultiplier

open SemistableGeometry.ActualResidueTorus
open SemistableGeometry.SpecialPointBinding
open SemistableGeometry.IntegralResidueActions
open RaynaudWild.FrobDescent

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- The original native residue action has the exact q^r-power law. -/
theorem residueAction_power_law (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (a : IsLocalRing.ResidueField w) :
    residueRingAction w (σ ^ r) (pow_mem hD r) a =
      a ^ (Nat.card (IsLocalRing.ResidueField O) ^ r) :=
  FrobLift.residue_toRingAut_apply (pow_mem hD r) (FrobLift.pow_congr hD hcong r) a

/-- The actual residue action intertwines the geometric torus point domain by the explicit comparison. -/
theorem native_action_domain_covariance (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) (r : ℕ) :
    letI : Finite (IsLocalRing.ResidueField O) := FrobLift.finite_residueField O
    letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
    specialActionArrow hw (σ ^ r) (pow_mem hD r) ≫ (torusDomainIso hw).inv =
      (torusDomainIso hw).inv ≫
        frobPt (k := IsLocalRing.ResidueField O)
          (Ω := AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) r
          (residueRingAction w (σ ^ r) (pow_mem hD r)) (residueAction_power_law σ hD hcong r) := by
  letI : Finite (IsLocalRing.ResidueField O) := FrobLift.finite_residueField O
  letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (residueRingAction w (σ ^ r) (pow_mem hD r))) ≫ 𝟙 _ =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (residueRingAction w (σ ^ r) (pow_mem hD r)))
  rw [Category.comp_id, Category.id_comp]

/-- The actual torus coordinate point is transported into the literal native residue domain. -/
def actualTorusPoint (hw : w.comap (algebraMap K Ω) = O)
    (U : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj U] (rk : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      letI := algK' (φbar' (IsLocalRing.ResidueField O)) R
      (Fin rk → Rˣ) →* (algPt' (IsLocalRing.ResidueField O) R ⟶ U))
    (t : Fin rk → (IsLocalRing.ResidueField w)ˣ) : specialDomain hw ⟶ U := by
  letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
  exact (torusDomainIso hw).inv ≫ e (IsLocalRing.ResidueField w) t

/-- The intrinsic natural torus presentation gives the actual original Frobenius multiplier, not a supplied eigenaction. -/
theorem actual_torus_frobenius_multiplier (hw : w.comap (algebraMap K Ω) = O)
    (U : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj U]
    [LocallyOfFinitePresentation U.hom] (rk : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      letI := algK' (φbar' (IsLocalRing.ResidueField O)) R
      (Fin rk → Rˣ) →* (algPt' (IsLocalRing.ResidueField O) R ⟶ U))
    (he : ResTTorusNat (IsLocalRing.ResidueField O) U rk e)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) :
    ∃ n : ℕ, ∀ j : ℕ, ∀ t : Fin rk → (IsLocalRing.ResidueField w)ˣ,
      specialActionArrow hw (σ ^ (n.factorial * j)) (pow_mem hD _) ≫ actualTorusPoint hw U rk e t =
        actualTorusPoint hw U rk e t ^ (Nat.card (IsLocalRing.ResidueField O) ^ (n.factorial * j)) := by
  letI : Finite (IsLocalRing.ResidueField O) := FrobLift.finite_residueField O
  letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
  obtain ⟨n, hn⟩ := resT_frob_pow (IsLocalRing.ResidueField O) U rk e he
  refine ⟨n, ?_⟩
  intro j t
  change specialActionArrow hw (σ ^ (n.factorial * j)) (pow_mem hD _) ≫
      ((torusDomainIso hw).inv ≫ e (IsLocalRing.ResidueField w) t) =
    ((torusDomainIso hw).inv ≫ e (IsLocalRing.ResidueField w) t) ^
      (Nat.card (IsLocalRing.ResidueField O) ^ (n.factorial * j))
  let p : kPt (k := IsLocalRing.ResidueField O)
      (Ω := AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) ⟶ U :=
    e (IsLocalRing.ResidueField w) t
  have hc := native_action_domain_covariance hw σ hD hcong (n.factorial * j)
  have hce := congrArg (fun f : specialDomain hw ⟶
      kPt (k := IsLocalRing.ResidueField O) (Ω := AlgebraicClosure (IsLocalRing.ResidueField O))
        (IsLocalRing.ResidueField w) ↦ f ≫ p) hc
  have hq := hn j (IsLocalRing.ResidueField w)
    (residueRingAction w (σ ^ (n.factorial * j)) (pow_mem hD _))
    (residueAction_power_law σ hD hcong (n.factorial * j)) t
  have hqe := congrArg (fun f : kPt (k := IsLocalRing.ResidueField O)
      (Ω := AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) ⟶ U ↦
        (torusDomainIso hw).inv ≫ f) hq
  exact (Category.assoc _ _ _).symm.trans
    (hce.trans ((Category.assoc _ _ _).trans (hqe.trans (MonObj.comp_pow _ _ _))))

end SemistableGeometry.ActualTorusMultiplier
