import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L1.DualInterface

/-!
# B3: descent through the actual finite-flat stabilizer quotient

The quotient's existence is an explicitly labelled ordinary input. No quotient,
group law, or abelian-variety property is installed as a desired Fact.
The kernel pair is the exact `H.K × A` action from `L1.StabilizerQuotient`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- INTERNAL UNPROVED INPUT: existence of the actual finite-flat quotient scheme.
This is a named ordinary hypothesis for downstream lemmas, not an instance. -/
def FiniteStabilizerQuotientExists : Prop :=
  ∀ {k : Type} [Field k] [CharZero k] (A : PkgI3.AbVar k)
    (L : A.X.left.Pic) (H : L1.FiniteStabilizerScheme A L),
    Nonempty (L1.StabilizerQuotient A L H)

/-- A map constant on the actual kernel pair descends through a finite-flat quotient. -/
theorem exists_desc_over_of_kernelPair {S : Scheme} {A Q T R : Over S}
    (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (t s : R ⟶ A) (hp : IsPullback t s q q)
    (f : A ⟶ T) (hf : t ≫ f = s ≫ f) : ∃ g : Q ⟶ T, q ≫ g = f := by
  haveI : Epi q.left := Flat.epi_of_flat_of_surjective q.left
  have hpl : IsPullback t.left s.left q.left q.left := hp.map (Over.forget S)
  have hfl : t.left ≫ f.left = s.left ≫ f.left := congrArg Over.Hom.left hf
  obtain ⟨g, hg⟩ := IsRegularEpi.exists_of_isKernelPair q.left hpl f.left hfl
  have hw : g ≫ T.hom = Q.hom := by
    apply (cancel_epi q.left).1
    rw [← Category.assoc, hg, Over.w, Over.w]
  refine ⟨Over.homMk g hw, ?_⟩
  exact Over.OverMorphism.ext hg

/-- A finite-flat surjection is an epimorphism in the actual slice category. -/
theorem epi_over_of_flat_surjective {S : Scheme} {A Q : Over S} (q : A ⟶ Q)
    [Flat q.left] [Surjective q.left] : Epi q := by
  haveI : Epi q.left := Flat.epi_of_flat_of_surjective q.left
  exact Over.epi_of_epi_left q

/-- Finite/flat/surjective morphisms stay so under the actual Cartesian tensor product. -/
theorem tensor_fpqc {S : Scheme} {A Q B V : Over S} (q : A ⟶ Q) (r : B ⟶ V)
    [IsFinite q.left] [IsFinite r.left] [Flat q.left] [Flat r.left]
    [Surjective q.left] [Surjective r.left] :
    IsFinite (q ⊗ₘ r).left ∧ Flat (q ⊗ₘ r).left ∧ Surjective (q ⊗ₘ r).left := by
  rw [Over.tensorHom_left]
  exact ⟨MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance (Over.w q).symm (Over.w r).symm,
    MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance (Over.w q).symm (Over.w r).symm,
    MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance (Over.w q).symm (Over.w r).symm⟩

section KernelPair

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [HasPullbacks C]
    {R A Q : C} (t s : R ⟶ A) (q : A ⟶ Q) (hp : IsPullback t s q q)

include hp in
/-- Products of the exact kernel-pair diagram remain exact kernel-pair diagrams. -/
theorem tensor_kernelPair : IsPullback (t ⊗ₘ t) (s ⊗ₘ s) (q ⊗ₘ q) (q ⊗ₘ q) := by
  have hw : (t ⊗ₘ t) ≫ (q ⊗ₘ q) = (s ⊗ₘ s) ≫ (q ⊗ₘ q) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hp.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c => lift
      (hp.lift (c.fst ≫ fst A A) (c.snd ≫ fst A A) (by
        have h := congrArg (· ≫ fst Q Q) c.condition
        simpa only [Category.assoc, tensorHom_fst] using h))
      (hp.lift (c.fst ≫ snd A A) (c.snd ≫ snd A A) (by
        have h := congrArg (· ≫ snd Q Q) c.condition
        simpa only [Category.assoc, tensorHom_snd] using h)))
    (fun c => by ext <;> simp)
    (fun c => by ext <;> simp)
    (fun c m hm₁ hm₂ => by
      ext
      · apply hp.hom_ext
        · simpa [Category.assoc] using congrArg (· ≫ fst A A) hm₁
        · simpa [Category.assoc] using congrArg (· ≫ fst A A) hm₂
      · apply hp.hom_ext
        · simpa [Category.assoc] using congrArg (· ≫ snd A A) hm₁
        · simpa [Category.assoc] using congrArg (· ≫ snd A A) hm₂))

end KernelPair

lemma tensor_comp_mul_eq {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {R G : C} [MonObj G] (f : R ⟶ G) :
    (f ⊗ₘ f) ≫ μ[G] = fst R R ≫ f * snd R R ≫ f := by
  rw [Hom.mul_def]
  congr 1
  ext <;> simp

section QuotientOperations

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L) (Q : L1.StabilizerQuotient A L H)

/-- The exact stabilizer action in the supplied quotient relation. -/
abbrev quotientTarget : H.K ⊗ A.X ⟶ A.X := fst H.K A.X ≫ H.j * snd H.K A.X

/-- A product of two quotient arrows in `H.K × A` is again a quotient arrow. -/
def quotientRelationMul : (H.K ⊗ A.X) ⊗ (H.K ⊗ A.X) ⟶ H.K ⊗ A.X :=
  lift ((fst _ _ ≫ fst _ _) * (snd _ _ ≫ fst _ _))
    ((fst _ _ ≫ snd _ _) * (snd _ _ ≫ snd _ _))

lemma quotientRelationMul_target : quotientRelationMul A L H ≫ quotientTarget A L H =
    (quotientTarget A L H ⊗ₘ quotientTarget A L H) ≫ μ[A.X] := by
  rw [tensor_comp_mul_eq]
  simp only [quotientRelationMul, quotientTarget, MonObj.comp_mul, lift_fst_assoc,
    lift_snd, MonObj.mul_comp, Category.assoc]
  ac_rfl

lemma quotientRelationMul_source : quotientRelationMul A L H ≫ snd H.K A.X =
    (snd H.K A.X ⊗ₘ snd H.K A.X) ≫ μ[A.X] := by
  rw [quotientRelationMul, lift_snd, tensor_comp_mul_eq]

/-- Multiplication descends from the actual group scheme to its quotient scheme. -/
theorem exists_quotientMul : ∃ m : Q.Q ⊗ Q.Q ⟶ Q.Q,
    (Q.q ⊗ₘ Q.q) ≫ m = μ[A.X] ≫ Q.q := by
  obtain ⟨hf, hflat, hs⟩ := tensor_fpqc Q.q Q.q
  haveI := hf
  haveI := hflat
  haveI := hs
  refine exists_desc_over_of_kernelPair (Q.q ⊗ₘ Q.q)
    (quotientTarget A L H ⊗ₘ quotientTarget A L H)
    (snd H.K A.X ⊗ₘ snd H.K A.X) (tensor_kernelPair _ _ _ Q.kernelPair) (μ[A.X] ≫ Q.q) ?_
  calc
    (quotientTarget A L H ⊗ₘ quotientTarget A L H) ≫ μ[A.X] ≫ Q.q =
        quotientRelationMul A L H ≫ quotientTarget A L H ≫ Q.q := by
          simpa only [Category.assoc] using
            congrArg (· ≫ Q.q) (quotientRelationMul_target A L H).symm
    _ = quotientRelationMul A L H ≫ snd H.K A.X ≫ Q.q := by rw [Q.kernelPair.w]
    _ = (snd H.K A.X ⊗ₘ snd H.K A.X) ≫ μ[A.X] ≫ Q.q := by
      rw [← Category.assoc, quotientRelationMul_source, Category.assoc]

/-- Inversion descends along the same exact kernel-pair relation. -/
theorem exists_quotientInv : ∃ v : Q.Q ⟶ Q.Q, Q.q ≫ v = ι[A.X] ≫ Q.q := by
  let u : H.K ⊗ A.X ⟶ H.K ⊗ A.X :=
    lift (fst H.K A.X)⁻¹ (snd H.K A.X)⁻¹
  have ht : u ≫ quotientTarget A L H = (quotientTarget A L H)⁻¹ := by
    simp [u, quotientTarget, MonObj.comp_mul, GrpObj.inv_comp, mul_inv_rev, mul_comm]
  have hs : u ≫ snd H.K A.X = (snd H.K A.X)⁻¹ := by simp [u]
  refine exists_desc_over_of_kernelPair Q.q (quotientTarget A L H) (snd H.K A.X)
    Q.kernelPair (ι[A.X] ≫ Q.q) ?_
  change (quotientTarget A L H)⁻¹ ≫ Q.q = (snd H.K A.X)⁻¹ ≫ Q.q
  rw [← ht, ← hs, Category.assoc, Category.assoc, Q.kernelPair.w]

end QuotientOperations

end ZInQ.Contrib.CloudR2Poincare.L4
