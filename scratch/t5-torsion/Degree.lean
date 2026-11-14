import ZInQKernel.Contrib.AbVarBC.Main
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# t5-torsion, part 12: the count `#A(K̄)[n] = n^{2g}` from `deg [n] = n^{2g}` and separability

Mumford's route (§4, Application 2; §6): the kernel `A[n] = [n]⁻¹(0)` is a finite `K`-scheme of
degree `n^{2g}`, unramified (hence étale) when `[n]` is; an étale `K`-algebra of dimension `d` has
exactly `d` points over an algebraically closed field. In characteristic `0`, `[n]` is unramified
by the kernel's proved `MulRigidity.mulUnramified_of_kerUnitOpen kerUnitOpen`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion.Degree

/-! ## §1 Points of a finite étale algebra -/

/-- **An étale `K`-algebra of dimension `d` has `d` points in an algebraically closed field.** -/
theorem natCard_algHom_eq_finrank {K R Ω : Type} [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] [Algebra.FormallyUnramified K R] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] :
    Nat.card (R →ₐ[K] Ω) = Module.finrank K R := by
  haveI : Algebra.EssFiniteType Ω (Ω ⊗[K] R) := inferInstance
  haveI : Algebra.FormallyUnramified Ω (Ω ⊗[K] R) := inferInstance
  haveI : Algebra.FormallyEtale Ω (Ω ⊗[K] R) :=
    Algebra.FormallyEtale.iff_formallyUnramified_of_field.2 inferInstance
  rw [Nat.card_congr (AlgHom.liftEquiv K Ω R Ω),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω (Ω ⊗[K] R)),
    ← Module.finrank_baseChange (R := Ω) (S := K) (M' := R),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[K] R)).toLinearEquiv.finrank_eq]
  haveI : Finite (PrimeSpectrum (Ω ⊗[K] R)) := by
    haveI := Algebra.FormallyUnramified.finite_of_free Ω (Ω ⊗[K] R)
    haveI : IsArtinianRing (Ω ⊗[K] R) := isArtinian_of_tower Ω inferInstance
    infer_instance
  haveI := Fintype.ofFinite (PrimeSpectrum (Ω ⊗[K] R))
  rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-! ## §2 The kernel `A[n]` and its points -/

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

/-- `[n] : A → A` as a morphism of schemes. -/
noncomputable abbrev mulN (n : ℕ) : A.X.left ⟶ A.X.left :=
  (((n : ℤ) : PkgI3.AbVar.End A).hom).left

/-- The unit section `Spec K → A`. -/
noncomputable abbrev unitS : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

/-- **The kernel `A[n] = [n]⁻¹(0)`** (scheme-theoretic fibre of `[n]` over the origin). -/
noncomputable abbrev kerN (n : ℕ) : Scheme := pullback (mulN A n) (unitS A)

/-- Its structure map to `Spec K`. -/
noncomputable abbrev kerToK (n : ℕ) : kerN A n ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (mulN A n) (unitS A)

theorem fst_comp_hom (n : ℕ) :
    pullback.fst (mulN A n) (unitS A) ≫ A.X.hom = kerToK A n := by
  have hw : mulN A n ≫ A.X.hom = A.X.hom := Over.w ((n : ℤ) : PkgI3.AbVar.End A).hom
  have he : unitS A ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]

variable (Ω : Type) [Field Ω] [Algebra K Ω]

/-- `Spec Ω → Spec K`. -/
noncomputable abbrev sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- **`A(Ω)[n]` = the `Ω`-points of the kernel over `K`.** -/
theorem natCard_torsion_eq_kerPts (n : ℕ) :
    Nat.card {x : A.Pt Ω // x ^ n = 1} =
      Nat.card {z : Spec (CommRingCat.of Ω) ⟶ kerN A n // z ≫ kerToK A n = sΩ Ω} := by
  have hcond : ∀ x : A.Pt Ω, x ^ n = 1 → x.left ≫ mulN A n = sΩ Ω ≫ unitS A := by
    intro x hx
    have h1 : x ≫ ((n : ℤ) : PkgI3.AbVar.End A).hom = 1 := by
      rw [ZInQ.Contrib.AbVarBC.comp_natCast_hom, hx]
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  let F : {x : A.Pt Ω // x ^ n = 1} →
      {z : Spec (CommRingCat.of Ω) ⟶ kerN A n // z ≫ kerToK A n = sΩ Ω} := fun x =>
    ⟨pullback.lift x.1.left (sΩ Ω) (hcond x.1 x.2), pullback.lift_snd _ _ _⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      have h1 := congrArg (fun z => z.1 ≫ pullback.fst (mulN A n) (unitS A)) h
      have hx : (F x).1 ≫ pullback.fst (mulN A n) (unitS A) = x.1.left := pullback.lift_fst _ _ _
      have hy : (F y).1 ≫ pullback.fst (mulN A n) (unitS A) = y.1.left := pullback.lift_fst _ _ _
      exact Subtype.ext (Over.OverMorphism.ext (hx.symm.trans (h1.trans hy)))
    · rintro ⟨z, hz⟩
      let x : A.Pt Ω := Over.homMk (z ≫ pullback.fst (mulN A n) (unitS A)) (by
        change (z ≫ pullback.fst (mulN A n) (unitS A)) ≫ A.X.hom = _
        rw [Category.assoc, fst_comp_hom, hz]
        rfl)
      have hx : x ^ n = 1 := by
        rw [← ZInQ.Contrib.AbVarBC.comp_natCast_hom]
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Hom.one_def]
        change (z ≫ pullback.fst (mulN A n) (unitS A)) ≫ mulN A n = _
        rw [Category.assoc, pullback.condition, ← Category.assoc, hz]
        rfl
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans rfl
      · exact (pullback.lift_snd _ _ _).trans hz.symm
  exact Nat.card_congr (Equiv.ofBijective F hF)

/-- **`Ω`-points of `Spec R` over `K` = `K`-algebra maps `R → Ω`.** -/
theorem natCard_specPts (R : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ R) :
    letI := φ.hom.toAlgebra
    Nat.card {w : Spec (CommRingCat.of Ω) ⟶ Spec R // w ≫ Spec.map φ = sΩ Ω} =
      Nat.card (R →ₐ[K] Ω) := by
  letI := φ.hom.toAlgebra
  let F : (R →ₐ[K] Ω) → {w : Spec (CommRingCat.of Ω) ⟶ Spec R // w ≫ Spec.map φ = sΩ Ω} :=
    fun f => ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
      rw [← Spec.map_comp]
      congr 1
      ext c
      exact f.commutes c⟩
  have hF : Function.Bijective F := by
    constructor
    · intro f f' h
      have h1 := Spec.map_injective (congrArg Subtype.val h)
      ext r
      exact congrArg (fun ψ : R ⟶ CommRingCat.of Ω => ψ r) h1
    · rintro ⟨w, hw⟩
      let ψ := Spec.preimage w
      have hψ : Spec.map ψ = w := Spec.map_preimage w
      have hcomp : φ ≫ ψ = CommRingCat.ofHom (algebraMap K Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, hw]
      let f : R →ₐ[K] Ω :=
        { ψ.hom with
          commutes' := fun c => congrArg (fun χ : CommRingCat.of K ⟶ CommRingCat.of Ω => χ c)
            hcomp }
      exact ⟨f, Subtype.ext hψ⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm

/-! ## §3 The leaves and the count -/

/-- **Leaf candidate `KernelDegree` (`deg [n] = n^{2g}`, fibre form).** For an abelian variety of
dimension `g` over `K` and `n ≥ 1` invertible in `K`, the kernel `A[n] = [n]⁻¹(0)` is affine,
`Spec R` with `R` a `K`-algebra of dimension `n^{2g}`. Mumford, *Abelian varieties*, §6
Application 2 (`deg n_X = n^{2g}`) with flatness of isogenies (§7), so every fibre has length
`n^{2g}` (locators UNVERIFIED). A consequence of the published statements. -/
def KernelDegree : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (g n : ℕ), A.dim = (g : WithBot ℕ∞) → 0 < n →
    (n : K) ≠ 0 →
    ∃ (R : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ R) (e : kerN A n ≅ Spec R),
      e.hom ≫ Spec.map φ = kerToK A n ∧
        (letI := φ.hom.toAlgebra; Module.finrank K R = n ^ (2 * g))

/-- **Leaf candidate `MulUnramifiedAll` (separability of `[n]`).** `[n]` is unramified when `n` is
invertible in `K` (Mumford §4 / §6 Application 2: `n_X` separable iff `char k ∤ n`; Milne,
*Abelian varieties*, Thm 8.2; locators UNVERIFIED). Proved in characteristic `0` (below). -/
def MulUnramifiedAll : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    FormallyUnramified (mulN A n)

/-- **The count from the degree and separability** (glue). -/
theorem natCard_torsion_of_degree (hD : KernelDegree) {K : Type} [Field K] (A : PkgI3.AbVar K)
    (g n : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (hU : FormallyUnramified (mulN A n)) :
    Nat.card {x : A.Pt (AlgebraicClosure K) // x ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨R, φ, e, he, hrank⟩ := hD K A g n hg hn hnK
  letI := φ.hom.toAlgebra
  have hsnd : FormallyUnramified (kerToK A n) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback (mulN A n) (unitS A)) hU
  have hφU : FormallyUnramified (Spec.map φ) := by
    have hsq : CommSq e.inv (Spec.map φ) (kerToK A n) (𝟙 _) :=
      ⟨by rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc]⟩
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_horiz_isIso hsq) hsnd
  have hRU : Algebra.FormallyUnramified K R := by
    have := (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hφU
    exact this
  have hpos : 0 < Module.finrank K R := by rw [hrank]; positivity
  haveI : Module.Finite K R := Module.finite_of_finrank_pos hpos
  rw [natCard_torsion_eq_kerPts]
  have h2 : Nat.card {z : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ kerN A n //
      z ≫ kerToK A n = sΩ (AlgebraicClosure K)} =
      Nat.card {w : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec R //
        w ≫ Spec.map φ = sΩ (AlgebraicClosure K)} := by
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ e.hom, by rw [Category.assoc, he]; exact z.2⟩
        invFun := fun w => ⟨w.1 ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact w.2⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
  rw [h2, natCard_specPts, natCard_algHom_eq_finrank, hrank]

/-- **`[n]` is unramified in characteristic `0`** (the kernel's `kerUnitOpen`). -/
theorem mulUnramified_charZero [CharZero K] (n : ℕ) (hn : 0 < n) :
    FormallyUnramified (mulN A n) :=
  ZInQ.Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen ZInQ.Contrib.AbVarBC.kerUnitOpen
    K A (n : ℤ) (by exact_mod_cast hn.ne')

/-- **The count in characteristic `0` from `KernelDegree` alone.** -/
theorem natCard_torsion_of_degree_charZero (hD : KernelDegree) [CharZero K] (g n : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (hn : 0 < n) :
    Nat.card {x : A.Pt (AlgebraicClosure K) // x ^ n = 1} = n ^ (2 * g) :=
  natCard_torsion_of_degree hD A g n hg hn (Nat.cast_ne_zero.2 hn.ne')
    (mulUnramified_charZero A n hn)

end T5Torsion.Degree

#print axioms T5Torsion.Degree.natCard_algHom_eq_finrank
#print axioms T5Torsion.Degree.natCard_torsion_of_degree
#print axioms T5Torsion.Degree.natCard_torsion_of_degree_charZero
