import ZInQKernel.Contrib.HomUnify.Corr
import ZInQKernel.HDecomp.Analytic.Hom

/-!
# av-split, row H-69 (`ZInQ.HomUnify.HomLatticeCorr`)

The row is imported from `ZInQKernel/Contrib/HomUnify/Corr.lean` (unchanged). It is the
conjunction of a lifting half (`HomLinearLift`, every `K`, `σ`) and a realization half over `ℂ`
(`corr_iff_lift_realize`, kernel). The published theorem behind the lifting half,
Birkenhake–Lange Prop. 1.2.1 (a holomorphic homomorphism of complex tori is induced by a unique
`ℂ`-linear map preserving the lattices), is **already a theorem of the kernel**:
`BPAnalytic.exists_complexLinear_lift` (`ZInQKernel/HDecomp/Analytic/Hom.lean`, bp-analytic, by
covering theory). So no leaf is needed for it. What remains:

* GLUE `UnifHoloLift`: for analytic uniformizations in leaf-push2's (weak) sense, the kernels are
  discrete and the torus map induced by an algebraic homomorphism is holomorphic;
* GLUE `ZInQ.HomUnify.HomRealize` (kernel definition): the realization half, existence form
  (GAGA/Chow content).

`homLatticeCorr_of` proves the row from these two.
-/

noncomputable section

set_option linter.style.haveILetI false

open scoped Manifold
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AvSplit.HomLattice

open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)
open BPAnalytic (Torus proj)

/-- The torus map `F : ℂ^g/Λ_A → ℂ^h/Λ_B` is induced by `f : A → B` through `Φ_A`, `Φ_B`. -/
def Induces {K : Type} [Field K] {A B : AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ) (f : AbVar.Hom A B)
    (F : Torus ΛA →+ Torus ΛB) : Prop :=
  ∀ z w, F (proj ΛA z) = proj ΛB w → ΦB w = ΦA z ≫ f.hom

/-- **GLUE `UnifHoloLift` (algebraic homomorphisms are holomorphic on the tori).** For abelian
varieties `A`, `B` over `K`, `σ : K → ℂ` and analytic uniformizations `Φ_A`, `Φ_B` in
leaf-push2's sense (`g = dim A`, `h = dim B`), the kernels `Λ_A`, `Λ_B` are discrete and every
group homomorphism `F : ℂ^g/Λ_A → ℂ^h/Λ_B` induced by a homomorphism `f : A → B` is holomorphic
(for the complex-manifold structure of bp-analytic's `Torus`). Content (not printed in this form):
leaf-push2's `IsUniformization` only says that `Φ` is a surjective homomorphism with kernel `Λ`,
that preimages of Zariski opens are open and that regular functions are holomorphic along `Φ`.
What it needs: local holomorphic coordinates on `A(ℂ)` given by regular functions (`A` smooth of
dimension `g`: an étale map to `𝔸^g` near each point, then the holomorphic inverse function
theorem), and that the topology defined by regular functions makes `A(ℂ)` compact Hausdorff
(`A` proper; Serre, GAGA, §2, Prop. 6 / SGA 1 XII 3.2, UNVERIFIED), so that `ℂ^g/Λ → A(ℂ)^an` is a
homeomorphism; then `f` is holomorphic in these coordinates (regular functions pull back to
regular functions). Equivalently: every weak uniformization is bp-analytic's strong
`BPAnalytic.Uniformization.IsUniformization` composed with a `ℂ`-linear isomorphism. -/
def UnifHoloLift : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∃ _ : DiscreteTopology ΛA, ∃ _ : DiscreteTopology ΛB,
      ∀ (f : AbVar.Hom A B) (F : Torus ΛA →+ Torus ΛB), Induces ΦA ΦB f F →
        MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin h → ℂ) F

section Lift

variable {K : Type} [Field K] {A B : AbVar K} {σ : K →+* ℂ} {g h : ℕ}
  {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
  {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}

/-- `Φ` as an additive map `ℂ^g → A(ℂ)`. -/
def addΦ (hU : IsUniformization σ ΛA ΦA) : (Fin g → ℂ) →+ Additive (CPts A σ) where
  toFun z := Additive.ofMul (ΦA z)
  map_zero' := congrArg Additive.ofMul ((hU.2.1 0).2 ΛA.zero_mem)
  map_add' z w := congrArg Additive.ofMul (hU.1 z w)

/-- `Φ` descends to the torus. -/
def barΦ (hU : IsUniformization σ ΛA ΦA) : Torus ΛA →+ Additive (CPts A σ) :=
  QuotientAddGroup.lift ΛA.toAddSubgroup (addΦ hU) (fun z hz =>
    congrArg Additive.ofMul ((hU.2.1 z).2 hz))

theorem barΦ_proj (hU : IsUniformization σ ΛA ΦA) (z : Fin g → ℂ) :
    barΦ hU (proj ΛA z) = Additive.ofMul (ΦA z) := rfl

theorem barΦ_bijective (hU : IsUniformization σ ΛA ΦA) : Function.Bijective (barΦ hU) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun P => ?_⟩
  · obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    have h1 : ΦA z = 1 := congrArg Additive.toMul hq
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hU.2.1 z).1 h1)
  · obtain ⟨z, hz⟩ := hU.2.2.1 (Additive.toMul P)
    exact ⟨proj ΛA z, by rw [barΦ_proj, hz]; rfl⟩

/-- `Φ̄ : ℂ^g/Λ ≃+ A(ℂ)_σ`. -/
def eΦ (hU : IsUniformization σ ΛA ΦA) : Torus ΛA ≃+ Additive (CPts A σ) :=
  AddEquiv.ofBijective (barΦ hU) (barΦ_bijective hU)

/-- The torus map induced by `f` (as a group homomorphism). -/
def torusMap (hUA : IsUniformization σ ΛA ΦA) (hUB : IsUniformization σ ΛB ΦB)
    (f : AbVar.Hom A B) : Torus ΛA →+ Torus ΛB :=
  QuotientAddGroup.lift ΛA.toAddSubgroup
    { toFun := fun z => (eΦ hUB).symm (Additive.ofMul (ΦA z ≫ f.hom))
      map_zero' := by
        rw [(hUA.2.1 0).2 ΛA.zero_mem, MonObj.one_comp]
        exact (eΦ hUB).symm.map_zero
      map_add' := fun z w => by
        rw [hUA.1 z w, MonObj.mul_comp]
        exact (eΦ hUB).symm.map_add _ _ }
    (fun z hz => by
      change (eΦ hUB).symm (Additive.ofMul (ΦA z ≫ f.hom)) = 0
      rw [(hUA.2.1 z).2 hz, MonObj.one_comp]
      exact (eΦ hUB).symm.map_zero)

theorem torusMap_induces (hUA : IsUniformization σ ΛA ΦA) (hUB : IsUniformization σ ΛB ΦB)
    (f : AbVar.Hom A B) : Induces ΦA ΦB f (torusMap hUA hUB f) := by
  intro z w hzw
  have h1 : (eΦ hUB).symm (Additive.ofMul (ΦA z ≫ f.hom)) = proj ΛB w := hzw
  have h2 := congrArg (eΦ hUB) h1
  rw [AddEquiv.apply_symm_apply] at h2
  have h3 : (eΦ hUB) (proj ΛB w) = Additive.ofMul (ΦB w) := rfl
  rw [h3] at h2
  exact (congrArg Additive.toMul h2).symm

end Lift

/-- **The lifting half from the GLUE `UnifHoloLift` (proved),** with Birkenhake–Lange Prop. 1.2.1
in the form of the kernel's `BPAnalytic.exists_complexLinear_lift`. -/
theorem homLinearLift_of (H : UnifHoloLift) : ZInQ.HomUnify.HomLinearLift := by
  intro K _ A B σ g h ΛA ΛB ΦA ΦB hA hB hUA hUB f
  obtain ⟨hdA, hdB, hhol⟩ := H K A B σ g h ΛA ΛB ΦA ΦB hA hB hUA hUB
  have hind := torusMap_induces hUA hUB f
  obtain ⟨T, -, hTF⟩ := BPAnalytic.exists_complexLinear_lift ΛA ΛB (torusMap hUA hUB f)
    (hhol f _ hind)
  exact ⟨T.toLinearMap, fun z => hind z (T z) (hTF z)⟩

/-- **Row H-69 from the GLUE `UnifHoloLift` and the GLUE `HomRealize` (proved).** -/
theorem homLatticeCorr_of (H1 : UnifHoloLift) (H2 : ZInQ.HomUnify.HomRealize) :
    ZInQ.HomUnify.HomLatticeCorr :=
  ZInQ.HomUnify.corr_iff_lift_realize.2 ⟨homLinearLift_of H1, H2⟩

end AvSplit.HomLattice

#print axioms AvSplit.HomLattice.homLinearLift_of
#print axioms AvSplit.HomLattice.homLatticeCorr_of
