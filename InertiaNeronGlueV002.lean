import NeronDescentEnlargeV001
import UnramifiedDescentV003

/-!
# Inertia-fixed points have unramified descents; integral sections of Néron models

The centre of `w` on the integral closure of `O` in a finite intermediate field `M`, defined through
the co-restricted inclusion of the integral closure into `w`, coincides with the ideal of integral
elements of `w`-valuation `< 1`. Hence every point of `A(Ω)` fixed by the inertia subgroup of `w`
has an unramified descent, and for any separated group model `(N, e)` of `A` with the Néron mapping
property:

* every inertia-fixed `m`-torsion point is the generic fibre of a unique `m`-torsion `w`-section;
* every element of the Tate module fixed by inertia (componentwise action of `A.galAct σ`) is the
  generic fibre of a unique compatible system of `w`-sections.

No unramifiedness or descent hypothesis remains: it is supplied by the arithmetic of inertia fields.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonObj

namespace InertiaNeronGlue

/-- Unramifiedness at equal prime ideals. -/
theorem isUnramifiedAt_of_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} [I.IsPrime] [J.IsPrime] (h : I = J) (hI : Algebra.IsUnramifiedAt R I) :
    Algebra.IsUnramifiedAt R J := by
  subst h
  exact hI

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

/-- **The two centres agree**: the comap of the maximal ideal of `w` along the co-restricted
inclusion of the integral closure is the ideal of integral elements of `w`-valuation `< 1`. -/
theorem center_eq_integralCenter [NumberField K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (M : IntermediateField K Ω) [FiniteDimensional K M] [Algebra O M] [IsScalarTower O K M] :
    NeronInvariantTorsion.center O w hw M = InertiaPointDescent.integralCenter O w hw M.val := by
  ext b
  rw [InertiaPointDescent.mem_integralCenter_iff]
  change NeronInvariantTorsion.toW O w hw M b ∈ IsLocalRing.maximalIdeal w ↔ _
  rw [ValuationSubring.valuation_lt_one_iff]
  rfl

variable [NumberField K] [IsAlgClosure K Ω] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

/-- **Inertia-fixed points have unramified descents.** -/
theorem inertiaFixedUnramified (A : PkgI3.AbVar K) :
    NeronInvariantTorsion.InertiaFixedUnramified O w hw A := by
  intro x hx
  obtain ⟨M, hfd, -, ⟨y, hy⟩, hU⟩ :=
    InertiaPointDescent.exists_unramified_point_field O w hw A x hx
  let _ : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  have hst : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsep : Algebra.IsSeparable K M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hU0 : Algebra.IsUnramifiedAt O (InertiaPointDescent.integralCenter O w hw M.val) := hU
  have hU' : Algebra.IsUnramifiedAt O (NeronInvariantTorsion.center O w hw M) :=
    isUnramifiedAt_of_eq (center_eq_integralCenter O w hw M).symm hU0
  exact ⟨M, hfd, hsep, inferInstance, hst, hU', y, hy⟩

variable {A : PkgI3.AbVar K} {N : Over (Spec (CommRingCat.of O))}
  (e : (Over.pullback (NeronInvariantTorsion.jO O)).obj N ≅ A.X)

open scoped Obj in
/-- **Inertia-fixed torsion lifts uniquely to torsion sections of a Néron model.** -/
theorem inertia_fixed_torsion_section [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (NeronInvariantTorsion.jO O)).obj N) :=
      Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (NeronInvariantTorsion.jO O)).map f ≫ e.hom)
    (x : A.Pt Ω) (hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x)
    (m : ℕ) (hxm : x ^ m = 1) :
    ∃! s : NeronInvariantTorsion.specW O w hw ⟶ N,
      s ^ m = 1 ∧ NeronInvariantTorsion.genericFibre O w hw e s = x :=
  NeronInvariantTorsion.inertia_fixed_sections O w hw e hgen hN
    (inertiaFixedUnramified O w hw A) x hfix m hxm

open scoped Obj in
/-- **Inertia-fixed Tate vectors lift uniquely to compatible systems of sections.** The hypothesis
is the componentwise action `PkgI3.Tate.map (A.galAct σ)` fixing `t`. -/
theorem inertia_fixed_tate_sections [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (NeronInvariantTorsion.jO O)).obj N) :=
      Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (NeronInvariantTorsion.jO O)).map f ≫ e.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω)))
    (hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
      PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ)) t = t) :
    ∃ s : ℕ → (NeronInvariantTorsion.specW O w hw ⟶ N), s 0 = 1 ∧
      (∀ n, s (n + 1) ^ ℓ = s n) ∧
      (∀ n, NeronInvariantTorsion.genericFibre O w hw e (s n) = Additive.toMul (t.1 n)) ∧
      ∀ s' : ℕ → (NeronInvariantTorsion.specW O w hw ⟶ N),
        (∀ n, NeronInvariantTorsion.genericFibre O w hw e (s' n) = Additive.toMul (t.1 n)) →
          s' = s := by
  refine NeronInvariantTorsion.exists_unique_compatible_sections_of_unramifiedDescent O w hw e
    hgen hN ℓ t (fun n => inertiaFixedUnramified O w hw A _ (fun σ hσ => ?_))
  have h := congrArg (fun s : PkgI3.Tate.T ℓ (Additive (A.Pt Ω)) => Additive.toMul (s.1 n))
    (hfix σ hσ)
  exact h

end InertiaNeronGlue
