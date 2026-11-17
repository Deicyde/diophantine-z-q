/-
# H5 / NOS round 2, lane 1: chart-surjectivity criterion for a closed ProjPresentation

Newly authored glue (H5 round-2 lane 1, 2026-11-15), additive to cp9/cp10. Inputs read-only: the canonical
Source port's LITERAL `Scheme.Modules.ProjPresentation` (FLT @ 6e837e75…; Apache-2.0, Anthropic, PBC) and
Mathlib (`IsClosedImmersion` is Zariski-local on the target; `IsClosedImmersion.of_surjective_of_isAffine`;
maps from empty schemes are closed immersions; `Proj.isAffineOpen_basicOpen`).

Corner D₁ (`isClosedImmersion_toProj_of_chart_surjective`): for an ACTUAL presentation `𝔓` whose map
`𝔓.toProj` is universally closed, if a set `I` of coordinate charts covers `X`, each such chart
`𝔓.toProj⁻¹ D₊(X_i)` is affine and the chart ring map `Γ(D₊(X_i)) → Γ(𝔓.toProj⁻¹ D₊(X_i))` is
surjective, then `𝔓.toProj` is a closed immersion — hence `ClosedImmersionBySections`. No finite = closed
identification: closedness of the range comes from universal closedness, and the complement of the range
is covered by an open with EMPTY preimage.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

section CornerD

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {L : X.Modules} {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- Surjectivity of `g.app` transports along an equality of opens. -/
theorem surjective_app_of_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z) {V V' : Z.Opens} (h : V = V')
    (hV : Function.Surjective (g.app V)) : Function.Surjective (g.app V') := by
  subst h
  exact hV

/-- **Corner D₁.** Chart surjectivity on a covering set of affine charts, plus universal closedness,
makes the presentation map a closed immersion. -/
theorem isClosedImmersion_toProj_of_chart_surjective
    (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation L f N)
    [UniversallyClosed 𝔓.toProj] (I : Set (Fin (N + 1)))
    (hcov : ∀ x : X, ∃ i ∈ I, x ∈ chart 𝔓 i)
    (haff : ∀ i ∈ I, IsAffineOpen (chart 𝔓 i))
    (hsurj : ∀ i ∈ I, Function.Surjective (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i)))) :
    IsClosedImmersion 𝔓.toProj := by
  have hclosed : IsClosed (Set.range 𝔓.toProj) := 𝔓.toProj.isClosedMap.isClosed_range
  let V0 : (Proj 𝒜).Opens := ⟨(Set.range 𝔓.toProj)ᶜ, hclosed.isOpen_compl⟩
  let U : Option I → (Proj 𝒜).Opens := fun o =>
    match o with
    | none => V0
    | some i => Proj.basicOpen 𝒜 (MvPolynomial.X i.1)
  have hU : iSup U = ⊤ := by
    refine top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
    by_cases hy : y ∈ Set.range 𝔓.toProj
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, hi, hx⟩ := hcov x
      exact ⟨some ⟨i, hi⟩, hx⟩
    · exact ⟨none, hy⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) U hU fun o => ?_
  match o with
  | none =>
    haveI : IsEmpty (𝔓.toProj ⁻¹ᵁ V0).toScheme :=
      ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
    infer_instance
  | some ⟨i, hi⟩ =>
    haveI : IsAffine (chart 𝔓 i).toScheme := haff i hi
    haveI : IsAffine (Proj.basicOpen 𝒜 (MvPolynomial.X i)).toScheme :=
      Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i) (X_mem_one (R := R) (N := N) i) Nat.one_pos
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [morphismRestrict_appTop]
    have h1 : Function.Surjective (𝔓.toProj.app
        ((Proj.basicOpen 𝒜 (MvPolynomial.X i)).ι ''ᵁ ⊤)) :=
      surjective_app_of_eq 𝔓.toProj (Scheme.Opens.ι_image_top _).symm (hsurj i hi)
    exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom
      (image_morphismRestrict_preimage 𝔓.toProj (Proj.basicOpen 𝒜 (MvPolynomial.X i)) ⊤)).op)).2.comp h1

/-- Consequently the presentation is a Source `ClosedImmersionBySections` witness. -/
theorem closedImmersionBySections_of_chart_surjective
    (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation L f N)
    [UniversallyClosed 𝔓.toProj] (I : Set (Fin (N + 1)))
    (hcov : ∀ x : X, ∃ i ∈ I, x ∈ chart 𝔓 i)
    (haff : ∀ i ∈ I, IsAffineOpen (chart 𝔓 i))
    (hsurj : ∀ i ∈ I, Function.Surjective (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i)))) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections L f :=
  ⟨N, 𝔓, isClosedImmersion_toProj_of_chart_surjective 𝔓 I hcov haff hsurj⟩

end CornerD

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
