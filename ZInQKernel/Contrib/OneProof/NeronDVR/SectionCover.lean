import ZInQKernel.Contrib.OneProof.NeronDVR.QuasiAffineDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Gluing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ClearDenominators

/-!
# Effective descent from invariant nonvanishing opens

For a fixed invertible module with an affine nonvanishing cover, the
nonvanishing locus of any other section is quasi-affine. Invariant such
loci therefore descend and give effective descent by gluing.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules} [L.IsInvertible]

set_option backward.isDefEq.respectTransparency false in
/-- A free generator on an open expresses the nonvanishing locus of a section
on that open as a basic open. -/
theorem basicOpen_coeff_eq_of_isFreeGenerator
    (s : 𝟙_ X.Modules ⟶ L) {U : X.Opens} {e : Γ(L, U)} (he : IsFreeGenerator e) :
    X.basicOpen (he.coeff (s.app U (unitSectionsEquiv U 1))) =
      U ⊓ s.zeroLocus.support.compl := by
  let a := he.coeff (s.app U (unitSectionsEquiv U 1))
  change X.basicOpen a = U ⊓ s.zeroLocus.support.compl
  ext x
  by_cases hx : x ∈ U
  · obtain ⟨V, hV, hxV, hSub⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
    have hVU : V ≤ U := hSub
    let i : V ⟶ U := homOfLE hVU
    have hsec : L.presheaf.map i.op (s.app U (unitSectionsEquiv U 1)) =
        s.app V (unitSectionsEquiv V 1) := by
      rw [← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one]
    have hcoeff : X.presheaf.map i.op a =
        (he.map hVU).coeff (s.app V (unitSectionsEquiv V 1)) := by
      apply (he.map hVU).smul_left_injective
      change X.presheaf.map i.op a • L.presheaf.map i.op e =
        (he.map hVU).coeff (s.app V (unitSectionsEquiv V 1)) • L.presheaf.map i.op e
      rw [(he.map hVU).coeff_smul]
      rw [← Scheme.Modules.map_smul, he.coeff_smul, hsec]
    have heq : V ⊓ X.basicOpen a = V ⊓ s.zeroLocus.support.compl := by
      rw [← X.basicOpen_res a i.op, hcoeff, basicOpen_coeff_eq s ⟨V, hV⟩ (he.map hVU)]
    exact ⟨fun h => ⟨hx, (heq.le ⟨hxV, h⟩).2⟩,
      fun h => (heq.ge ⟨hxV, h.2⟩).2⟩
  · exact ⟨fun h => (hx (X.basicOpen_le a h)).elim, fun h => (hx h.1).elim⟩

/-- When affine nonvanishing loci of finitely many sections cover a scheme,
the nonvanishing locus of any section of the same invertible module is
quasi-affine. The ratios with that section give affine basic opens. -/
theorem isQuasiAffine_nonvanishing_of_affine_cover {I : Type*} [Finite I]
    (s : I → (𝟙_ X.Modules ⟶ L))
    (haff : ∀ i, IsAffineOpen (s i).zeroLocus.support.compl)
    (hcover : ∀ x : X, ∃ i, x ∈ (s i).zeroLocus.support.compl)
    (t : 𝟙_ X.Modules ⟶ L) : (Scheme.Opens.toScheme (X := X) t.zeroLocus.support.compl).IsQuasiAffine := by
  let U : X.Opens := t.zeroLocus.support.compl
  let V (i : I) := (s i).zeroLocus.support.compl
  let e := isFreeGenerator_app_one_of_le t (openSubset := U) le_rfl
  let a (i : I) := e.coeff ((s i).app U (unitSectionsEquiv U 1))
  have hbasic (i : I) : X.basicOpen (a i) = U ⊓ V i :=
    basicOpen_coeff_eq_of_isFreeGenerator (s i) e
  have hIntersection (i : I) : IsAffineOpen (U ⊓ V i) := by
    let e' := isFreeGenerator_app_one_of_le (s i) (openSubset := V i) le_rfl
    rw [inf_comm, ← basicOpen_coeff_eq t ⟨V i, haff i⟩ e']
    exact (haff i).basicOpen _
  have hUnion : (U : Set X) = ⋃ i, (↑(U ⊓ V i) : Set X) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, hi⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi.1
  have hCompact : IsCompact (U : Set X) := by
    rw [hUnion]
    exact isCompact_iUnion fun i => (hIntersection i).isCompact
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hCompact
  change U.toScheme.IsQuasiAffine
  apply Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen
  intro x
  obtain ⟨i, hi⟩ := hcover (U.ι x)
  let b := U.topIso.inv (a i)
  refine ⟨b, ?_, ?_⟩
  · apply (U.ι.isAffineOpen_iff_of_isOpenImmersion (U := U.toScheme.basicOpen b)).mp
    rw [U.ι_image_basicOpen_topIso_inv, hbasic]
    exact hIntersection i
  · have hx : U.ι x ∈ U.ι ''ᵁ U.toScheme.basicOpen b := by
      rw [U.ι_image_basicOpen_topIso_inv, hbasic]
      exact ⟨x.2, hi⟩
    obtain ⟨y, hy, hxy⟩ := hx
    exact U.ι.isOpenEmbedding.injective hxy ▸ hy

/-- A quasi-compact scheme needs only a pointwise affine nonvanishing
neighborhood from the fixed invertible module. -/
theorem isQuasiAffine_nonvanishing_of_exists_affine [CompactSpace X]
    (hcover : ∀ x : X, ∃ s : 𝟙_ X.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl)
    (t : 𝟙_ X.Modules ⟶ L) : (Scheme.Opens.toScheme (X := X) t.zeroLocus.support.compl).IsQuasiAffine := by
  classical
  choose s hs hAff using hcover
  obtain ⟨indices, hIndices⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((s x).zeroLocus.support.compl : Set X))
    (fun x => (s x).zeroLocus.support.compl.isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hs x⟩)
  refine isQuasiAffine_nonvanishing_of_affine_cover (fun x : indices => s x)
    (fun x => hAff x) ?_ t
  intro x
  have hx := hIndices (Set.mem_univ x)
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hix⟩ := hx
  exact ⟨⟨i, hi⟩, hix⟩

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Over.DescentDatum

/-- A covering by invariant nonvanishing opens suffices for effectivity
when the same invertible module also has an affine nonvanishing cover. -/
theorem isEffective_of_nonvanishing_cover {S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    {p : S' ⟶ S} [Flat p] [Surjective p] [QuasiCompact p] {X : Over S'}
    [CompactSpace X.left] (d : DescentDatum p X) {L : X.left.Modules} [L.IsInvertible]
    (hAffine : ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl)
    (hInvariant : ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ d.IsInvariant s.zeroLocus.support.compl) :
    d.IsEffective := by
  apply d.isEffective_of_forall_exists_mem
  intro x
  obtain ⟨s, hx, hs⟩ := hInvariant x
  let U : X.left.Opens := s.zeroLocus.support.compl
  have : (Over.mk (U.ι ≫ X.hom)).left.IsQuasiAffine :=
    Scheme.Modules.isQuasiAffine_nonvanishing_of_exists_affine hAffine s
  exact ⟨U, hs, hx, (d.restrict U hs).isEffective_of_isQuasiAffine⟩

end CategoryTheory.Over.DescentDatum
