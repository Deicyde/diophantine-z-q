import ZInQKernel.OneProof.H.TailR
import ZInQKernel.Contrib.OneProof.SmoothRegular.Basic

/-!
# smooth-regular: `CurveSplit.RegularSmoothPerfect` (Stacks 00TV, ⇐) proved

Task smooth-regular (2026-11-16). Report: `docs/research/smooth-regular.md`; log: `scratch/smooth-regular/log.md`.

The open field `HDec.HSyn.OpenTextbookLeaves11.regularSmoothPerfect` (statement `CurveSplit.RegularSmoothPerfect`,
`ZInQKernel/OneProof/H/TailR.lean`) is proved outright, with no new leaf:

* `Algebra.FormallySmooth.localization_of_isRegularLocalRing` (vendored Jacobian-Challenge,
  `ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/RingTheory/Smooth/RegularLocalRing.lean`): `S_q` regular with
  residue field formally smooth over `k` ⇒ `S_q` formally smooth over `k` (the Jacobian criterion);
* Mathlib's `Algebra.FormallySmooth.of_perfectField`: the residue field of `S_q`, essentially of finite type over
  the perfect field `k`, is formally smooth over `k`;
* Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth`: the smooth locus of a finitely presented algebra is open,
  so some `g ∉ q` has `S_g` smooth.

The scheme forms (smooth ⇔ regular ⇔ nonsingular over a perfect field, smooth ⇔ geometrically regular over any
field) are in `ZInQKernel/Contrib/OneProof/SmoothRegular/Basic.lean`.

No `sorry`, no `axiom`.
-/

namespace ZInQ.Contrib.SmoothRegular

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Stacks 00TV (⇐), proved.** Over a perfect field `k`, a finite type `k`-algebra `S` is smooth at every
prime `q` with `S_q` regular: some `g ∉ q` has `S_g` smooth over `k`. -/
theorem regularSmoothPerfect : CurveSplit.RegularSmoothPerfect := by
  intro k _ _ S _ _ _ q _ hreg
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsRegularLocalRing (Localization.AtPrime q) := hreg
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstanceAs (Algebra.EssFiniteType k (Localization.AtPrime q ⧸ _))
  have : Algebra.IsSmoothAt k q := Algebra.FormallySmooth.localization_of_isRegularLocalRing q
  exact Algebra.IsSmoothAt.exists_notMem_smooth k q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Stacks 00TV (⇒)**, the converse direction in the same algebraic form: if `S` is smooth over a field `k`,
every localization `S_q` is a regular local ring (`k` any field). -/
theorem isRegularLocalRing_of_smooth (k : Type) [Field k] (S : Type) [CommRing S] [Algebra k S]
    [Algebra.Smooth k S] (q : Ideal S) [q.IsPrime] : IsRegularLocalRing (Localization.AtPrime q) := by
  let f : Spec (.of S) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k S))
  have : Smooth f := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.2 ‹_›
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  have h := Smooth.isRegularLocalRing_stalk f p
  have : IsRegularLocalRing ((structurePresheafInCommRingCat S).stalk p) := h
  exact .of_ringEquiv (AlgebraicGeometry.StructureSheaf.stalkIso S p).toRingEquiv.symm

end ZInQ.Contrib.SmoothRegular
