import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OpenGermEvaluation
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Basic
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual analytic residue maps from the already proved Oka germ evaluation

The genuine analytic-space local model supplies actual surjective stalk maps.
Starting from the proved open-Oka germ evaluation and real constants, those maps
construct the coefficient field of EVERY actual analytic stalk. This avoids the
unneeded Weierstrass/Taylor-example import cone for the native point dictionary.
No residue field, model compatibility, GAGA or algebraic F/H witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Actual open holomorphic stalk constants realize ℂ as the residue coefficient field,
proved from the real germ-colimit evaluation rather than from Taylor expansion. -/
theorem intrinsicOpenStalkCoefficients (n : ℕ) (V : Opens (_root_.complexAffineSpace.{0} n))
    (w : (_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding) :
    IsCoefficientField (((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).stalkAlgMap
      (constantsAlgMap n V) w) := by
  let E := openOkaGermEval V w
  let α := ((_root_.complexAffineSpace.{0} n).restrict V.isOpenEmbedding).stalkAlgMap
    (constantsAlgMap n V) w
  have hc (c : ℂ) : E (α c) = c := openOkaGermEval_const V w c
  intro a
  refine ⟨E a, ?_⟩
  have hz : E (a - α (E a)) = 0 :=
    (map_sub E a (α (E a))).trans ((congrArg (fun t => E a - t) (hc (E a))).trans (sub_self _))
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact not_isUnit_zero ((congrArg IsUnit hz).mp (hu.map E))

/-- The ACTUAL analytic local-model charts prove that the actual constants realize
ℂ in every genuine analytic stalk. No compatibility structure is supplied. -/
theorem intrinsicStalkCoefficients (Z : AnalyticSpace.{0}) (z : Z) :
    IsCoefficientField (Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap z) := by
  obtain ⟨U, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z
  exact ((intrinsicOpenStalkCoefficients n V (i.base ⟨z, U.2⟩)).of_surjective
    (hcut.surjective_stalkMap ⟨z, U.2⟩) (hlin.stalkAlgMap ⟨z, U.2⟩)).of_surjective
    (f := (Z.toLocallyRingedSpace.restrictStalkIso U.1.isOpenEmbedding ⟨z, U.2⟩).hom.hom)
    (ConcreteCategory.bijective_of_isIso _).surjective
    fun _ => LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap _ _ _ ⟨z, U.2⟩ _

/-- The actual intrinsic residue-value ring map of a genuine analytic stalk. -/
def intrinsicStalkEval (Z : AnalyticSpace.{0}) (z : Z) : Z.presheaf.stalk z →+* ℂ :=
  (intrinsicStalkCoefficients Z z).evalHom

/-- The actual section-value ring map, composed with the genuine germ. -/
def intrinsicEval (Z : AnalyticSpace.{0}) {U : Opens Z} (z : Z) (hz : z ∈ U) :
    Z.presheaf.obj (op U) →+* ℂ :=
  (intrinsicStalkEval Z z).comp (Z.presheaf.germ U z hz).hom

/-- The actual stalk constants have their original complex values. -/
theorem intrinsicStalkEval_const (Z : AnalyticSpace.{0}) (z : Z) (c : ℂ) :
    intrinsicStalkEval Z z (Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap z c) = c :=
  (intrinsicStalkCoefficients Z z).evalHom_const c

/-- The actual intrinsic evaluation is characterized by the actual maximal ideal. -/
theorem intrinsicStalkEval_eq_iff (Z : AnalyticSpace.{0}) (z : Z)
    (a : Z.presheaf.stalk z) (c : ℂ) :
    intrinsicStalkEval Z z a = c ↔
      a - Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap z c ∈ maximalIdeal (Z.presheaf.stalk z) :=
  (intrinsicStalkCoefficients Z z).evalHom_eq_iff

/-- The intrinsic section evaluation preserves literal original complex constants. -/
theorem intrinsicEval_const (Z : AnalyticSpace.{0}) (z : Z) (c : ℂ) :
    intrinsicEval Z (U := ⊤) z trivial (Z.algebraMap c) = c :=
  intrinsicStalkEval_const Z z c

/-- The actual intrinsic residue evaluation is local; no reducedness/completeness is needed. -/
instance intrinsicStalkEval_isLocalHom (Z : AnalyticSpace.{0}) (z : Z) :
    IsLocalHom (intrinsicStalkEval Z z) := by
  refine ⟨fun a ha => ?_⟩
  have hn : intrinsicStalkEval Z z a ≠ 0 := isUnit_iff_ne_zero.mp ha
  have hh : a ∉ maximalIdeal (Z.presheaf.stalk z) :=
    fun h => hn ((intrinsicStalkCoefficients Z z).evalHom_eq_zero_iff.mpr h)
  simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hh

end ZInQ.Contrib.CloudB3W17bOkaComparison
