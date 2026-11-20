import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Model
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Integral
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.BirationalComparison

/-! The comparison with the fixed rational curve, and uniqueness of the
integral involution. Tex 8476–8479, 8487–8489; on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ModularCurve (modularFunctionField jq jqN jq_mem jqN_mem)
open scoped TauCeti.ExactDivisor

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.PMWire

open GoodReduction (generic)
open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- Moduli construction data: the generic source embeds densely into its
smooth proper curve, and the pullbacks of the two modular functions give
the specified presentation of its function field as ℚ(j,j_N). For a
proper model use the identity open immersion. The field comparison must
use those moduli functions, whose normalizations are part of constructing
the model; the following isomorphism extends that specified pullback. -/
structure GenericSource (B : Over (Spec (.of ℚ))) (N : ℕ) [NeZero N] where
  compact : Over (Spec (.of ℚ))
  incl : B ⟶ compact
  [openIncl : IsOpenImmersion incl.left]
  [denseIncl : IsDominant incl.left]
  [integral : IsIntegral compact.left]
  [proper : IsProper compact.hom]
  [smooth : Smooth compact.hom]
  dimension : topologicalKrullDim compact.left = 1
  /-- The invariant of the source elliptic curve on the moduli chart. -/
  sourceJ : compact.left.functionField
  /-- The invariant after quotienting by the universal cyclic subgroup. -/
  quotientJ : compact.left.functionField
  chartField : compact.left.functionField ≃+* modularFunctionField N
  chart_sourceJ : chartField sourceJ = ⟨jq, jq_mem N⟩
  chart_quotientJ : chartField quotientJ = ⟨jqN N, jqN_mem N⟩

attribute [instance] GenericSource.openIncl GenericSource.denseIncl GenericSource.integral
  GenericSource.proper GenericSource.smooth

abbrev rationalSource (N : ℕ) [NeZero N] : Over (Spec (.of ℚ)) :=
  Over.mk (X0Branch.model N).overQ

namespace GenericSource

variable {B : Over (Spec (.of ℚ))} {N : ℕ} [NeZero N] (D : GenericSource B N)

/-- The specified pullback from the fixed normalization to the compactification. -/
def pullbackField :
    letI : IsIntegral (rationalSource N).left := (X0Branch.model N).integral
    (rationalSource N).left.functionField ≃+* D.compact.left.functionField :=
  (X0Model.functionField N).trans D.chartField.symm

/-- The comparison uses the source and cyclic quotient invariants in
their ordered roles. This is the moduli chart pin on the generic map. -/
theorem pullback_generators :
    letI : IsIntegral (rationalSource N).left := (X0Branch.model N).integral
    D.pullbackField ((X0Model.functionField N).symm ⟨jq, jq_mem N⟩) = D.sourceJ ∧
      D.pullbackField ((X0Model.functionField N).symm ⟨jqN N, jqN_mem N⟩) = D.quotientJ := by
  change D.chartField.symm ((X0Model.functionField N) ((X0Model.functionField N).symm
    ⟨jq, jq_mem N⟩)) = D.sourceJ ∧
    D.chartField.symm ((X0Model.functionField N) ((X0Model.functionField N).symm
      ⟨jqN N, jqN_mem N⟩)) = D.quotientJ
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← D.chart_sourceJ, ← D.chart_quotientJ]
  exact ⟨D.chartField.symm_apply_apply _, D.chartField.symm_apply_apply _⟩

/-- The proper-curve comparison at the specified function field map. -/
theorem exists_compactIso :
    letI : IsIntegral (rationalSource N).left := (X0Branch.model N).integral
    ∃ i : D.compact ≅ rationalSource N,
      fromFunctionField D.compact.left ≫ i.hom.left =
        Spec.map (CommRingCat.ofHom D.pullbackField.toRingHom) ≫
          fromFunctionField (rationalSource N).left := by
  let X := X0Branch.model N
  letI : IsIntegral (rationalSource N).left := X.integral
  letI : IsProper (rationalSource N).hom := X.proper
  letI : Smooth (rationalSource N).hom := X.smooth
  obtain ⟨i, hi, hη⟩ := isomorphism_of_functionField_equiv D.compact.hom
    (rationalSource N).hom (smooth_curve_valuation_stalk D.compact.hom D.dimension)
    (smooth_curve_valuation_stalk (rationalSource N).hom (ParamAtScale.model_dimension X))
    D.pullbackField
  exact ⟨Over.isoMk i hi, hη⟩

/-- The proved comparison with the proper normalization. -/
def compactIso : D.compact ≅ rationalSource N :=
  D.exists_compactIso.choose

theorem compactIso_generic :
    letI : IsIntegral (rationalSource N).left := (X0Branch.model N).integral
    fromFunctionField D.compact.left ≫ D.compactIso.hom.left =
      Spec.map (CommRingCat.ofHom D.pullbackField.toRingHom) ≫
        fromFunctionField (rationalSource N).left :=
  D.exists_compactIso.choose_spec

/-- The identification of the generic source with the corresponding open of
the fixed curve. In the proper case this is the entire comparison iso. -/
def jX : B ⟶ rationalSource N := D.incl ≫ D.compactIso.hom

instance jX_open : IsOpenImmersion D.jX.left := by
  change IsOpenImmersion (D.incl.left ≫ D.compactIso.hom.left)
  infer_instance

instance jX_dominant : IsDominant D.jX.left := by
  change IsDominant (D.incl.left ≫ D.compactIso.hom.left)
  infer_instance

end GenericSource

section Integral

variable {R : Type} [CommRing R] [Algebra R ℚ] {M : Over (Spec (.of R))}

/-- Projection from the generic fibre of the integral model. -/
abbrev genericProjection (M : Over (Spec (.of R))) :
    ((generic R ℚ).obj M).left ⟶ M.left :=
  pullback.fst M.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))

/-- Equality after generic restriction implies integral equality for the
reduced separated model with dense generic fibre. This argument uses the
separated diagonal, so it works for either choice of modular model. -/
theorem integralEnd_ext [IsReduced M.left] [IsSeparated M.hom]
    [IsDominant (genericProjection M)] {u v : M ⟶ M}
    (h : (generic R ℚ).map u = (generic R ℚ).map v) : u = v := by
  ext1
  apply ext_of_isDominant_of_isSeparated M.hom ((Over.w u).trans (Over.w v).symm)
    (genericProjection M)
  have hh := congrArg (fun z => z.left ≫ genericProjection M) h
  simpa [generic, genericProjection, Over.pullback_map_left] using hh

variable {N : ℕ} [NeZero N]

/-- The rational involution at the full prime power in the level. -/
def rationalW (N : ℕ) [NeZero N] (q : ℕ) : rationalSource N ⟶ rationalSource N :=
  let a := AtkinRational.rationalAtkin (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q))
  Over.homMk a.hom a.overQ

/-- The extension condition to be supplied by construction of the model.
On the open moduli space this comes from quotient by the canonical cyclic
subgroup and the dual isogeny (Vélu over fields is already in the tree).
For a smooth proper model one can use extension of automorphisms in genus
at least one (Lichtenbaum–Shafarevich; Liu, Algebraic Geometry and Arithmetic
Curves, chapters 9–10, UNVERIFIED). The elliptic quotient of J₀(N) gives
positive genus here. -/
def ExtendsAtkin (D : GenericSource ((generic R ℚ).obj M) N)
    (q : ℕ) (W : M ⟶ M) : Prop :=
  (generic R ℚ).map W ≫ D.jX = D.jX ≫ rationalW N q

/-- There is at most one extension of the fixed rational involution. -/
theorem extendsAtkin_unique [IsReduced M.left] [IsSeparated M.hom]
    [IsDominant (genericProjection M)] (D : GenericSource ((generic R ℚ).obj M) N)
    {q : ℕ} {u v : M ⟶ M} (hu : ExtendsAtkin D q u) (hv : ExtendsAtkin D q v) :
    u = v := by
  haveI : Mono D.jX.left := inferInstance
  apply integralEnd_ext
  ext1
  apply (cancel_mono D.jX.left).mp
  exact congrArg CommaMorphism.left (hu.trans hv.symm)

end Integral


end ZInQ.Manuscript.RC.PMWire
