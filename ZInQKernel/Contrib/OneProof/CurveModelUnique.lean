import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# h33-d1: uniqueness of the normal proper model of a function field over `ℚ`

Task h33-d1 (2026-11-17). Report: `docs/research/h33-d1.md`; scratch and log: `scratch/h33-d1/`.

**Model uniqueness** (Hartshorne I.6.7–6.9, II.4.7, UNVERIFIED numbers): let `X`, `Y` be integral
schemes, proper over `ℚ`, whose local rings are valuation rings (normal proper curves). Every
isomorphism of function fields `e : K(X) ≃ K(Y)` is induced by a unique isomorphism `f : X ≅ Y`
(`exists_iso_of_functionField`, `ext_of_fromSpecFunctionField`): valuative extension in both
directions (Jacobian-Challenge's `exists_hom_of_valuationRing_stalk`) and Mathlib's
`ext_of_isDominant_of_isSeparated` for the two composites.

Also: a morphism `h : X ⟶ Y` inducing `c : K(Y) → K(X)` on function fields induces `c` on local
rings (`algebraMap_stalkMap`), the input for transporting point and cusp conditions along `f`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace ZInQ.CurveModel

/-! ## §1. `Spec K(X) ⟶ X` is dominant -/

theorem range_fromSpecFunctionField (X : Scheme.{0}) [IsIntegral X] :
    Set.range X.fromSpecFunctionField = {genericPoint X} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint (CommRingCat.of X.functionField) :=
      Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
    subst hw
    exact Scheme.fromSpecStalk_closedPoint
  · intro hz
    exact ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      hz.symm ▸ Scheme.fromSpecStalk_closedPoint⟩

instance isDominant_fromSpecFunctionField (X : Scheme.{0}) [IsIntegral X] :
    IsDominant X.fromSpecFunctionField := by
  constructor
  rw [DenseRange, range_fromSpecFunctionField, dense_iff_closure_eq]
  have := genericPoint_spec X
  rw [isGenericPoint_def] at this
  rw [this]

/-- **Two morphisms out of an integral scheme into a separated scheme agreeing at the generic
point are equal.** -/
theorem ext_of_fromSpecFunctionField {X Y S : Scheme.{0}} [IsIntegral X] (s : Y ⟶ S)
    [IsSeparated s] {f g : X ⟶ Y} (h : f ≫ s = g ≫ s)
    (hg : X.fromSpecFunctionField ≫ f = X.fromSpecFunctionField ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated s h X.fromSpecFunctionField hg

/-! ## §2. Model uniqueness -/

theorem specQ_ext' {Y : Scheme.{0}} (f g : Y ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  have h1 := Scheme.toSpecΓ_naturality f
  have h2 := Scheme.toSpecΓ_naturality g
  have hA : f.appTop = g.appTop := by
    have : (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ f.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ g.appTop := by
      ext1; exact Subsingleton.elim _ _
    simpa using this
  rw [← cancel_mono (Spec (CommRingCat.of ℚ)).toSpecΓ, h1, h2, hA]

theorem isSeparated_of_proper {Y : Scheme.{0}} (sY : Y ⟶ Spec (CommRingCat.of ℚ)) [IsProper sY] :
    Y.IsSeparated := by
  refine ⟨?_⟩
  rw [← Limits.terminal.comp_from sY]
  infer_instance

/-- **Valuative extension**: a morphism `Spec K(X) ⟶ Y` extends to `X` when the local rings of `X`
are valuation rings and `Y` is proper over `ℚ`. -/
theorem exists_extension_of_generic {X Y : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (CommRingCat.of ℚ)) (sY : Y ⟶ Spec (CommRingCat.of ℚ)) [IsProper sY]
    (hX : ∀ p : X, ValuationRing (X.presheaf.stalk p)) (γ : Spec X.functionField ⟶ Y) :
    ∃ f : X ⟶ Y, X.fromSpecFunctionField ≫ f = γ := by
  let _ : X.Over (Spec (CommRingCat.of ℚ)) := ⟨sX⟩
  let _ : Y.Over (Spec (CommRingCat.of ℚ)) := ⟨sY⟩
  have : IsProper (Y ↘ Spec (CommRingCat.of ℚ)) := ‹IsProper sY›
  have := isSeparated_of_proper sY
  obtain ⟨f, -, hf⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := Spec (CommRingCat.of ℚ))
    (target := Y) hX γ (specQ_ext' _ _)
  exact ⟨f, hf⟩

/-- **Model uniqueness.** Let `X`, `Y` be integral schemes, proper over `ℚ`, whose local rings are
valuation rings. An isomorphism `e : K(X) ≃ K(Y)` is induced by an isomorphism `f : X ⟶ Y`:
`Spec K(X) → X → Y` is `Spec K(X) → Spec K(Y) → Y` (`Spec` of `e⁻¹`). -/
theorem exists_iso_of_functionField {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (CommRingCat.of ℚ)) (sY : Y ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX]
    [IsProper sY] (hX : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (hY : ∀ p : Y, ValuationRing (Y.presheaf.stalk p)) (e : X.functionField ≃+* Y.functionField) :
    ∃ f : X ⟶ Y, IsIso f ∧ X.fromSpecFunctionField ≫ f =
      Spec.map (CommRingCat.ofHom (e.symm : Y.functionField →+* X.functionField)) ≫
        Y.fromSpecFunctionField := by
  obtain ⟨f, hf⟩ := exists_extension_of_generic sX sY hX
    (Spec.map (CommRingCat.ofHom (e.symm : Y.functionField →+* X.functionField)) ≫
      Y.fromSpecFunctionField)
  obtain ⟨g, hg⟩ := exists_extension_of_generic sY sX hY
    (Spec.map (CommRingCat.ofHom (e : X.functionField →+* Y.functionField)) ≫
      X.fromSpecFunctionField)
  have hee : Spec.map (CommRingCat.ofHom (e.symm : Y.functionField →+* X.functionField)) ≫
      Spec.map (CommRingCat.ofHom (e : X.functionField →+* Y.functionField)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e.symm : Y.functionField →+* X.functionField).comp
        (e : X.functionField →+* Y.functionField) = RingHom.id _ := by
      ext a; simp
    rw [this]
    exact Spec.map_id _
  have hee' : Spec.map (CommRingCat.ofHom (e : X.functionField →+* Y.functionField)) ≫
      Spec.map (CommRingCat.ofHom (e.symm : Y.functionField →+* X.functionField)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : X.functionField →+* Y.functionField).comp
        (e.symm : Y.functionField →+* X.functionField) = RingHom.id _ := by
      ext a; simp
    rw [this]
    exact Spec.map_id _
  have h1 : f ≫ g = 𝟙 X := by
    refine ext_of_fromSpecFunctionField sX (specQ_ext' _ _) ?_
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, hee]
    exact Category.id_comp _
  have h2 : g ≫ f = 𝟙 Y := by
    refine ext_of_fromSpecFunctionField sY (specQ_ext' _ _) ?_
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, hee']
    exact Category.id_comp _
  exact ⟨f, ⟨g, h1, h2⟩, hf⟩

/-! ## §3. Local rings along a morphism inducing a map of function fields -/

theorem genericPoint_mem_of_nonempty (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) {p : X}
    (hp : p ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨p, trivial, hp⟩

/-- **A morphism inducing `c : K(Y) → K(X)` induces `c` on local rings.** -/
theorem algebraMap_stalkMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y)
    (c : Y.functionField ⟶ X.functionField)
    (hc : X.fromSpecFunctionField ≫ h = Spec.map c ≫ Y.fromSpecFunctionField) (p : X)
    (s : Y.presheaf.stalk (h p)) :
    algebraMap (X.presheaf.stalk p) X.functionField (h.stalkMap p s) =
      c.hom (algebraMap (Y.presheaf.stalk (h p)) Y.functionField s) := by
  obtain ⟨W, hpW, t₀, rfl⟩ := Y.presheaf.exists_germ_eq (x := h p) s
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hpW W.isOpen
  set t := Y.presheaf.map (homOfLE hVW).op t₀
  have hgerm : Y.presheaf.germ W (h p) hpW t₀ = Y.presheaf.germ V (h p) hpV t := by
    exact (Y.presheaf.germ_res_apply (homOfLE hVW) (h p) hpV t₀).symm
  rw [hgerm]
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ h ⁻¹ᵁ V from hpV) (h ⁻¹ᵁ V).isOpen
  have hUV' : U ≤ h ⁻¹ᵁ V := hUV
  have hηX : genericPoint X ∈ U := genericPoint_mem_of_nonempty X U hpU
  have hηY : genericPoint Y ∈ V := genericPoint_mem_of_nonempty Y V hpV
  rw [Scheme.Hom.germ_stalkMap_apply]
  have e1 : X.presheaf.germ (h ⁻¹ᵁ V) p hpV (h.app V t) =
      X.presheaf.germ U p hpU (h.appLE V U hUV' t) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rw [e1]
  have e2 : ∀ (Z : Scheme.{0}) [IsIntegral Z] (O : Z.Opens) (q : Z) (hq : q ∈ O)
      (hη : genericPoint Z ∈ O) (a : Γ(Z, O)),
      algebraMap (Z.presheaf.stalk q) Z.functionField (Z.presheaf.germ O q hq a) =
        Z.presheaf.germ O (genericPoint Z) hη a := by
    intro Z _ O q hq hη a
    change (Z.presheaf.stalkSpecializes (genericPoint_specializes q)).hom
      (Z.presheaf.germ O q hq a) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [e2 X U p hpU hηX, e2 Y V (h p) hpV hηY]
  -- the two ring maps `Γ(Y, V) → K(X)` agree
  have key : h.appLE V U hUV' ≫ X.presheaf.germ U (genericPoint X) hηX =
      Y.presheaf.germ V (genericPoint Y) hηY ≫ c := by
    apply Spec.map_injective
    rw [← cancel_mono hV.fromSpec]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec h hV hU hUV']
    have hfX : Spec.map (X.presheaf.germ U (genericPoint X) hηX) ≫ hU.fromSpec =
        X.fromSpecFunctionField := hU.fromSpecStalk_eq_fromSpecStalk hηX
    have hfY : Spec.map (Y.presheaf.germ V (genericPoint Y) hηY) ≫ hV.fromSpec =
        Y.fromSpecFunctionField := hV.fromSpecStalk_eq_fromSpecStalk hηY
    rw [← Category.assoc, hfX, hc, hfY]
  exact congrArg (fun φ => φ.hom t) key

end ZInQ.CurveModel
