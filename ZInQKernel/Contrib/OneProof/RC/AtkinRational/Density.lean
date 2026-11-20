import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Model

/-! Descent of a constant on the interior chart. Tex 2943–2946;
rational Laurent descent and separatedness, on the spot (c). -/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane
open scoped Topology
open ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.AtkinRational

variable {N : ℕ} [NeZero N]

private theorem eq_over_rat {R : Type} [CommRing R]
    (u v : Spec (.of R) ⟶ Spec (.of ℚ)) : u = v := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

private theorem exp_eq_qpow (z : ℂ) (n : ℤ) :
    Function.Periodic.qParam 1 z ^ n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem section_constant_rational (U : (X0Model.curve N).Opens) [Nonempty U]
    (r : Γ(X0Model.curve N, U)) (c : ℂ)
    (hm : ∀ τ : ℍ, X0Model.complexPoint N τ default ∈ U)
    (hc : ∀ τ : ℍ, X0Branch.affineEval (X0Model.complexPoint N τ) U (hm τ) r = c) :
    (((X0Model.functionField N ((X0Model.curve N).germToFunctionField U r) :
      LaurentSeries ℚ).coeff 0 : ℚ) : ℂ) = c := by
  obtain ⟨g, T, _, hg, hval⟩ := X0Model2.sectionExpansion N U r
  have he (τ : ℍ) : g τ = c := ((hval τ (hm τ)).2).symm.trans (hc τ)
  have hreal : Realizes
      (complexify (X0Model.functionField N ((X0Model.curve N).germToFunctionField U r)))
      (fun _ => c) := by
    have htail : ∀ᶠ τ : ℍ in atImInfty, T < τ.im :=
      (atImInfty_mem _).mpr ⟨T + 1, fun _ hτ => (lt_add_of_pos_right T zero_lt_one).trans_le hτ⟩
    filter_upwards [htail] with τ hτ
    simpa only [complexify_coeff, exp_eq_qpow, he τ] using hg τ hτ
  have h := Realizes.eq_of_eventuallyEq hreal (Realizes.const c) (Eventually.of_forall fun _ => rfl)
  have hc₀ := congrArg (fun x : LaurentSeries ℂ => x.coeff 0) h
  simpa [complexify_coeff, HahnSeries.algebraMap_apply', HahnSeries.ofPowerSeries_C] using hc₀

set_option backward.isDefEq.respectTransparency false in
/-- A rational morphism out of the reduced modular curve that is constant
on the complex chart is constant over the rationals. Work on an affine
neighborhood of the common value. The regular functions pulled back to
the chart have constant complex values; uniqueness of the Laurent
expansion identifies these values with their rational constant
coefficients. The common complex point therefore factors through a
rational point. The chart contains a dominant point and the target is
separated, so the morphism is constant. Evaluation at any rational
basepoint then identifies its constant, and the equality can be
precomposed with every field-valued point. -/
theorem eq_constant_of_chart {Y : Scheme.{0}} (q : Y ⟶ Spec (.of ℚ)) [IsSeparated q]
    (D : X0Model.curve N ⟶ Y) (hD : D ≫ q = X0Model.overQ N)
    (b : Spec (.of ℚ) ⟶ X0Model.curve N)
    (c : Spec (.of ℂ) ⟶ Y) (hc : ∀ τ : ℍ, X0Model.complexPoint N τ ≫ D = c) :
    D = X0Model.overQ N ≫ b ≫ D := by
  obtain ⟨V, hV, hcV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := c default) trivial
  let U := D ⁻¹ᵁ V
  have hm (τ : ℍ) : X0Model.complexPoint N τ default ∈ U := by
    change (X0Model.complexPoint N τ ≫ D) default ∈ V
    rwa [hc τ]
  let : Nonempty U := ⟨⟨_, hm default⟩⟩
  let C := X0Branch.affineEval c V hcV
  have hp (τ : ℍ) (r : Γ(Y, V)) :
      X0Branch.affineEval (X0Model.complexPoint N τ) U (hm τ) (D.app V r) = C r := by
    let p := (X0Branch.model N).complexPoint τ
    have hmem : (X0Model.complexPoint N τ ≫ D) default ∈ V := by rwa [hc τ]
    have h := ParamAtScale.evalSection_comp p D hD V hmem r
    change X0Branch.affineEval (X0Model.complexPoint N τ ≫ D) V hmem r = _ at h
    rw [X0Branch.affineEval_congr _ hcV (hc τ)] at h
    exact h.symm
  let a (r : Γ(Y, V)) : ℚ :=
    (X0Model.functionField N ((X0Model.curve N).germToFunctionField U (D.app V r)) :
      LaurentSeries ℚ).coeff 0
  have ha (r : Γ(Y, V)) : (a r : ℂ) = C r :=
    section_constant_rational U _ (C r) hm (fun τ => hp τ r)
  let ρ : Γ(Y, V) →+* ℚ :=
    { toFun := a
      map_zero' := Rat.cast_injective (α := ℂ) (by simpa only [map_zero, Rat.cast_zero] using ha 0)
      map_one' := Rat.cast_injective (α := ℂ) (by simpa only [map_one, Rat.cast_one] using ha 1)
      map_add' := fun r s => Rat.cast_injective (α := ℂ)
        (by rw [ha (r + s), Rat.cast_add, ha r, ha s, map_add])
      map_mul' := fun r s => Rat.cast_injective (α := ℂ)
        (by rw [ha (r * s), Rat.cast_mul, ha r, ha s, map_mul]) }
  let d := Spec.map (CommRingCat.ofHom ρ) ≫ hV.fromSpec
  have hfactor :
      Spec.map (CommRingCat.ofHom C) ≫ hV.fromSpec = c := by
    have hu : ⊤ ≤ c ⁻¹ᵁ V := fun x _ => by rwa [Subsingleton.elim x (default : Spec (.of ℂ))]
    change Spec.map (c.appLE V ⊤ hu ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) ≫ hV.fromSpec = c
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec c _
      (isAffineOpen_top _) hu, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
      Iso.hom_inv_id_assoc]
  have hc' : Spec.map (CommRingCat.ofHom (Rat.castHom ℂ)) ≫ d = c := by
    rw [← hfactor, ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext ha
  have hq : d ≫ q = 𝟙 _ := eq_over_rat _ _
  have hd : D = X0Model.overQ N ≫ d := by
    apply ext_model_of_chart q (by rw [hD, Category.assoc, hq, Category.comp_id])
    intro τ
    rw [hc τ, ← Category.assoc, X0Model.complexPoint_overQ,
      show algebraMap ℚ ℂ = Rat.castHom ℂ from RingHom.ext_rat _ _, hc']
  have hb : b ≫ D = d := by
    rw [hd, ← Category.assoc, eq_over_rat (b ≫ X0Model.overQ N) (𝟙 _), Category.id_comp]
  rw [hb, ← hd]


end ZInQ.Manuscript.RC.AtkinRational
