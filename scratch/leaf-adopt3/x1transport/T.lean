import HDPrefix

/-! leaf-adopt3: g0-split's glue piece `X1BelyiOnModel` from `LeafModCurves.BelyiX1` (transport). -/

noncomputable section

namespace X1Transport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Copy of g0-split's piece 3 (statement identical to `HSyn.G0Split.X1BelyiOnModel`). -/
def X1BelyiOnModel : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (_ : LeafModCurves.IsCurve X) (_ : IsIntegral X.left)
      (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X) (aj : X ⟶ J.X),
      LeafModCurves.IsJacobian X P₀ J aj ∧ ∃ t : X.left.functionField,
        (letI := ZInQ.LeafPush2.ffAlgebra X; LeafModCurves.IsBelyiFunction ℚ X.left.functionField t) ∧
        ∃ d : ℕ,
          (letI := ZInQ.LeafPush2.ffAlgebra X
           Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField = d) ∧
          0 < d ∧ d ≤ N ^ 2

/-- A Belyi function is carried to a Belyi function by a `k`-algebra isomorphism. -/
theorem isBelyiFunction_map {k F F' : Type} [Field k] [Field F] [Field F'] [Algebra k F]
    [Algebra k F'] (ψ : F ≃ₐ[k] F') {t : F} (h : LeafModCurves.IsBelyiFunction k F t) :
    LeafModCurves.IsBelyiFunction k F' (ψ t) := by
  obtain ⟨hT, hB⟩ := h
  refine ⟨fun ha => hT ((isAlgebraic_algHom_iff (ψ : F →ₐ[k] F') ψ.injective).mp ha), ?_⟩
  intro w hk ht q hqm hqi hqX hqX1 hq x hx
  have hnu : ∀ y : F, y ∈ (w.comap (ψ : F →+* F')).nonunits ↔ ψ y ∈ w.nonunits := by
    intro y
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      ValuationSubring.mem_comap]
    simp [map_inv₀]
  have haev : ∀ y : F, ψ (Polynomial.aeval y q) = Polynomial.aeval (ψ y) q :=
    fun y => (Polynomial.aeval_algHom_apply (ψ : F →ₐ[k] F') y q).symm
  obtain ⟨y, hy, hxy⟩ := hB (w.comap (ψ : F →+* F'))
    (fun c => by rw [ValuationSubring.mem_comap]; simpa using hk c)
    (by rw [ValuationSubring.mem_comap]; exact ht)
    q hqm hqi hqX hqX1 ((hnu _).2 (by rw [haev]; exact hq)) (ψ.symm x)
    ((hnu _).2 (by simpa using hx))
  refine ⟨ψ y, ValuationSubring.mem_comap.1 hy, ?_⟩
  have h2 := congrArg ψ hxy
  rw [map_mul, haev] at h2
  simpa using h2

/-- The image of a polynomial in `ℚ(j)` under a ring hom `g` lies in `ℚ(g j)`. -/
theorem polyImage_mem {F' : Type} [Field F'] [Algebra ℚ F'] (g : LeafModCurves.Qj →+* F')
    (p : Polynomial ℚ) :
    g (algebraMap (Polynomial ℚ) LeafModCurves.Qj p) ∈
      IntermediateField.adjoin ℚ {g RatFunc.X} := by
  have hring : g.comp (algebraMap (Polynomial ℚ) LeafModCurves.Qj) =
      Polynomial.eval₂RingHom (algebraMap ℚ F') (g RatFunc.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have e1 := eq_ratCast ((g.comp (algebraMap (Polynomial ℚ) LeafModCurves.Qj)).comp
        Polynomial.C) a
      have e2 := eq_ratCast (algebraMap ℚ F') a
      simp only [RingHom.comp_apply] at e1
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [e1, e2]
    · simp [RatFunc.algebraMap_X]
  have h1 : g (algebraMap (Polynomial ℚ) LeafModCurves.Qj p) = Polynomial.aeval (g RatFunc.X) p := by
    rw [← RingHom.comp_apply, hring, Polynomial.aeval_def]; rfl
  rw [h1]
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ _
    (Polynomial.aeval_mem_adjoin_singleton ℚ (g RatFunc.X))

theorem image_mem {F' : Type} [Field F'] [Algebra ℚ F'] (g : LeafModCurves.Qj →+* F')
    (x : LeafModCurves.Qj) : g x ∈ IntermediateField.adjoin ℚ {g RatFunc.X} := by
  rw [← RatFunc.num_div_denom x, map_div₀]
  exact div_mem (polyImage_mem g _) (polyImage_mem g _)

/-- **Glue piece 3 from `BelyiX1` (proved, leaf-adopt3).** -/
theorem x1BelyiOnModel_of_belyiX1 (hB : LeafModCurves.BelyiX1) : X1BelyiOnModel := by
  rintro N hN J ⟨X, P₀, aj, ⟨hC, hI, P, hP, ⟨φ⟩⟩, hJac⟩
  letI := ZInQ.LeafPush2.ffAlgebra X
  obtain ⟨hBel, hdeg⟩ := hB N P hN hP
  let ψ : LeafModCurves.fieldX1 P ≃ₐ[ℚ] X.left.functionField := φ.symm.toRatAlgEquiv
  let g : LeafModCurves.Qj →+* X.left.functionField :=
    (φ.symm : LeafModCurves.fieldX1 P →+* X.left.functionField).comp
      (algebraMap LeafModCurves.Qj (LeafModCurves.fieldX1 P))
  let t : X.left.functionField :=
    ψ (algebraMap LeafModCurves.Qj (LeafModCurves.fieldX1 P) (RatFunc.X / 1728))
  have ht : t = g (RatFunc.X / 1728) := rfl
  have h1728 : (1728 : X.left.functionField) ≠ 0 := by
    rw [← map_ofNat g 1728]; exact (map_ne_zero g).2 (by norm_num)
  have hgX : g RatFunc.X = 1728 * t := by
    rw [ht, map_div₀, map_ofNat]
    field_simp
  have hmem : ∀ x, g x ∈ IntermediateField.adjoin ℚ {t} := by
    intro x
    have h1 : IntermediateField.adjoin ℚ {g RatFunc.X} ≤ IntermediateField.adjoin ℚ {t} := by
      rw [IntermediateField.adjoin_simple_le_iff, hgX]
      exact mul_mem (by simpa using IntermediateField.natCast_mem _ 1728)
        (IntermediateField.mem_adjoin_simple_self ℚ t)
    exact h1 (image_mem g x)
  have hsurj : ∀ y ∈ IntermediateField.adjoin ℚ {t}, ∃ x, g x = y := by
    intro y hy
    let S : IntermediateField ℚ X.left.functionField :=
      g.fieldRange.toIntermediateField (fun q => ⟨(q : LeafModCurves.Qj), by simp⟩)
    have hle : IntermediateField.adjoin ℚ {t} ≤ S := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨RatFunc.X / 1728, rfl⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  let i0 : LeafModCurves.Qj →+* IntermediateField.adjoin ℚ {t} := g.codRestrict _ hmem
  have hi0 : Function.Bijective i0 := by
    refine ⟨fun a b hab => g.injective (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hsurj y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  let i := RingEquiv.ofBijective i0 hi0
  have hfin : Module.finrank LeafModCurves.Qj (LeafModCurves.fieldX1 P) =
      Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField :=
    Algebra.finrank_eq_of_equiv_equiv i φ.symm (RingHom.ext fun _ => rfl)
  haveI : FiniteDimensional LeafModCurves.Qj (LeafModCurves.fieldX1 P) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := LeafModCurves.Qj) (LeafModCurves.xCoord P))
  refine ⟨X, hC, hI, P₀, aj, hJac, t, isBelyiFunction_map ψ hBel, _, hfin.symm,
    Module.finrank_pos, hdeg⟩

end X1Transport
