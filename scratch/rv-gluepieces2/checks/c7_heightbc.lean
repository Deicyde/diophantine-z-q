/-! ## rv-gluepieces2 check (g): height-bc's reduction of field 9 (`HodgeLineBaseChange`), re-elaborated
over G0Assemble's `ZInQ.DefFaltings.AbVar` copy: scratch/height-bc/Final.lean minus its import and
#print lines, with the one line `open PkgI3 (AbVar)` removed (so `AbVar` is DefFaltings' copy). -/


/-! # height-bc: glue H4a (`ModelHeightBaseChange`) and `HodgeLineBaseChange`

Self-contained (Mathlib + project only; no `sorry`, no `axiom`).
* Verbatim copies: `IsBaseChangeOf`, `ModelHeightBaseChange` (from `scratch/h5-glue/H5Final.lean`,
  over the kernel's objects); `ModelHeightBaseChangeLE`, the Arakelov half of H4a,
  `MetrizationBaseChange`, `HodgeLineBaseChange` and `metrizationBaseChange_of_hodgeLine` (from
  `scratch/g0-stablebc/Main.part`, there over a verbatim copy of the same objects).
* Part A (new): the descent half `ModelHeightBaseChangeGE` and the reduction of H4a (`=`) to one
  geometric statement `HodgeLineBaseChangeDescent` (`modelHeightBaseChange_of_descent`).
* Part B (new): the natural map of a base change `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`: `bcProj` (π), `bcMap`
  (stalk map at the origin), `bcCot`, `bcExt`, `bcHodge` (ψ = L' ⊗ ⋀^g π^*), `bcPts` (β on complex
  points); compatibility of germs and Jacobians (`jacDet_bcPts`); half of the lattice clause
  (`span_bcHodge_le`).
* Part C (new): glue statements over the natural map. Proved here: `ptsBaseChangeMul`,
  `ptsBaseChangeBij`, `detLatticeBC_of_omega`, `hodgeSpanBC_of`, `jacobianPullbackSpan_of`,
  `uniformizationLift_of`, `jacobianSemilinear_of`, and the glue statement `GermDerivation`
  itself (`germDerivation`, from the section `GermDer`: germs along `Φ` form a ring
  homomorphism near `0`, germs in `𝔪_ξ` vanish at the unit point, structure sections take the
  value `τ(r)`).
  **Main results** (final form): `modelHeightBaseChange_of_glue4` and
  `hodgeLineBaseChange_of_glue4` (H4a and `HodgeLineBaseChange`, verbatim, from the four glue
  statements `HodgeBCInjective`, `CotangentSpanBC`, `OmegaBaseChange`,
  `UniformizationLiftAnalytic`), and `modelHeightBaseChangeGE_of_main` (the descent half from
  `HodgeBCInjective` and `OmegaBaseChange`). Coarser forms: `_of_final`, `_of_glue5`,
  `_of_five`, `_of_main`, `_of_four`, `_of_glue`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-! ## Verbatim copies -/

/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

-- copied verbatim from scratch/h5-glue/H5Final.lean

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

-- copied verbatim from scratch/g0-stablebc/Main.part

/-- **Glue H4a, the inequality half (used here).** `h(𝒢_{L'}) ≤ h(𝒢)` for a group model `𝒢` and
a base change `𝒢'` of it. Implied by `ModelHeightBaseChange` (`modelHeightBaseChangeLE`
below). Same justification (h5-neron §2): `ω` of a smooth model commutes with base change, the
Arakelov degree is multiplied by `[L':L]`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_{τ'|_L}`. -/
def ModelHeightBaseChangeLE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height


-- copied verbatim from scratch/g0-stablebc/Main.part (lines 240-500)
/-! ### The Arakelov half of H4a (proved) and the geometric half (glue, stated)

`modelHeight_eq_of_isHodgeBaseChange`: if `D'` over `L'` is obtained from `D` over `L` by base
change (a semilinear injection `ψ` on the Hodge lines, with `⋀^g ω' = 𝓞_{L'} · ψ(⋀^g ω)`,
restricted period lattices and compatible coefficient maps), the model heights agree. The finite
part reduces to fractional ideals (`N(𝔞𝓞_{L'}) = N(𝔞)^{[L':L]}`, def-faltings'
`absNorm_extendedHom`) and the archimedean part to `sum_embeddings_comp`. -/

section ArakelovBC

open scoped nonZeroDivisors

/-- `secIndex` is invariant under an injective linear map. -/
theorem secIndex_map {K : Type*} [Field K] [NumberField K] {V W : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (f : V →ₗ[𝓞 K] W) (hf : Function.Injective f)
    (Λ : Submodule (𝓞 K) V) (w : V) : secIndex (Λ.map f) (f w) = secIndex Λ w := by
  unfold secIndex
  rw [← Set.image_singleton, ← Submodule.map_span, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/-- A finite index kills the quotient: `#(Λ/𝓞η) • x ∈ 𝓞η` for `x ∈ Λ`. -/
theorem secIndex_nsmul_mem {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) (w : V)
    {x : V} (hx : x ∈ Λ) : secIndex Λ w • x ∈ Submodule.span (𝓞 K) {w} :=
  AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 K) {w}).toAddSubgroup hx

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- **The finite part of base change**: `#(Λ'/𝓞_{L'}ιη) = #(Λ/𝓞_Lη)^{[L':L]}` for
`Λ' = 𝓞_{L'} · ψ(Λ)`. -/
theorem secIndex_baseChange {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1) (ψ : V →+ V')
    (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) (Λ : Submodule (𝓞 L) V)
    {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0) (hi : secIndex Λ w ≠ 0) :
    secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) = secIndex Λ w ^ Module.finrank L L' := by
  -- coordinates `c ↦ c • w` and `c ↦ c • ιη`
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  let φ' : L' →ₗ[𝓞 L'] V' := (LinearMap.toSpanSingleton L' V' (ψ w)).restrictScalars (𝓞 L')
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφ' : ∀ c, φ' c = c • ψ w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφ'inj : Function.Injective φ' := fun a b h => by
    rw [hφ', hφ'] at h
    exact smul_left_injective L' hη' h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  -- `ψ(Λ) = φ'(L'-image of I)`
  have himg : ψ '' (Λ : Set V) = φ' '' (algebraMap L L' '' (I : Set L)) := by
    rw [hΛ, Submodule.map_coe, Set.image_image, Set.image_image]
    refine Set.image_congr fun c _ => ?_
    rw [hφ, hφ', hsmul]
  have hspan : Submodule.span (𝓞 L') (ψ '' (Λ : Set V)) =
      (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))).map φ' := by
    rw [himg, Submodule.map_span]
  have hidx' : secIndex (Submodule.span (𝓞 L') (ψ '' (Λ : Set V))) (ψ w) =
      secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 := by
    rw [hspan, show ψ w = φ' 1 by simp [hφ']]
    exact secIndex_map φ' hφ'inj _ 1
  -- `I` is a fractional ideal
  set N := secIndex I 1 with hN
  have hN0 : N ≠ 0 := hidx ▸ hi
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0), fun b hb => ?_⟩
    have hm := secIndex_nsmul_mem I 1 hb
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← ha, Algebra.smul_def, _root_.mul_one]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have hI₀ : (I₀ : Submodule (𝓞 L) L) = I := rfl
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  have e2 := secIndex_mul_absNorm (FractionalIdeal.extendedHom L' (𝓞 L') I₀) (x := 1)
    (by
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span]
      exact Submodule.subset_span ⟨1, h1I, map_one _⟩) one_ne_zero
  rw [FractionalIdeal.coe_extendedHom_eq_span, absNorm_extendedHom, map_one, abs_one] at e2
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  have e2' : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) *
      FractionalIdeal.absNorm I₀ ^ Module.finrank L L' = 1 := e2
  rw [← hidx, hidx']
  have key : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) =
      (secIndex I 1 : ℚ) ^ Module.finrank L L' := by
    rw [eq_inv_of_mul_eq_one_left e1', eq_inv_of_mul_eq_one_left e2', inv_pow]
  exact_mod_cast key

/-- **Base change data for Hodge data** `D/L ↦ D'/L'` along a semilinear injection `ψ`. -/
structure IsHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    (D : HodgeData L g V) (D' : HodgeData L' g V') (ψ : V →+ V') : Prop where
  smul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v
  ne_zero : ∀ v, v ≠ 0 → ψ v ≠ 0
  lattice : D'.lattice = Submodule.span (𝓞 L') (ψ '' D.lattice)
  periods : ∀ τ' : L' →+* ℂ, D'.periods τ' = D.periods (τ'.comp (algebraMap L L'))
  coeff : ∀ (τ' : L' →+* ℂ) v, D'.coeff τ' (ψ v) = D.coeff (τ'.comp (algebraMap L L')) v

/-- **The model height is invariant under base change of Hodge data.** Proved. -/
theorem modelHeight_eq_of_isHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (D : HodgeData L g V) (D' : HodgeData L' g V')
    (ψ : V →+ V') (h : IsHodgeBaseChange D D' ψ) : D'.modelHeight = D.modelHeight := by
  obtain ⟨w, hηM, hη, hi⟩ := D.isLattice
  have hη' : ψ w ≠ 0 := h.ne_zero w hη
  have hηM' : ψ w ∈ D'.lattice := by
    rw [h.lattice]; exact Submodule.subset_span ⟨w, hηM, rfl⟩
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη']
  have hsec : secIndex D'.lattice (ψ w) = secIndex D.lattice w ^ Module.finrank L L' := by
    rw [h.lattice]
    exact secIndex_baseChange D.finrank_eq_one ψ h.smul D.lattice hηM hη hη' hi
  have hsum : ∑ τ' : L' →+* ℂ, Real.log (torusMetricSq (D'.periods τ') (D'.coeff τ' (ψ w))) =
      Module.finrank L L' *
        ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) := by
    simp only [h.periods, h.coeff]
    exact sum_embeddings_comp (fun σ => Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)))
  rw [hsec, hsum, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end ArakelovBC

/-- **Glue H4a, geometric half (stated).** A metrization of a group model `𝒢/𝓞_L` induces one of
its base change `𝒢'/𝓞_{L'}`, by base change of the Hodge data: `ψ` is the natural map
`⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (from `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`), `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`
(formation of `e*Ω¹` of a smooth group scheme commutes with base change; EGA IV 17.2.3,
UNVERIFIED locator), and at `τ' : L' → ℂ` the uniformization of `𝒢(ℂ)_{τ'|_L}` composed with the
bijection `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` (universal property of the pullback). Glue (a property of
def-faltings' definitions), STANDARD; not a literature leaf. -/
def MetrizationBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 →
    ∀ (g : ℕ) (Mm : MetrizedModel A L g), Mm.model = 𝒢 →
    ∃ (Mm' : MetrizedModel A L' g) (ψ : Mm.model.hodgeSpace g →+ Mm'.model.hodgeSpace g),
      Mm'.model = 𝒢' ∧ IsHodgeBaseChange Mm.hodge Mm'.hodge ψ

/-- **`ModelHeightBaseChangeLE` from the geometric half.** Proved. -/
theorem modelHeightBaseChangeLE_of_metrization (h : MetrizationBaseChange) :
    ModelHeightBaseChangeLE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  obtain ⟨Mm', ψ, hM', hι⟩ := h K A L L' 𝒢 𝒢' h𝒢 g Mm hM
  refine iInf_le_of_le g (iInf_le_of_le Mm' (iInf_le_of_le hM' ?_))
  rw [modelHeight_eq_of_isHodgeBaseChange Mm.hodge Mm'.hodge ψ hι]

/-- **Glue H4a, geometric content, stated without metrized models.** For a base change `𝒢'` of
`𝒢` and each `g`, the natural map `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (induced by
`𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`):
* is `L`-semilinear over `L → L'` and injective on nonzero vectors, and the Hodge space of `𝒢'` is
  an `L'`-line when that of `𝒢` is an `L`-line (it is `L' ⊗_L` of it);
* carries the lattice: `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)` (formation of `e*Ω¹` of a smooth group
  scheme commutes with base change; EGA IV 17.2.3, UNVERIFIED locator);
* is compatible with uniformizations: an analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` gives one
  `Φ'` of `𝒢'(ℂ)_{τ'}` with the same kernel (compose with the bijection
  `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` of the pullback), and if a coefficient map `c` is computed by `Φ` on
  wedges of germs, its `τ'`-semilinear extension `c'` (`c' ∘ ψ = c`) is computed by `Φ'` on wedges
  of germs of `𝒢'` (both sides are `τ'`-semilinear alternating functions of the differentials
  `df'_i`, and they agree on pulled-back germs, which span).
Glue (a property of def-faltings' definitions), STANDARD; not a literature leaf. -/
def HodgeLineBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 → Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      ∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **`MetrizationBaseChange` from `HodgeLineBaseChange`.** The Hodge data of `𝒢'`: lattice
`⋀^g ω_{𝒢'}`, restricted period lattices, and the `τ'`-semilinear extension of the coefficient
maps along `ψ` (through the coordinate `c ↦ c · ψ(w)` on the `L'`-line). Proved. -/
theorem metrizationBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    MetrizationBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g Mm hM
  subst hM
  obtain ⟨ψ, hsmul, hne, hfin, hlat, harch⟩ := h K A L L' Mm.model 𝒢' h𝒢 g
  obtain ⟨w, hwM, hw, hi⟩ := Mm.hodge.isLattice
  have hw' : ψ w ≠ 0 := hne w hw
  have hfin' : Module.finrank L' (𝒢'.hodgeSpace g) = 1 := hfin Mm.hodge.finrank_eq_one
  -- the coordinate `c ↦ c • ψ w` on the `L'`-line
  have hinj : Function.Injective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun a b hab => smul_left_injective L' hw' hab
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun v => (finrank_eq_one_iff_of_nonzero' (ψ w) hw').mp hfin' v
  let e : L' ≃ₗ[L'] 𝒢'.hodgeSpace g := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have he : ∀ c, e c = c • ψ w := fun c => rfl
  -- the extended coefficient maps
  let lin : ∀ τ' : L' →+* ℂ, L' →ₛₗ[τ'] ℂ := fun τ' =>
    { toFun := fun c => τ' c * Mm.hodge.coeff (τ'.comp (algebraMap L L')) w
      map_add' := fun a b => by rw [map_add, add_mul]
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc] }
  let coeff' : ∀ τ' : L' →+* ℂ, 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ := fun τ' =>
    (lin τ').comp e.symm.toLinearMap
  have hcoeff' : ∀ (τ' : L' →+* ℂ) v,
      coeff' τ' (ψ v) = Mm.hodge.coeff (τ'.comp (algebraMap L L')) v := by
    intro τ' v
    obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp Mm.hodge.finrank_eq_one v
    have h1 : e.symm (ψ (a • w)) = algebraMap L L' a := by
      rw [LinearEquiv.symm_apply_eq, he, hsmul]
    show lin τ' (e.symm (ψ (a • w))) = _
    rw [h1]
    show τ' (algebraMap L L' a) * _ = _
    rw [map_smulₛₗ, smul_eq_mul]
    rfl
  have hlat' : 𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' Mm.hodge.lattice) := by
    rw [hlat, Mm.lattice_eq]
  let D' : HodgeData L' g (𝒢'.hodgeSpace g) :=
    { lattice := 𝒢'.detLattice g
      finrank_eq_one := hfin'
      isLattice := by
        refine ⟨ψ w, ?_, hw', ?_⟩
        · rw [hlat']; exact Submodule.subset_span ⟨w, hwM, rfl⟩
        · rw [hlat', secIndex_baseChange Mm.hodge.finrank_eq_one ψ hsmul _ hwM hw hw' hi]
          exact pow_ne_zero _ hi
      periods := fun τ' => Mm.hodge.periods (τ'.comp (algebraMap L L'))
      periods_discrete := fun τ' => Mm.hodge.periods_discrete _
      periods_isZLattice := fun τ' => Mm.hodge.periods_isZLattice _
      coeff := coeff'
      coeff_ne_zero := fun τ' h0 => by
        have h2 := hcoeff' τ' w
        rw [h0, LinearMap.zero_apply] at h2
        exact Mm.hodge.coeff_apply_ne_zero _ hw h2.symm }
  let Mm' : MetrizedModel A L' g :=
    { model := 𝒢'
      hodge := D'
      lattice_eq := rfl
      arch := fun τ' => by
        obtain ⟨Φ, hΦ, hc⟩ := Mm.arch (τ'.comp (algebraMap L L'))
        obtain ⟨Φ', hΦ', hc'⟩ := harch τ' _ Φ hΦ
        exact ⟨Φ', hΦ', hc' _ (coeff' τ') hc (hcoeff' τ')⟩ }
  exact ⟨Mm', ψ, rfl,
    { smul := hsmul
      ne_zero := hne
      lattice := hlat'
      periods := fun _ => rfl
      coeff := hcoeff' }⟩


/-! ## Part A (new): the descent half of H4a -/

section DescentArakelov

open scoped nonZeroDivisors

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- Every complex embedding of `L` extends to `L'`. -/
theorem exists_comp_eq (σ : L →+* ℂ) : ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ := by
  let _ : Algebra L ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic L L' := Algebra.IsAlgebraic.of_finite L L'
  refine ⟨(IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).commutes x

/-- An element of `L` whose image in `L'` is an algebraic integer is an algebraic integer. -/
theorem exists_ringOfIntegers_of_algebraMap {c : L} {a : 𝓞 L'}
    (h : algebraMap (𝓞 L') L' a = algebraMap L L' c) : ∃ y : 𝓞 L, algebraMap (𝓞 L) L y = c := by
  have h1 : IsIntegral ℤ (algebraMap L L' c) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 L')).mpr ⟨a, h⟩
  have h2 : IsIntegral ℤ c :=
    (isIntegral_algHom_iff (algebraMap L L').toIntAlgHom (algebraMap L L').injective).mp h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp h2

/-- **Descent of finite index**: if `Λ' = 𝓞_{L'} · ψ(Λ)` has finite index over `𝓞_{L'} ψ(w)`,
then `Λ` has finite index over `𝓞_L w` (`Λ` is then a fractional ideal in coordinates). -/
theorem secIndex_ne_zero_of_baseChange {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1)
    (ψ : V →+ V') (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v)
    (Λ : Submodule (𝓞 L) V) {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0)
    (hi' : secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) ≠ 0) : secIndex Λ w ≠ 0 := by
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  set N := secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) with hN
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hi'), fun b hb => ?_⟩
    have hbΛ : b • w ∈ Λ := hb
    have hm := secIndex_nsmul_mem (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w)
      (Submodule.subset_span ⟨_, hbΛ, rfl⟩)
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    rw [hsmul] at ha
    have h2 : (algebraMap (𝓞 L') L' a) • ψ w = algebraMap L L' ((N : L) * b) • ψ w := by
      rw [algebraMap_smul, ha, map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    obtain ⟨y, hy⟩ := exists_ringOfIntegers_of_algebraMap (smul_left_injective L' hη' h2)
    refine ⟨y, ?_⟩
    rw [hy, Algebra.smul_def, map_natCast]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  rw [← hidx]
  intro h0
  rw [h0] at e1'
  simp at e1'

end DescentArakelov

/-- **Glue H4a, the descent half.** `h(𝒢) ≤ h(𝒢_{L'})` for a base change `𝒢'` of `𝒢`. Together
with `ModelHeightBaseChangeLE` it is `ModelHeightBaseChange`. -/
def ModelHeightBaseChangeGE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢.height ≤ 𝒢'.height

/-- **Glue H4a, geometric content in both directions** (a property of def-faltings' definitions;
STANDARD, not a literature leaf). For a base change `𝒢'` of `𝒢` and each `g`, there is a map
`ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (the Prop asserts `∃ ψ`; the witness used in Part C is the
natural map `bcHodge`, induced by `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`) satisfying the clauses of
`HodgeLineBaseChange`, with the line clause as an equivalence (`hodgeSpace' = L' ⊗_L hodgeSpace`),
and in addition the *descent* clause: an analytic uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` gives one
`Φ` of `𝒢(ℂ)_σ`, `σ = τ'|_L`, with the same kernel (compose with the bijection
`β : 𝒢'(ℂ)_{τ'} ≅ 𝒢(ℂ)_σ` of the pullback), and a coefficient map `c'` computed by `Φ'` on wedges of
germs of `𝒢'` computes `jacDet Φ` on wedges of germs of `𝒢` through `ψ`
(`ψ(wedge f) = wedge' (f pulled back)`, and the Jacobians agree along the bijection). -/
def HodgeLineBaseChangeDescent : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

/-- **The descent half of `HodgeLineBaseChangeDescent`** (all clauses except the forward
uniformization clause); it is what `ModelHeightBaseChangeGE` uses. -/
def HodgeLineDescentHalf : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

theorem descentHalf_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineDescentHalf := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, -, h6⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3, h4, h6⟩

/-- `HodgeLineBaseChangeDescent` implies `HodgeLineBaseChange`. Proved. -/
theorem hodgeLineBaseChange_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, h5, -⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3.mp, h4, h5⟩

/-- **`ModelHeightBaseChangeGE` from the geometric statement.** A metrization of `𝒢'` gives one
of `𝒢`: lattice `⋀^g ω_𝒢`, and at each `σ : L → ℂ` the data of `𝒢'` at a place `τ'` above `σ`
that maximizes `log ‖ψ w‖²_{τ'}` (the maximum over the fibre is at least the average). Proved. -/
theorem modelHeightBaseChangeGE_of_descentHalf (h : HodgeLineDescentHalf) :
    ModelHeightBaseChangeGE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm' => le_iInf fun hM' => ?_
  subst hM'
  obtain ⟨ψ, hsmul, hne, hfin, hlat, hdesc⟩ := h K A L L' 𝒢 Mm'.model h𝒢 g
  have hfinL : Module.finrank L (𝒢.hodgeSpace g) = 1 := hfin.mpr Mm'.hodge.finrank_eq_one
  have hlat' : Mm'.hodge.lattice = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) := by
    rw [Mm'.lattice_eq, hlat]
  obtain ⟨s', hs'M, hs', -⟩ := Mm'.hodge.isLattice
  have hex : ∃ w ∈ 𝒢.detLattice g, ψ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hs'
    rw [hlat'] at hs'M
    have hsub : ψ '' (𝒢.detLattice g : Set (𝒢.hodgeSpace g)) ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcon x hx
    have h0 := Submodule.span_mono (R := 𝓞 L') hsub hs'M
    simpa using h0
  obtain ⟨w, hwM, hw'⟩ := hex
  have hw : w ≠ 0 := by
    rintro rfl
    exact hw' (map_zero ψ)
  have hψwM : ψ w ∈ Mm'.hodge.lattice := by
    rw [hlat']
    exact Submodule.subset_span ⟨w, hwM, rfl⟩
  have hi' : secIndex Mm'.hodge.lattice (ψ w) ≠ 0 :=
    Mm'.hodge.hodgeBundle.secIndex_ne_zero hψwM hw'
  have hi : secIndex (𝒢.detLattice g) w ≠ 0 :=
    secIndex_ne_zero_of_baseChange hfinL ψ hsmul _ hwM hw hw' (hlat' ▸ hi')
  -- the place above `σ` maximizing the archimedean term
  let F : (L' →+* ℂ) → ℝ := fun τ' =>
    Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w)))
  have hext : ∀ σ : L →+* ℂ, ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ ∧
      ∀ τ'' : L' →+* ℂ, τ''.comp (algebraMap L L') = σ → F τ'' ≤ F τ' := by
    intro σ
    classical
    obtain ⟨τ₀, hτ₀⟩ := exists_comp_eq (L' := L') σ
    have hne' : (Finset.univ.filter
        fun τ' : L' →+* ℂ => τ'.comp (algebraMap L L') = σ).Nonempty :=
      ⟨τ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ₀⟩⟩
    obtain ⟨τ', hτ'm, hmax⟩ := Finset.exists_max_image _ F hne'
    exact ⟨τ', (Finset.mem_filter.mp hτ'm).2,
      fun τ'' h'' => hmax τ'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h''⟩)⟩
  choose ch hch hmax using hext
  let coeff : ∀ σ : L →+* ℂ, 𝒢.hodgeSpace g →ₛₗ[σ] ℂ := fun σ =>
    { toFun := fun v => Mm'.hodge.coeff (ch σ) (ψ v)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a v => by
        rw [hsmul, map_smulₛₗ, smul_eq_mul, smul_eq_mul]
        have hσa : (ch σ) (algebraMap L L' a) = σ a := by
          have := congrArg (fun f : L →+* ℂ => f a) (hch σ)
          simpa using this
        rw [hσa] }
  let D : HodgeData L g (𝒢.hodgeSpace g) :=
    { lattice := 𝒢.detLattice g
      finrank_eq_one := hfinL
      isLattice := ⟨w, hwM, hw, hi⟩
      periods := fun σ => Mm'.hodge.periods (ch σ)
      periods_discrete := fun σ => Mm'.hodge.periods_discrete _
      periods_isZLattice := fun σ => Mm'.hodge.periods_isZLattice _
      coeff := coeff
      coeff_ne_zero := fun σ h0 => by
        have h2 : coeff σ w = 0 := by rw [h0]; rfl
        exact Mm'.hodge.coeff_apply_ne_zero (ch σ) hw' h2 }
  let Mm : MetrizedModel A L g :=
    { model := 𝒢
      hodge := D
      lattice_eq := rfl
      arch := fun σ => by
        obtain ⟨Φ', hΦ', hc'⟩ := Mm'.arch (ch σ)
        obtain ⟨Φ, hΦ, hc⟩ := hdesc σ (ch σ) (hch σ) _ Φ' hΦ'
        exact ⟨Φ, hΦ, fun f => hc _ hc' f⟩ }
  refine iInf_le_of_le g (iInf_le_of_le Mm (iInf_le_of_le rfl ?_))
  refine EReal.coe_le_coe_iff.mpr ?_
  show D.modelHeight ≤ Mm'.hodge.modelHeight
  rw [D.modelHeight_eq hwM hw, Mm'.hodge.modelHeight_eq hψwM hw']
  have hsec : secIndex Mm'.hodge.lattice (ψ w) =
      secIndex (𝒢.detLattice g) w ^ Module.finrank L L' := by
    rw [hlat']
    exact secIndex_baseChange hfinL ψ hsmul _ hwM hw hw' hi
  have hsum : ∑ τ' : L' →+* ℂ, F τ' ≤ Module.finrank L L' * ∑ σ : L →+* ℂ, F (ch σ) := by
    rw [← sum_embeddings_comp (fun σ => F (ch σ))]
    exact Finset.sum_le_sum fun τ' _ => hmax _ τ' rfl
  have hD : ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) =
      ∑ σ : L →+* ℂ, F (ch σ) := rfl
  have hD' : ∑ τ' : L' →+* ℂ,
      Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w))) =
      ∑ τ' : L' →+* ℂ, F τ' := rfl
  rw [hD, hD', hsec, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow, div_le_div_iff₀ hK (mul_pos hK hL)]
  have := mul_le_mul_of_nonneg_left hsum hK.le
  nlinarith

theorem modelHeightBaseChangeGE_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_descentHalf (descentHalf_of_descent h)

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim statement) from `HodgeLineBaseChangeDescent`.**
Proved. -/
theorem modelHeightBaseChange_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  exact le_antisymm
    (modelHeightBaseChangeLE_of_metrization
      (metrizationBaseChange_of_hodgeLine (hodgeLineBaseChange_of_descent h)) K A L L' 𝒢 𝒢' h𝒢)
    (modelHeightBaseChangeGE_of_descent h K A L L' 𝒢 𝒢' h𝒢)


/-! # Part B: the natural map of a base change (from `Natural.lean`) -/

/-- `Spec 𝓞_{L'} → Spec 𝓞_L`. -/
noncomputable abbrev bO (L L' : Type) [Field L] [Field L'] [Algebra L L'] :
    Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

section Construction

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

theorem bO_genericPt : bO L L' (genericPt L') = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) (𝓞 L')) (genericPt L') = _
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 L) (𝓞 L')) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L'))

theorem bO_appTop (r : 𝓞 L) :
    (bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv (algebraMap (𝓞 L) (𝓞 L') r) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom
      ((bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
        algebraMap (𝓞 L) (𝓞 L') r := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← h3, Iso.hom_inv_id_apply]

variable (𝒢 : GroupModel A L) (𝒢' : GroupModel A L')
  (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)

/-- `e` is an isomorphism of group schemes (the content of `IsBaseChangeOf`). -/
def IsMonBC : Prop :=
  letI : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  IsMonHom e.hom

/-- The projection `π : 𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'} → 𝒢`. -/
noncomputable def bcProj : 𝒢'.G.left ⟶ 𝒢.G.left := e.hom.left ≫ pullback.fst _ _

theorem bcProj_w : bcProj 𝒢 𝒢' e ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := by
  unfold bcProj
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w e.hom

variable {𝒢 𝒢' e} in
theorem bcProj_unit (he : IsMonBC 𝒢 𝒢' e) :
    𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e = bO L L' ≫ 𝒢.unitSection := by
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  have h1 : (η[𝒢'.G] ≫ e.hom).left = (η[(Over.pullback (bO L L')).obj 𝒢.G]).left :=
    congrArg Over.Hom.left (IsMonHom.one_hom (f := e.hom))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.fst _ _ =
      bO L L' := by
    have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback (bO L L')))
    have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
      (g := bO L L')
    calc _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫
          (pullback.fst _ _ ≫ (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) := by
            exact congrArg (fun k => _ ≫ k) (Category.comp_id _).symm
      _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.snd _ _ ≫ bO L L' := by
            rw [hc]
      _ = bO L L' := by
            rw [← Category.assoc]
            erw [hw]
            exact Category.id_comp _
  unfold GroupModel.unitSection bcProj
  rw [← Category.assoc, ← Over.comp_left]
  erw [h1]
  show (Functor.LaxMonoidal.ε _ ≫ (Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ = _
  have hmap : ((Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ η[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc]
  erw [hmap]
  rw [← Category.assoc]
  erw [hε]

variable {𝒢 𝒢' e} in
theorem bcProj_genericUnit (he : IsMonBC 𝒢 𝒢' e) :
    bcProj 𝒢 𝒢' e 𝒢'.genericUnit = 𝒢.genericUnit := by
  have h2 := congrArg (fun φ => φ (genericPt L')) (bcProj_unit he)
  unfold GroupModel.genericUnit
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  simp only
  rw [bO_genericPt]

variable {𝒢 𝒢' e}

/-- The comparison `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}` along `π` (`π(ξ') = ξ`). -/
noncomputable def bcMap (he : IsMonBC 𝒢 𝒢' e) : 𝒢.genStalk ⟶ 𝒢'.genStalk :=
  𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (bcProj_genericUnit he)).specializes ≫
    (bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit

/-- `bcMap` is `π^*` on germs. -/
theorem bcMap_germ (he : IsMonBC 𝒢 𝒢' e) (U : 𝒢.G.left.Opens) (hx : 𝒢.genericUnit ∈ U)
    (hx' : 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) (s : Γ(𝒢.G.left, U)) :
    (bcMap he) (𝒢.G.left.presheaf.germ U 𝒢.genericUnit hx s) =
      𝒢'.G.left.presheaf.germ ((bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) 𝒢'.genericUnit hx'
        ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold bcMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem isIso_stalkSpecializes_bcMap (he : IsMonBC 𝒢 𝒢' e) :
    IsIso (𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes) :=
  Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (bcProj_genericUnit he)).symm)

theorem bcMap_mem_maximalIdeal (he : IsMonBC 𝒢 𝒢' e) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcMap he t ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := by
  haveI := isIso_stalkSpecializes_bcMap he
  set e' := 𝒢.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (bcProj_genericUnit he)).specializes
  have h1 : e' t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e').hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  exact map_nonunit ((bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit).hom _ h1

/-- `bcMap` is compatible with the structure maps `𝓞_L → 𝓞_{L'}`. -/
theorem bcMap_structMap (he : IsMonBC 𝒢 𝒢' e) (r : 𝓞 L) :
    bcMap he (𝒢.structMap r) = 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) =
      𝒢'.G.left.presheaf.germ ⊤ 𝒢'.genericUnit trivial
      (𝒢'.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv
        (algebraMap (𝓞 L) (𝓞 L') r))) := rfl
  rw [e1, e2, bcMap_germ he ⊤ (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
    (show 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) from trivial)]
  have hw := bcProj_w 𝒢 𝒢' e
  have : 𝒢.G.hom.appTop ≫ (bcProj 𝒢 𝒢' e).appTop = (bO L L').appTop ≫ 𝒢'.G.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop]
  rw [← bO_appTop, ← CommRingCat.comp_apply (bO L L').appTop, ← this, CommRingCat.comp_apply]
  rfl

/-- The `𝓞_L`-module structure on `ω_{A_{L'}}` by restriction along `𝓞_L → 𝓞_{L'}`. -/
noncomputable abbrev cotRes (𝒢' : GroupModel A L') : Module (𝓞 L) 𝒢'.cotangent :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

/-- **The induced map `ω_{A_L} → ω_{A_{L'}}` on cotangent spaces at the origin** (`π^*`),
semilinear over `𝓞_L → 𝓞_{L'}`. -/
noncomputable def bcCot (he : IsMonBC 𝒢 𝒢' e) :
    𝒢.cotangent →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] 𝒢'.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
    (IsLocalRing.maximalIdeal 𝒢'.genStalk) (bcMap he).hom.toIntAlgHom
    (fun t ht => bcMap_mem_maximalIdeal he t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (bcMap he).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒢.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢'.genStalk).comap ψ :=
      fun t ht => bcMap_mem_maximalIdeal he t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
        (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h (𝒢.structMap r • Ideal.toCotangent _ m) =
      𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) • Ideal.mapCotangent
        (IsLocalRing.maximalIdeal 𝒢.genStalk) (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h
        (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [bcMap_structMap]

theorem bcCot_dCls (he : IsMonBC 𝒢 𝒢' e) (t : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcCot he (𝒢.dCls t) = 𝒢'.dCls ⟨bcMap he t, bcMap_mem_maximalIdeal he t t.2⟩ := rfl

/-! ### The map of Hodge lines `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` -/

open scoped TensorProduct
open ExteriorAlgebra

/-- The `𝓞_L`-module structure on `⋀^g_{𝓞_{L'}} ω_{A_{L'}}` by restriction of scalars. -/
noncomputable abbrev extRes (𝒢' : GroupModel A L') (g : ℕ) :
    Module (𝓞 L) (exteriorPower (𝓞 L') g 𝒢'.cotangent) :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

theorem bcCot_update (he : IsMonBC 𝒢 𝒢' e) {g : ℕ} [DecidableEq (Fin g)]
    (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent) :
    (fun j => bcCot he (Function.update m i z j)) =
      Function.update (fun j => bcCot he (m j)) i (bcCot he z) := by
  funext j
  exact Function.apply_update (fun _ => bcCot he) m i z j

/-- `v ↦ π^*v₁ ∧ ⋯ ∧ π^*v_g`, alternating over `𝓞_L`. -/
noncomputable def bcAlt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    letI := extRes (L := L) 𝒢' g
    𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  { toFun := fun v => exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i))
    map_update_add' := by
      intro _ m i x y
      simp only [bcCot_update he, map_add]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_add _ i _ _
    map_update_smul' := by
      intro _ m i r x
      simp only [bcCot_update he, map_smulₛₗ]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_smul _ i _ _
    map_eq_zero_of_eq' := by
      intro v i j hv hij
      exact (exteriorPower.ιMulti (𝓞 L') g).map_eq_zero_of_eq _ (by simp only [hv]) hij }

/-- `⋀^g π^* : ⋀^g_{𝓞_L} ω_{A_L} → ⋀^g_{𝓞_{L'}} ω_{A_{L'}}`, additive and semilinear. -/
noncomputable def bcExt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    exteriorPower (𝓞 L) g 𝒢.cotangent →+ exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).toAddMonoidHom

theorem bcExt_ιMulti (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (v : Fin g → 𝒢.cotangent) :
    bcExt he g (exteriorPower.ιMulti (𝓞 L) g v) =
      exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i)) := by
  letI := extRes (L := L) 𝒢' g
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (bcAlt he g) v

theorem bcExt_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (r : 𝓞 L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcExt he g (r • x) = algebraMap (𝓞 L) (𝓞 L') r • bcExt he g x := by
  letI := extRes (L := L) 𝒢' g
  exact (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).map_smul r x

/-- **The natural map of Hodge spaces** `ψ = L' ⊗ ⋀^g π^* : hodgeSpace g → hodgeSpace' g`. -/
noncomputable def bcHodge (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk'
      (fun x => algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x)
      (fun x y => by rw [map_add, TensorProduct.tmul_add]))
      (fun a b => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          TensorProduct.add_tmul]))
    (fun r a x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [bcExt_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl)

theorem bcHodge_tmul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (a : L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcHodge he g (a ⊗ₜ[𝓞 L] x) = algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x := rfl

theorem bcHodge_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (c : L) (v : 𝒢.hodgeSpace g) :
    bcHodge he g (c • v) = algebraMap L L' c • bcHodge he g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', bcHodge_tmul, bcHodge_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `ψ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = 1 ⊗ d(π^*f₁) ∧ ⋯ ∧ d(π^*f_g)`. -/
theorem bcHodge_wedge (he : IsMonBC 𝒢 𝒢' e) {g : ℕ}
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcHodge he g (𝒢.wedge f) =
      𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.wedge
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  rfl

/-! ### Complex points and Jacobians along `π` -/

omit [NumberField L] [NumberField L'] in
/-- (copied from `scratch/h5-glue/BaseChangePts.lean`, proved there) -/
theorem ptC_hom_comp_bO (τ' : L' →+* ℂ) :
    (GroupModel.ptC (L := L') τ').hom ≫ bO L L' =
      (GroupModel.ptC (L := L) (τ'.comp (algebraMap L L'))).hom := by
  simp only [GroupModel.ptC, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) Restriction does not change values
at points that land in the smaller open. -/
theorem evalAt_res {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem ptC_hom_apply {L : Type} [Field L] [NumberField L] (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem one_mem_dom {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

variable (e) in
/-- **Complex points along the base change**: `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`, `p' ↦ π ∘ p'`, for
`σ = τ'|_L`. -/
noncomputable def bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') : 𝒢.Pts σ :=
  Over.homMk (p.left ≫ bcProj 𝒢 𝒢' e) (by
    subst hστ
    refine (Category.assoc _ _ _).trans ?_
    rw [bcProj_w]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ bO L L') (Over.w p)).trans (ptC_hom_comp_bO τ'))

theorem evalAt_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt (bcPts e σ τ' hστ p) U s =
      𝒢'.evalAt p (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ}
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) :
    𝒢.dom (fun z => bcPts e σ τ' hστ (Φ' z)) U = 𝒢'.dom Φ' (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) := rfl

/-- **The germ along `β ∘ Φ'` of `t` agrees near `0` with the germ along `Φ'` of `π^* t`.** -/
theorem germAlong_bcPts_eventuallyEq (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (t : 𝒢.genStalk) :
    𝒢.germAlong (fun z => bcPts e σ τ' hστ (Φ' z)) t =ᶠ[nhds 0] 𝒢'.germAlong Φ' (bcMap he t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢'.genericUnit ∈ bcProj 𝒢 𝒢' e ⁻¹ᵁ U := by
    show bcProj 𝒢 𝒢' e 𝒢'.genericUnit ∈ U
    rw [bcProj_genericUnit he]; exact m
  set U' := (𝒢'.exists_rep (bcMap he t)).choose
  set m' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose
  set s' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose
  have hs' : 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' = bcMap he t :=
    (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢'.G.left.presheaf.germ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) 𝒢'.genericUnit hx'
      ((bcProj 𝒢 𝒢' e).app U s) = 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' := by
    rw [hs', ← hs, bcMap_germ he U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢'.dom Φ' W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ' 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ' hmul]
    exact one_mem_dom 𝒢' τ' mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) U s = 𝒢'.evalAt (Φ' z) U' s'
  rw [evalAt_bcPts, evalAt_res 𝒢' (Φ' z) iU hz, hW, ← evalAt_res 𝒢' (Φ' z) iV hz]

/-- **Jacobian determinants along the base change**:
`jacDet (β ∘ Φ') f = jacDet' Φ' (π^* f)`. -/
theorem jacDet_bcPts (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => bcPts e σ τ' hστ (Φ' z)) f =
      𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_bcPts_eventuallyEq he σ τ' hστ Λ Φ' hΦ (f i)).fderiv_eq]

end Construction

/-! ### Half of BC-lat: `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}` (proved) -/

section LatticeHalf

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_stalkSpecializes_apply' {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_self_apply' {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- At each point `s'` of `Spec 𝓞_{L'}`, `π^*` maps `(ω_𝒢)_{s}` (`s` the image of `s'`) into
`(ω_{𝒢'})_{s'}`. -/
theorem bcCot_omegaAt (he : IsMonBC 𝒢 𝒢' e) (s' : Spec (CommRingCat.of (𝓞 L')))
    (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omegaAt (bO L L' s')) : bcCot he m ∈ 𝒢'.omegaAt s' := by
  have hE := bcProj_unit he
  have hp : bcProj 𝒢 𝒢' e (𝒢'.unitSection s') = 𝒢.unitSection (bO L L' s') :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => φ s') hE).trans (Scheme.Hom.comp_apply _ _ _))
  let T := 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := (bcProj 𝒢 𝒢' e).stalkMap (𝒢'.unitSection s') (T g)
    have hspec : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' =
        bcMap he (𝒢.G.left.presheaf.stalkSpecializes
          (𝒢.specializes_genericUnit (bO L L' s')) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold bcMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply', stalkSpecializes_stalkSpecializes_apply']
    have hker : g' ∈ RingHom.ker (𝒢'.unitSection.stalkMap s').hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢'.unitSection (bcProj 𝒢 𝒢' e) s'
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s'
      have h1' : (𝒢'.unitSection.stalkMap s') g' =
          ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) =
          ((bO L L' ≫ 𝒢.unitSection).stalkMap s') ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h3 := Scheme.Hom.stalkMap_comp (bO L L') 𝒢.unitSection s'
      have h3' := congrArg (fun φ => (ConcreteCategory.hom φ) ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g))) h3
      simp only at h3'
      rw [h3']
      have h4 : ∀ y : 𝒢.G.left.presheaf.stalk (𝒢.unitSection (bO L L' s')), y = g →
          (𝒢.unitSection.stalkMap (bO L L' s')) y = 0 := by
        rintro y rfl; exact hg
      have h5 : (𝒢.unitSection.stalkMap (bO L L' s')) ((𝒢.G.left.presheaf.stalkCongr
          (Inseparable.of_eq hp)).hom (T g)) = 0 := by
        apply h4
        show 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes
          (T g) = g
        exact (stalkSpecializes_stalkSpecializes_apply' _ _ g).trans
          (stalkSpecializes_self_apply' _ g)
      exact (congrArg (fun y => ((bO L L').stalkMap s') y) h5).trans (map_zero _)
    have hmem' : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' ∈
        IsLocalRing.maximalIdeal 𝒢'.genStalk := by
      rw [hspec]; exact bcMap_mem_maximalIdeal he _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [bcCot_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- `π^*(ω_𝒢) ⊆ ω_{𝒢'}`. -/
theorem bcCot_omega (he : IsMonBC 𝒢 𝒢' e) (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omega) :
    bcCot he m ∈ 𝒢'.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s' => bcCot_omegaAt he s' m (hm _)

/-- `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem bcHodge_detLattice (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (x : 𝒢.hodgeSpace g)
    (hx : x ∈ 𝒢.detLattice g) : bcHodge he g x ∈ 𝒢'.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [bcHodge_tmul, map_one, bcExt_ιMulti]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨bcCot he (v i), bcCot_omega he _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, bcHodge_smul]
    have : algebraMap L L' (algebraMap (𝓞 L) L r) • bcHodge he g y =
        (algebraMap (𝓞 L) (𝓞 L') r) • bcHodge he g y := by
      rw [← algebraMap_smul L' (algebraMap (𝓞 L) (𝓞 L') r)]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- **Half of BC-lat (proved)**: `𝓞_{L'} · ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem span_bcHodge_le (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g) ≤ 𝒢'.detLattice g :=
  Submodule.span_le.mpr (by
    rintro _ ⟨x, hx, rfl⟩
    exact bcHodge_detLattice he g x hx)

/-- A multilinear map sends a tuple of vectors of `span S` into the span of its values on tuples
of vectors of `S` (induction on the number of coordinates not yet in `S`). -/
theorem multilinear_mem_span {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) N)
    (S : Set M) : ∀ (k : ℕ) (v : Fin n → M), (∀ i : Fin n, (i : ℕ) < k → v i ∈ Submodule.span R S) →
      (∀ i : Fin n, k ≤ (i : ℕ) → v i ∈ S) →
      f v ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
  classical
  intro k
  induction k with
  | zero =>
    intro v _ hS
    exact Submodule.subset_span ⟨v, fun i => hS i (Nat.zero_le _), rfl⟩
  | succ k ih =>
    intro v hspan hS
    by_cases hk : k < n
    · set i0 : Fin n := ⟨k, hk⟩
      have hmot : ∀ x ∈ Submodule.span R S,
          f (Function.update v i0 x) ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          apply ih
          · intro i hi
            rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]
            exact hspan i (Nat.lt_succ_of_lt hi)
          · intro i hi
            by_cases hii : i = i0
            · rw [hii, Function.update_self]; exact hy
            · rw [Function.update_of_ne hii]
              apply hS i
              have : (i : ℕ) ≠ k := fun h => hii (Fin.ext h)
              omega
        | zero => rw [f.map_update_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
        | smul r x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ r hx
      have := hmot (v i0) (hspan i0 (Nat.lt_succ_self k))
      rwa [Function.update_eq_self] at this
    · apply ih v
      · intro i hi; exact hspan i (Nat.lt_succ_of_lt hi)
      · intro i hi
        apply hS i
        have := i.2
        omega

end LatticeHalf

/-- **Glue BC-omega (flat base change of `e*Ω¹`, the hard inclusion).** Every element of
`ω_{𝒢'} = Γ(Spec 𝓞_{L'}, e'*Ω¹_{𝒢'/𝓞_{L'}})` is an `𝓞_{L'}`-combination of pull-backs
`π^*η`, `η ∈ ω_𝒢`. True: `e*Ω¹_{𝒢/𝓞_L}` is locally free (`𝒢` smooth), its formation commutes with
base change (EGA IV 16.4.5 / 17.2.5, UNVERIFIED locators), and for the projective `𝓞_L`-module
`ω_𝒢`, `Γ(Spec 𝓞_{L'}, f^*ω̃) = 𝓞_{L'} ⊗ ω_𝒢`. The other inclusion is proved (`bcCot_omega`).
A model review notes that this inclusion needs less: `e` is a closed immersion (`𝒢` separated),
`omegaAt s` is the image of the stalk of the quasi-coherent conormal `e^*(I/I²)`, and
`I'_{e'(s')} = I_{e(s)} · 𝒪_{𝒢',e'(s')}` for the base-changed section, so
`d(a · π^*f) = e'^#(a) · π^*(df)`; smoothness is not used. STANDARD. -/
def OmegaBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), 𝒢'.omega ≤ Submodule.span (𝓞 L') (bcCot he '' 𝒢.omega)


/-! ### The differential at the origin along `Φ` (proves `GermDerivation`) -/

section GermDer

variable {K : Type} [Field K] {A : AbVar K}

variable {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)

/-- Values at a point of `V(ℂ)` are additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ + r₂) = 𝒢.evalAt p V r₁ + 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_add]
  exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

/-- Values at a point of `V(ℂ)` are multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ * r₂) = 𝒢.evalAt p V r₁ * 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_mul]
  exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

variable {𝒢}

/-- **Any representative computes the germ along `Φ` near `0`.** -/
theorem germAlong_eventuallyEq_rep {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (V : 𝒢.G.left.Opens) (mV : 𝒢.genericUnit ∈ V) (r : Γ(𝒢.G.left, V))
    (ht : 𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r = t) :
    𝒢.germAlong Φ t =ᶠ[nhds 0] fun z => 𝒢.evalAt (Φ z) V r := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r := by rw [hs, ht]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ m mV _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (Φ z) U s = 𝒢.evalAt (Φ z) V r
  rw [evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- The germ along `Φ` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨V, mV, r, hr⟩ := 𝒢.exists_rep t
  have hev := germAlong_eventuallyEq_rep hΦ t V mV r hr
  obtain ⟨hmul, -, -, hopen, hdiff⟩ := hΦ
  have h0 : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V := by
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ V
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mV
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V r) 0 :=
    (hdiff V r).differentiableAt ((hopen V).mem_nhds h0)
  exact hev.differentiableAt_iff.mpr hd

/-- **Eventual additivity and multiplicativity of germs along `Φ`.** -/
theorem germAlong_add_mul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    (𝒢.germAlong Φ (t₁ + t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z + 𝒢.germAlong Φ t₂ z) ∧
      (𝒢.germAlong Φ (t₁ * t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z * 𝒢.germAlong Φ t₂ z) := by
  obtain ⟨V₁, m₁, r₁, h₁⟩ := 𝒢.exists_rep t₁
  obtain ⟨V₂, m₂, r₂, h₂⟩ := 𝒢.exists_rep t₂
  have e₁ := germAlong_eventuallyEq_rep hΦ t₁ V₁ m₁ r₁ h₁
  have e₂ := germAlong_eventuallyEq_rep hΦ t₂ V₂ m₂ r₂ h₂
  set W := V₁ ⊓ V₂
  have mW : 𝒢.genericUnit ∈ W := ⟨m₁, m₂⟩
  let i₁ : W ⟶ V₁ := homOfLE inf_le_left
  let i₂ : W ⟶ V₂ := homOfLE inf_le_right
  let ρ₁ := 𝒢.G.left.presheaf.map i₁.op r₁
  let ρ₂ := 𝒢.G.left.presheaf.map i₂.op r₂
  have g₁ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₁ = t₁ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₁
  have g₂ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₂ = t₂ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₂
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  constructor
  · have eS := germAlong_eventuallyEq_rep hΦ (t₁ + t₂) W mW (ρ₁ + ρ₂)
      (by rw [map_add, g₁, g₂])
    filter_upwards [eS, e₁, e₂, hnhds] with z hS hz₁ hz₂ hz
    rw [hS, hz₁, hz₂, evalAt_add 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]
  · have eP := germAlong_eventuallyEq_rep hΦ (t₁ * t₂) W mW (ρ₁ * ρ₂)
      (by rw [map_mul, g₁, g₂])
    filter_upwards [eP, e₁, e₂, hnhds] with z hP hz₁ hz₂ hz
    rw [hP, hz₁, hz₂, evalAt_mul 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]

/-- `appLE ⊤ ⊤` is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (U := ⊤) f

/-- **Structure sections take the value `τ(r)` at every complex point.** -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (r : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
      τ (algebraMap (𝓞 L) L r) := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  rw [dif_pos h, appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have hw : p.left ≫ 𝒢.G.hom = Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))) :=
    Over.w p
  rw [hw]
  have hN := congrArg (fun φ => (ConcreteCategory.hom φ)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  refine hN.trans ?_
  erw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- **Germs in `𝔪_ξ` vanish at the unit complex point.** -/
theorem evalAt_one_eq_zero (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := one_mem_dom 𝒢 τ hU
  rw [dif_pos h]
  have h1 : (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := rfl
  have hgen : genericPt L ∈ 𝒢.unitSection ⁻¹ᵁ U := hU
  have hz : 𝒢.unitSection.app U s = 0 := by
    apply germ_injective_of_isIntegral _ (genericPt L) hgen
    rw [map_zero]
    refine (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hgen s).symm.trans ?_
    have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
      have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
        (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
      rw [this]
      exact Field.toIsField _
    have hloc := map_nonunit (𝒢.unitSection.stalkMap (genericPt L)).hom _
      ((IsLocalRing.mem_maximalIdeal _).mp hs)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  have h2 : (1 : 𝒢.Pts τ).left.appLE U ⊤ h s =
      ((GroupModel.ptC τ).hom.appLE (𝒢.unitSection ⁻¹ᵁ U) ⊤ h) (𝒢.unitSection.app U s) := by
    have := Scheme.Hom.comp_appLE (GroupModel.ptC τ).hom 𝒢.unitSection U ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) s) this
  rw [h2, hz, map_zero]
  exact map_zero _

section Derivation

variable {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}

/-- Germs in `𝔪_ξ` vanish at `0` along `Φ`. -/
theorem germAlong_zero_of_mem (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ t 0 = 0 := by
  have hs : 𝒢.G.left.presheaf.germ (𝒢.exists_rep t).choose 𝒢.genericUnit
      (𝒢.exists_rep t).choose_spec.choose (𝒢.exists_rep t).choose_spec.choose_spec.choose = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  show 𝒢.evalAt (Φ 0) _ _ = 0
  rw [map_zero_of_hom Φ hΦ.1]
  exact evalAt_one_eq_zero τ _ _ _ (hs ▸ ht)

/-- Structure sections are constant `τ(r)` along `Φ` near `0`. -/
theorem germAlong_structMap (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) :
    𝒢.germAlong Φ (𝒢.structMap r) =ᶠ[nhds 0] fun _ => τ (algebraMap (𝓞 L) L r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  filter_upwards [germAlong_eventuallyEq_rep hΦ _ ⊤ trivial _ e1.symm] with z hz
  rw [hz, evalAt_structSection]

/-- The derivative at `0` of the germ along `Φ`. -/
noncomputable def D0 (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (t : 𝒢.genStalk) : (Fin g → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (𝒢.germAlong Φ t) 0

theorem D0_add (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ + t₂) = D0 Φ t₁ + D0 Φ t₂ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).1.fderiv_eq]
  exact fderiv_add (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ * t₂) = 𝒢.germAlong Φ t₁ 0 • D0 Φ t₂ + 𝒢.germAlong Φ t₂ 0 • D0 Φ t₁ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).2.fderiv_eq]
  exact fderiv_mul (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ * t₂) v =
      𝒢.germAlong Φ t₁ 0 * D0 Φ t₂ v + 𝒢.germAlong Φ t₂ 0 * D0 Φ t₁ v := by
  rw [D0_mul hΦ]
  rfl

theorem D0_add_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ + t₂) v = D0 Φ t₁ v + D0 Φ t₂ v := by
  rw [D0_add hΦ]
  rfl

theorem D0_structMap_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) (t : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (𝒢.structMap r * t) v = τ (algebraMap (𝓞 L) L r) * D0 Φ t v := by
  rw [D0_mul_apply hΦ]
  have h0 : D0 Φ (𝒢.structMap r) = 0 := by
    unfold D0
    rw [(germAlong_structMap hΦ r).fderiv_eq, fderiv_const_apply]
  rw [h0, (germAlong_structMap hΦ r).eq_of_nhds]
  simp

theorem D0_sq (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x : 𝒢.genStalk)
    (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) (v : Fin g → ℂ) : D0 Φ x v = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on (C := fun x => D0 Φ x v = 0) hx ?_ ?_
  · intro a ha b hb
    rw [D0_mul_apply hΦ, germAlong_zero_of_mem hΦ a ha, germAlong_zero_of_mem hΦ b hb]
    ring
  · intro x y hx hy
    rw [D0_add_apply hΦ, hx, hy, add_zero]

/-- **`GermDerivation` holds for every analytic uniformization** (proved). -/
theorem germDerivation_at (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1) := by
  let 𝔪 := IsLocalRing.maximalIdeal 𝒢.genStalk
  let D1 : 𝔪 → (Fin g → ℂ) := fun t j => D0 Φ (t : 𝒢.genStalk) (Pi.single j 1)
  have hD1add : ∀ a b : 𝔪, D1 (a + b) = D1 a + D1 b := by
    intro a b
    funext j
    simp only [D1, Submodule.coe_add, D0_add_apply hΦ, Pi.add_apply]
  have hD1wd : ∀ a b : 𝔪, 𝔪.toCotangent a = 𝔪.toCotangent b → D1 a = D1 b := by
    intro a b hab
    rw [Ideal.toCotangent_eq] at hab
    have this : D0 Φ (a : 𝒢.genStalk) = D0 Φ ((a : 𝒢.genStalk) - b) + D0 Φ (b : 𝒢.genStalk) := by
      rw [← D0_add hΦ, sub_add_cancel]
    funext j
    simp only [D1]
    rw [this, ContinuousLinearMap.add_apply, D0_sq hΦ _ hab, zero_add]
  let sec : 𝒢.cotangent → 𝔪 := Function.surjInv (𝔪.toCotangent_surjective)
  have hsec : ∀ x : 𝒢.cotangent, 𝔪.toCotangent (sec x) = x :=
    Function.surjInv_eq _
  let D : 𝒢.cotangent →+ (Fin g → ℂ) :=
    { toFun := fun x => D1 (sec x)
      map_zero' := by
        have : D1 (sec 0) = D1 0 := hD1wd _ _ (by rw [hsec, map_zero]; rfl)
        rw [this]
        have h00 : D0 Φ (0 : 𝒢.genStalk) = 0 := by
          have := D0_add hΦ (0 : 𝒢.genStalk) 0
          rw [add_zero] at this
          exact add_eq_left.mp this.symm
        funext j
        simp [D1, h00]
      map_add' := fun x y => by
        show D1 (sec (x + y)) = D1 (sec x) + D1 (sec y)
        rw [← hD1add]
        exact hD1wd _ _ (by rw [hsec, map_add, hsec, hsec]; rfl) }
  have hD : ∀ t : 𝔪, D (𝔪.toCotangent t) = D1 t := fun t => hD1wd _ _ (hsec _)
  refine ⟨D, fun r x => ?_, fun t j => ?_⟩
  · obtain ⟨t, rfl⟩ := 𝔪.toCotangent_surjective x
    have hrx : r • 𝒢.dCls t = 𝔪.toCotangent (𝒢.structMap r • t) := by
      show 𝒢.structMap r • 𝔪.toCotangent t = _
      rw [LinearMap.map_smul]
    show D (r • 𝒢.dCls t) = _ • D (𝒢.dCls t)
    rw [hrx]
    show D (𝔪.toCotangent _) = _ • D (𝔪.toCotangent t)
    rw [hD, hD]
    funext j
    simp only [D1, SetLike.val_smul, smul_eq_mul, Pi.smul_apply]
    rw [D0_structMap_mul hΦ]
  · show D (𝔪.toCotangent t) j = _
    rw [hD]
    rfl

end Derivation

end GermDer

/-! # Part C: `HodgeLineBaseChangeDescent` from glue statements over the natural map

All six are about the honest natural map: `π = e.hom.left ≫ pullback.fst : 𝒢' → 𝒢`, its stalk map
`bcMap : 𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`, `ψ = bcHodge = L' ⊗ ⋀^g π^*` and `β = bcPts : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`,
`p' ↦ π ∘ p'`. None is a literature leaf; each is glue (a property of def-faltings' definitions).
Six statements are stated; `PtsBaseChangeMul` and `PtsBaseChangeBij` are then proved, and
`DetLatticeBC` is reduced to `OmegaBaseChange` (`detLatticeBC_of_omega`). -/

/-- **Glue BC-alg (cotangent base change).** `ψ` is injective on nonzero vectors and the Hodge space
of `𝒢'` is an `L'`-line iff that of `𝒢` is an `L`-line. True because `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`
(the cotangent space at a rational point commutes with field extension: `𝒪_{𝒢',ξ'}` is a
localization of `𝒪_{𝒢,ξ} ⊗_L L'` with maximal ideal generated by that of `𝒪_{𝒢,ξ}`), and `⋀^g`
commutes with base change; with `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} V ≅ ⋀^g_L V` (exterior powers commute with
localization) this gives `L' ⊗_L hodgeSpace ≅ hodgeSpace'` through `ψ`. STANDARD. -/
def HodgeBCInjective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    (∀ v, v ≠ 0 → bcHodge he g v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1)

/-- **Glue BC-lat (flat base change of `e*Ω¹`).** `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`. True because
formation of `e*Ω¹_{𝒢/𝓞_L}` (locally free, `𝒢` smooth) commutes with base change
(EGA IV 16.4.5 for `Ω¹`, IV 17.2.5 for conormal `≅ e*Ω¹`; UNVERIFIED locators), so
`ω_{𝒢'} = 𝓞_{L'} · π^*(ω_𝒢)` inside `ω_{A_{L'}}`. It relies on `omegaAt s` being the conormal stalk
and on `omega` being the intersection of the stalks, as every statement about `ω` does.
Reduced to `OmegaBaseChange` below (`detLatticeBC_of_omega`). STANDARD. -/
def DetLatticeBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    𝒢'.detLattice g = Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g)

open ExteriorAlgebra in
/-- **BC-lat from BC-omega** (proved; the inclusion `⊇` is `span_bcHodge_le`). -/
theorem detLatticeBC_of_omega (h : OmegaBaseChange) : DetLatticeBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  refine le_antisymm ?_ (span_bcHodge_le he g)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v', rfl⟩
  let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
    (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
      (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
  have key := multilinear_mem_span F (bcCot he '' 𝒢.omega) g (fun i => (v' i : 𝒢'.cotangent))
    (fun i _ => h K A L L' 𝒢 𝒢' e he (v' i).2) (fun i hi => absurd i.2 (not_lt.mpr hi))
  show F (fun i => (v' i : 𝒢'.cotangent)) ∈ _
  refine Submodule.span_mono ?_ key
  rintro _ ⟨w, hw, rfl⟩
  choose u hu hwu using hw
  refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => u i),
    Submodule.subset_span ⟨fun i => ⟨u i, hu i⟩, rfl⟩, ?_⟩
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  have hw' : (fun i => bcCot he (u i)) = w := funext hwu
  rw [hw']
  rfl

/-- **Glue BC-pts-mul.** `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ` is multiplicative (it is induced by the
pullback, a monoidal functor, and `e` is a homomorphism). Category theory; STANDARD. -/
def PtsBaseChangeMul : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p q : 𝒢'.Pts τ'), bcPts e σ τ' hστ (p * q) = bcPts e σ τ' hστ p * bcPts e σ τ' hστ q

/-- **Glue BC-pts-bij.** `β` is bijective (universal property of the pullback; h5-glue's
`ptsBaseChangeEquiv` is a bijection with the same underlying map). STANDARD. -/
def PtsBaseChangeBij : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ),
    Function.Bijective (bcPts e σ τ' hστ)

/-- **Glue BC-lift (local structure of the base change).** A map `Φ' : ℂ^g → 𝒢'(ℂ)_{τ'}` whose
composite with `β` is an analytic uniformization of `𝒢(ℂ)_σ` is an analytic uniformization of
`𝒢'(ℂ)_{τ'}`: `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}` is covered by affine opens `Spec(R ⊗_{𝓞_L} 𝓞_{L'})`, whose
regular functions are, locally, quotients of sums `∑ fᵢ ⊗ aᵢ`, so their values along `Φ'` are
holomorphic where those of the `fᵢ` along `β ∘ Φ'` are (`evalAt_bcPts`). Openness of
`Φ'⁻¹(U'(ℂ))` for opens `U'` defined over `L'` (not pulled back from `𝒢`): `U'` is a union of
basic opens `D(h') ⊂ π⁻¹V`, and `{z ∈ dom (β ∘ Φ') V : h'(Φ' z) ≠ 0}` is open by continuity.
Neither `Λ` nor the group clauses are used for these two clauses. STANDARD. -/
def UniformizationLift : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      𝒢'.IsAnalyticUniformization τ' Λ Φ'

/-- **Glue BC-span (Jacobians are determined by pulled-back germs).** For an analytic
uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` and a `τ'`-semilinear `c'` on the Hodge space of `𝒢'`: if `c'`
computes `jacDet Φ'` on wedges of germs pulled back from `𝒢`, it does so on all wedges. True: the
derivative at `0` of `t ↦ germAlong Φ' t` kills `𝔪'²` and is `τ'`-semilinear, so `jacDet Φ'` is a
`τ'`-semilinear alternating function of `(df'_i)`, as is `c' ∘ wedge`; the classes `d(π^*f)`
span `ω_{A_{L'}}` over `𝓞_{L'}` (cotangent base change `V' = L' · bcCot(V)`, clearing
denominators; this spanning fact is part of this statement, not of `HodgeBCInjective`).
STANDARD. -/
def JacobianPullbackSpan : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (τ' : L' →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'), 𝒢'.IsAnalyticUniformization τ' Λ Φ' →
    ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ,
      (∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
        c' (𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) =
          𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) →
      ∀ f' : Fin g → IsLocalRing.maximalIdeal 𝒢'.genStalk, c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **BC-pts-bij is a theorem** (universal property of the pullback). -/
theorem ptsBaseChangeBij : PtsBaseChangeBij := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ
  subst hστ
  have hhominv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id]; rfl
  have hinvhom : e.inv.left ≫ e.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw : e.hom.left ≫ pullback.snd _ _ = 𝒢'.G.hom := Over.w e.hom
  constructor
  · intro p q hpq
    have h1 : p.left ≫ bcProj 𝒢 𝒢' e = q.left ≫ bcProj 𝒢 𝒢' e := congrArg Over.Hom.left hpq
    have h2 : p.left ≫ e.hom.left = q.left ≫ e.hom.left := by
      apply pullback.hom_ext
      · simpa only [bcProj, Category.assoc] using h1
      · rw [Category.assoc, Category.assoc, hw]
        exact (Over.w p).trans (Over.w q).symm
    have h3 := congrArg (· ≫ e.inv.left) h2
    simp only [Category.assoc, hhominv, Category.comp_id] at h3
    exact Over.OverMorphism.ext h3
  · intro q
    have w : q.left ≫ 𝒢.G.hom = (GroupModel.ptC (L := L') τ').hom ≫ bO L L' :=
      (Over.w q).trans (ptC_hom_comp_bO (L := L) τ').symm
    let pl : (GroupModel.ptC (L := L') τ').left ⟶ 𝒢'.G.left :=
      pullback.lift q.left (GroupModel.ptC (L := L') τ').hom w ≫ e.inv.left
    have hpl : pl ≫ 𝒢'.G.hom = (GroupModel.ptC (L := L') τ').hom := by
      have hw' : e.inv.left ≫ 𝒢'.G.hom = pullback.snd _ _ := Over.w e.inv
      simp only [pl, Category.assoc, hw']
      exact pullback.lift_snd _ _ _
    refine ⟨Over.homMk pl hpl, ?_⟩
    apply Over.OverMorphism.ext
    show pl ≫ bcProj 𝒢 𝒢' e = q.left
    simp only [pl, bcProj, Category.assoc]
    rw [reassoc_of% hinvhom]
    exact pullback.lift_fst _ _ _

/-- **BC-pts-mul is a theorem** (`e` is a homomorphism; components of `μ` of `Over.pullback`). -/
theorem ptsBaseChangeMul : PtsBaseChangeMul := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ p q
  subst hστ
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  apply Over.OverMorphism.ext
  show (p * q).left ≫ bcProj 𝒢 𝒢' e =
    (bcPts e _ τ' rfl p * bcPts e _ τ' rfl q).left
  have h1 : (p * q) ≫ e.hom = (p ≫ e.hom) * (q ≫ e.hom) := MonObj.mul_comp p q e.hom
  have h2 : (p * q).left ≫ bcProj 𝒢 𝒢' e =
      ((p ≫ e.hom) * (q ≫ e.hom)).left ≫ pullback.fst _ _ := by
    rw [← h1, Over.comp_left, Category.assoc]
    rfl
  rw [h2]
  show (lift (p ≫ e.hom) (q ≫ e.hom) ≫ (Functor.LaxMonoidal.μ (Over.pullback (bO L L')) 𝒢.G 𝒢.G ≫
      (Over.pullback (bO L L')).map μ[𝒢.G])).left ≫ pullback.fst _ _ =
    (lift (bcPts e _ τ' rfl p) (bcPts e _ τ' rfl q) ≫ μ[𝒢.G]).left
  have hmap : ((Over.pullback (bO L L')).map μ[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ μ[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hmap,
    ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst, Over.lift_left,
      Over.lift_left, pullback.lift_fst_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd, Over.lift_left,
      Over.lift_left, pullback.lift_snd_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_snd _ _ _).symm

/-- **Glue AN-jac (the Jacobian is a semilinear function of the wedge).** For an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` (any group model, any `g`), `f ↦ jacDet Φ f` factors through
`wedge` by a `τ`-semilinear map on the Hodge space. True: near `0`, `t ↦ germAlong Φ t` is a ring
homomorphism into germs of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U`
are open), so `D(t) = d(germAlong Φ t)(0)` is a derivation at evaluation at `0`: it kills `𝔪_ξ²`
and is `τ`-semilinear on `𝔪_ξ/𝔪_ξ²` (structure sections are constant `τ(r)` along `Φ`), and
`det(D(fᵢ)(e_j))` is alternating in the `dfᵢ`; it extends to `L ⊗ ⋀^g` by `a ⊗ x ↦ τ(a) J(x)`.
A statement about one group model; analytic glue. STANDARD. -/
def JacobianSemilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, 𝒢.jacDet Φ f = J (𝒢.wedge f)

/-- **Glue AN-der (the differential at the origin along `Φ`).** For an analytic uniformization
`Φ` of `𝒢(ℂ)_τ`, `t ↦ d(germAlong Φ t)(0)` on `𝔪_ξ` descends to an additive map
`D : 𝔪_ξ/𝔪_ξ² → ℂ^g` (the `j`-th coordinate is the derivative in the direction `e_j`) which is
`τ`-semilinear over `𝓞_L`. True: near `0`, `t ↦ germAlong Φ t` is a ring homomorphism into germs
of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U` are open, representatives
agree near `0`), germs in `𝔪_ξ` vanish at `0`, so the product rule kills `𝔪_ξ²`; structure
sections are the constants `τ(r)` along `Φ`. A statement about one group model; analytic glue.
STANDARD. -/
def GermDerivation : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)

open ExteriorAlgebra in
/-- **AN-jac from AN-der** (determinants and the universal property of `⋀^g`; proved). -/
theorem jacobianSemilinear_of (h : GermDerivation) : JacobianSemilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨D, hDs, hDf⟩ := h K A L 𝒢 τ Λ Φ hΦ
  let σ0 : 𝓞 L →+* ℂ := τ.comp (algebraMap (𝓞 L) L)
  let _ : Module (𝓞 L) ℂ := Module.compHom ℂ σ0
  have e : ∀ [DecidableEq (Fin g)] (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent),
      (Matrix.of fun i' j => D (Function.update m i z i') j) =
        (Matrix.of fun i' j => D (m i') j).updateRow i (D z) := by
    intro _ m i z
    ext i' j
    by_cases hi : i' = i
    · subst hi
      simp [Matrix.updateRow_self]
    · simp [Matrix.updateRow_ne hi, Function.update_of_ne hi]
  let alt : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => (Matrix.of fun i j => D (v i) j).det
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, e, map_add]
        exact Matrix.det_updateRow_add _ _ _ _
      map_update_smul' := by
        intro inst m i r x
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, hDs, Matrix.det_updateRow_smul]
        rfl
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact Matrix.det_zero_of_row_eq hij (by funext k; simp [hv]) }
  let J0 : exteriorPower (𝓞 L) g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    exteriorPower.alternatingMapLinearEquiv alt
  have hJ0 : ∀ (r : 𝓞 L) x, J0 (r • x) = σ0 r * J0 x := fun r x => J0.map_smul r x
  let Jadd : 𝒢.hodgeSpace g →+ ℂ :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk' (fun x => τ a * J0 x)
        (fun x y => by rw [map_add, mul_add]))
        (fun a b => by
          ext x
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
      (fun r a x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [hJ0, Algebra.smul_def, map_mul]
        show τ (algebraMap (𝓞 L) L r) * τ a * J0 x = τ a * (σ0 r * J0 x)
        simp only [σ0, RingHom.comp_apply]
        ring)
  have hJt : ∀ (a : L) x, Jadd (a ⊗ₜ[𝓞 L] x) = τ a * J0 x := fun a x => rfl
  let J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := Jadd
      map_add' := map_add Jadd
      map_smul' := fun c v => by
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
          rw [TensorProduct.smul_tmul', hJt, hJt, smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  refine ⟨J, fun f => ?_⟩
  show 𝒢.jacDet Φ f = Jadd ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [hJt, map_one, _root_.one_mul]
  show _ = exteriorPower.alternatingMapLinearEquiv alt
    (exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  show _ = (Matrix.of fun i j => D (𝒢.dCls (f i)) j).det
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [hDf]

/-- **AN-der is a theorem** (`germDerivation_at`). -/
theorem germDerivation : GermDerivation :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hΦ => germDerivation_at hΦ

/-- **AN-jac is a theorem.** -/
theorem jacobianSemilinear : JacobianSemilinear := jacobianSemilinear_of germDerivation

/-- **Glue BC-hspan (the image of `ψ` spans).** `L' · ψ(hodgeSpace g) = hodgeSpace' g`. True by
cotangent base change `ω_{A_{L'}} = L' · π^*(ω_{A_L})` and multilinearity; proved from
`CotangentSpanBC` below (`hodgeSpanBC_of`). (The `L'`-linear extension `L' ⊗_L hodgeSpace →
hodgeSpace'` is in fact an isomorphism, but that does not follow from this statement and
`HodgeBCInjective` alone unless `hodgeSpace` is a line.) STANDARD. -/
def HodgeSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    Submodule.span L' (Set.range (bcHodge he g)) = ⊤

/-- **Glue BC-cot (cotangent base change, spanning half).** The classes `π^*v`, `v ∈ ω_{A_L}`,
span `ω_{A_{L'}}` over `𝓞_{L'}`. True: `𝒪_{𝒢',ξ'}` is a localization of `𝒪_{𝒢,ξ} ⊗_L L'` whose
maximal ideal is generated by `𝔪_ξ`, so `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`; denominators in `L'` are
cleared because `ω_{A_L}` is a `ℚ`-vector space. A statement about the local rings at the origin
only (no Hodge data). STANDARD. -/
def CotangentSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), Submodule.span (𝓞 L') (Set.range (bcCot he)) = ⊤

open ExteriorAlgebra in
/-- **BC-hspan from BC-cot** (multilinearity; proved). -/
theorem hodgeSpanBC_of (h : CotangentSpanBC) : HodgeSpanBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  rw [eq_top_iff]
  rintro w -
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a x =>
    rw [show a ⊗ₜ[𝓞 L'] x = a • ((1 : L') ⊗ₜ[𝓞 L'] x) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]]
    refine Submodule.smul_mem _ a ?_
    have hx : x ∈ Submodule.span (𝓞 L') (Set.range (exteriorPower.ιMulti (𝓞 L') g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v', rfl⟩ := hy
      let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
        (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
          (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
      have key := multilinear_mem_span F (Set.range (bcCot he)) g v'
        (fun i _ => by rw [h K A L L' 𝒢 𝒢' e he]; trivial)
        (fun i hi => absurd i.2 (not_lt.mpr hi))
      have hsub : Submodule.span (𝓞 L') (F '' {w | ∀ i, w i ∈ Set.range (bcCot he)}) ≤
          (Submodule.span L' (Set.range (bcHodge he g))).restrictScalars (𝓞 L') := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        choose u hu using hw
        apply Submodule.subset_span
        refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g u, ?_⟩
        rw [bcHodge_tmul, map_one, bcExt_ιMulti]
        have hw' : (fun i => bcCot he (u i)) = w := funext hu
        rw [hw']
        rfl
      exact hsub key
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ r hy
  | add x y hx hy => exact add_mem hx hy

open ExteriorAlgebra in
/-- **BC-span from AN-jac and BC-hspan** (proved). -/
theorem jacobianPullbackSpan_of (hJ : JacobianSemilinear) (hS : HodgeSpanBC) :
    JacobianPullbackSpan := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he τ' g Λ Φ' hΦ' c' hc f'
  obtain ⟨J, hJf⟩ := hJ K A L' 𝒢' τ' Λ Φ' hΦ'
  suffices hcJ : c' = J by rw [hcJ, hJf]
  have hwedge : ∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      c' (bcHodge he g (𝒢.wedge f)) = J (bcHodge he g (𝒢.wedge f)) := by
    intro f
    rw [bcHodge_wedge, hc f, hJf]
  have hagree : ∀ v, c' (bcHodge he g v) = J (bcHodge he g v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have hx : x ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hx using Submodule.span_induction generalizing a with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        choose f hf using fun i => (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (v i)
        have h1 : a ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v = a • 𝒢.wedge f := by
          unfold GroupModel.wedge GroupModel.dCls
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
          congr 2
          funext i
          exact (hf i).symm
        rw [h1, bcHodge_smul, map_smulₛₗ, map_smulₛₗ, hwedge f]
      | zero => simp
      | add y z _ _ hy hz =>
        rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz]
      | smul r y _ hy =>
        rw [← TensorProduct.smul_tmul]
        exact hy _
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  apply LinearMap.ext
  intro w
  have hw : w ∈ Submodule.span L' (Set.range (bcHodge he g)) := by
    rw [hS K A L L' 𝒢 𝒢' e he g]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact hagree v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- **Glue BC-lift-an (the analytic core of BC-lift).** If `β ∘ Φ'` is an analytic
uniformization of `𝒢(ℂ)_σ`, then the sets `Φ'⁻¹(U'(ℂ))` are open and the regular functions of
`𝒢'` are holomorphic along `Φ'`, for every open `U'` of `𝒢'` (including opens defined over `L'`
and not pulled back from `𝒢`). Same justification as `UniformizationLift` (affine opens
`Spec(R ⊗_{𝓞_L} 𝓞_{L'})` and basic opens `D(h')`). STANDARD. -/
def UniformizationLiftAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      (∀ U, IsOpen (𝒢'.dom Φ' U)) ∧
        ∀ U (s : Γ(𝒢'.G.left, U)),
          DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ' z) U s) (𝒢'.dom Φ' U)

/-- **BC-lift from its analytic core** (the group clauses come from `β` being a bijective
homomorphism: `ptsBaseChangeMul`, `ptsBaseChangeBij`). Proved. -/
theorem uniformizationLift_of (h : UniformizationLiftAnalytic) : UniformizationLift := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ g Λ Φ' hU
  obtain ⟨hopen, hdiff⟩ := h K A L L' 𝒢 𝒢' e he σ τ' hστ Λ Φ' hU
  obtain ⟨hmul, hker, hsurj, -, -⟩ := hU
  have hbij := ptsBaseChangeBij K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hm := ptsBaseChangeMul K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, hopen, hdiff⟩
  · intro z w
    apply hbij.1
    rw [hm]
    exact hmul z w
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      show bcPts e σ τ' hστ (Φ' z) = 1
      rw [hz, h1]
    · intro hz
      apply hbij.1
      rw [h1]
      exact hz
  · intro p
    obtain ⟨z, hz⟩ := hsurj (bcPts e σ τ' hστ p)
    exact ⟨z, hbij.1 hz⟩

/-- **Descent of analytic uniformizations along `β`** (proved, from BC-pts-mul and BC-pts-bij). -/
theorem isAnalyticUniformization_bcPts (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij)
    {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}
    (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ')
    (h : 𝒢'.IsAnalyticUniformization τ' Λ Φ') :
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hbij := hb K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hmul' := hm K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hmul' 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, hmul']
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      apply hbij.1
      have hz' : bcPts e σ τ' hστ (Φ' z) = 1 := hz
      rw [hz', h1]
    · intro hz
      simp only
      rw [hz, h1]
  · intro q
    obtain ⟨p, rfl⟩ := hbij.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_bcPts]
    exact hopen _
  · intro U s
    rw [dom_bcPts]
    simp only [evalAt_bcPts]
    exact hdiff _ _

/-- **`HodgeLineBaseChangeDescent` from the six glue statements over the natural map** (two of
them, `PtsBaseChangeMul` and `PtsBaseChangeBij`, are proved above). Proved. -/
theorem hodgeLineBaseChangeDescent_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChangeDescent := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_, ?_⟩
  · intro τ' Λ Φ hΦ
    have hbij := hb K A L L' 𝒢 𝒢' e he _ τ' rfl
    choose Φ' hΦ' using fun z => hbij.2 (Φ z)
    have hΦeq : (fun z => bcPts e _ τ' rfl (Φ' z)) = Φ := funext hΦ'
    have hU' : 𝒢'.IsAnalyticUniformization τ' Λ Φ' := by
      refine hl K A L L' 𝒢 𝒢' e he _ τ' rfl Λ Φ' ?_
      rw [hΦeq]
      exact hΦ
    refine ⟨Φ', hU', fun c c' hc hcc' => hj K A L L' 𝒢 𝒢' e he τ' Λ Φ' hU' c' (fun f => ?_)⟩
    rw [← bcHodge_wedge he f, hcc', hc, ← jacDet_bcPts he _ τ' rfl Λ Φ' hU' f, hΦeq]
  · intro σ τ' hστ Λ Φ' hΦ'
    refine ⟨fun z => bcPts e σ τ' hστ (Φ' z),
      isAnalyticUniformization_bcPts hm hb he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
    rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim) from the six glue statements.** Proved. -/
theorem modelHeightBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **`HodgeLineBaseChange` (verbatim) from the six glue statements.** Proved. -/
theorem hodgeLineBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements**
(BC-alg, BC-lat, BC-lift, BC-span; BC-pts-mul and BC-pts-bij are now theorems). Proved. -/
theorem modelHeightBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **`ModelHeightBaseChangeGE` (descent half of H4a) needs only BC-alg and BC-lat** (the
uniformization descent is proved). -/
theorem modelHeightBaseChangeGE_of_two (h1 : HodgeBCInjective) (h2 : DetLatticeBC) :
    ModelHeightBaseChangeGE := by
  refine modelHeightBaseChangeGE_of_descentHalf ?_
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_⟩
  intro σ τ' hστ Λ Φ' hΦ'
  refine ⟨fun z => bcPts e σ τ' hστ (Φ' z), isAnalyticUniformization_bcPts ptsBaseChangeMul
    ptsBaseChangeBij he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
  rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements over
the natural map**: BC-alg (`HodgeBCInjective`), BC-omega (`OmegaBaseChange`), BC-lift
(`UniformizationLift`), BC-span (`JacobianPullbackSpan`). Proved. -/
theorem modelHeightBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **The descent half of H4a from BC-alg and BC-omega only.** -/
theorem modelHeightBaseChangeGE_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_two h1 (detLatticeBC_of_omega hω)

/-- **Main result (finest form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-hspan (`HodgeSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **Main result (finest form, with BC-cot): glue H4a (`ModelHeightBaseChange`, verbatim) from
five glue statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-der (`GermDerivation`). Proved. -/
theorem modelHeightBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements** (final form). -/
theorem hodgeLineBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from four glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`). `GermDerivation` is proved.
Proved. -/
theorem modelHeightBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_final h1 hc hω hl germDerivation

/-- **`HodgeLineBaseChange` (verbatim) from the same four glue statements** (final form). -/
theorem hodgeLineBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_final h1 hc hω hl germDerivation


end ZInQ.HeightBC

namespace RvGP2
/-- Field 9 of `GluePieces2` from height-bc's four glue statements. -/
theorem hodgeLineBaseChange (h1 : ZInQ.HeightBC.HodgeBCInjective)
    (hc : ZInQ.HeightBC.CotangentSpanBC) (hω : ZInQ.HeightBC.OmegaBaseChange)
    (hl : ZInQ.HeightBC.UniformizationLiftAnalytic) : G0StableBC.HodgeLineBaseChange :=
  ZInQ.HeightBC.hodgeLineBaseChange_of_glue4 h1 hc hω hl
end RvGP2

#print axioms RvGP2.hodgeLineBaseChange
