import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPK

/-!
**Theorem 5.3: homology-level switching data with a genuine switch (lane RC29, non-vacuity)**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195: the nonquadratic switch (tex 4997–5003), the exact sequences
(5.5a) (tex 5055–5086) and the localization duality `U = U^⊥` (tex 5068–5075).

`HomologySwitchDataPK` (`GenuineSwitchHPK.lean`) is inhabited here with `1 < fiberDim` at the
actual configuration, so that its switch field is genuinely exercised: the actual stage (fibre
dimension three) switches, through a homology-level nonquadratic step (the RC53 group's
`QuasiNonquadStep`) whose sides ARE the two configurations' fibres, to a stage of fibre dimension
one.

This is a STRUCTURE-LEVEL example over `A = F = k = ℚ` (`ι = ρ = id`): `ℚ` is not a DVR (so
`regular_of_homologyPK` does not apply to it), and the fibres are Selmer complexes of finite Selmer
data over `ℚ`, not genuine Galois fibres.

**Design.** The relaxed Selmer data `swxRelD`: `G = ℚ`, `U_rel = F ⊕ S = ℚ² × ℚ²`,
`L = S ⊕ ℚ = ℚ² × ℚ`, all in degree one, `res = 0`, `ι(f, s) = (s, 0)`; `W_rel = F ⊕ S`, `g_R = id`.
The sides `swxSideF`, `swxSideS` are batch 3's `exSideF`, `exSideS` restated over these data, on the
shared strict condition `0` (`swxStrict`). Compared with batch 3's `exRel` (where `L = S`, so the
side complexes are not square), the extra summand `ℚ` of `L` makes both side complexes square:
* `C(F) = [ℚ³ --0--> ℚ³]` (as `ι ∘ inl = 0`), isomorphic to the two-term fibre of batch 3's
  `exStage3 u` (`swxIsoF`);
* `C(S) = [ℚ³ → ℚ³]`, `(a, s) ↦ (−s, 0)`, isomorphic (`swxIsoS`) to the two-term fibre of
  `swxStage1 u`: `D̄ = diag(0, 1, 1)`, cycle `e₀`, closed functional `u e₀^*`, coordinate `u`
  (`adj D̄ = e₀ e₀^*`).
Both isomorphisms are `(a, s, x) ↦ (a₀, −s₀, −s₁)` in degree one and `(l, m) ↦ (m₀, l₀, l₁)` in
degree two (zero elsewhere). The model matrix of the singular side is `diag(0, 1, 1)` rather than
the nilpotent `−(E₀₁ + E₁₂)` of `L = ℚ³` with `ι(f, s) = (s₀, s₁, 0)`: the two are the same complex
in other bases, and this choice keeps `ι` uniform in the degree and the adjugate diagonal.

PROVED here: `swxRel_U` (`U = F`: `U ≤ F` directly, `dim(U ⊓ F) = 3 − 1` from (5.5a)),
`swxSideF_str` (`K₀ = ℚ`), `swxStep : QuasiNonquadStep id (exStage3 u) (swxStage1 u')` (duality
from batch 3's `exLocalizationDuality`, detection `F ≤ U`, `φ`, `φ'` from the models),
`swxStep_drop` (`3 → 1`), the family `swxFamily` (configurations `Bool`, one prime, `t = 1`;
`swxFamily_not_quadratic`), the datum `swxData : HomologySwitchDataPK swxFamily id id u_F`
(coordinate step batch 3's `exCoordStep`, `u_F = 1 → u_S = −1`), `swxData_fiberDim_actual` (`= 3`),
`swxData_fiberDim_next` (`= 1`), `swxFamily_h1` (`dim H¹` of the two fibres: `3` and `1`) and
`swxData_coords`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### The relaxed Selmer data and the two sides -/

section Data

/-- The full local complex `L = S ⊕ ℚ = ℚ² × ℚ` in degree one, `0` elsewhere. Kind: definition. -/
abbrev swxLn (n : ℤ) : ModuleCat.{0} ℚ :=
  ModuleCat.of ℚ ((Fin (dimAt 2 n) → ℚ) × (Fin (dimAt 1 n) → ℚ))

/-- **The relaxed Selmer data of the example** (tex 5068–5075): `G = ℚ` in degree one with
`res = 0`, the relaxed condition `U_rel = F ⊕ S = ℚ² × ℚ²`, the full local complex `L = S ⊕ ℚ`, and
`ι(f, s) = (s, 0)`, all concentrated in degree one. Kind: definition. -/
def swxRelD : SelData ℚ where
  G := zGCx (Pn 1)
  U := zGCx Qn
  L := zGCx swxLn
  res := zHom fun _ => 0
  ι := zHom fun _ => (LinearMap.inl ℚ _ _).comp (LinearMap.snd ℚ _ _)

/-- **The relaxed localization of the example**: the relaxed quotient `W_rel = F ⊕ S`, `g_R = id`,
coordinates `W_rel¹ ≃ ℚ² × ℚ²` (tex 5070–5075). Kind: definition. -/
def swxRel : RelaxedLocalization ℚ where
  D := swxRelD
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- **The finite side** (tex 5080–5083): `U_F = F` (`f₁ = inl`), `W₂ = S` (`g₂ = snd`),
`U_str = 0`, `W₁ = F`. Kind: definition. -/
def swxSideF : SwitchSide swxRel (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inl ℚ _ _
  g₂ := zHom fun _ => LinearMap.snd ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inl ℚ _ _
  p := zHom fun _ => LinearMap.snd ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inl_injective
  g₂_surj _ := LinearMap.snd_surjective
  ex₂ _ u h := ⟨u.1, Prod.ext rfl h.symm⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inl_injective
  ip_exact y := ⟨fun h => ⟨y.1, Prod.ext rfl h.symm⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_finPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.1, Prod.ext ?_ ?_⟩
      · change (eqvA 2) ((eqvA 2).symm z.1) = z.1
        exact LinearEquiv.apply_symm_apply _ _
      · change (eqvA 2) 0 = z.2
        rw [map_zero, hz]

/-- **The singular side** (tex 5080–5083): `U_S = S` (`f₁ = inr`), `W₂ = F` (`g₂ = fst`),
`U_str = 0`, `W₁ = S`. Kind: definition. -/
def swxSideS : SwitchSide swxRel (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inr ℚ _ _
  g₂ := zHom fun _ => LinearMap.fst ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inr ℚ _ _
  p := zHom fun _ => LinearMap.fst ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inr_injective
  g₂_surj _ := LinearMap.fst_surjective
  ex₂ _ u h := ⟨u.2, Prod.ext h.symm rfl⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inr_injective
  ip_exact y := ⟨fun h => ⟨y.2, Prod.ext h.symm rfl⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_singPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.2, Prod.ext ?_ ?_⟩
      · change (eqvA 2) 0 = z.1
        rw [map_zero, hz]
      · change (eqvA 2) ((eqvA 2).symm z.2) = z.2
        exact LinearEquiv.apply_symm_apply _ _

/-- **The two sides share the strict condition** `U_str = 0` (tex 5072–5083, "with `D⁰`
retained"). Kind: definition. -/
def swxStrict : StrictIdentification swxSideF swxSideS where
  e := idGHom (zGCx Zn)
  e' := idGHom (zGCx Zn)
  he'e _ _ := rfl
  hee' _ _ := rfl
  hι n x := by
    have hx : x = 0 := funext fun i => Fin.elim0 i
    subst hx
    exact ((swxSideF.Dstr.ι.f n n rfl).map_zero).trans ((swxSideS.Dstr.ι.f n n rfl).map_zero).symm

/-- The finite fibre `C(F)`: the Selmer data of the finite side. Kind: definition. -/
abbrev swxFibF : SelData ℚ := swxSideF.Dside

/-- The singular fibre `C(S)`: the Selmer data of the singular side. Kind: definition. -/
abbrev swxFibS : SelData ℚ := swxSideS.Dside

end Data

/-! ### The stages -/

section Stages

/-- The two-term model of the singular fibre: `D̄ = diag(0, 1, 1)`. Kind: definition. -/
def swxM : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![0, 1, 1]

/-- **The stage of fiber dimension one** (tex 4983–4992, 5154–5157): the model `[ℚ³ --D̄--> ℚ³]`
with `D̄ = diag(0, 1, 1)`, cycle `e₀`, closed functional `u e₀^*` and coordinate `u`
(`adj D̄ = e₀ e₀^*`). Kind: definition. -/
def swxStage1 (u : ℚ) : TwoTermStage (RingHom.id ℚ) where
  n := 2
  D := swxM
  z := ![1, 0, 0]
  w := ![u, 0, 0]
  u := u
  hz := by
    ext i; fin_cases i <;> simp [swxM, mulVec_diagonal]
  hw := by
    ext i; fin_cases i <;> simp [swxM, vecMul_diagonal]
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swxM, Matrix.adjugate_fin_three, vecMulVec_apply, Matrix.diagonal]

end Stages

/-! ### The two models: isomorphisms of complexes -/

section Models

/-- The underlying modules of both fibres, `G^n × U₁^n × L^{n−1}`. Kind: definition. -/
abbrev swxT (n : ℤ) : Type :=
  (Fin (dimAt 1 n) → ℚ) × (Fin (dimAt 2 n) → ℚ) ×
    ((Fin (dimAt 2 (n - 1)) → ℚ) × (Fin (dimAt 1 (n - 1)) → ℚ))

/-- `dimAt a (2 − 1) = a` (the degree-two index of `L^{n−1}`). Kind: PROVED. -/
theorem swx_dimAt_two_sub (a : ℕ) : dimAt a (2 - 1) = a := by unfold dimAt; norm_num

/-- `ℚ^{dimAt a (2 − 1)} ≃ ℚ^a`. Kind: definition. -/
def swxEqvB (a : ℕ) : (Fin (dimAt a (2 - 1)) → ℚ) ≃ₗ[ℚ] (Fin a → ℚ) :=
  LinearEquiv.funCongrLeft ℚ ℚ (finCongr (swx_dimAt_two_sub a)).symm

/-- `swxEqvB` and batch 3's `eqvA` agree. Kind: PROVED. -/
theorem swxEqvB_eq (a : ℕ) (v : Fin (dimAt a 1) → ℚ) : swxEqvB a v = eqvA a v := rfl

/-- Outside degrees one and two both fibres vanish. Kind: PROVED. -/
theorem swxT_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : Subsingleton (swxT n) := by
  have := subsingleton_dimAt 1 h1
  have := subsingleton_dimAt 2 h1
  have := subsingleton_dimAt 2 (n := n - 1) (by omega)
  have := subsingleton_dimAt 1 (n := n - 1) (by omega)
  infer_instance

/-- `dim C¹ = 3`. Kind: PROVED. -/
theorem swxT_finrank_one : finrank ℚ (swxT 1) = 3 := by
  unfold swxT
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- `dim C² = 3`. Kind: PROVED. -/
theorem swxT_finrank_two : finrank ℚ (swxT 2) = 3 := by
  unfold swxT
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- Degree one: `(a, s, x) ↦ (a₀, −s₀, −s₁)`. Kind: definition. -/
def swxF1 : swxT 1 →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun c := ![eqvA 1 c.1 0, -eqvA 2 c.2.1 0, -eqvA 2 c.2.1 1]
  map_add' c c' := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r c := by ext i; fin_cases i <;> simp

/-- Degree two: `(a, s, (l, m)) ↦ (m₀, l₀, l₁)`. Kind: definition. -/
def swxF2 : swxT 2 →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun c := ![swxEqvB 1 c.2.2.2 0, swxEqvB 2 c.2.2.1 0, swxEqvB 2 c.2.2.1 1]
  map_add' c c' := by ext i; fin_cases i <;> simp
  map_smul' r c := by ext i; fin_cases i <;> simp

/-- Kind: PROVED. -/
theorem swxF1_injective : Function.Injective swxF1 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, s, x⟩ hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [swxF1] at h0 h1 h2
  have ha : eqvA 1 a = 0 := by funext i; fin_cases i; exact h0
  have hs : eqvA 2 s = 0 := by funext i; fin_cases i; exacts [h1, h2]
  have : Subsingleton ((Fin (dimAt 2 (1 - 1)) → ℚ) × (Fin (dimAt 1 (1 - 1)) → ℚ)) := by
    have := subsingleton_dimAt 2 (n := 1 - 1) (by norm_num)
    have := subsingleton_dimAt 1 (n := 1 - 1) (by norm_num)
    infer_instance
  exact Prod.ext ((eqvA 1).map_eq_zero_iff.1 ha)
    (Prod.ext ((eqvA 2).map_eq_zero_iff.1 hs) (Subsingleton.elim _ _))

/-- Kind: PROVED. -/
theorem swxF2_injective : Function.Injective swxF2 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, s, l, m⟩ hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [swxF2] at h0 h1 h2
  have hm : swxEqvB 1 m = 0 := by funext i; fin_cases i; exact h0
  have hl : swxEqvB 2 l = 0 := by funext i; fin_cases i; exacts [h1, h2]
  have := subsingleton_dimAt 1 (n := 2) (by norm_num)
  have := subsingleton_dimAt 2 (n := 2) (by norm_num)
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _)
    (Prod.ext ((swxEqvB 2).map_eq_zero_iff.1 hl) ((swxEqvB 1).map_eq_zero_iff.1 hm)))

/-- The degree-one isomorphism. Kind: definition. -/
def swxE1 : swxT 1 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  LinearMap.linearEquivOfInjective swxF1 swxF1_injective (by rw [swxT_finrank_one]; simp)

/-- The degree-two isomorphism. Kind: definition. -/
def swxE2 : swxT 2 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  LinearMap.linearEquivOfInjective swxF2 swxF2_injective (by rw [swxT_finrank_two]; simp)

/-- The degreewise isomorphisms of both models: `swxE1`, `swxE2` in degrees one and two, the zero
isomorphism elsewhere. Kind: definition. -/
def swxIsoX : ∀ n : ℤ,
    ModuleCat.of ℚ (swxT n) ≅ threeTermX ℚ PUnit.{1} (Fin (2 + 1) → ℚ) (Fin (2 + 1) → ℚ) n
  | .ofNat 0 => (@LinearEquiv.ofSubsingleton ℚ (swxT 0) PUnit.{1} _ _ _ _ _
      (swxT_subsingleton 0 (by norm_num) (by norm_num)) _).toModuleIso
  | .ofNat 1 => swxE1.toModuleIso
  | .ofNat 2 => swxE2.toModuleIso
  | .ofNat (k + 3) => (@LinearEquiv.ofSubsingleton ℚ (swxT (k + 3)) PUnit.{1} _ _ _ _ _
      (swxT_subsingleton (k + 3) (by omega) (by omega)) _).toModuleIso
  | .negSucc k => (@LinearEquiv.ofSubsingleton ℚ (swxT (.negSucc k)) PUnit.{1} _ _ _ _ _
      (swxT_subsingleton (.negSucc k) (by omega) (by omega)) _).toModuleIso

/-- A differential with a zero source or target vanishes. Kind: PROVED. -/
theorem swx_d_eq_zero (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)
    (hK : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (K.X n)) (i : ℤ) (hi : i ≠ 1) :
    K.d i (i + 1) = 0 := by
  by_cases h0 : i = 0
  · subst h0
    have := hK 0 (by norm_num) (by norm_num)
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  · have := hK (i + 1) (by omega) (by omega)
    ext x
    exact Subsingleton.elim _ _

/-- Outside degrees one and two the two-term fibre vanishes. Kind: PROVED. -/
theorem swx_twoTerm_subsingleton {S : TwoTermStage (RingHom.id ℚ)} (n : ℤ) (h1 : n ≠ 1)
    (h2 : n ≠ 2) : Subsingleton ((twoTermFiberComplex (RingHom.id ℚ) S).X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact (inferInstance : Subsingleton PUnit)
  · exact threeTermX_subsingleton n h0 h1 h2

/-- **The finite fibre has zero differential** (`res = 0`, `ι ∘ inl = 0`). Kind: PROVED. -/
theorem swxFibF_d12 : (selCx swxFibF).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] _) a -
    (LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 1 1) → ℚ))
      ((LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
        ((LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) u)) - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ rfl

/-- **The differential of the singular fibre**: `d(a, s, x) = (0, 0, (−s, 0))` in its local
component. Kind: PROVED. -/
theorem swxFibS_d3 (a : Fin (dimAt 1 1) → ℚ) (s : Fin (dimAt 2 1) → ℚ)
    (x : (Fin (dimAt 2 (1 - 1)) → ℚ) × (Fin (dimAt 1 (1 - 1)) → ℚ)) :
    (((selCx swxFibS).toCC.d 1 2).hom (a, s, x)).2.2 =
      (-(s : Fin (dimAt 2 (2 - 1)) → ℚ), (0 : Fin (dimAt 1 (2 - 1)) → ℚ)) := by
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] _) a -
    (LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 1 1) → ℚ))
      ((LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
        ((LinearMap.inr ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) s)) - 0 = _
  simp

/-- The two-term fibre of `exStage3 u` has zero differential. Kind: PROVED. -/
theorem swx_exStage3_d12 (u : ℚ) :
    (twoTermFiberComplex (RingHom.id ℚ) (exStage3 u)).d 1 2 = 0 := by
  change ModuleCat.ofHom (((exStage3 u).D.map (RingHom.id ℚ)).mulVecLin) = 0
  rw [show ((exStage3 u).D.map (RingHom.id ℚ)).mulVecLin = 0 from by
    apply LinearMap.ext; intro x; ext i; simp [exStage3]; rfl]
  rfl

/-- The two-term fibre of `swxStage1 u` has differential `D̄ = diag(0, 1, 1)`. Kind: PROVED. -/
theorem swx_swxStage1_d12 (u : ℚ) :
    (twoTermFiberComplex (RingHom.id ℚ) (swxStage1 u)).d 1 2 = ModuleCat.ofHom swxM.mulVecLin := by
  change ModuleCat.ofHom (((swxStage1 u).D.map (RingHom.id ℚ)).mulVecLin) = _
  rfl

/-- **The finite model** (tex 4983–4996): the finite fibre `C(F) = [ℚ³ --0--> ℚ³]` is isomorphic
to the two-term fibre of `exStage3 u`. Kind: definition. -/
def swxIsoF (u : ℚ) : (selCx swxFibF).toCC ≅ twoTermFiberComplex (RingHom.id ℚ) (exStage3 u) :=
  HomologicalComplex.Hom.isoOfComponents swxIsoX fun i j hij => by
    simp only [ComplexShape.up_Rel] at hij
    by_cases h1 : i = 1
    · subst h1
      obtain rfl : j = 2 := by omega
      rw [swx_exStage3_d12, swxFibF_d12, Limits.comp_zero, Limits.zero_comp]
    · subst hij
      rw [swx_d_eq_zero _ (fun n h1 h2 => swx_twoTerm_subsingleton n h1 h2) i h1,
        swx_d_eq_zero _ (fun n h1 h2 => swxT_subsingleton n h1 h2) i h1,
        Limits.comp_zero, Limits.zero_comp]

/-- **The singular model** (tex 4983–4996): the singular fibre `C(S) = [ℚ³ → ℚ³]`,
`(a, s) ↦ (−s, 0)`, is isomorphic to the two-term fibre of `swxStage1 u` (`D̄ = diag(0, 1, 1)`).
Kind: definition. -/
def swxIsoS (u : ℚ) : (selCx swxFibS).toCC ≅ twoTermFiberComplex (RingHom.id ℚ) (swxStage1 u) :=
  HomologicalComplex.Hom.isoOfComponents swxIsoX fun i j hij => by
    simp only [ComplexShape.up_Rel] at hij
    by_cases h1 : i = 1
    · subst h1
      obtain rfl : j = 2 := by omega
      rw [swx_swxStage1_d12]
      ext c
      obtain ⟨a, s, x⟩ := c
      have h3 := swxFibS_d3 a s x
      change swxM *ᵥ swxF1 (a, s, x) = swxF2 (((selCx swxFibS).toCC.d 1 2).hom (a, s, x))
      generalize ((selCx swxFibS).toCC.d 1 2).hom (a, s, x) = y at h3 ⊢
      obtain ⟨y1, y2, y3⟩ := y
      change y3 = _ at h3
      subst h3
      funext i
      fin_cases i <;> simp [swxF1, swxF2, swxM, mulVec_diagonal] <;> rfl
    · subst hij
      rw [swx_d_eq_zero _ (fun n h1 h2 => swx_twoTerm_subsingleton n h1 h2) i h1,
        swx_d_eq_zero _ (fun n h1 h2 => swxT_subsingleton n h1 h2) i h1,
        Limits.comp_zero, Limits.zero_comp]

end Models

/-! ### The relaxed image, the strict cohomology, and the step -/

section Step

/-- **The relaxed image lies in the finite plane** (tex 5072–5074): a relaxed cocycle
`(a, (f, s), x)` has `res a − ι(f, s) = −(s, 0) = 0`. Kind: PROVED. -/
theorem swxRel_U_le : swxRel.U ≤ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  intro z hz
  obtain ⟨c, ⟨c', rfl⟩, rfl⟩ := hz
  set K := (selCx swxRel.D).toCC
  obtain ⟨y, rfl⟩ : ∃ y, (K.homologyπ 1).hom y = c' :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance c'
  have hnat := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.homologyπ_naturality (GHom.toCC (quotMap swxRel.D swxRel.gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [mem_finPlane]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hnat, h1Equiv_apply]
  have hπ := congrArg (fun f => ModuleCat.Hom.hom f
    ((HomologicalComplex.cyclesMap (GHom.toCC (quotMap swxRel.D swxRel.gR)) 1).hom y))
    (homologyπ_h1Iso swxRel.Wrel swxRel.hWrel)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ]
  have hi := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.cyclesMap_i (GHom.toCC (quotMap swxRel.D swxRel.gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi]
  have hd := congrArg (fun f => ModuleCat.Hom.hom f y) (K.iCycles_d 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hd
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  generalize (K.iCycles 1).hom y = w at hd ⊢
  obtain ⟨a, u, x⟩ := w
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 1 1) → ℚ)) -
    (LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 1 1) → ℚ))
      (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 - 0 = 0 at h3
  have h4 : (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0 := by
    simpa using h3
  change (eqvA 2) (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0
  rw [h4, map_zero]

/-- The strict complex has zero differential in degree one. Kind: PROVED. -/
theorem swxSideF_str_d12 : (selCx swxSideF.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt 1 1) → ℚ) →ₗ[ℚ] ((Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 1 1) → ℚ))) a -
    _ - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ (map_zero _)

/-- **The strict cohomology** `K₀ = H¹(C_str) = ℚ` (tex 5072–5074). Kind: PROVED. -/
theorem swxSideF_str : finrank ℚ ((selCx swxSideF.Dstr).toCC.homology 1) = 1 := by
  have h0 : Subsingleton
      (swxSideF.Dstr.G.X 0 × swxSideF.Dstr.U.X 0 × swxSideF.Dstr.L.X (0 - 1)) := by
    have := subsingleton_dimAt 1 (n := 0) (by norm_num)
    have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
    have := subsingleton_dimAt 1 (n := 0 - 1) (by norm_num)
    change Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) ×
      ((Fin (dimAt 2 (0 - 1)) → ℚ) × (Fin (dimAt 1 (0 - 1)) → ℚ)))
    infer_instance
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ h0) swxSideF_str_d12]
  have : FiniteDimensional ℚ (swxSideF.Dstr.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  have : FiniteDimensional ℚ (swxSideF.Dstr.U.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin 0 → ℚ))
  have : FiniteDimensional ℚ (swxSideF.Dstr.L.X (1 - 1)) :=
    (inferInstance : FiniteDimensional ℚ
      ((Fin (dimAt 2 (1 - 1)) → ℚ) × (Fin (dimAt 1 (1 - 1)) → ℚ)))
  rw [finrank_selX1]
  change finrank ℚ (Fin (dimAt 1 1) → ℚ) + (finrank ℚ (Fin 0 → ℚ) +
    finrank ℚ ((Fin (dimAt 2 (1 - 1)) → ℚ) × (Fin (dimAt 1 (1 - 1)) → ℚ))) = 1
  rw [Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- **`dim H¹(C(F)) = 3`**, from the finite model. Kind: PROVED. -/
theorem swxFibF_h1 : finrank ℚ ((selCx swxFibF).toCC.homology 1) = 3 := by
  rw [← fiberDim_eq_h1 ℚ ℚ ℚ (RingHom.id ℚ) (RingHom.id ℚ) (exStage3 0) swxFibF
    ⟨HomotopyEquiv.ofIso (swxIsoF 0)⟩, exStage3_fiberDim]

/-- **The relaxed image is the finite plane**, `U = F` (tex 4997–5003, 5072–5074): `U ≤ F` directly,
and `dim(U ⊓ F) = 3 − 1 = 2` from (5.5a) on the finite side. Kind: PROVED. -/
theorem swxRel_U : swxRel.U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  have : FiniteDimensional ℚ (swxRel.D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  have : FiniteDimensional ℚ (swxRel.D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ ((Fin (dimAt 2 0) → ℚ) × (Fin (dimAt 1 0) → ℚ)))
  have : FiniteDimensional ℚ (swxSideF.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have : FiniteDimensional ℚ (swxSideS.U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have h := (switchDims_of_selmerData swxRel swxSideF swxSideS).1
  rw [show finrank ℚ ((selCx swxSideF.Dside).toCC.homology 1) = 3 from swxFibF_h1,
    swxSideF_str] at h
  have h2 : finrank ℚ ↥(swxRel.U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) =
      finrank ℚ ↥(finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) := by
    rw [finrank_finPlane_two]; omega
  have hF : swxRel.U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right h2
  exact le_antisymm swxRel_U_le (hF ▸ inf_le_left)

/-- **The homology-level nonquadratic step** of the example (tex 4997–5003, 5055–5086): the quasi
relaxed localization and sides of `swxRel`, `swxSideF`, `swxSideS`, the shared strict condition
(`hk0`), the duality `U = U^⊥` (tex 5068–5075; `U = F`, `exLocalizationDuality`), detection
`F ≤ U`, and the side `H¹`s identified with the stage fibres through the models. Kind:
definition. -/
def swxStep (u u' : ℚ) : QuasiNonquadStep (RingHom.id ℚ) (exStage3 u) (swxStage1 u') where
  R := swxRel.toQuasi
  SF := swxSideF.toQuasi
  SS := swxSideS.toQuasi
  hk0 := swxStrict.hk0
  ε := 1
  σ := 1
  J := J₀
  hε := one_ne_zero
  hσ := one_ne_zero
  hJ2 := J₀_sq
  hdual := by
    unfold LocalizationDualityInput
    rw [RelaxedLocalization.toQuasi_U, swxRel_U]
    exact exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq
  hdet := swxRel_U.ge
  φ := h1EquivOfHomotopyEquiv (RingHom.id ℚ) (exStage3 u) swxFibF
    (HomotopyEquiv.ofIso (swxIsoF u))
  φ' := h1EquivOfHomotopyEquiv (RingHom.id ℚ) (swxStage1 u') swxFibS
    (HomotopyEquiv.ofIso (swxIsoS u'))

/-- **The step drops the fibre dimension by two**, `3 → 1` (tex 4997–5003). Kind: PROVED. -/
theorem swxStep_drop (u u' : ℚ) :
    (swxStage1 u').fiberDim (RingHom.id ℚ) + 2 = (exStage3 u).fiberDim (RingHom.id ℚ) :=
  (swxStep u u').toNonquadDims.drop

/-- `swxStage1` has fibre dimension one. Kind: PROVED. -/
theorem swxStage1_fiberDim (u : ℚ) : (swxStage1 u).fiberDim (RingHom.id ℚ) = 1 := by
  have h := swxStep_drop 0 u
  rw [exStage3_fiberDim] at h
  omega

/-- **`dim H¹(C(S)) = 1`**, from the singular model. Kind: PROVED. -/
theorem swxFibS_h1 : finrank ℚ ((selCx swxFibS).toCC.homology 1) = 1 := by
  rw [← fiberDim_eq_h1 ℚ ℚ ℚ (RingHom.id ℚ) (RingHom.id ℚ) (swxStage1 0) swxFibS
    ⟨HomotopyEquiv.ofIso (swxIsoS 0)⟩, swxStage1_fiberDim]

end Step

/-! ### The family and the homology-level switching data -/

section Family

/-- The actual coordinate `u_F` of `exCoordStep` (`u_F = 1`, `swxData_coords`). Kind: definition. -/
abbrev swxUF : ℚ := (exSwitchCoordData 1 1).uF

/-- The switched coordinate `u_S` of `exCoordStep`. Kind: definition. -/
abbrev swxUS : ℚ := (exSwitchCoordData 1 1).uS

/-- The fibres of the two configurations: `false ↦ C(F)`, `true ↦ C(S)`. Kind: definition. -/
def swxFibre : Bool → SelData ℚ
  | false => swxFibF
  | true => swxFibS

/-- **The example configuration family** (tex 4976–5003): configurations `Bool` (actual `false`),
one prime, `next _ _ = true`, fibres `C(F)` and `C(S)`, moving variable `t = 1` (nonquadratic),
actual class the preimage of `e₀` under the finite model, actual functional `0`. Kind:
definition. -/
def swxFamily : SwitchFamily ℚ ℚ where
  Config := Bool
  Prime := Unit
  actual := false
  next _ _ := true
  fibre := swxFibre
  t := 1
  zAct := ((swxIsoF swxUF).inv.f 1).hom ![1, 0, 0]
  hzAct := by
    change ((selCx swxFibF).toCC.d 1 2).hom _ = 0
    rw [swxFibF_d12]
    rfl
  lamAct := 0
  hlamAct _ := rfl

/-- **The family is nonquadratic**: `t̄ (t̄ + 2) = 3 ≠ 0` (tex 5005–5008). Kind: PROVED. -/
theorem swxFamily_not_quadratic : ¬ swxFamily.quadratic (RingHom.id ℚ) := by
  change ¬ (RingHom.id ℚ) 1 * ((RingHom.id ℚ) 1 + 2) = 0
  norm_num

/-- The stages: `false ↦ exStage3 u_F` (fibre dimension three), `true ↦ swxStage1 u_S` (fibre
dimension one). Kind: definition. -/
def swxStage : Bool → TwoTermStage (RingHom.id ℚ)
  | false => exStage3 swxUF
  | true => swxStage1 swxUS

/-- The models of the two configurations (isomorphisms of complexes). Kind: definition. -/
def swxModel : ∀ c : Bool,
    HomotopyEquiv (selCx (swxFamily.fibre c)).toCC (twoTermFiberComplex (RingHom.id ℚ) (swxStage c))
  | false => HomotopyEquiv.ofIso (swxIsoF swxUF)
  | true => HomotopyEquiv.ofIso (swxIsoS swxUS)

/-- **Homology-level switching data with a genuine switch** (non-vacuity of
`HomologySwitchDataPK` with `1 < fiberDim` at the actual configuration; tex 4976–5195): the actual
stage `exStage3 u_F` (fibre dimension three) switches at the one prime, nonquadratically
(`swxStep`, coordinate step `exCoordStep`), to `swxStage1 u_S` (fibre dimension one). Kind:
definition. -/
def swxData : HomologySwitchDataPK swxFamily (RingHom.id ℚ) (RingHom.id ℚ) swxUF where
  stage := swxStage
  model := swxModel
  hz0 := by
    change ((swxIsoF swxUF).inv.f 1 ≫ (swxIsoF swxUF).hom.f 1).hom ![1, 0, 0] = _
    rw [← HomologicalComplex.comp_f, (swxIsoF swxUF).inv_hom_id]
    rfl
  hw0 y := by
    change (0 : ℚ) = (fun i => RingHom.id ℚ ((exStage3 swxUF).w i)) ⬝ᵥ _
    have hw : (fun i => RingHom.id ℚ ((exStage3 swxUF).w i)) = 0 := by
      funext i
      rfl
    rw [hw]
    exact (zero_dotProduct _).symm
  hu0 := rfl
  σ _ := LinearMap.id
  h2 _ := two_ne_zero
  hσ _ _ := LinearMap.id_comp _
  class_ne_zero c _ := by
    cases c
    · exact ⟨0, by simp [swxStage, exStage3]⟩
    · exact ⟨0, by simp [swxStage, swxStage1]⟩
  switch_mixed c _ _ hs := by
    cases c
    · exact ⟨(), ⟨exCoordStep⟩, fun hq => absurd hq swxFamily_not_quadratic,
        fun _ => ⟨swxStep swxUF swxUS, rfl, rfl⟩⟩
    · exfalso
      have h1 : (swxStage true).fiberDim (RingHom.id ℚ) = 1 := swxStage1_fiberDim swxUS
      omega
  switch_single _ _ hq := absurd hq swxFamily_not_quadratic

/-- **The actual stage has fibre dimension three** (the case `s(𝔭) > 1` of the switching argument
is exercised). Kind: PROVED. -/
theorem swxData_fiberDim_actual :
    (swxData.stage swxFamily.actual).fiberDim (RingHom.id ℚ) = 3 :=
  exStage3_fiberDim swxUF

/-- **The switched stage has fibre dimension one**. Kind: PROVED. -/
theorem swxData_fiberDim_next :
    (swxData.stage (swxFamily.next swxFamily.actual ())).fiberDim (RingHom.id ℚ) = 1 :=
  swxStage1_fiberDim swxUS

/-- **The actual fibre has `dim H¹ = 3`, the switched fibre `dim H¹ = 1`** (sanity). Kind:
PROVED. -/
theorem swxFamily_h1 :
    finrank ℚ ((selCx (swxFamily.fibre swxFamily.actual)).toCC.homology 1) = 3 ∧
      finrank ℚ ((selCx (swxFamily.fibre (swxFamily.next swxFamily.actual ()))).toCC.homology 1)
        = 1 :=
  ⟨swxFibF_h1, swxFibS_h1⟩

/-- **The coordinates of the example**: `u_F = 1` at the actual stage, `u_S = −1` after the
switch. Kind: PROVED. -/
theorem swxData_coords :
    (swxData.stage swxFamily.actual).u = 1 ∧
      (swxData.stage (swxFamily.next swxFamily.actual ())).u = -1 :=
  ⟨exSwitchCoordData_uF 1 1, exSwitchCoordData_uS 1 1⟩

end Family

end ZInQ.Manuscript.RC.Wiring
