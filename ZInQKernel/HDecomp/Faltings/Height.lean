import ZInQKernel.HDecomp.Faltings.Models

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/def-faltings/Faltings.lean`, §18-§20.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra
open PkgI3 (AbVar)

/-! ## 18. Metrized models and the stable Faltings height (node H3) -/

/-- **A metrized model of `A_L` of dimension `g`**: a smooth group model `𝒢` (node M1) with its
metrized Hodge line. The lattice is the genuine `⋀^g ω_𝒢` (`lattice_eq`), and at every `τ` the
period lattice and the coefficient map come from an analytic uniformization of `𝒢(ℂ)_τ`
(`arch`): `coeff_τ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = det(∂(f_i ∘ Φ)/∂z_j(0))`. Since the wedges `wedge f`
span `hodgeSpace g` over `L`, `arch` determines `coeff`; by `AnalyticUniformizationUnique` and
`HodgeData.modelHeight_recoord`, `hodge.modelHeight` depends only on `𝒢`. A wrong `g` makes the
structure empty: for `0 < g ≠ dim A`, `hodge.finrank_eq_one` fails (and for `g > dim A` also
`periods_discrete`); `g = 0` passes `finrank_eq_one` (`hodgeSpace 0 ≅ L`) but is excluded for
`dim A ≥ 1` by surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)` (STANDARD reasoning, not proved). -/
structure MetrizedModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (g : ℕ) where
  /-- the smooth group model -/
  model : GroupModel A L
  /-- its Hodge data: lattice, period lattices, coefficient maps -/
  hodge : HodgeData L g (model.hodgeSpace g)
  /-- the lattice is `⋀^g ω_𝒢` -/
  lattice_eq : hodge.lattice = model.detLattice g
  /-- the archimedean data come from analytic uniformizations -/
  arch : ∀ τ : L →+* ℂ, ∃ Φ : (Fin g → ℂ) → model.Pts τ,
    model.IsAnalyticUniformization τ (hodge.periods τ) Φ ∧
    ∀ f : Fin g → IsLocalRing.maximalIdeal model.genStalk,
      hodge.coeff τ (model.wedge f) = model.jacDet Φ f

/-- A number field `L` with a `K`-algebra structure (the index type of the infimum). -/
structure FinExt (K : Type) [Field K] where
  /-- the field -/
  L : Type
  [field : Field L]
  [numberField : NumberField L]
  [algebra : Algebra K L]

attribute [instance] FinExt.field FinExt.numberField FinExt.algebra

/-- **Node H3. The stable Faltings height** (Faltings' original normalization `(i/2)^g`):
`h_F^st(A) = inf_{L, 𝒢} h(A_L, 𝒢) ∈ EReal`, over all number fields `L ⊇ K` and all smooth
separated finite-type group models `𝒢/𝓞_L` of `A_L`, each with its metrized Hodge line.
(pkg-I5 §2.1; equal to the Néron-model value over a semistable `L` by the Néron mapping property
and SGA 7 IX: node H5, not proved. `⊤` if there is no metrized model, which
`AnalyticUniformizationExists` and `HodgeLatticeTheorem` exclude once proved.) -/
noncomputable def stableFaltingsHeight {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), (M.hodge.modelHeight : EReal)

/-- **Node H6. Deligne's normalization** `(i/2π)^g`: each model height shifts by `(g/2) log π`. -/
noncomputable def stableFaltingsHeightDeligne {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g),
    ((M.hodge.modelHeight + g / 2 * Real.log Real.pi : ℝ) : EReal)

section HeightLemmas

variable {K : Type} [Field K] (A : AbVar K)

theorem stableFaltingsHeight_le {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : MetrizedModel A L g) : stableFaltingsHeight A ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le (FinExt.mk L) (iInf_le_of_le g (iInf_le_of_le M le_rfl))

theorem le_stableFaltingsHeight {x : EReal}
    (h : ∀ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), x ≤ (M.hodge.modelHeight : EReal)) :
    x ≤ stableFaltingsHeight A :=
  le_iInf fun E => le_iInf fun g => le_iInf fun M => h E g M

theorem EReal.add_coe_add_neg_coe (x : EReal) (c : ℝ) : x + (c : EReal) + ((-c : ℝ) : EReal) = x :=
    by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- **H6 for the infimum**: if every metrized model of `A` has dimension `g` (true for
`g = dim A`), `h_D^st(A) = h_F^st(A) + (g/2) log π`. Proved. -/
theorem stableFaltingsHeightDeligne_eq (g : ℕ)
    (hg : ∀ (E : FinExt K) (g' : ℕ), Nonempty (MetrizedModel A E.L g') → g' = g) :
    stableFaltingsHeightDeligne A =
      stableFaltingsHeight A + ((g / 2 * Real.log Real.pi : ℝ) : EReal) := by
  set c : ℝ := g / 2 * Real.log Real.pi
  apply le_antisymm
  · -- `hD + (-c) ≤ hF`
    have key : stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) ≤ stableFaltingsHeight A := by
      refine le_stableFaltingsHeight A fun E g' M => ?_
      obtain rfl := hg E g' ⟨M⟩
      have h1 : stableFaltingsHeightDeligne A ≤
          ((M.hodge.modelHeight + g' / 2 * Real.log Real.pi : ℝ) : EReal) :=
        iInf_le_of_le E (iInf_le_of_le g' (iInf_le_of_le M le_rfl))
      calc stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal)
          ≤ ((M.hodge.modelHeight + c : ℝ) : EReal) + ((-c : ℝ) : EReal) := by gcongr
        _ = (M.hodge.modelHeight : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
    calc stableFaltingsHeightDeligne A
        = stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) + ((c : ℝ) : EReal) := by
          have := EReal.add_coe_add_neg_coe (stableFaltingsHeightDeligne A) (-c)
          rw [neg_neg] at this; exact this.symm
      _ ≤ stableFaltingsHeight A + (c : EReal) := by gcongr
  · refine le_iInf fun E => le_iInf fun g' => le_iInf fun M => ?_
    obtain rfl := hg E g' ⟨M⟩
    rw [EReal.coe_add]
    gcongr
    exact stableFaltingsHeight_le A M

end HeightLemmas

/-! ### Independence of the uniformization (node H2, archimedean part)

Under the uniqueness half of AN3, the height of a metrized model depends only on the group model:
the coefficient map is determined by its values on the wedges `1 ⊗ df₁ ∧ ⋯ ∧ df_g`
(`GroupModel.semilinear_ext_wedge`), which change by `det T` under `Φ ↦ Φ ∘ T`
(`GroupModel.jacDet_comp`, the chain rule), and `HodgeData.modelHeight_recoord` absorbs `T`. -/

section UnifIndep

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

namespace GroupModel

variable (𝒢 : GroupModel A L)

/-- A `τ`-semilinear functional on the Hodge line is determined by its values on the wedges
`1 ⊗ df₁ ∧ ⋯ ∧ df_g` of germs `f_i ∈ 𝔪_ξ`. -/
theorem semilinear_ext_wedge {g : ℕ} {τ : L →+* ℂ} (φ ψ : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ)
    (h : ∀ f, φ (𝒢.wedge f) = ψ (𝒢.wedge f)) : φ = ψ := by
  have h1 : ∀ n : exteriorPower (𝓞 L) g 𝒢.cotangent,
      φ ((1 : L) ⊗ₜ[𝓞 L] n) = ψ ((1 : L) ⊗ₜ[𝓞 L] n) := by
    intro n
    have hn : n ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have hm : ∀ i, ∃ f, 𝒢.dCls f = m i := fun i =>
        (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (m i)
      choose f hf using hm
      have := h f
      simp only [wedge, hf] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L c, map_smulₛₗ, map_smulₛₗ, hx]
  ext v
  induction v using TensorProduct.inductionOn with
  | tmul l n =>
    have : l ⊗ₜ[𝓞 L] n = l • ((1 : L) ⊗ₜ[𝓞 L] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smulₛₗ, map_smulₛₗ, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Chain rule**: `jacDet (Φ ∘ T) f = jacDet Φ f · det T`. -/
theorem jacDet_comp {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => Φ (T z)) f =
      𝒢.jacDet Φ f * LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := by
  set Tc := T.toContinuousLinearEquiv
  have hd : ∀ t, fderiv ℂ (𝒢.germAlong (fun z => Φ (T z)) t) 0 =
      (fderiv ℂ (𝒢.germAlong Φ t) 0).comp (Tc : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := by
    intro t
    have : 𝒢.germAlong (fun z => Φ (T z)) t = 𝒢.germAlong Φ t ∘ Tc := rfl
    rw [this, Tc.comp_right_fderiv, map_zero]
  unfold jacDet
  simp only [hd]
  rw [← LinearMap.det_toMatrix', ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.comp_apply]
  show (fderiv ℂ (𝒢.germAlong Φ ↑(f i)) 0) (T (Pi.single j 1)) = _
  conv_lhs => rw [← Finset.univ_sum_single (T (Pi.single j 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : (Pi.single k ((T (Pi.single j 1)) k) : Fin g → ℂ) =
      ((T (Pi.single j 1)) k) • (Pi.single k (1 : ℂ) : Fin g → ℂ) := by
    ext m; by_cases hm : m = k
    · subst hm; simp
    · simp [hm]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
  rfl

end GroupModel

/-- **The model height does not depend on the uniformization** (given the uniqueness half of
AN3): two metrized models with the same group model have the same height. Proved. -/
theorem MetrizedModel.modelHeight_eq_of_model_eq (hU : AnalyticUniformizationUnique) {g : ℕ}
    (M M' : MetrizedModel A L g) (h : M.model = M'.model) :
    M.hodge.modelHeight = M'.hodge.modelHeight := by
  obtain ⟨𝒢, D, hl, ha⟩ := M
  obtain ⟨𝒢', D', hl', ha'⟩ := M'
  dsimp only at h ⊢
  subst h
  have key : ∀ τ, ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ z, z ∈ D'.periods τ ↔ T z ∈ D.periods τ) ∧
      D'.coeff τ = LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • D.coeff τ := by
    intro τ
    obtain ⟨Φ, hΦ, hc⟩ := ha τ
    obtain ⟨Φ', hΦ', hc'⟩ := ha' τ
    obtain ⟨T, hT, hΛ⟩ := hU K A L 𝒢 τ g _ _ Φ Φ' hΦ hΦ'
    refine ⟨T, hΛ, ?_⟩
    apply GroupModel.semilinear_ext_wedge
    intro f
    have hΦ'T : Φ' = fun z => Φ (T z) := funext hT
    rw [hc', LinearMap.smul_apply, hc, smul_eq_mul, hΦ'T, GroupModel.jacDet_comp, mul_comm]
  choose T hTp hTc using key
  have hD' : D' = D.recoord T := by
    obtain ⟨l', f1', il', p', pd', pz', c', cn'⟩ := D'
    obtain ⟨l, f1, il, p, pd, pz, c, cn⟩ := D
    simp only [HodgeData.recoord, HodgeData.mk.injEq]
    refine ⟨hl'.trans hl.symm, ?_, ?_⟩
    · funext τ
      ext z
      rw [hTp τ z]
      rfl
    · funext τ
      exact hTc τ
  show D.modelHeight = D'.modelHeight
  rw [hD', HodgeData.modelHeight_recoord]

/-- **The height of a group model** `h(A_L, 𝒢)`: the infimum over its metrizations (all of which
have the same height, `MetrizedModel.modelHeight_eq_of_model_eq`, given the uniqueness half of
AN3). -/
noncomputable def GroupModel.height (𝒢 : GroupModel A L) : EReal :=
  ⨅ (g : ℕ) (M : MetrizedModel A L g) (_ : M.model = 𝒢), (M.hodge.modelHeight : EReal)

/-- Given the uniqueness half of AN3, a metrized model computes the height of its group model
(among metrizations of the same dimension; the dimension is unique by `hodge.finrank_eq_one` and
the surjectivity in `IsAnalyticUniformization`). -/
theorem GroupModel.height_eq (hU : AnalyticUniformizationUnique) {g : ℕ} (M : MetrizedModel A L g)
    (hg : ∀ (g' : ℕ), Nonempty (MetrizedModel A L g') → g' = g) :
    M.model.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le rfl le_rfl))) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hg g' ⟨M'⟩
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' hM'.symm]

/-- `stableFaltingsHeight A = inf_{L, 𝒢} h(A_L, 𝒢)`. -/
theorem stableFaltingsHeight_eq_iInf_height (A : AbVar K) :
    stableFaltingsHeight A = ⨅ (E : FinExt K) (𝒢 : GroupModel A E.L), 𝒢.height := by
  unfold stableFaltingsHeight GroupModel.height
  refine le_antisymm ?_ ?_
  · refine le_iInf fun E => le_iInf fun 𝒢 => le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    exact iInf_le_of_le E (iInf_le_of_le g (iInf_le_of_le M le_rfl))
  · refine le_iInf fun E => le_iInf fun g => le_iInf fun M => ?_
    exact iInf_le_of_le E (iInf_le_of_le M.model (iInf_le_of_le g (iInf_le_of_le M
      (iInf_le_of_le rfl le_rfl))))

end UnifIndep

/-! ### The theorems that tie the definition to the literature (node H5), stated

`IsNeronModel` is the Néron mapping property (BLR 1.2/1, UNVERIFIED locator), stated with
Mathlib's objects: every morphism from the generic fibre of a smooth `𝓞_L`-scheme to `A_L`
extends uniquely. H5 is unproved; it needs Néron models (existence: BLR 1.4/3), semistable
reduction (SGA 7 IX 3.6) and the base change of semistable Néron models (SGA 7 IX 3.3), all
absent from Mathlib (locators UNVERIFIED). -/

section NeronSec

variable {K : Type} [Field K]

/-- **The Néron mapping property** for a group model `𝒩` of `A_L`. -/
def GroupModel.IsNeronModel {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ 𝒩.G =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ 𝒩.gen.hom

/-- **H5, finiteness (statement).** Over a number field, the stable height is a real number. -/
def StableHeightFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    stableFaltingsHeight A ≠ ⊤ ∧ stableFaltingsHeight A ≠ ⊥

/-- **H5, minimality of the Néron model (statement).** Over any `L`, the Néron model has the
least height among group models (from the mapping property, `ω_𝒩 ⊆ ω_𝒢`, and
`HodgeData.modelHeight_le_of_le`). -/
def NeronModelMinimal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 𝒢 : GroupModel A L), 𝒩.IsNeronModel → 𝒩.height ≤ 𝒢.height

/-- The real-valued stable Faltings height. Meaningful only together with `StableHeightFinite`
(`EReal.toReal` sends `⊤` and `⊥` to `0`); the leaves above therefore never use it. -/
noncomputable def faltingsHeight (A : AbVar K) : ℝ := (stableFaltingsHeight A).toReal

theorem faltingsHeight_coe (hfin : StableHeightFinite) [NumberField K] (A : AbVar K) :
    (faltingsHeight A : EReal) = stableFaltingsHeight A :=
  EReal.coe_toReal (hfin K A).1 (hfin K A).2

end NeronSec

/-! ## 19. Acceptance test AT1: elliptic curves

`IsEllipticCurveOf A W` identifies an abelian variety with the elliptic curve of a Weierstrass
equation using only Mathlib objects: the complement of the origin is an affine open whose ring of
functions is `K`-isomorphic to the affine coordinate ring `K[x, y]/(W)`. (Then `A` is the smooth
projective model of the function field of `W` with origin `O`, so `A ≅ E_W` as pointed curves,
and the group law with a given origin is unique by rigidity: STANDARD.) Mathlib v4.35 cannot yet
construct such an `A` from `W` (node AV7), so `AcceptanceEC` is a statement, not a theorem. -/

section AT1

open Polynomial

variable {K : Type} [Field K]

/-- The structure map `K → Γ(U, 𝒪_A)`. -/
noncomputable def _root_.PkgI3.AbVar.structMapOn (A : AbVar K) (U : A.X.left.Opens) : K →+*
    Γ(A.X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.X.hom.appTop ≫
    A.X.left.presheaf.map (homOfLE le_top).op).hom

/-- The origin of `A` (image of the unit section). -/
noncomputable def _root_.PkgI3.AbVar.origin (A : AbVar K) : A.X.left :=
  (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left
    ((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) : Spec (CommRingCat.of K))

/-- `A` is the elliptic curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`: `A ∖ {O}` is affine with
ring of functions `K[x, y]/(W)`, compatibly with `K`. -/
def IsEllipticCurveOf (A : AbVar K) (W : WeierstrassCurve K) : Prop :=
  ∃ U : A.X.left.Opens, (U : Set A.X.left) = {A.origin}ᶜ ∧ IsAffineOpen U ∧
    ∃ e : W.toAffine.CoordinateRing ≃+* Γ(A.X.left, U),
      ∀ c : K, e (algebraMap K W.toAffine.CoordinateRing c) = A.structMapOn U c

/-- **Acceptance test AT1 (statement).** For an elliptic curve over a number field, the general
definition agrees with pkg-I5's closed formula. Unproved: needs AV7 (an `A` with
`IsEllipticCurveOf A W` exists), AN3 for `g = 1` (AN4: `℘`), AN5 (`PeriodAreaFormula`), M2 for
the minimal Weierstrass model, AT1a (the Néron lattice) and H5 (the infimum is attained at the
Néron model over a semistable field). -/
def AcceptanceEC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K),
    IsEllipticCurveOf A W → stableFaltingsHeight A = (faltingsHeightEC W : EReal)

/-- **AT1, conditional form over the general definition (proved).** Let `M` be a metrized model
of `A` over `K` itself whose Hodge lattice is free on `η₀` with `η₀ ↦ dz` for period pairs
`Lp σ` (outputs of AN4 and M2 for a minimal semistable Weierstrass model: `η₀ = dx/(2y+a₁x+a₃)`),
with the Weierstrass polynomial equal to `4x³ − g₂x − g₃` after a translation `x ↦ x + c_σ`
(so any `b₂` is allowed: `g₂ = σ(c₄)/12`, `g₃ = σ(c₆)/216`) and the finite part of
`faltingsHeightEC` vanishing (AT1a: the model is semistable and minimal everywhere). Then, given
the area formula AN5, `M.hodge.modelHeight = faltingsHeightEC W` (the content of the theorem),
and with `hmin` the stable height equals it.

Caveat: `hmin` ("no metrized model of `A` has smaller height") is literally the `≥` half of the
conclusion. It is the output H5 must supply for this `A`: the Néron mapping property
(`GroupModel.IsNeronModel`, `NeronModelMinimal`) plus semistable base change (SGA 7 IX), none of
which is proved. The theorem ties `M` to `W` only through the hypotheses on `M`; it does not
assume `IsEllipticCurveOf A W`. -/
theorem stableFaltingsHeight_eq_faltingsHeightEC [NumberField K] (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K) (M : MetrizedModel A K 1)
    {η₀ : M.model.hodgeSpace 1}
    (hspan : M.hodge.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (Lp : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, M.hodge.periods σ = (Lp σ).lattice1)
    (hco : ∀ σ, M.hodge.coeff σ η₀ = 1) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (Lp σ).g₂ * X - C (Lp σ).g₃).comp (X + C (c σ)))
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖)
    (hmin : ∀ (E : FinExt K) (g : ℕ) (M' : MetrizedModel A E.L g),
      faltingsHeightEC W ≤ M'.hodge.modelHeight) :
    stableFaltingsHeight A = (faltingsHeightEC W : EReal) := by
  have hM : M.hodge.modelHeight = faltingsHeightEC W := by
    rw [M.hodge.modelHeight_of_span hspan hη₀, faltingsHeightEC, hfin, sub_self, zero_div,
      zero_sub]
    have hterm : ∀ σ : K →+* ℂ, torusMetricSq (M.hodge.periods σ) (M.hodge.coeff σ η₀) =
        hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
      intro σ
      rw [hco, hper, hP, hypVol_one_comp_add, torusMetricSq, PeriodPair.covolume_lattice1, hA]
      simp
    simp only [hterm]
    have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    field_simp
  refine le_antisymm ?_ ?_
  · exact (stableFaltingsHeight_le A M).trans_eq (by rw [hM])
  · exact le_stableFaltingsHeight A fun E g M' => EReal.coe_le_coe_iff.mpr (hmin E g M')

end AT1

/-! ## 20. Acceptance test AT2: genus-2 curves with a smooth model

`Genus2Eq`, `Genus2Eq.P`, `Genus2Eq.binDisc`, `Genus2Eq.Good` and `faltingsHeightGood` are copied
from `scratch/pkg-I5/I5.lean`. A statement "`stableFaltingsHeight (Jac C) = faltingsHeightGood E`"
cannot be written: Mathlib v4.35 has no Jacobians (node AV7) and no way to say that an `AbVar` is
the Jacobian of a curve. What is proved is the conditional form: a metrized model whose Hodge
lattice is free on `η₀` (M8: for a smooth Weierstrass model `𝒞/𝓞_K`, the Néron lattice is
`∧² H⁰(𝒞, ω) = 𝓞_K · (dx/(2y+h)) ∧ (x dx/(2y+h))`, BLR 9.5 Thm 4, Liu, UNVERIFIED locators) and
whose archimedean metric of `η₀` is the Gram determinant `hypVol 2` (AN6: Riemann's bilinear
relations), with `hmin` (H5), has `stableFaltingsHeight = faltingsHeightGood E`. -/

section AT2

open Polynomial

/-- (copied from pkg-I5) A genus-2 Weierstrass equation `y² + h(x) y = f(x)`. -/
structure Genus2Eq (R : Type*) [CommRing R] where
  f : R[X]
  h : R[X]
  deg_f : f.natDegree ≤ 6
  deg_h : h.natDegree ≤ 3

namespace Genus2Eq

variable {R : Type*} [CommRing R]

/-- (copied) `P = 4f + h²`. -/
noncomputable def P (E : Genus2Eq R) : R[X] := 4 * E.f + E.h ^ 2

/-- (copied) The discriminant of `P` as a binary sextic. -/
noncomputable def binDisc (E : Genus2Eq R) : R :=
  if E.P.natDegree = 6 then E.P.discr
  else if E.P.natDegree = 5 then E.P.leadingCoeff ^ 2 * E.P.discr else 0

/-- (copied) Smooth Weierstrass model over `𝓞 K`: `disc₆(P) = 2¹²·u`, `u` a unit. -/
def Good {K : Type*} [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)) : Prop :=
  ∃ u : (𝓞 K)ˣ, E.binDisc = 2 ^ 12 * (u : 𝓞 K)

end Genus2Eq

/-- (copied from pkg-I5) `h_F(Jac C) = −(2[K:ℚ])⁻¹ ∑_σ log ‖ω₀∧ω₁‖²_σ` for a good equation. -/
noncomputable def faltingsHeightGood {K : Type*} [Field K] [NumberField K]
    (E : Genus2Eq (𝓞 K)) : ℝ :=
  -(∑ σ : K →+* ℂ, Real.log (hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ))) /
    (2 * Module.finrank ℚ K)

/-- **AT2 bridge at the level of Hodge data (proved).** -/
theorem HodgeData.modelHeight_eq_faltingsHeightGood {K : Type*} [Field K] [NumberField K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (E : Genus2Eq (𝓞 K)) (D : HodgeData K 2 V) {η₀ : V}
    (hspan : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (hgram : ∀ σ, torusMetricSq (D.periods σ) (D.coeff σ η₀) =
      hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ)) :
    D.modelHeight = faltingsHeightGood E := by
  rw [D.modelHeight_of_span hspan hη₀, faltingsHeightGood]
  simp only [hgram]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

/-- **AT2, conditional form over the general definition (proved).** As in AT1, `hmin` is the `≥`
half of the conclusion (the output H5 must supply); the content is
`HodgeData.modelHeight_eq_faltingsHeightGood`. -/
theorem stableFaltingsHeight_eq_faltingsHeightGood {K : Type} [Field K] [NumberField K]
    (E : Genus2Eq (𝓞 K)) (A : AbVar K) (M : MetrizedModel A K 2) {η₀ : M.model.hodgeSpace 2}
    (hspan : M.hodge.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (hgram : ∀ σ, torusMetricSq (M.hodge.periods σ) (M.hodge.coeff σ η₀) =
      hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ))
    (hmin : ∀ (F : FinExt K) (g : ℕ) (M' : MetrizedModel A F.L g),
      faltingsHeightGood E ≤ M'.hodge.modelHeight) :
    stableFaltingsHeight A = (faltingsHeightGood E : EReal) := by
  have hM := HodgeData.modelHeight_eq_faltingsHeightGood E M.hodge hspan hη₀ hgram
  refine le_antisymm ?_ ?_
  · exact (stableFaltingsHeight_le A M).trans_eq (by rw [hM])
  · exact le_stableFaltingsHeight A fun F g M' => EReal.coe_le_coe_iff.mpr (hmin F g M')

end AT2


end ModelsSec

end ZInQ.DefFaltings
