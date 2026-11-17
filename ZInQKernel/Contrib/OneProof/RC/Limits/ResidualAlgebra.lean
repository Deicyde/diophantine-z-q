import Mathlib

/-!
# Residual algebra for the transfer to the original support (Lane RC6-limits)

This file formalizes the algebraic inputs of the last two paragraphs of the proof of
Lemma `ex:limits-residual-bound` ("The reduced generic residual rank bound", tex 4612-4647),
together with the local free model (4.4) of the actual support comparisons (tex 3471-3481).

* Part 1 (tex 4623-4626): `((1+t)^e - 1)/t` and `((1+t)^{-e} - 1)/t` are units of `𝔽₂[[t]]`
  for odd `e`; hence `(1+t)^{±e} - 1` becomes a unit after inverting `t`, e.g. in `𝔽₂((t))`.
* Part 2 (tex 4618-4627 with (4.4)): the reduced local model at an oriented active place has
  `C = 0`, `A = D = ((1+t)^e - 1) I₂`; the full, unramified and singular comparison blocks are
  contractible after inverting `t`, with explicit contracting homotopies.
* Part 3 (tex 4633-4640): for a field `F` of characteristic two and a group `G` of exponent
  dividing two, every element of the augmentation ideal of `F[G]` squares to zero, the
  augmentation ideal is nilpotent when `G` is finite, and `F[G]` is local with maximal ideal the
  augmentation ideal; in particular for `F = 𝔽₂((t))`.
* Part 4 (tex 4637-4640): one-step cancellation of a unit entry (Gaussian elimination) with its
  explicit homotopy equivalence data, the residue computation for minimal complexes, and the
  existence of minimal models stated as a `GLUE` proposition.

The manuscript's `t` is Mathlib's `PowerSeries.X`; `𝔽₂[[t]]` is `PowerSeries (ZMod 2)` and
`𝔽₂((t))` is `LaurentSeries (ZMod 2)`.
-/

namespace ZInQ.Manuscript.RC.Limits

open PowerSeries

/-! ## Part 1: the units `((1+t)^{±e} - 1)/t` of `𝔽₂[[t]]` -/

section Units

variable (R : Type*) [CommRing R]

/-- The quotient `((1+t)^e - 1)/t`, written as the geometric sum `∑_{i<e} (1+t)^i`.

Tex 4624 ("`((1+t)^e-1)/t`"). Kind: definition (used by the `PROVED` statements below). -/
noncomputable def geomFactor (e : ℕ) : R⟦X⟧ :=
  ∑ i ∈ Finset.range e, (1 + X) ^ i

/-- `(1+t)^e - 1 = t · ((1+t)^e - 1)/t`, with the quotient given by `geomFactor`.

Tex 4624. Kind: `PROVED`. -/
theorem one_add_X_pow_sub_one (e : ℕ) :
    ((1 : R⟦X⟧) + X) ^ e - 1 = X * geomFactor R e := by
  rw [geomFactor, ← mul_geom_sum, add_sub_cancel_left]

/-- The constant coefficient of `((1+t)^e - 1)/t` is `e`.

Tex 4624. Kind: `PROVED`. -/
theorem constantCoeff_geomFactor (e : ℕ) :
    constantCoeff (geomFactor R e) = (e : R) := by
  simp [geomFactor, map_sum]

/-- `((1+t)^e - 1)/t` is a unit of `R[[t]]` exactly when `e` is a unit of `R`.

Tex 4624. Kind: `PROVED`. DEPARTURE: stated over an arbitrary commutative ring `R`; the
manuscript's case is `R = 𝔽₂` (see `isUnit_geomFactor_of_odd`). -/
theorem isUnit_geomFactor_iff (e : ℕ) :
    IsUnit (geomFactor R e) ↔ IsUnit (e : R) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_geomFactor]

/-- `1 + t` is a unit of `R[[t]]`.

Tex 4623 (the exponent `-e` at the conjugate place needs `(1+t)^{-1}`). Kind: `PROVED`. -/
theorem isUnit_one_add_X : IsUnit ((1 : R⟦X⟧) + X) := by
  rw [isUnit_iff_constantCoeff]
  simp

/-- The unit `1 + t` of `R[[t]]`; its integer powers are the `(1+t)^{e}`, `e ∈ ℤ`.

Tex 4623. Kind: definition. -/
noncomputable def onePlusX : R⟦X⟧ˣ :=
  (isUnit_one_add_X R).unit

@[simp]
theorem val_onePlusX : ((onePlusX R : R⟦X⟧ˣ) : R⟦X⟧) = 1 + X :=
  IsUnit.unit_spec _

/-- `(1+t)^{-e} - 1 = t · (-(1+t)^{-e} · ((1+t)^e - 1)/t)`.

Tex 4623-4624 ("at the conjugate place the exponent is `-e`"). Kind: `PROVED`. -/
theorem onePlusX_inv_pow_sub_one (e : ℕ) :
    ((((onePlusX R)⁻¹ ^ e : R⟦X⟧ˣ)) : R⟦X⟧) - 1 =
      X * (-(((onePlusX R)⁻¹ ^ e : R⟦X⟧ˣ) : R⟦X⟧) * geomFactor R e) := by
  set w : R⟦X⟧ := (((onePlusX R)⁻¹ ^ e : R⟦X⟧ˣ) : R⟦X⟧) with hw_def
  have hw : w * ((1 : R⟦X⟧) + X) ^ e = 1 := by
    rw [hw_def, ← val_onePlusX R, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow,
      inv_mul_cancel, Units.val_one]
  calc w - 1 = w - w * ((1 : R⟦X⟧) + X) ^ e := by rw [hw]
    _ = -(w * (((1 : R⟦X⟧) + X) ^ e - 1)) := by ring
    _ = X * (-w * geomFactor R e) := by rw [one_add_X_pow_sub_one]; ring

end Units

section UnitsF2

/-- For odd `e`, `((1+t)^e - 1)/t` is a unit of `𝔽₂[[t]]`.

Tex 4624-4625 ("Both `((1+t)^e-1)/t` and ... are units of `𝔽₂[[t]]`"). Kind: `PROVED`. -/
theorem isUnit_geomFactor_of_odd {e : ℕ} (he : Odd e) : IsUnit (geomFactor (ZMod 2) e) := by
  rw [isUnit_geomFactor_iff, ZMod.natCast_eq_one_iff_odd.mpr he]
  exact isUnit_one

/-- For odd `e`: `(1+t)^e - 1 = t · u` with `u` a unit of `𝔽₂[[t]]`.

Tex 4621-4625 ("`((1+t)^e-1)/t` is a unit of `𝔽₂[[t]]`", `e` odd). Kind: `PROVED`. -/
theorem one_add_X_pow_sub_one_eq_X_mul_unit {e : ℕ} (he : Odd e) :
    ∃ u : (ZMod 2)⟦X⟧, IsUnit u ∧ ((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1 = X * u :=
  ⟨geomFactor (ZMod 2) e, isUnit_geomFactor_of_odd he, one_add_X_pow_sub_one _ e⟩

/-- For odd `e`: `((1+t)^{-1})^e - 1 = t · u'` with `u'` a unit of `𝔽₂[[t]]`.

Tex 4623-4625 ("at the conjugate place the exponent is `-e`"; "`((1+t)^{-e}-1)/t` is a unit
of `𝔽₂[[t]]`"). Kind: `PROVED`. -/
theorem onePlusX_inv_pow_sub_one_eq_X_mul_unit {e : ℕ} (he : Odd e) :
    ∃ u : (ZMod 2)⟦X⟧, IsUnit u ∧
      ((((onePlusX (ZMod 2))⁻¹ ^ e : (ZMod 2)⟦X⟧ˣ)) : (ZMod 2)⟦X⟧) - 1 = X * u :=
  ⟨_, (Units.isUnit _).neg.mul (isUnit_geomFactor_of_odd he), onePlusX_inv_pow_sub_one _ e⟩

/-- For odd `e : ℤ`: `(1+t)^e - 1 = t · u` with `u` a unit of `𝔽₂[[t]]`, where `(1+t)^e` is the
`e`-th power of the unit `1 + t`. This covers both the oriented place (exponent `e > 0`) and the
conjugate place (exponent `-e`).

Tex 4621-4625. Kind: `PROVED`. -/
theorem onePlusX_zpow_sub_one_eq_X_mul_unit {e : ℤ} (he : Odd e) :
    ∃ u : (ZMod 2)⟦X⟧, IsUnit u ∧
      (((onePlusX (ZMod 2)) ^ e : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) - 1 = X * u := by
  rcases e with n | n
  · have hn : Odd n := by
      have := Int.natAbs_odd.mpr he
      simpa using this
    obtain ⟨u, hu, h⟩ := one_add_X_pow_sub_one_eq_X_mul_unit hn
    refine ⟨u, hu, ?_⟩
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, val_onePlusX, h]
  · have hn : Odd (n + 1) := by
      have := Int.natAbs_odd.mpr he
      simpa [Int.natAbs_negSucc] using this
    obtain ⟨u, hu, h⟩ := onePlusX_inv_pow_sub_one_eq_X_mul_unit hn
    refine ⟨u, hu, ?_⟩
    rw [zpow_negSucc, ← inv_pow, h]

end UnitsF2

section AfterInvertingT

variable {B : Type*} [CommRing B] [Algebra (ZMod 2)⟦X⟧ B]

/-- After inverting `t`: in a `𝔽₂[[t]]`-algebra `B` in which `t` maps to a unit, the image of
`(1+t)^e - 1` (`e` odd) is a unit.

Tex 4625-4626 ("... become contractible after inverting `t`"). Kind: `PROVED`. -/
theorem isUnit_algebraMap_one_add_X_pow_sub_one (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X))
    {e : ℕ} (he : Odd e) :
    IsUnit (algebraMap (ZMod 2)⟦X⟧ B (((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1)) := by
  obtain ⟨u, hu, h⟩ := one_add_X_pow_sub_one_eq_X_mul_unit he
  rw [h, map_mul]
  exact hX.mul (hu.map _)

/-- After inverting `t`: the image of `(1+t)^e - 1` is a unit for every odd `e : ℤ` (so for the
exponents `e` and `-e` of the two places above an active prime).

Tex 4623-4626. Kind: `PROVED`. -/
theorem isUnit_algebraMap_onePlusX_zpow_sub_one (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X))
    {e : ℤ} (he : Odd e) :
    IsUnit (algebraMap (ZMod 2)⟦X⟧ B
      ((((onePlusX (ZMod 2)) ^ e : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) - 1)) := by
  obtain ⟨u, hu, h⟩ := onePlusX_zpow_sub_one_eq_X_mul_unit he
  rw [h, map_mul]
  exact hX.mul (hu.map _)

end AfterInvertingT

section LaurentInstance

/-- `t` is a unit of `𝔽₂((t))`: inverting `t` in `𝔽₂[[t]]` is realized by `𝔽₂((t))`.

Tex 4626 ("after inverting `t`"). Kind: `PROVED`. -/
theorem isUnit_algebraMap_X_laurentSeries :
    IsUnit (algebraMap (ZMod 2)⟦X⟧ (LaurentSeries (ZMod 2)) X) := by
  rw [isUnit_iff_ne_zero, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X]
  exact HahnSeries.single_ne_zero one_ne_zero

/-- In `𝔽₂((t))`, `(1+t)^e - 1` is a unit for odd `e`.

Tex 4623-4626. Kind: `PROVED`. -/
theorem isUnit_laurentSeries_one_add_X_pow_sub_one {e : ℕ} (he : Odd e) :
    IsUnit (algebraMap (ZMod 2)⟦X⟧ (LaurentSeries (ZMod 2)) (((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1)) :=
  isUnit_algebraMap_one_add_X_pow_sub_one isUnit_algebraMap_X_laurentSeries he

/-- In `𝔽₂((t))`, `(1+t)^e - 1` is a unit for every odd `e : ℤ`.

Tex 4623-4626. Kind: `PROVED`. -/
theorem isUnit_laurentSeries_onePlusX_zpow_sub_one {e : ℤ} (he : Odd e) :
    IsUnit (algebraMap (ZMod 2)⟦X⟧ (LaurentSeries (ZMod 2))
      ((((onePlusX (ZMod 2)) ^ e : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) - 1)) :=
  isUnit_algebraMap_onePlusX_zpow_sub_one isUnit_algebraMap_X_laurentSeries he

end LaurentInstance

/-! ## Part 2: the reduced active-place model and its contractions -/

section Contractions

variable {B : Type*} [CommRing B]
variable {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module B V₀] [AddCommGroup V₁] [Module B V₁]
  [AddCommGroup V₂] [Module B V₂]

/-- A contracting homotopy of the two-term complex `[V₀ --d--> V₁]` (degrees zero and one): a map
`s : V₁ → V₀` with `s ∘ d = 1` (degree zero) and `d ∘ s = 1` (degree one).

Tex 3479-3481 and 4625-4626 (the unramified block `[Φ-1]` and the singular quotient block
`[Φ-q]`). Kind: definition. -/
structure TwoTermContraction (d : V₀ →ₗ[B] V₁) where
  /-- The contracting homotopy `s : V₁ → V₀`. -/
  s : V₁ →ₗ[B] V₀
  /-- Degree zero: `s ∘ d = 1`. -/
  s_comp_d : s ∘ₗ d = LinearMap.id
  /-- Degree one: `d ∘ s = 1`. -/
  d_comp_s : d ∘ₗ s = LinearMap.id

/-- A contracting homotopy of the three-term complex `V₀ --d⁰--> V₁ --d¹--> V₂` (degrees zero,
one and two): maps `s¹ : V₁ → V₀` and `s² : V₂ → V₁` with `s¹ ∘ d⁰ = 1`,
`d⁰ ∘ s¹ + s² ∘ d¹ = 1` and `d¹ ∘ s² = 1`.

Tex 3471-3481 and 4625-4626 (the full comparison block). Kind: definition. -/
structure ThreeTermContraction (d0 : V₀ →ₗ[B] V₁) (d1 : V₁ →ₗ[B] V₂) where
  /-- The homotopy `s¹ : V₁ → V₀`. -/
  s1 : V₁ →ₗ[B] V₀
  /-- The homotopy `s² : V₂ → V₁`. -/
  s2 : V₂ →ₗ[B] V₁
  /-- Degree zero: `s¹ ∘ d⁰ = 1`. -/
  s1_comp_d0 : s1 ∘ₗ d0 = LinearMap.id
  /-- Degree one: `d⁰ ∘ s¹ + s² ∘ d¹ = 1`. -/
  homotopy_one : d0 ∘ₗ s1 + s2 ∘ₗ d1 = LinearMap.id
  /-- Degree two: `d¹ ∘ s² = 1`. -/
  d1_comp_s2 : d1 ∘ₗ s2 = LinearMap.id

/-- Transport a two-term contraction along an equality of differentials (the homotopy is
unchanged).

Kind: `PROVED` (bookkeeping). -/
def TwoTermContraction.ofEq {d d' : V₀ →ₗ[B] V₁} (h : d = d') (c : TwoTermContraction d) :
    TwoTermContraction d' where
  s := c.s
  s_comp_d := h ▸ c.s_comp_d
  d_comp_s := h ▸ c.d_comp_s

/-- A two-term complex `[V₀ --d--> V₁]` with `d` an isomorphism is contractible, with
`s = d⁻¹`.

Tex 3479-3481, 4625-4626. Kind: `PROVED`. -/
def TwoTermContraction.ofLinearEquiv (d : V₀ ≃ₗ[B] V₁) :
    TwoTermContraction (d : V₀ →ₗ[B] V₁) where
  s := d.symm
  s_comp_d := LinearMap.ext fun v => d.symm_apply_apply v
  d_comp_s := LinearMap.ext fun v => d.apply_symm_apply v

/-- The two-term complex `[V --A--> V]` with `A` invertible in `End_B(V)` is contractible, with
`s = A⁻¹`.

Tex 3479-3481, 4625-4626. Kind: `PROVED`. -/
noncomputable def TwoTermContraction.ofIsUnit {V : Type*} [AddCommGroup V] [Module B V]
    {A : V →ₗ[B] V} (hA : IsUnit A) : TwoTermContraction A where
  s := ((hA.unit⁻¹ : (Module.End B V)ˣ) : Module.End B V)
  s_comp_d := by
    rw [← Module.End.mul_eq_comp, IsUnit.val_inv_mul, Module.End.one_eq_id]
  d_comp_s := by
    rw [← Module.End.mul_eq_comp, IsUnit.mul_val_inv, Module.End.one_eq_id]

/-- The two-term complex `[V --c--> V]` (multiplication by a unit `c` of `B`) is contractible,
with the explicit homotopy `s = c⁻¹`.

Tex 4621, 4625-4626 (`A = D = ((1+t)^e-1) I₂` after inverting `t`). Kind: `PROVED`. -/
def TwoTermContraction.ofUnitSMul {V : Type*} [AddCommGroup V] [Module B V] (c : Bˣ) :
    TwoTermContraction ((c : B) • LinearMap.id : V →ₗ[B] V) where
  s := ((c⁻¹ : Bˣ) : B) • LinearMap.id
  s_comp_d := LinearMap.ext fun v => by
    simp [smul_smul]
  d_comp_s := LinearMap.ext fun v => by
    simp [smul_smul]

@[simp]
theorem TwoTermContraction.ofUnitSMul_s_apply {V : Type*} [AddCommGroup V] [Module B V] (c : Bˣ)
    (v : V) : (TwoTermContraction.ofUnitSMul c).s v = ((c⁻¹ : Bˣ) : B) • v :=
  rfl

/-- A contraction forces the complex condition: `d¹ ∘ d⁰ = 0`.

Kind: `PROVED`. -/
theorem ThreeTermContraction.d1_comp_d0 {d0 : V₀ →ₗ[B] V₁} {d1 : V₁ →ₗ[B] V₂}
    (h : ThreeTermContraction d0 d1) : d1 ∘ₗ d0 = 0 := by
  have key : d1 ∘ₗ d0 = d1 ∘ₗ d0 + d1 ∘ₗ d0 := by
    calc d1 ∘ₗ d0 = d1 ∘ₗ (d0 ∘ₗ h.s1 + h.s2 ∘ₗ d1) ∘ₗ d0 := by
          rw [h.homotopy_one]; rfl
      _ = (d1 ∘ₗ d0) ∘ₗ (h.s1 ∘ₗ d0) + (d1 ∘ₗ h.s2) ∘ₗ (d1 ∘ₗ d0) := by
          rw [LinearMap.add_comp, LinearMap.comp_add]; rfl
      _ = d1 ∘ₗ d0 + d1 ∘ₗ d0 := by
          rw [h.s1_comp_d0, h.d1_comp_s2]; rfl
  exact left_eq_add.mp key

end Contractions

section MathlibBridge

open CategoryTheory

universe v

variable {B : Type*} [CommRing B]
variable {V₀ V₁ V₂ : Type v} [AddCommGroup V₀] [Module B V₀] [AddCommGroup V₁] [Module B V₁]
  [AddCommGroup V₂] [Module B V₂]

/-- The short complex `V₀ --d⁰--> V₁ --d¹--> V₂` in `ModuleCat B` attached to a three-term
contraction (the contraction forces `d¹ ∘ d⁰ = 0`).

Kind: definition (bridge to Mathlib's `ShortComplex`). -/
def ThreeTermContraction.shortComplex {d0 : V₀ →ₗ[B] V₁} {d1 : V₁ →ₗ[B] V₂}
    (c : ThreeTermContraction d0 d1) : ShortComplex (ModuleCat.{v} B) :=
  ShortComplex.mk (ModuleCat.ofHom d0) (ModuleCat.ofHom d1) (by
    rw [← ModuleCat.ofHom_comp, c.d1_comp_d0]
    rfl)

/-- A three-term contraction is exactly a splitting, in Mathlib's sense, of the short complex
`V₀ → V₁ → V₂` (retraction `r = s¹`, section `s = s²`). In particular the complex
`0 → V₀ → V₁ → V₂ → 0` is split exact, i.e. contractible.

Kind: `PROVED` (bridge to Mathlib's `ShortComplex.Splitting`). -/
def ThreeTermContraction.toSplitting {d0 : V₀ →ₗ[B] V₁} {d1 : V₁ →ₗ[B] V₂}
    (c : ThreeTermContraction d0 d1) : c.shortComplex.Splitting where
  r := ModuleCat.ofHom c.s1
  s := ModuleCat.ofHom c.s2
  f_r := by
    apply ModuleCat.hom_ext
    exact c.s1_comp_d0
  s_g := by
    apply ModuleCat.hom_ext
    exact c.d1_comp_s2
  id := by
    apply ModuleCat.hom_ext
    exact c.homotopy_one

/-- A three-term contraction makes `0 → V₀ → V₁ → V₂ → 0` short exact.

Kind: `PROVED` (via Mathlib's `ShortComplex.Splitting.shortExact`). -/
theorem ThreeTermContraction.shortExact {d0 : V₀ →ₗ[B] V₁} {d1 : V₁ →ₗ[B] V₂}
    (c : ThreeTermContraction d0 d1) : c.shortComplex.ShortExact :=
  c.toSplitting.shortExact

/-- A two-term contraction is an isomorphism `V₀ ≃ V₁` with inverse the homotopy.

Kind: `PROVED`. -/
def TwoTermContraction.toLinearEquiv {d : V₀ →ₗ[B] V₁} (c : TwoTermContraction d) :
    V₀ ≃ₗ[B] V₁ :=
  LinearEquiv.ofLinearMap d c.s c.d_comp_s c.s_comp_d

end MathlibBridge

section LocalModel

variable {B : Type*} [CommRing B] {V : Type*} [AddCommGroup V] [Module B V]

/-- The local free model (4.4): `d⁰(v) = (Av, Cv)`.

Tex 3473. Kind: definition. -/
def localModel_d0 (A C : V →ₗ[B] V) : V →ₗ[B] V × V :=
  A.prod C

/-- The local free model (4.4): `d¹(v,w) = -Cv + Dw`.

Tex 3473. Kind: definition. -/
def localModel_d1 (C D : V →ₗ[B] V) : V × V →ₗ[B] V :=
  (-C).coprod D

@[simp]
theorem localModel_d0_apply (A C : V →ₗ[B] V) (v : V) : localModel_d0 A C v = (A v, C v) :=
  rfl

@[simp]
theorem localModel_d1_apply (C D : V →ₗ[B] V) (p : V × V) :
    localModel_d1 C D p = -C p.1 + D p.2 :=
  rfl

/-- (4.4): the relation `DC = CA` makes `d⁰, d¹` a complex, `d¹ ∘ d⁰ = 0`.

Tex 3473-3477. Kind: `PROVED`. -/
theorem localModel_d1_comp_d0 {A C D : V →ₗ[B] V} (h : D ∘ₗ C = C ∘ₗ A) :
    localModel_d1 C D ∘ₗ localModel_d0 A C = 0 := by
  refine LinearMap.ext fun v => ?_
  have hv : D (C v) = C (A v) := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply, localModel_d0_apply, localModel_d1_apply, hv,
    LinearMap.zero_apply, neg_add_cancel]

/-- The explicit homotopy `s¹(v,w) = A⁻¹ v` (here `sA` plays the role of `A⁻¹`).

Tex 4618-4627. Kind: definition. -/
def localModel_s1 (sA : V →ₗ[B] V) : V × V →ₗ[B] V :=
  sA ∘ₗ LinearMap.fst B V V

/-- The explicit homotopy `s²(w) = (0, D⁻¹ w)` (here `sD` plays the role of `D⁻¹`).

Tex 4618-4627. Kind: definition. -/
def localModel_s2 (sD : V →ₗ[B] V) : V →ₗ[B] V × V :=
  LinearMap.inr B V V ∘ₗ sD

@[simp]
theorem localModel_s1_apply (sA : V →ₗ[B] V) (p : V × V) : localModel_s1 sA p = sA p.1 :=
  rfl

@[simp]
theorem localModel_s2_apply (sD : V →ₗ[B] V) (w : V) : localModel_s2 sD w = (0, sD w) :=
  rfl

/-- When `C = 0` the local model (4.4) is the direct sum of the unramified block `[V --A--> V]`
in degrees zero and one and the singular quotient block `[V --D--> V]` in degrees one and two,
and contractions of the two blocks assemble to the explicit contraction
`s¹(v,w) = A⁻¹ v`, `s²(w) = (0, D⁻¹ w)` of the full block.

Tex 3479-3481, 4618-4627 ("the full, unramified and singular comparison blocks all become
contractible"). Kind: `PROVED`. -/
def localModel_contraction {A C D : V →ₗ[B] V} (hC : C = 0) (hA : TwoTermContraction A)
    (hD : TwoTermContraction D) :
    ThreeTermContraction (localModel_d0 A C) (localModel_d1 C D) where
  s1 := localModel_s1 hA.s
  s2 := localModel_s2 hD.s
  s1_comp_d0 := LinearMap.ext fun v => by
    subst hC
    simpa using LinearMap.congr_fun hA.s_comp_d v
  homotopy_one := LinearMap.ext fun p => by
    subst hC
    have h1 : A (hA.s p.1) = p.1 := by simpa using LinearMap.congr_fun hA.d_comp_s p.1
    have h2 : hD.s (D p.2) = p.2 := by simpa using LinearMap.congr_fun hD.s_comp_d p.2
    ext
    · simp [h1]
    · simp [h2]
  d1_comp_s2 := LinearMap.ext fun w => by
    subst hC
    simpa using LinearMap.congr_fun hD.d_comp_s w

@[simp]
theorem localModel_contraction_s1_apply {A C D : V →ₗ[B] V} (hC : C = 0)
    (hA : TwoTermContraction A) (hD : TwoTermContraction D) (p : V × V) :
    (localModel_contraction hC hA hD).s1 p = hA.s p.1 :=
  rfl

@[simp]
theorem localModel_contraction_s2_apply {A C D : V →ₗ[B] V} (hC : C = 0)
    (hA : TwoTermContraction A) (hD : TwoTermContraction D) (w : V) :
    (localModel_contraction hC hA hD).s2 w = (0, hD.s w) :=
  rfl

/-- The four identities for the explicit homotopies `s¹(v,w) = A⁻¹ v`, `s²(w) = (0, D⁻¹ w)` of the
local model (4.4) with `C = 0`, `A`, `D` invertible (inverses `Ainv`, `Dinv`):
`s¹ ∘ d⁰ = 1`, `d⁰ ∘ s¹ + s² ∘ d¹ = 1`, `d¹ ∘ s² = 1`, and `d¹ ∘ d⁰ = 0`.

Tex 4618-4627 with (4.4) at tex 3471-3481. Kind: `PROVED`. -/
theorem localModel_homotopy_identities {A D Ainv Dinv : V →ₗ[B] V}
    (hA₁ : Ainv ∘ₗ A = LinearMap.id) (hA₂ : A ∘ₗ Ainv = LinearMap.id)
    (hD₁ : Dinv ∘ₗ D = LinearMap.id) (hD₂ : D ∘ₗ Dinv = LinearMap.id) :
    localModel_s1 Ainv ∘ₗ localModel_d0 A 0 = LinearMap.id ∧
      localModel_d0 A 0 ∘ₗ localModel_s1 Ainv + localModel_s2 Dinv ∘ₗ localModel_d1 0 D =
        LinearMap.id ∧
      localModel_d1 0 D ∘ₗ localModel_s2 Dinv = LinearMap.id ∧
      localModel_d1 0 D ∘ₗ localModel_d0 A 0 = 0 :=
  let c := localModel_contraction rfl (⟨Ainv, hA₁, hA₂⟩ : TwoTermContraction A)
    (⟨Dinv, hD₁, hD₂⟩ : TwoTermContraction D)
  ⟨c.s1_comp_d0, c.homotopy_one, c.d1_comp_s2, c.d1_comp_d0⟩

/-- With `C = 0` and `A`, `D` invertible, the local model (4.4) is a contractible complex:
`d¹ ∘ d⁰ = 0` and there is an explicit contraction.

Tex 4618-4627. Kind: `PROVED`. -/
theorem localModel_contractible {A C D : V →ₗ[B] V} (hC : C = 0) (hA : IsUnit A)
    (hD : IsUnit D) :
    localModel_d1 C D ∘ₗ localModel_d0 A C = 0 ∧
      Nonempty (ThreeTermContraction (localModel_d0 A C) (localModel_d1 C D)) :=
  ⟨localModel_d1_comp_d0 (by subst hC; simp),
    ⟨localModel_contraction hC (.ofIsUnit hA) (.ofIsUnit hD)⟩⟩

/-- The scalar model: `A = D = c · id` for a unit `c` of `B`, `C = 0`; explicit contraction
`s¹(v,w) = c⁻¹ v`, `s²(w) = (0, c⁻¹ w)`.

Tex 4618-4627 ("`C=0, A=D=((1+t)^e-1)I₂`", after inverting `t`). Kind: `PROVED`. -/
def scalarModelContraction (c : Bˣ) :
    ThreeTermContraction (localModel_d0 ((c : B) • LinearMap.id : V →ₗ[B] V) 0)
      (localModel_d1 0 ((c : B) • LinearMap.id : V →ₗ[B] V)) :=
  localModel_contraction rfl (.ofUnitSMul c) (.ofUnitSMul c)

end LocalModel

section Reduction

/-- The norm element of (4.4): `N_q(g) = (q+1)/2 + ((q-1)/2) g` for `g` in a ring `E`
(natural-number division, exact for odd `q`).

Tex 3477. Kind: definition. -/
def normQ {E : Type*} [Ring E] (q : ℕ) (g : E) : E :=
  (((q + 1) / 2 : ℕ) : E) + (((q - 1) / 2 : ℕ) : E) * g

/-- The block `A = Φ - 1` of (4.4).

Tex 3474. Kind: definition. -/
def model_A {E : Type*} [Ring E] (Φ : E) : E :=
  Φ - 1

/-- The block `C = g - 1` of (4.4).

Tex 3474. Kind: definition. -/
def model_C {E : Type*} [Ring E] (g : E) : E :=
  g - 1

/-- The block `D = Φ - N_q(g)` of (4.4).

Tex 3474. Kind: definition. -/
def model_D {E : Type*} [Ring E] (q : ℕ) (Φ g : E) : E :=
  Φ - normQ q g

/-- At augmentation `g = 1`: `N_q(1) = q` for odd `q`.

Tex 3477-3481 ("At augmentation `g=1`, ... the singular quotient `[Φ-q]`"). Kind: `PROVED`. -/
theorem normQ_one {E : Type*} [Ring E] {q : ℕ} (hq : Odd q) : normQ q (1 : E) = q := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [normQ, h1, h2, mul_one, ← Nat.cast_add]
  exact congrArg _ (by omega)

/-- In characteristic two an odd `q` is `1`.

Tex 4613-4621 (reduction modulo two). Kind: `PROVED`. -/
theorem natCast_eq_one_of_two_eq_zero {E : Type*} [Ring E] (h2 : (2 : E) = 0) {q : ℕ}
    (hq : Odd q) : (q : E) = 1 := by
  obtain ⟨k, rfl⟩ := hq
  push_cast
  rw [h2, zero_mul, zero_add]

/-- In characteristic two, at augmentation `g = 1` and for odd `q`: `C = g - 1 = 0` and
`D = Φ - N_q(g) = Φ - q = Φ - 1 = A`.

Tex 3473-3481, 4619-4621. Kind: `PROVED`. -/
theorem model_C_one_and_model_D_one_eq_model_A {E : Type*} [Ring E] (h2 : (2 : E) = 0) (Φ : E)
    {q : ℕ} (hq : Odd q) : model_C (1 : E) = 0 ∧ model_D q Φ 1 = model_A Φ := by
  refine ⟨sub_self 1, ?_⟩
  rw [model_D, model_A, normQ_one hq, natCast_eq_one_of_two_eq_zero h2 hq]

/-- `2 = 0` passes to algebras.

Kind: `PROVED` (bookkeeping). -/
theorem two_eq_zero_of_algebra {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
    (h : (2 : R) = 0) : (2 : E) = 0 := by
  rw [← map_ofNat (algebraMap R E) 2, h, map_zero]

/-- `2 = 0` in `𝔽₂[[t]]`.

Kind: `PROVED` (bookkeeping). -/
theorem two_eq_zero_powerSeries : (2 : (ZMod 2)⟦X⟧) = 0 :=
  two_eq_zero_of_algebra (R := ZMod 2) (by decide)

variable (B : Type*) [CommRing B] [Algebra (ZMod 2)⟦X⟧ B]

/-- The scalar `(1+t)^e - 1` in a `𝔽₂[[t]]`-algebra `B`, for `e : ℤ` (the exponent is `e` at an
oriented active place and `-e` at the conjugate place).

Tex 4621-4623. Kind: definition. -/
noncomputable def activeScalar (e : ℤ) : B :=
  algebraMap (ZMod 2)⟦X⟧ B ((((onePlusX (ZMod 2)) ^ e : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) - 1)

/-- The reduced Frobenius matrix `Φ = (1+t)^e I₂` over `B`.

Tex 4619-4623. Kind: definition. -/
noncomputable def activePhi (e : ℤ) : Matrix (Fin 2) (Fin 2) B :=
  algebraMap (ZMod 2)⟦X⟧ B (((onePlusX (ZMod 2)) ^ e : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) • 1

/-- For a natural exponent, `activePhi` is literally `(1+t)^e I₂`.

Kind: `PROVED` (bookkeeping). -/
theorem activePhi_natCast (e : ℕ) :
    activePhi B e = algebraMap (ZMod 2)⟦X⟧ B (((1 : (ZMod 2)⟦X⟧) + X) ^ e) • 1 := by
  rw [activePhi, zpow_natCast, Units.val_pow_eq_pow_val, val_onePlusX]

theorem activeScalar_natCast (e : ℕ) :
    activeScalar B e = algebraMap (ZMod 2)⟦X⟧ B (((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1) := by
  rw [activeScalar, zpow_natCast, Units.val_pow_eq_pow_val, val_onePlusX]

/-- The reduction of (4.4) at an oriented active place: with `Φ = (1+t)^e I₂`, `g = 1` (the
coefficient system is unramified after reduction modulo two) and `q` odd,
`A = Φ - 1 = ((1+t)^e - 1) I₂`, `C = g - 1 = 0`, and `D = Φ - N_q(g) = Φ - q = A` since `q ≡ 1`
in characteristic two.

Tex 4613-4623 ("reduction of (4.4) has `C=0, A=D=((1+t)^e-1)I₂`") with tex 3473-3481.
Kind: `PROVED`. -/
theorem activePlace_reduction (e : ℤ) {q : ℕ} (hq : Odd q) :
    model_A (activePhi B e) = activeScalar B e • (1 : Matrix (Fin 2) (Fin 2) B) ∧
      model_C (1 : Matrix (Fin 2) (Fin 2) B) = 0 ∧
      model_D q (activePhi B e) 1 = activeScalar B e • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have hA : model_A (activePhi B e) = activeScalar B e • (1 : Matrix (Fin 2) (Fin 2) B) := by
    rw [model_A, activePhi, activeScalar, map_sub, map_one, sub_smul, one_smul]
  refine ⟨hA, sub_self _, ?_⟩
  have h2 : (2 : Matrix (Fin 2) (Fin 2) B) = 0 :=
    two_eq_zero_of_algebra (R := B) (two_eq_zero_of_algebra two_eq_zero_powerSeries)
  rw [model_D, normQ_one hq, natCast_eq_one_of_two_eq_zero h2 hq, ← model_A, hA]

/-- The singular quotient block at augmentation is `[Φ - q]`, which in characteristic two is
`[Φ - 1]`.

Tex 3479-3481, 4621. Kind: `PROVED`. -/
theorem activePhi_sub_natCast (e : ℤ) {q : ℕ} (hq : Odd q) :
    activePhi B e - (q : Matrix (Fin 2) (Fin 2) B) =
      activeScalar B e • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have h := (activePlace_reduction B e hq).2.2
  rwa [model_D, normQ_one hq] at h

variable {B}

/-- The unit `(1+t)^e - 1` of `B` (`e` odd, `t` invertible in `B`).

Tex 4624-4626. Kind: definition. -/
noncomputable def activeScalarUnit (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) : Bˣ :=
  (isUnit_algebraMap_onePlusX_zpow_sub_one hX he).unit

@[simp]
theorem val_activeScalarUnit (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ} (he : Odd e) :
    ((activeScalarUnit hX he : Bˣ) : B) = activeScalar B e :=
  IsUnit.unit_spec _

theorem toLin'_activeScalar_smul_one (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) :
    ((activeScalarUnit hX he : Bˣ) : B) • (LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) =
      Matrix.toLin' (activeScalar B e • (1 : Matrix (Fin 2) (Fin 2) B)) := by
  rw [map_smul, Matrix.toLin'_one, val_activeScalarUnit]

/-- The unramified block `[Φ - 1]` at an active place becomes contractible after inverting `t`,
with homotopy `s = ((1+t)^e - 1)⁻¹`.

Tex 3479-3481, 4625-4626. Kind: `PROVED`. -/
noncomputable def unramifiedBlockContraction (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) : TwoTermContraction (Matrix.toLin' (activePhi B e - 1)) :=
  TwoTermContraction.ofEq
    (by
      rw [toLin'_activeScalar_smul_one hX he, ← (activePlace_reduction B e (q := 1) odd_one).1,
        model_A])
    (TwoTermContraction.ofUnitSMul (activeScalarUnit hX he))

/-- The singular quotient block `[Φ - q]` at an active place (`q` odd) becomes contractible after
inverting `t`, with homotopy `s = ((1+t)^e - 1)⁻¹`.

Tex 3479-3481, 4625-4626. Kind: `PROVED`. -/
noncomputable def singularBlockContraction (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) {q : ℕ} (hq : Odd q) :
    TwoTermContraction (Matrix.toLin' (activePhi B e - (q : Matrix (Fin 2) (Fin 2) B))) :=
  TwoTermContraction.ofEq
    (by rw [toLin'_activeScalar_smul_one hX he, activePhi_sub_natCast B e hq])
    (TwoTermContraction.ofUnitSMul (activeScalarUnit hX he))

/-- The full comparison block at an oriented active place: the reduced local model (4.4)
with `A = Φ - 1`, `C = g - 1`, `D = Φ - N_q(g)`, `Φ = (1+t)^e I₂`, `g = 1`, `q` odd, is a
complex and becomes contractible after inverting `t`, with the explicit homotopies
`s¹(v,w) = ((1+t)^e-1)⁻¹ v` and `s²(w) = (0, ((1+t)^e-1)⁻¹ w)`
(see `activePlaceContraction_s1_apply`, `activePlaceContraction_s2_apply`).

Tex 4618-4627 with (4.4) at tex 3471-3481. Kind: `PROVED`. -/
noncomputable def activePlaceContraction (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) {q : ℕ} (hq : Odd q) :
    ThreeTermContraction
      (localModel_d0 (Matrix.toLin' (model_A (activePhi B e)))
        (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B))))
      (localModel_d1 (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B)))
        (Matrix.toLin' (model_D q (activePhi B e) 1))) :=
  localModel_contraction
    (by rw [(activePlace_reduction B e hq).2.1, map_zero])
    (TwoTermContraction.ofEq
      (by rw [toLin'_activeScalar_smul_one hX he, (activePlace_reduction B e hq).1])
      (TwoTermContraction.ofUnitSMul (activeScalarUnit hX he)))
    (TwoTermContraction.ofEq
      (by rw [toLin'_activeScalar_smul_one hX he, (activePlace_reduction B e hq).2.2])
      (TwoTermContraction.ofUnitSMul (activeScalarUnit hX he)))

@[simp]
theorem activePlaceContraction_s1_apply (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) {q : ℕ} (hq : Odd q) (p : (Fin 2 → B) × (Fin 2 → B)) :
    (activePlaceContraction hX he hq).s1 p = (((activeScalarUnit hX he)⁻¹ : Bˣ) : B) • p.1 :=
  rfl

@[simp]
theorem activePlaceContraction_s2_apply (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) {q : ℕ} (hq : Odd q) (w : Fin 2 → B) :
    (activePlaceContraction hX he hq).s2 w = (0, (((activeScalarUnit hX he)⁻¹ : Bˣ) : B) • w) :=
  rfl

/-- The reduced local model (4.4) at an active place is a complex (`d¹ ∘ d⁰ = 0`), and after
inverting `t` it is contractible; this holds at the oriented place (exponent `e`) and at the
conjugate place (exponent `-e`).

Tex 4618-4627. Kind: `PROVED`. -/
theorem activePlace_contractible (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) {q : ℕ} (hq : Odd q) :
    (∀ e' ∈ ({e, -e} : Set ℤ),
      localModel_d1 (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B)))
          (Matrix.toLin' (model_D q (activePhi B e') 1)) ∘ₗ
        localModel_d0 (Matrix.toLin' (model_A (activePhi B e')))
          (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B))) = 0 ∧
      Nonempty (ThreeTermContraction
        (localModel_d0 (Matrix.toLin' (model_A (activePhi B e')))
          (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B))))
        (localModel_d1 (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) B)))
          (Matrix.toLin' (model_D q (activePhi B e') 1))))) := by
  intro e' he'
  have hodd : Odd e' := by
    rcases he' with rfl | rfl
    · exact he
    · exact he.neg
  exact ⟨(activePlaceContraction hX hodd hq).d1_comp_d0, ⟨activePlaceContraction hX hodd hq⟩⟩

/-- The specialization requested by the reduced model: over a `𝔽₂[[t]]`-algebra `B` in which
`t` is a unit, on `V = B²`, with `A = D = ((1+t)^e - 1) · id` (`e` odd) and `C = 0`, the local model
(4.4) is contractible.

Tex 4618-4627. Kind: `PROVED`. -/
theorem reducedScalarModel_contractible (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℕ}
    (he : Odd e) :
    Nonempty (ThreeTermContraction
      (localModel_d0 (algebraMap (ZMod 2)⟦X⟧ B (((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1) •
        LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) 0)
      (localModel_d1 0 (algebraMap (ZMod 2)⟦X⟧ B (((1 : (ZMod 2)⟦X⟧) + X) ^ e - 1) •
        LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)))) := by
  obtain ⟨c, hc⟩ := isUnit_algebraMap_one_add_X_pow_sub_one hX he
  rw [← hc]
  exact ⟨scalarModelContraction c⟩

/-- The same specialization for every odd integer exponent (`e` at the oriented place, `-e` at
the conjugate place), `A = D = ((1+t)^e - 1) · id`, `C = 0`.

Tex 4618-4627. Kind: `PROVED`. -/
theorem reducedScalarModel_contractible_zpow (hX : IsUnit (algebraMap (ZMod 2)⟦X⟧ B X)) {e : ℤ}
    (he : Odd e) :
    Nonempty (ThreeTermContraction
      (localModel_d0 (activeScalar B e • LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) 0)
      (localModel_d1 0 (activeScalar B e • LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)))) := by
  rw [← val_activeScalarUnit hX he]
  exact ⟨scalarModelContraction (activeScalarUnit hX he)⟩

end Reduction

/-! ## Part 3: the group ring `F[G]` of a group of exponent two in characteristic two -/

section GroupRing

/-- A group in which every element squares to one is commutative.

Tex 4633-4636 (the binary group `G`). Kind: `PROVED`. -/
theorem mul_comm_of_mul_self_eq_one {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) :
    a * b = b * a := by
  have hinv : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

/-- The commutative group structure of a group in which every element squares to one (it
extends the given group structure, so nothing is lost by stating the results below for a
`CommGroup`).

Tex 4633-4636. Kind: `PROVED`. -/
abbrev commGroupOfMulSelfEqOne (G : Type*) [Group G] (h : ∀ g : G, g * g = 1) : CommGroup G :=
  { ‹Group G› with mul_comm := mul_comm_of_mul_self_eq_one h }

variable (F : Type*) [Field F] (G : Type*) [CommGroup G]

/-- The augmentation `ε : F[G] → F`, `∑ a_g g ↦ ∑ a_g` (the lift of the trivial character).

Tex 4635 ("augmentation `𝔽₂[G] → 𝔽₂`"). Kind: definition. -/
noncomputable def augmentation : MonoidAlgebra F G →ₐ[F] F :=
  MonoidAlgebra.lift F F G 1

@[simp]
theorem augmentation_single (g : G) (a : F) :
    augmentation F G (MonoidAlgebra.single g a) = a := by
  simp [augmentation, MonoidAlgebra.lift_single]

theorem augmentation_algebraMap (a : F) :
    augmentation F G (algebraMap F (MonoidAlgebra F G) a) = a :=
  (augmentation F G).commutes a

theorem augmentation_surjective : Function.Surjective (augmentation F G) :=
  fun a => ⟨algebraMap F _ a, augmentation_algebraMap F G a⟩

/-- Cross-check: the augmentation is Mathlib's bialgebra counit of `F[G]`.

Kind: `PROVED`. -/
theorem augmentation_eq_counitAlgHom :
    augmentation F G = Bialgebra.counitAlgHom F (MonoidAlgebra F G) := by
  ext g
  simp [augmentation, MonoidAlgebra.lift_single]

/-- `F[G]` has characteristic two when `F` does.

Kind: `PROVED`. -/
theorem charP_monoidAlgebra [CharP F 2] : CharP (MonoidAlgebra F G) 2 :=
  charP_of_injective_algebraMap (algebraMap F (MonoidAlgebra F G)).injective 2

/-- Frobenius in characteristic two: `(∑ a_g g)² = ∑ a_g² g² = (∑ a_g)² · 1` when every `g`
satisfies `g² = 1`.

Tex 4633-4637. Kind: `PROVED`. -/
theorem sq_eq_algebraMap_augmentation_sq [CharP F 2] (h : ∀ g : G, g * g = 1)
    (x : MonoidAlgebra F G) :
    x ^ 2 = algebraMap F (MonoidAlgebra F G) (augmentation F G x ^ 2) := by
  have := charP_monoidAlgebra F G
  have key : frobenius (MonoidAlgebra F G) 2 =
      (algebraMap F (MonoidAlgebra F G)).comp
        ((frobenius F 2).comp (augmentation F G).toRingHom) := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [frobenius_def, sq, MonoidAlgebra.single_mul_single]
    · intro g
      simp [frobenius_def, sq, MonoidAlgebra.single_mul_single, h]
  have hx := congrArg (fun φ : MonoidAlgebra F G →+* MonoidAlgebra F G => φ x) key
  simpa [frobenius_def] using hx

/-- Every element of the augmentation ideal squares to zero.

Tex 4636-4637 ("nilpotent augmentation ideal"). Kind: `PROVED`. -/
theorem mul_self_eq_zero_of_mem_ker_augmentation [CharP F 2] (h : ∀ g : G, g * g = 1)
    {x : MonoidAlgebra F G} (hx : x ∈ RingHom.ker (augmentation F G)) : x * x = 0 := by
  rw [← sq, sq_eq_algebraMap_augmentation_sq F G h, RingHom.mem_ker.mp hx,
    zero_pow two_ne_zero, map_zero]

/-- An element of `F[G]` is a unit exactly when its augmentation is nonzero.

Tex 4636-4637. Kind: `PROVED`. -/
theorem isUnit_iff_augmentation_ne_zero [CharP F 2] (h : ∀ g : G, g * g = 1)
    (x : MonoidAlgebra F G) : IsUnit x ↔ augmentation F G x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (augmentation F G)).ne_zero
  · intro hx
    have hn : IsNilpotent (x - algebraMap F (MonoidAlgebra F G) (augmentation F G x)) := by
      refine ⟨2, ?_⟩
      rw [sq_eq_algebraMap_augmentation_sq F G h, map_sub, augmentation_algebraMap, sub_self,
        zero_pow two_ne_zero, map_zero]
    have hu : IsUnit (algebraMap F (MonoidAlgebra F G) (augmentation F G x)) :=
      (Ne.isUnit hx).map _
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    rwa [add_sub_cancel] at this

/-- `F[G]` is a local ring.

Tex 4636-4637 ("the ring `𝔽₂((t))[G]` is local"). Kind: `PROVED`. DEPARTURE: stated for any field
`F` of characteristic two (the manuscript's case is `F = 𝔽₂((t))`, see
`isLocalRing_laurentSeries_monoidAlgebra`) and any, possibly infinite, `G` with `g² = 1`; `G` is
taken as a `CommGroup`, which is no restriction by `mul_comm_of_mul_self_eq_one` (see
`isLocalRing_monoidAlgebra_of_group` for the statement for a `Group`). -/
theorem isLocalRing_monoidAlgebra [CharP F 2] (h : ∀ g : G, g * g = 1) :
    IsLocalRing (MonoidAlgebra F G) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : augmentation F G a = 0
  · right
    rw [isUnit_iff_augmentation_ne_zero F G h, map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · left
    exact (isUnit_iff_augmentation_ne_zero F G h a).mpr ha

/-- The maximal ideal of the local ring `F[G]` is the augmentation ideal `ker ε`.

Tex 4636-4637. Kind: `PROVED`. -/
theorem maximalIdeal_eq_ker_augmentation [CharP F 2] (h : ∀ g : G, g * g = 1) :
    letI := isLocalRing_monoidAlgebra F G h
    IsLocalRing.maximalIdeal (MonoidAlgebra F G) = RingHom.ker (augmentation F G) := by
  let := isLocalRing_monoidAlgebra F G h
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_augmentation_ne_zero F G h,
    RingHom.mem_ker, not_not]

/-- For finite `G` the augmentation ideal of `F[G]` is nilpotent.

Tex 4636-4637 ("local with nilpotent augmentation ideal"). Kind: `PROVED`. The finiteness of `G`
is the manuscript's ("a finite binary group `G`", tex 2851); without it the augmentation ideal is
still nil (`mul_self_eq_zero_of_mem_ker_augmentation`). -/
theorem isNilpotent_ker_augmentation [CharP F 2] [Finite G] (h : ∀ g : G, g * g = 1) :
    IsNilpotent (RingHom.ker (augmentation F G)) := by
  have : IsNoetherianRing (MonoidAlgebra F G) :=
    isNoetherian_of_tower F (IsNoetherian.iff_fg.mpr inferInstance)
  rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
  intro x hx
  exact mem_nilradical.mpr ⟨2, by rw [sq, mul_self_eq_zero_of_mem_ker_augmentation F G h hx]⟩

/-- The local-ring statement for a `Group` in which every element squares to one (no
commutativity assumed).

Tex 4633-4637. Kind: `PROVED`. -/
theorem isLocalRing_monoidAlgebra_of_group {G' : Type*} [Group G'] [CharP F 2]
    (h : ∀ g : G', g * g = 1) : IsLocalRing (MonoidAlgebra F G') :=
  letI := commGroupOfMulSelfEqOne G' h
  isLocalRing_monoidAlgebra F G' h

end GroupRing

section LaurentGroupRing

/-- `𝔽₂((t))` has characteristic two.

Tex 4636. Kind: `PROVED`. -/
instance charP_laurentSeries_zmod_two : CharP (LaurentSeries (ZMod 2)) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (LaurentSeries (ZMod 2))).injective 2

variable (G : Type*) [CommGroup G]

/-- `𝔽₂((t))[G]` is local (for `G` with `g² = 1` for all `g`).

Tex 4636-4637. Kind: `PROVED`. -/
theorem isLocalRing_laurentSeries_monoidAlgebra (h : ∀ g : G, g * g = 1) :
    IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) G) :=
  isLocalRing_monoidAlgebra _ G h

/-- The maximal ideal of `𝔽₂((t))[G]` is the augmentation ideal.

Tex 4636-4637. Kind: `PROVED`. -/
theorem maximalIdeal_laurentSeries_monoidAlgebra (h : ∀ g : G, g * g = 1) :
    letI := isLocalRing_laurentSeries_monoidAlgebra G h
    IsLocalRing.maximalIdeal (MonoidAlgebra (LaurentSeries (ZMod 2)) G) =
      RingHom.ker (augmentation (LaurentSeries (ZMod 2)) G) :=
  maximalIdeal_eq_ker_augmentation _ G h

/-- For finite `G`, the augmentation ideal of `𝔽₂((t))[G]` is nilpotent.

Tex 4636-4637. Kind: `PROVED`. -/
theorem isNilpotent_ker_augmentation_laurentSeries [Finite G] (h : ∀ g : G, g * g = 1) :
    IsNilpotent (RingHom.ker (augmentation (LaurentSeries (ZMod 2)) G)) :=
  isNilpotent_ker_augmentation _ G h

/-- Instance form: for a group recorded (via `Fact`) to have exponent dividing two,
`𝔽₂((t))[G]` is a local ring.

Tex 4636-4637. Kind: `PROVED`. -/
instance isLocalRing_laurentSeries_monoidAlgebra_of_fact [Fact (∀ g : G, g * g = 1)] :
    IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) G) :=
  isLocalRing_laurentSeries_monoidAlgebra G Fact.out

end LaurentGroupRing

/-! ## Part 4: cancellation of unit entries and minimal models -/

section Cancellation

variable (R : Type*) [CommRing R]
variable (X₀ B₁ M B₂ N Y : Type*) [AddCommGroup X₀] [Module R X₀] [AddCommGroup B₁]
  [Module R B₁] [AddCommGroup M] [Module R M] [AddCommGroup B₂] [Module R B₂] [AddCommGroup N]
  [Module R N] [AddCommGroup Y] [Module R Y]

/-- A window `X₀ --a--> B₁ × M --d--> B₂ × N --c--> Y` of a complex of `R`-modules, written in
block form `a = (α, β)`, `d = [[φ, δ], [γ, ε]]`, `c = (μ, ν)`, in which the block `φ : B₁ → B₂`
of `d` is invertible (for `B₁ = B₂ = R`, a unit entry of the differential matrix). The four
equations are `d ∘ a = 0` and `c ∘ d = 0` written blockwise.

Tex 4637-4639 ("a minimal model obtained by cancelling unit entries"). Kind: definition. -/
structure CancellationWindow where
  /-- The block `X₀ → B₁` of `a`. -/
  α : X₀ →ₗ[R] B₁
  /-- The block `X₀ → M` of `a`. -/
  β : X₀ →ₗ[R] M
  /-- The invertible block `B₁ → B₂` of `d` (the unit entry). -/
  φ : B₁ ≃ₗ[R] B₂
  /-- The block `M → B₂` of `d`. -/
  δ : M →ₗ[R] B₂
  /-- The block `B₁ → N` of `d`. -/
  γ : B₁ →ₗ[R] N
  /-- The block `M → N` of `d`. -/
  ε : M →ₗ[R] N
  /-- The block `B₂ → Y` of `c`. -/
  μ : B₂ →ₗ[R] Y
  /-- The block `N → Y` of `c`. -/
  ν : N →ₗ[R] Y
  /-- First block of `d ∘ a = 0`. -/
  da_fst : (φ : B₁ →ₗ[R] B₂) ∘ₗ α + δ ∘ₗ β = 0
  /-- Second block of `d ∘ a = 0`. -/
  da_snd : γ ∘ₗ α + ε ∘ₗ β = 0
  /-- First block of `c ∘ d = 0`. -/
  cd_fst : μ ∘ₗ (φ : B₁ →ₗ[R] B₂) + ν ∘ₗ γ = 0
  /-- Second block of `c ∘ d = 0`. -/
  cd_snd : μ ∘ₗ δ + ν ∘ₗ ε = 0

namespace CancellationWindow

variable {R X₀ B₁ M B₂ N Y}
variable (W : CancellationWindow R X₀ B₁ M B₂ N Y)

/-- The original differential `a = (α, β)`. -/
def a : X₀ →ₗ[R] B₁ × M := W.α.prod W.β

/-- The original differential `d(x, y) = (φ x + δ y, γ x + ε y)`. -/
def d : B₁ × M →ₗ[R] B₂ × N := ((W.φ : B₁ →ₗ[R] B₂).coprod W.δ).prod (W.γ.coprod W.ε)

/-- The original differential `c(u, w) = μ u + ν w`. -/
def c : B₂ × N →ₗ[R] Y := W.μ.coprod W.ν

/-- The reduced differential `a' = β`. -/
def a' : X₀ →ₗ[R] M := W.β

/-- The reduced differential `d' = ε - γ φ⁻¹ δ` (the Schur complement of the unit entry). -/
def d' : M →ₗ[R] N := W.ε - W.γ ∘ₗ (W.φ.symm : B₂ →ₗ[R] B₁) ∘ₗ W.δ

/-- The reduced differential `c' = ν`. -/
def c' : N →ₗ[R] Y := W.ν

/-- The chain map to the reduced complex in the first cancelled degree: `(x, y) ↦ y`. -/
def f₁ (_ : CancellationWindow R X₀ B₁ M B₂ N Y) : B₁ × M →ₗ[R] M := LinearMap.snd R B₁ M

/-- The chain map to the reduced complex in the second cancelled degree:
`(u, w) ↦ w - γ φ⁻¹ u`. -/
def f₂ : B₂ × N →ₗ[R] N := (-(W.γ ∘ₗ (W.φ.symm : B₂ →ₗ[R] B₁))).coprod LinearMap.id

/-- The chain map from the reduced complex in the first cancelled degree:
`y ↦ (-φ⁻¹ δ y, y)`. -/
def g₁ : M →ₗ[R] B₁ × M := (-((W.φ.symm : B₂ →ₗ[R] B₁) ∘ₗ W.δ)).prod LinearMap.id

/-- The chain map from the reduced complex in the second cancelled degree: `w ↦ (0, w)`. -/
def g₂ (_ : CancellationWindow R X₀ B₁ M B₂ N Y) : N →ₗ[R] B₂ × N := LinearMap.inr R B₂ N

/-- The homotopy `h(u, w) = (φ⁻¹ u, 0)` from the second to the first cancelled degree. -/
def h : B₂ × N →ₗ[R] B₁ × M :=
  LinearMap.inl R B₁ M ∘ₗ (W.φ.symm : B₂ →ₗ[R] B₁) ∘ₗ LinearMap.fst R B₂ N

@[simp] theorem a_apply (x : X₀) : W.a x = (W.α x, W.β x) := rfl
@[simp] theorem d_apply (p : B₁ × M) : W.d p = (W.φ p.1 + W.δ p.2, W.γ p.1 + W.ε p.2) := rfl
@[simp] theorem c_apply (p : B₂ × N) : W.c p = W.μ p.1 + W.ν p.2 := rfl
@[simp] theorem a'_apply (x : X₀) : W.a' x = W.β x := rfl
@[simp] theorem d'_apply (y : M) : W.d' y = W.ε y - W.γ (W.φ.symm (W.δ y)) := rfl
@[simp] theorem c'_apply (w : N) : W.c' w = W.ν w := rfl
@[simp] theorem f₁_apply (p : B₁ × M) : W.f₁ p = p.2 := rfl
@[simp] theorem f₂_apply (p : B₂ × N) : W.f₂ p = -W.γ (W.φ.symm p.1) + p.2 := rfl
@[simp] theorem g₁_apply (y : M) : W.g₁ y = (-W.φ.symm (W.δ y), y) := rfl
@[simp] theorem g₂_apply (w : N) : W.g₂ w = (0, w) := rfl
@[simp] theorem h_apply (p : B₂ × N) : W.h p = (W.φ.symm p.1, 0) := rfl

theorem da_fst_apply (x : X₀) : W.φ (W.α x) + W.δ (W.β x) = 0 :=
  LinearMap.congr_fun W.da_fst x

theorem da_snd_apply (x : X₀) : W.γ (W.α x) + W.ε (W.β x) = 0 :=
  LinearMap.congr_fun W.da_snd x

theorem cd_fst_apply (x : B₁) : W.μ (W.φ x) + W.ν (W.γ x) = 0 :=
  LinearMap.congr_fun W.cd_fst x

theorem cd_snd_apply (y : M) : W.μ (W.δ y) + W.ν (W.ε y) = 0 :=
  LinearMap.congr_fun W.cd_snd y

/-- `δ β = -φ α`, from `d ∘ a = 0`. -/
theorem δ_β (x : X₀) : W.δ (W.β x) = -W.φ (W.α x) :=
  eq_neg_of_add_eq_zero_right (W.da_fst_apply x)

/-- `ν γ φ⁻¹ = -μ`, from `c ∘ d = 0`. -/
theorem ν_γ_φsymm (u : B₂) : W.ν (W.γ (W.φ.symm u)) = -W.μ u := by
  have := W.cd_fst_apply (W.φ.symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  exact eq_neg_of_add_eq_zero_right this

/-- The window is part of a complex: `d ∘ a = 0`.

Kind: `PROVED`. -/
theorem d_comp_a : W.d ∘ₗ W.a = 0 := by
  refine LinearMap.ext fun x => ?_
  simp [W.da_fst_apply x, W.da_snd_apply x]

/-- The window is part of a complex: `c ∘ d = 0`.

Kind: `PROVED`. -/
theorem c_comp_d : W.c ∘ₗ W.d = 0 := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply, d_apply, c_apply, map_add, LinearMap.zero_apply]
  rw [add_add_add_comm, W.cd_fst_apply p.1, W.cd_snd_apply p.2, add_zero]

/-- The reduced window is a complex: `d' ∘ a' = 0`.

Tex 4637-4639. Kind: `PROVED`. -/
theorem d'_comp_a' : W.d' ∘ₗ W.a' = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, a'_apply, d'_apply, W.δ_β x, map_neg,
    LinearEquiv.symm_apply_apply, sub_neg_eq_add, LinearMap.zero_apply]
  rw [add_comm, W.da_snd_apply x]

/-- The reduced window is a complex: `c' ∘ d' = 0`.

Tex 4637-4639. Kind: `PROVED`. -/
theorem c'_comp_d' : W.c' ∘ₗ W.d' = 0 := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, d'_apply, c'_apply, map_sub, W.ν_γ_φsymm, sub_neg_eq_add,
    LinearMap.zero_apply]
  rw [add_comm, W.cd_snd_apply y]

/-- Chain map condition for `f` in degree `X₀ → B₁ × M`: `f₁ ∘ a = a'` (with `f = 1` on `X₀`).

Kind: `PROVED`. -/
theorem f₁_comp_a : W.f₁ ∘ₗ W.a = W.a' :=
  LinearMap.ext fun x => by simp

/-- Chain map condition for `f` across the cancelled differential: `f₂ ∘ d = d' ∘ f₁`.

Kind: `PROVED`. -/
theorem f₂_comp_d : W.f₂ ∘ₗ W.d = W.d' ∘ₗ W.f₁ := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply, d_apply, f₂_apply, f₁_apply, d'_apply, map_add,
    LinearEquiv.symm_apply_apply, neg_add]
  abel

/-- Chain map condition for `f` in degree `B₂ × N → Y`: `c' ∘ f₂ = c` (with `f = 1` on `Y`).

Kind: `PROVED`. -/
theorem c'_comp_f₂ : W.c' ∘ₗ W.f₂ = W.c := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply, f₂_apply, c'_apply, c_apply, map_add, map_neg, W.ν_γ_φsymm,
    neg_neg]

/-- Chain map condition for `g` in degree `X₀ → M`: `g₁ ∘ a' = a` (with `g = 1` on `X₀`).

Kind: `PROVED`. -/
theorem g₁_comp_a' : W.g₁ ∘ₗ W.a' = W.a := by
  refine LinearMap.ext fun x => ?_
  simp [W.δ_β x]

/-- Chain map condition for `g` across the cancelled differential: `g₂ ∘ d' = d ∘ g₁`.

Kind: `PROVED`. -/
theorem g₂_comp_d' : W.g₂ ∘ₗ W.d' = W.d ∘ₗ W.g₁ := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, d'_apply, g₂_apply, g₁_apply, d_apply, map_neg,
    LinearEquiv.apply_symm_apply, neg_add_cancel]
  ext
  · rfl
  · simp only [sub_eq_add_neg]
    abel

/-- Chain map condition for `g` in degree `N → Y`: `c ∘ g₂ = c'` (with `g = 1` on `Y`).

Kind: `PROVED`. -/
theorem c_comp_g₂ : W.c ∘ₗ W.g₂ = W.c' :=
  LinearMap.ext fun w => by simp

/-- `f ∘ g = 1` in the first cancelled degree.

Kind: `PROVED`. -/
theorem f₁_comp_g₁ : W.f₁ ∘ₗ W.g₁ = LinearMap.id :=
  LinearMap.ext fun y => by simp

/-- `f ∘ g = 1` in the second cancelled degree.

Kind: `PROVED`. -/
theorem f₂_comp_g₂ : W.f₂ ∘ₗ W.g₂ = LinearMap.id :=
  LinearMap.ext fun w => by simp

/-- `g ∘ f ≃ 1` in the first cancelled degree: `1 - g₁ ∘ f₁ = h ∘ d` (the homotopy vanishes in
the degree of `X₀`).

Kind: `PROVED`. -/
theorem homotopy_one : LinearMap.id - W.g₁ ∘ₗ W.f₁ = W.h ∘ₗ W.d := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, f₁_apply, g₁_apply,
    d_apply, h_apply, map_add, LinearEquiv.symm_apply_apply]
  ext
  · simp only [Prod.fst_sub, sub_neg_eq_add]
  · simp

/-- `g ∘ f ≃ 1` in the second cancelled degree: `1 - g₂ ∘ f₂ = d ∘ h` (the homotopy vanishes in
the degree of `Y`).

Kind: `PROVED`. -/
theorem homotopy_two : LinearMap.id - W.g₂ ∘ₗ W.f₂ = W.d ∘ₗ W.h := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, f₂_apply, g₂_apply,
    d_apply, h_apply, LinearEquiv.apply_symm_apply, map_zero, add_zero]
  ext
  · simp
  · simp only [Prod.snd_sub]
    abel

end CancellationWindow

/-- One-step cancellation of a unit entry (Gaussian elimination), all identities at once.

Let `K` be a complex with `K^n = B₁ × M`, `K^{n+1} = B₂ × N`, `d^{n-1} = a`, `d^n = d`,
`d^{n+1} = c`, in which the block `φ : B₁ → B₂` of `d^n` is invertible, and let `K'` be the complex
obtained by replacing `K^n, K^{n+1}` by `M, N` and `a, d, c` by `a' = β`, `d' = ε - γ φ⁻¹ δ`,
`c' = ν` (all other terms and differentials unchanged). Then `K'` is a complex, and `f : K → K'`
(`f₁, f₂` in degrees `n, n+1`, the identity elsewhere), `g : K' → K` (`g₁, g₂`, the identity
elsewhere) are chain maps with `f ∘ g = 1`, and `h` (in degree `n+1 → n`, zero elsewhere) is a
homotopy `1 ≃ g ∘ f`. These are exactly the identities below: every other chain-map or homotopy
condition involves only identity maps and zero homotopies. With `B₁ = B₂ = R` the total rank drops
by two (`finrank_cancel`).

Tex 4637-4639 ("a minimal model obtained by cancelling unit entries"). Kind: `PROVED`. -/
theorem CancellationWindow.homotopyEquivalence_data (W : CancellationWindow R X₀ B₁ M B₂ N Y) :
    (W.d ∘ₗ W.a = 0 ∧ W.c ∘ₗ W.d = 0) ∧ (W.d' ∘ₗ W.a' = 0 ∧ W.c' ∘ₗ W.d' = 0) ∧
      (W.f₁ ∘ₗ W.a = W.a' ∧ W.f₂ ∘ₗ W.d = W.d' ∘ₗ W.f₁ ∧ W.c' ∘ₗ W.f₂ = W.c) ∧
      (W.g₁ ∘ₗ W.a' = W.a ∧ W.g₂ ∘ₗ W.d' = W.d ∘ₗ W.g₁ ∧ W.c ∘ₗ W.g₂ = W.c') ∧
      (W.f₁ ∘ₗ W.g₁ = LinearMap.id ∧ W.f₂ ∘ₗ W.g₂ = LinearMap.id) ∧
      (LinearMap.id - W.g₁ ∘ₗ W.f₁ = W.h ∘ₗ W.d ∧ LinearMap.id - W.g₂ ∘ₗ W.f₂ = W.d ∘ₗ W.h) :=
  ⟨⟨W.d_comp_a, W.c_comp_d⟩, ⟨W.d'_comp_a', W.c'_comp_d'⟩,
    ⟨W.f₁_comp_a, W.f₂_comp_d, W.c'_comp_f₂⟩, ⟨W.g₁_comp_a', W.g₂_comp_d', W.c_comp_g₂⟩,
    ⟨W.f₁_comp_g₁, W.f₂_comp_g₂⟩, ⟨W.homotopy_one, W.homotopy_two⟩⟩


end Cancellation

section CancellationRank

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Cancelling a unit entry (`B₁ = B₂ = R`) lowers the total rank by two: the two cancelled
degrees have ranks `1 + m` and `1 + n` before and `m`, `n` after.

Tex 4637-4639 ("a minimal model obtained by cancelling unit entries"). Kind: `PROVED`. -/
theorem finrank_cancel (m n : ℕ) :
    Module.finrank R (R × (Fin m → R)) + Module.finrank R (R × (Fin n → R)) =
      Module.finrank R (Fin m → R) + Module.finrank R (Fin n → R) + 2 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun,
    Module.finrank_fin_fun]
  omega

end CancellationRank

section MinimalModels

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Over a local ring, a matrix has no unit entry exactly when all its entries lie in the maximal
ideal (the minimality condition left after all unit entries are cancelled).

Tex 4637-4639. Kind: `PROVED`. -/
theorem forall_mem_maximalIdeal_iff_forall_not_isUnit {m n : Type*} (Mx : Matrix m n R) :
    (∀ i j, Mx i j ∈ IsLocalRing.maximalIdeal R) ↔ ∀ i j, ¬IsUnit (Mx i j) := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- A minimal differential (entries in the maximal ideal) reduces to zero over the residue
field.

Tex 4638-4639. Kind: `PROVED`. -/
theorem map_residue_eq_zero_of_minimal {m n : Type*} (Mx : Matrix m n R)
    (hM : ∀ i j, Mx i j ∈ IsLocalRing.maximalIdeal R) :
    Mx.map (IsLocalRing.residue R) = 0 := by
  ext i j
  simpa [IsLocalRing.residue_eq_zero_iff] using hM i j

/-- The cohomology `ker g / im f` of a complex with zero differentials is the whole middle term.

Kind: `PROVED`. -/
theorem finrank_cohomology_zero {k : Type*} [Field k] {U V W : Type*} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] :
    Module.finrank k (LinearMap.ker (0 : V →ₗ[k] W) ⧸
      (LinearMap.range (0 : U →ₗ[k] V)).comap (LinearMap.ker (0 : V →ₗ[k] W)).subtype) =
      Module.finrank k V := by
  rw [LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, LinearMap.ker_zero, finrank_top]

/-- For a minimal finite free model over a local ring, the rank in each degree is the dimension
of the cohomology after reduction to the residue field: if the incoming and outgoing
differentials at a term `R^r` have all entries in the maximal ideal, then the residual
cohomology `ker d̄_out / im d̄_in` at that term has dimension `r`.

Tex 4637-4640 ("its ranks are the dimensions of the cohomology after augmentation").
Kind: `PROVED`. -/
theorem finrank_residualCohomology_of_minimal {r s t : ℕ} (dIn : Matrix (Fin r) (Fin t) R)
    (dOut : Matrix (Fin s) (Fin r) R) (hIn : ∀ i j, dIn i j ∈ IsLocalRing.maximalIdeal R)
    (hOut : ∀ i j, dOut i j ∈ IsLocalRing.maximalIdeal R) :
    Module.finrank (IsLocalRing.ResidueField R)
      (LinearMap.ker (Matrix.toLin' (dOut.map (IsLocalRing.residue R))) ⧸
        (LinearMap.range (Matrix.toLin' (dIn.map (IsLocalRing.residue R)))).comap
          (LinearMap.ker (Matrix.toLin' (dOut.map (IsLocalRing.residue R)))).subtype) = r := by
  rw [map_residue_eq_zero_of_minimal dOut hOut, map_residue_eq_zero_of_minimal dIn hIn,
    map_zero, map_zero, finrank_cohomology_zero, Module.finrank_fin_fun]

end MinimalModels

section MinimalModelsGroupRing

variable (F : Type*) [Field F] [CharP F 2] (G : Type*) [CommGroup G]

/-- In `F[G]` (`g² = 1` for all `g`), a matrix entry is a non-unit exactly when it lies in the
augmentation ideal; so a minimal model over `F[G]` is one whose differentials have entries in
`ker ε`.

Tex 4636-4639. Kind: `PROVED`. -/
theorem not_isUnit_iff_mem_ker_augmentation (h : ∀ g : G, g * g = 1) (x : MonoidAlgebra F G) :
    ¬IsUnit x ↔ x ∈ RingHom.ker (augmentation F G) := by
  rw [isUnit_iff_augmentation_ne_zero F G h, RingHom.mem_ker, not_not]

/-- Over `F[G]`: for a minimal finite free model (no unit entries), the rank `r` of a term is
the dimension over `F` of the cohomology after augmentation `ε : F[G] → F` at that term.

Tex 4637-4640 ("its ranks are the dimensions of the cohomology after augmentation").
Kind: `PROVED`. -/
theorem finrank_augmentedCohomology_of_minimal (h : ∀ g : G, g * g = 1) {r s t : ℕ}
    (dIn : Matrix (Fin r) (Fin t) (MonoidAlgebra F G))
    (dOut : Matrix (Fin s) (Fin r) (MonoidAlgebra F G))
    (hIn : ∀ i j, ¬IsUnit (dIn i j)) (hOut : ∀ i j, ¬IsUnit (dOut i j)) :
    Module.finrank F
      (LinearMap.ker (Matrix.toLin' (dOut.map (augmentation F G))) ⧸
        (LinearMap.range (Matrix.toLin' (dIn.map (augmentation F G)))).comap
          (LinearMap.ker (Matrix.toLin' (dOut.map (augmentation F G)))).subtype) = r := by
  have hIn' : dIn.map (augmentation F G) = 0 := by
    ext i j
    exact RingHom.mem_ker.mp ((not_isUnit_iff_mem_ker_augmentation F G h _).mp (hIn i j))
  have hOut' : dOut.map (augmentation F G) = 0 := by
    ext i j
    exact RingHom.mem_ker.mp ((not_isUnit_iff_mem_ker_augmentation F G h _).mp (hOut i j))
  rw [hIn', hOut', map_zero, map_zero, finrank_cohomology_zero, Module.finrank_fin_fun]

end MinimalModelsGroupRing

section MinimalModelsGlue

open CategoryTheory

universe u

/-- `GLUE` (textbook fact, stated, not proved): minimal models over a local ring.

Every bounded cochain complex `K` of finite free modules over a local ring `R` is homotopy
equivalent to a minimal one `L` (finite free, with `d(L) ⊆ 𝔪 L`), whose ranks are at most those
of `K` and equal, degree by degree, the dimensions over the residue field `k` of the cohomology
of `k ⊗_R K`.

Tex 4637-4640 ("A finite free model over this ring has a minimal model obtained by cancelling
unit entries; its ranks are the dimensions of the cohomology after augmentation").

Proof sketch. Induct on the total rank of `K`. If some differential `d^i` does not map into
`𝔪 K^{i+1}`, then in suitable bases one of its matrix entries is a unit; the one-step
cancellation `CancellationWindow` (with `B₁ = B₂ = R` and `φ` the unit entry; the chain maps `f`,
`g` extended by the identity and the homotopy `h` extended by zero outside the two cancelled
degrees; identities `f₁_comp_a` ... `homotopy_two`) gives a homotopy equivalent finite free
complex of total rank two less (`finrank_cancel`), with no rank increased. When no unit entry
remains, `L` is minimal, so `k ⊗ L` has zero differentials (`map_residue_eq_zero_of_minimal`)
and `dim_k H^i(k ⊗ L) = rank L^i` (`finrank_residualCohomology_of_minimal`); since `k ⊗ -`
preserves homotopy equivalences, `H^i(k ⊗ K) ≅ H^i(k ⊗ L)`. For `R = F[G]` the residue map is the
augmentation `ε` (`maximalIdeal_eq_ker_augmentation`, `augmentation_surjective`). -/
def MinimalModelsExist (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
    (∀ i, Module.Free R (K.X i) ∧ Module.Finite R (K.X i)) →
    (∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (K.X i)) →
    ∃ L : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (HomotopyEquiv K L) ∧
      (∀ i, Module.Free R (L.X i) ∧ Module.Finite R (L.X i)) ∧
      (∀ i j (x : L.X i),
        (L.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (L.X j))) ∧
      (∀ i, Module.finrank R (L.X i) ≤ Module.finrank R (K.X i)) ∧
      (∀ i, Module.finrank R (L.X i) = Module.finrank (IsLocalRing.ResidueField R)
        ((((ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology i))

end MinimalModelsGlue

/-! ## Non-vacuity examples -/

section Examples

/-! ### Part 1 -/

/-- Inverting `t` is a genuine condition: `t` is not a unit of `𝔽₂[[t]]` (but it is in `𝔽₂((t))`,
`isUnit_algebraMap_X_laurentSeries`). -/
example : ¬IsUnit (X : (ZMod 2)⟦X⟧) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

example : IsUnit (geomFactor (ZMod 2) 3) :=
  isUnit_geomFactor_of_odd ⟨1, rfl⟩

/-- Oddness is needed: `((1+t)^2 - 1)/t` is not a unit of `𝔽₂[[t]]`. -/
example : ¬IsUnit (geomFactor (ZMod 2) 2) := by
  rw [isUnit_geomFactor_iff]
  have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h]
  exact not_isUnit_zero

/-- The conjugate place with `e = 3`: `(1+t)^{-3} - 1` is a unit of `𝔽₂((t))`. -/
example : IsUnit (algebraMap (ZMod 2)⟦X⟧ (LaurentSeries (ZMod 2))
    ((((onePlusX (ZMod 2)) ^ (-3 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) - 1)) :=
  isUnit_laurentSeries_onePlusX_zpow_sub_one ⟨-2, by norm_num⟩

/-! ### Part 2 -/

/-- The general local model with `C = 0` and `A = D = 1` over any ring. -/
example (B : Type*) [CommRing B] :
    Nonempty (ThreeTermContraction (localModel_d0 (LinearMap.id : B →ₗ[B] B) 0)
      (localModel_d1 0 (LinearMap.id : B →ₗ[B] B))) :=
  (localModel_contractible rfl isUnit_one isUnit_one).2

/-- The reduced active-place model over `𝔽₂((t))` at the oriented place (`e = 1`, `q = 3`). -/
noncomputable example :
    ThreeTermContraction
      (localModel_d0 (Matrix.toLin' (model_A (activePhi (LaurentSeries (ZMod 2)) 1)))
        (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) (LaurentSeries (ZMod 2))))))
      (localModel_d1 (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) (LaurentSeries (ZMod 2)))))
        (Matrix.toLin' (model_D 3 (activePhi (LaurentSeries (ZMod 2)) 1) 1))) :=
  activePlaceContraction isUnit_algebraMap_X_laurentSeries odd_one ⟨1, rfl⟩

/-- The same at both places above an active prime, with `e = 5`, `q = 7`, as a split short exact
sequence in Mathlib's sense. -/
example : ∀ e' ∈ ({5, -5} : Set ℤ),
    Nonempty (ThreeTermContraction
      (localModel_d0 (Matrix.toLin' (model_A (activePhi (LaurentSeries (ZMod 2)) e')))
        (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) (LaurentSeries (ZMod 2))))))
      (localModel_d1 (Matrix.toLin' (model_C (1 : Matrix (Fin 2) (Fin 2) (LaurentSeries (ZMod 2)))))
        (Matrix.toLin' (model_D 7 (activePhi (LaurentSeries (ZMod 2)) e') 1)))) :=
  fun e' he' =>
    (activePlace_contractible isUnit_algebraMap_X_laurentSeries (e := 5) ⟨2, rfl⟩ ⟨3, rfl⟩ e'
      he').2

example : (activePlaceContraction (B := LaurentSeries (ZMod 2))
    isUnit_algebraMap_X_laurentSeries (e := 1) odd_one (q := 3) ⟨1, rfl⟩).shortComplex.ShortExact :=
  ThreeTermContraction.shortExact _

/-! ### Part 3 -/

example : CharP (LaurentSeries (ZMod 2)) 2 := inferInstance

/-- A group given only as a `Group` with `g² = 1` (here `Perm (Fin 2)`) is commutative. -/
example : ∀ a b : Equiv.Perm (Fin 2), a * b = b * a :=
  mul_comm_of_mul_self_eq_one (by decide)

/-- `ℤˣ = {±1}` is a binary group: `𝔽₂((t))[ℤˣ]` is local with nilpotent augmentation ideal. -/
example : IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) ℤˣ) :=
  isLocalRing_laurentSeries_monoidAlgebra ℤˣ Int.units_mul_self

example : IsNilpotent (RingHom.ker (augmentation (LaurentSeries (ZMod 2)) ℤˣ)) :=
  isNilpotent_ker_augmentation_laurentSeries ℤˣ Int.units_mul_self

/-- The instance form, through `Fact`. -/
example : IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) ℤˣ) :=
  have : Fact (∀ g : ℤˣ, g * g = 1) := ⟨Int.units_mul_self⟩
  inferInstance

/-- Products of binary groups, `(ℤˣ)ⁿ`. -/
example (n : ℕ) : IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) (Fin n → ℤˣ)) :=
  isLocalRing_laurentSeries_monoidAlgebra _ fun g => funext fun i => Int.units_mul_self (g i)

example (n : ℕ) : IsNilpotent (RingHom.ker (augmentation (LaurentSeries (ZMod 2)) (Fin n → ℤˣ))) :=
  isNilpotent_ker_augmentation_laurentSeries _ fun g => funext fun i => Int.units_mul_self (g i)

/-- The element `[-1] - 1` of `𝔽₂((t))[ℤˣ]`. -/
noncomputable def minusOneSubOne : MonoidAlgebra (LaurentSeries (ZMod 2)) ℤˣ :=
  MonoidAlgebra.single (-1) 1 - 1

theorem minusOneSubOne_mem_ker :
    minusOneSubOne ∈ RingHom.ker (augmentation (LaurentSeries (ZMod 2)) ℤˣ) := by
  rw [RingHom.mem_ker, minusOneSubOne, map_sub, map_one, augmentation_single, sub_self]

/-- The augmentation ideal is not zero: `[-1] - 1 ≠ 0` lies in it, squares to zero, and is not a
unit. -/
example : minusOneSubOne ≠ 0 ∧ minusOneSubOne * minusOneSubOne = 0 ∧ ¬IsUnit minusOneSubOne := by
  refine ⟨fun h0 => ?_, mul_self_eq_zero_of_mem_ker_augmentation _ _ Int.units_mul_self
    minusOneSubOne_mem_ker, (not_isUnit_iff_mem_ker_augmentation _ _ Int.units_mul_self _).mpr
    minusOneSubOne_mem_ker⟩
  have h := congrArg (fun y : MonoidAlgebra (LaurentSeries (ZMod 2)) ℤˣ => y.coeff (-1)) h0
  simp [minusOneSubOne, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] at h

/-! ### Part 4 -/

/-- A cancellation window exists for every unit entry: `[0 → R --u--> R → 0]`. -/
example (R : Type*) [CommRing R] (u : Rˣ) : CancellationWindow R PUnit R PUnit R PUnit PUnit where
  α := 0
  β := 0
  φ := LinearEquiv.smulOfUnit u
  δ := 0
  γ := 0
  ε := 0
  μ := 0
  ν := 0
  da_fst := by ext; simp
  da_snd := by ext
  cd_fst := by ext
  cd_snd := by ext

/-- A minimal `1 × 1` model over `𝔽₂((t))[ℤˣ]` with the nonzero entry `[-1] - 1`: its rank `1` is
the dimension of the cohomology after augmentation. -/
example :
    Module.finrank (LaurentSeries (ZMod 2))
      (LinearMap.ker (Matrix.toLin'
          ((Matrix.of fun _ _ => minusOneSubOne : Matrix (Fin 1) (Fin 1) _).map
            (augmentation (LaurentSeries (ZMod 2)) ℤˣ))) ⧸
        (LinearMap.range (Matrix.toLin'
          ((Matrix.of fun _ _ => minusOneSubOne : Matrix (Fin 1) (Fin 1) _).map
            (augmentation (LaurentSeries (ZMod 2)) ℤˣ)))).comap
          (LinearMap.ker (Matrix.toLin'
            ((Matrix.of fun _ _ => minusOneSubOne : Matrix (Fin 1) (Fin 1) _).map
              (augmentation (LaurentSeries (ZMod 2)) ℤˣ)))).subtype) = 1 :=
  finrank_augmentedCohomology_of_minimal _ _ Int.units_mul_self _ _
    (fun _ _ => (not_isUnit_iff_mem_ker_augmentation _ _ Int.units_mul_self _).mpr
      minusOneSubOne_mem_ker)
    (fun _ _ => (not_isUnit_iff_mem_ker_augmentation _ _ Int.units_mul_self _).mpr
      minusOneSubOne_mem_ker)

end Examples

end ZInQ.Manuscript.RC.Limits
