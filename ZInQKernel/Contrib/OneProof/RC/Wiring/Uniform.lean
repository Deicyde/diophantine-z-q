import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.HeightOneProposition
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Bridges

/-!
# Theorem 5.3, Lane RC0 round 2: wiring lane RC16 (height-one regularity and (3.5))

Lane RC16 (namespace `ZInQ.Manuscript.RC.Uniform`) proved Proposition
`ex:limits-uniform-lower-bound` (tex 4909–5202) from Elliot's switching steps: the uniform lower
bound (5.5), height-one regularity `u_prim ∈ Λ[1/2]` (`mem_lambdaHalf_of_regularity`) and
(5.5) + (4.6) ⇒ (3.5) (`exLimitsUniformLowerBound`). Batch 3's `PairedFunctional` proved the
integrality of the paired functional at every height-one prime `𝔭 ≠ (2)`
(`pairedFunctionalHeightOne_proof`, tex 3715–3719, 3753–3765, reused at 5162–5189) and the
functional exponent bound used at the terminal step of (5.5) (`functionalExponentBound_proof`,
tex 4957–4962). This file wires these results to two targets of `Data.lean`:

* (a) `HeightOneTarget D` (tex 4909–5205, 5703–5704): every corrected coordinate `ũ_x` of a final
  family lies in `Λ[1/2]`.
  - `heightOneTarget_of_prim` (PROVED algebra): `ũ_x = ε_x u_{prim,x}` with `ε_x ∈ Λ^×` ((4.7),
    `CommonCoordinateTarget D`) and `u_{prim,x} ∈ Λ[1/2]` give `ũ_x ∈ Λ[1/2]`.
  - `primLambdaHalf_of_inputs`: `u_{prim,x} ∈ Λ[1/2]` from `PrimRegularityInputs D`, by RC16's
    `mem_lambdaHalf_of_regularity`, with the terminal step of each height-one process discharged
    by batch 3's `pairedFunctionalHeightOne_proof`.
* (b) `Eq35Target W` ((3.5) for each fixed `A` at the rough companions, tex 2441–2446, 5200–5202)
  from `Eq35Inputs W`, by RC16's `exLimitsUniformLowerBound`, with the terminal functional bound
  `hβ` of each outer process discharged by batch 3's `functionalExponentBound_proof`
  (`eq35Target_of_inputs`).

The remaining hypotheses are collected in `PrimRegularityInputs` and `Eq35Inputs`; their docstrings
list every conjunct with its tex lines, kind and owner.

Vocabulary added here:
* `lamIncl : Λ → ℚ₂[[t]]` and `IsTExpansion u U` — `U ∈ ℚ₂[[t]]` is the `t`-expansion of
  `u ∈ Frac Λ` (the identification of the interface's power series with RC16's elements of
  `Frac Λ`; it is a partial bijection, `IsTExpansion.unique_left` / `unique_right`), and the
  consistency `central U = centralSpecialization uh` of the two central values;
* `TerminalPairedFunctional 𝔭 u`, `RegularitySwitchProcessPF 𝔭`, `RegularityInputs u` — RC16's
  height-one switching process, its terminal step stated through batch 3's paired functional;
* `OuterSwitchProcessPF v 𝒰` — RC16's outer switching process, its terminal functional given as
  an integral functional (exponent `a = 0`);
* `CompanionPair W A` — the ring instances `(h, k')` of (3.5) with `ω(k') ≤ A`.

`DEPARTURE` (form only): the refined processes repeat RC16's fields verbatim except the terminal
step, which is stated in the form batch 3's theorems consume; `toProcess` rebuilds RC16's
structures from them (PROVED).

Non-vacuity (PROVED, last section): at a height-one prime `𝔭 ≠ (2)` the refined terminal step is
equivalent to RC16's (`terminalPairedFunctional_iff`); `RegularityInputs u ↔ u ∈ Λ[1/2]`;
`PrimRegularityInputs D` holds exactly when every `u_{prim,x}` lies in `Λ[1/2]`;
`OuterSwitchProcessPF` is inhabited.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## `Λ ⊂ ℚ₂[[t]]`, `Λ[1/2]` and `t`-expansions -/

/-- The inclusion `Λ = ℤ₂[[t]] ⊂ ℚ₂[[t]]` (coefficientwise `ℤ₂ ⊂ ℚ₂`); `LamUnit ε` says that `ε`
is the image of a unit. Kind: definition. -/
abbrev lamIncl : Lambda →+* PowerSeries ℚ_[2] := PowerSeries.map PadicInt.Coe.ringHom

/-- `Λ → ℚ₂[[t]]` is injective. Kind: PROVED. -/
theorem lamIncl_injective : Function.Injective lamIncl :=
  PowerSeries.map_injective _ (fun _ _ h => Subtype.ext h)

/-- `InLamHalf U` (`U = g / 2^e`, `g ∈ Λ`) in product form: `U = 2^{-e} · G` with `G ∈ Λ`.
Kind: PROVED. -/
theorem inLamHalf_iff (U : PowerSeries ℚ_[2]) :
    InLamHalf U ↔ ∃ (e : ℕ) (G : Lambda), U = PowerSeries.C ((2 : ℚ_[2]) ^ e)⁻¹ * lamIncl G := by
  constructor
  · rintro ⟨e, g, hg⟩
    refine ⟨e, PowerSeries.mk g, PowerSeries.ext fun n => ?_⟩
    rw [hg n, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, div_eq_inv_mul]
    rfl
  · rintro ⟨e, G, rfl⟩
    refine ⟨e, fun n => PowerSeries.coeff n G, fun n => ?_⟩
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, div_eq_inv_mul]
    rfl

/-- **`Λ · Λ[1/2] ⊆ Λ[1/2]`** in `ℚ₂[[t]]`. Kind: PROVED. -/
theorem inLamHalf_lamIncl_mul {U : PowerSeries ℚ_[2]} (hU : InLamHalf U) (E : Lambda) :
    InLamHalf (lamIncl E * U) := by
  obtain ⟨e, G, rfl⟩ := (inLamHalf_iff U).mp hU
  refine (inLamHalf_iff _).mpr ⟨e, E * G, ?_⟩
  rw [map_mul]
  ring

/-- **A `Λ`-unit multiple of an element of `Λ[1/2]` lies in `Λ[1/2]`** (the step from
`u_{prim,x}` to `ũ_x = ε_x u_{prim,x}`, tex 4142–4152 with 5192–5194 and 5703–5704).
Kind: PROVED. -/
theorem inLamHalf_lamUnit_mul {ε U : PowerSeries ℚ_[2]} (hε : LamUnit ε) (hU : InLamHalf U) :
    InLamHalf (ε * U) := by
  obtain ⟨e, rfl⟩ := hε
  exact inLamHalf_lamIncl_mul hU _

/-- **`U ∈ ℚ₂[[t]]` is the `t`-expansion of `u ∈ Frac Λ`**: `u = a / b` with `a, b ∈ Λ`, `b ≠ 0`,
and `U · b = a` in `ℚ₂[[t]]`. Both rings embed in the fraction field `ℚ₂((t))` of `ℚ₂[[t]]`, and the
relation says that `u` and `U` have the same image there (remark, not used: some `U` exists
exactly when `u` has no pole at `t = 0`). It is a partial bijection (`IsTExpansion.unique_left`,
`IsTExpansion.unique_right`). This is how the interface's power series `u_{prim,x}` (tex
3877–3892, the coordinate of `[z] ⊗ [λ]`, regular at the centre by the height-one regularity at
`𝔭 = (t)`, tex 5004–5008, 5191–5192, and, at the base, Lemma `ex:arith-base-zero`, tex 4334–4336,
4350–4368) is identified with the element of `Frac Λ` that lane RC16 studies. Kind: definition. -/
def IsTExpansion (u : FractionRing Lambda) (U : PowerSeries ℚ_[2]) : Prop :=
  ∃ a b : Lambda, b ≠ 0 ∧
    u * algebraMap Lambda (FractionRing Lambda) b = algebraMap Lambda (FractionRing Lambda) a ∧
    U * lamIncl b = lamIncl a

/-- The `t`-expansion of an element of `Λ` is its image in `ℚ₂[[t]]`. Kind: PROVED. -/
theorem isTExpansion_algebraMap (f : Lambda) :
    IsTExpansion (algebraMap Lambda (FractionRing Lambda) f) (lamIncl f) :=
  ⟨f, 1, one_ne_zero, by rw [map_one, mul_one], by rw [map_one, mul_one]⟩

/-- A `t`-expansion is unique. Kind: PROVED. -/
theorem IsTExpansion.unique_right {u : FractionRing Lambda} {U U' : PowerSeries ℚ_[2]}
    (h : IsTExpansion u U) (h' : IsTExpansion u U') : U = U' := by
  obtain ⟨a, b, hb, hu, hU⟩ := h
  obtain ⟨a', b', hb', hu', hU'⟩ := h'
  have hinj := IsFractionRing.injective Lambda (FractionRing Lambda)
  have key : a * b' = a' * b := by
    apply hinj
    rw [map_mul, map_mul, ← hu, ← hu']
    ring
  have hB : lamIncl b * lamIncl b' ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ lamIncl_injective).mpr hb)
      ((map_ne_zero_iff _ lamIncl_injective).mpr hb')
  apply mul_right_cancel₀ hB
  calc U * (lamIncl b * lamIncl b') = (U * lamIncl b) * lamIncl b' := by ring
    _ = lamIncl (a * b') := by rw [hU, map_mul]
    _ = lamIncl (a' * b) := by rw [key]
    _ = (U' * lamIncl b') * lamIncl b := by rw [hU', map_mul]
    _ = U' * (lamIncl b * lamIncl b') := by ring

/-- An element of `Frac Λ` is determined by its `t`-expansion. Kind: PROVED. -/
theorem IsTExpansion.unique_left {u u' : FractionRing Lambda} {U : PowerSeries ℚ_[2]}
    (h : IsTExpansion u U) (h' : IsTExpansion u' U) : u = u' := by
  obtain ⟨a, b, hb, hu, hU⟩ := h
  obtain ⟨a', b', hb', hu', hU'⟩ := h'
  have hinj := IsFractionRing.injective Lambda (FractionRing Lambda)
  have key : a * b' = a' * b := by
    apply lamIncl_injective
    rw [map_mul, map_mul, ← hU, ← hU']
    ring
  have hB : algebraMap Lambda (FractionRing Lambda) b * algebraMap Lambda (FractionRing Lambda) b'
      ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hb) ((map_ne_zero_iff _ hinj).mpr hb')
  apply mul_right_cancel₀ hB
  calc u * (algebraMap Lambda (FractionRing Lambda) b * algebraMap Lambda (FractionRing Lambda) b')
      = (u * algebraMap Lambda (FractionRing Lambda) b) *
          algebraMap Lambda (FractionRing Lambda) b' := by ring
    _ = algebraMap Lambda (FractionRing Lambda) (a * b') := by rw [hu, map_mul]
    _ = algebraMap Lambda (FractionRing Lambda) (a' * b) := by rw [key]
    _ = (u' * algebraMap Lambda (FractionRing Lambda) b') *
          algebraMap Lambda (FractionRing Lambda) b := by rw [hu', map_mul]
    _ = u' * (algebraMap Lambda (FractionRing Lambda) b *
          algebraMap Lambda (FractionRing Lambda) b') := by ring

/-- If `u ∈ Frac Λ` lies in (the image of) `Λ[1/2]`, say `u = f / 2^m`, its `t`-expansion `U`
satisfies `U · 2^m = f` in `ℚ₂[[t]]`. Kind: PROVED. -/
theorem IsTExpansion.exists_two_pow {uh : LambdaHalf} {U : PowerSeries ℚ_[2]}
    (hT : IsTExpansion (lambdaHalfToFrac uh) U) :
    ∃ (f : Lambda) (m : ℕ), uh * algebraMap Lambda LambdaHalf (2 ^ m) =
        algebraMap Lambda LambdaHalf f ∧ U * lamIncl (2 ^ m) = lamIncl f := by
  obtain ⟨a, b, hb, hub, hUb⟩ := hT
  obtain ⟨f, m, hf⟩ := exists_mul_two_pow_eq uh
  refine ⟨f, m, hf, ?_⟩
  have h1 : lambdaHalfToFrac uh * algebraMap Lambda (FractionRing Lambda) (2 ^ m) =
      algebraMap Lambda (FractionRing Lambda) f := by
    have := congrArg lambdaHalfToFrac hf
    rwa [map_mul, AlgHom.commutes, AlgHom.commutes] at this
  have h2 : a * 2 ^ m = f * b := by
    apply IsFractionRing.injective Lambda (FractionRing Lambda)
    rw [map_mul, map_mul, ← hub, ← h1]
    ring
  have hB : lamIncl b ≠ 0 := (map_ne_zero_iff _ lamIncl_injective).mpr hb
  apply mul_right_cancel₀ hB
  calc U * lamIncl (2 ^ m) * lamIncl b = (U * lamIncl b) * lamIncl (2 ^ m) := by ring
    _ = lamIncl (a * 2 ^ m) := by rw [hUb, map_mul]
    _ = lamIncl (f * b) := by rw [h2]
    _ = lamIncl f * lamIncl b := by rw [map_mul]

/-- `lamIncl (2^m) = C (2^m)`. Kind: PROVED. -/
theorem lamIncl_two_pow (m : ℕ) : lamIncl (2 ^ m) = PowerSeries.C ((2 : ℚ_[2]) ^ m) := by
  rw [map_pow, map_pow, map_ofNat, map_ofNat]

/-- **Transfer of `Λ[1/2]`-membership to the `t`-expansion**: if `u ∈ Frac Λ` lies in `Λ[1/2]`
(RC16's conclusion) and `U` is its `t`-expansion, then `InLamHalf U` (bounded denominators in
`ℚ₂[[t]]`). Kind: PROVED. -/
theorem inLamHalf_of_isTExpansion {u : FractionRing Lambda} {U : PowerSeries ℚ_[2]}
    (hT : IsTExpansion u U) (hu : u ∈ lambdaHalfToFrac.range) : InLamHalf U := by
  obtain ⟨uh, rfl⟩ := hu
  obtain ⟨f, m, -, hU⟩ := hT.exists_two_pow
  refine ⟨m, fun n => PowerSeries.coeff n f, fun n => ?_⟩
  have h2m : (2 : ℚ_[2]) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have := congrArg (PowerSeries.coeff n) hU
  rw [lamIncl_two_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map] at this
  rw [eq_div_iff h2m, this]
  rfl

/-- **The two central values agree**: if `U` is the `t`-expansion of `uh ∈ Λ[1/2]`, the central
value `central U = U(0)` used by the interface (`CalibrationTarget`, (4.6)) is RC16's
`centralSpecialization uh` (tex 4914–4920). Kind: PROVED. -/
theorem IsTExpansion.central_eq {uh : LambdaHalf} {U : PowerSeries ℚ_[2]}
    (hT : IsTExpansion (lambdaHalfToFrac uh) U) : central U = centralSpecialization uh := by
  obtain ⟨f, m, hf, hU⟩ := hT.exists_two_pow
  have h2m : (2 : ℚ_[2]) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have h1 : central U * (2 : ℚ_[2]) ^ m = ((PowerSeries.constantCoeff f : ℤ_[2]) : ℚ_[2]) := by
    have := congrArg (PowerSeries.coeff 0) hU
    rw [lamIncl_two_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map] at this
    rw [central, this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rfl
  have h2 : centralSpecialization uh * (2 : ℚ_[2]) ^ m =
      ((PowerSeries.constantCoeff f : ℤ_[2]) : ℚ_[2]) := by
    have := congrArg centralSpecialization hf
    rw [map_mul, centralSpecialization_algebraMap, centralSpecialization_algebraMap] at this
    rw [← this, map_pow, map_ofNat, PadicInt.coe_pow, show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl]
  exact mul_right_cancel₀ h2m (h1.trans h2.symm)

/-! ## The height-one switching process, terminal step through batch 3's paired functional -/

section HeightOne

open CategoryTheory CategoryTheory.Limits

variable (P : Ideal Lambda) [P.IsPrime]

/-- **The terminal step of the height-one descent, through the paired functional** (tex
5159–5189), for the coordinate `u ∈ Frac Λ` of a terminal configuration (fiber dimension one) at a
height-one prime `𝔭 ≠ (2)`, over `R = Λ_𝔭`. Conjuncts, in order:

1. the data and hypotheses of batch 3's `PairedFunctionalHeightOne` at `𝔭`: complexes
   `C_U`, `C' = C_{U^⊥}`, `C = τ^* C_U`, `Z` of `R`-modules, the comparison `j : C' → C`, the
   conjugate transport `c : Z → C`, the actual class `z ∈ Z¹`, the retained duality
   `PD₁, PD₂, PD₃` with constants `ε, ε'`, and finitely many places `v` with tame local models
   `(A_v, C_v, D_v)` over `Λ` (4.4), `D_v C_v = C_v A_v`:
   * every place is primitive (`PrimitivePlace`: inertia minus one is `−2`, or `t` times a
     `Λ`-unit with nonzero central Frobenius determinants at `(t)`; tex 3755–3760, 5183–5187);
   * the cone of `j` is homotopy equivalent to the sum of the base-changed local models (tex
     3842–3846; after the switches the comparison at each derivative prime is the identity, tex
     5162–5183, so only the active and moving places remain);
   * `z` is a cocycle, and the two Leibniz rules of the duality (tex 3850–3863);
   Kind: ELLIOT/GLUE (Selmer-complex cone formalism, Nekovář 6.2.5–6.2.8 and Theorem 6.3.4,
   UNVERIFIED). Owner: batch 3 (Duality, HeegnerCohomology).
2. the terminal factorization: an integral coefficient `α ∈ R` of the actual class ("The actual
   class is integral", tex 5162), a determinant-basis unit `μ ∈ R^×` and a vector `w₀ ∈ C_U²` such
   that for every homotopy inverse `e` of `j` over `R` (`e.hom = j`), `u` is the image in `Frac Λ`
   of `α · λ_z(w₀) · μ`, with `λ_z = PD₂(−, e⁻¹ c(z))` batch 3's `pairedFunctional` ("The terminal
   coordinate is the product of the two integral coefficients, up to a determinant-basis unit",
   tex 5188–5189; Definition `ex:arith-coordinate`, tex 3877–3892, on the terminal complex
   `[R --0--> R]`, tex 5159–5161). At a cocycle `w₀` the value does not depend on `e` (batch 3's
   clause (iv), tex 3755–3758). Kind: definition + ELLIOT (integrality of the class). Owner:
   RC16 / RC15.

The integrality of `λ_z` over `R` is not assumed: it is batch 3's `pairedFunctionalHeightOne_proof`
(see `regularAtPrime_of_terminalPairedFunctional`). -/
def TerminalPairedFunctional (u : FractionRing Lambda) : Prop :=
  ∃ (CU C' C Z : CochainComplex (ModuleCat.{0} (Localization.AtPrime P)) ℤ) (j : C' ⟶ C)
    (c : Z ⟶ C) (z : Z.X 1)
    (pd1 : CU.X 1 →ₗ[Localization.AtPrime P] C'.X 2 →ₗ[Localization.AtPrime P]
      Localization.AtPrime P)
    (pd2 : CU.X 2 →ₗ[Localization.AtPrime P] C'.X 1 →ₗ[Localization.AtPrime P]
      Localization.AtPrime P)
    (pd3 : CU.X 3 →ₗ[Localization.AtPrime P] C'.X 0 →ₗ[Localization.AtPrime P]
      Localization.AtPrime P)
    (ε ε' : Localization.AtPrime P) (V : Type) (_ : Fintype V) (m : V → ℕ)
    (A Cm D : ∀ v, Matrix (Fin (m v)) (Fin (m v)) Lambda) (hDC : ∀ v, D v * Cm v = Cm v * A v)
    (n : V → ℤ),
    (∀ v, PairedFunctional.PrimitivePlace P (A v) (Cm v) (D v)) ∧
    Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (PairedFunctional.tameComplex
        (Matrix.toLin' ((A v).map (algebraMap Lambda (Localization.AtPrime P))))
        (Matrix.toLin' ((Cm v).map (algebraMap Lambda (Localization.AtPrime P))))
        (Matrix.toLin' ((D v).map (algebraMap Lambda (Localization.AtPrime P))))
        (PairedFunctional.toLin'_map_comm _ (hDC v)))⟦n v⟧)) ∧
    (Z.d 1 2).hom z = 0 ∧
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y)) ∧
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) ∧
    ∃ (α : Localization.AtPrime P) (μ : (Localization.AtPrime P)ˣ) (w₀ : CU.X 2),
      ∀ e : HomotopyEquiv C' C, e.hom = j →
        u = Localization.mapToFractionRing (FractionRing Lambda) P.primeCompl
          (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
          (α * PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z) w₀ * μ)

variable {P}

/-- **The terminal coordinate lies in `R = Λ_𝔭`** (tex 5159–5189): from
`TerminalPairedFunctional`, batch 3's `pairedFunctionalHeightOne_proof` gives a homotopy inverse of
`j` over `Λ_𝔭` itself (the paired functional has an integral closed representative at every
height-one prime `𝔭 ≠ (2)`, tex 3715–3719, 3753–3765), so `u = α · λ_z(w₀) · μ` lies in `Λ_𝔭`.
Kind: PROVED from `TerminalPairedFunctional`. -/
theorem regularAtPrime_of_terminalPairedFunctional (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2}) {u : FractionRing Lambda} (h : TerminalPairedFunctional P u) :
    RegularAtPrime P u := by
  obtain ⟨CU, C', C, Z, j, c, z, pd1, pd2, pd3, ε, ε', V, _, m, A, Cm, D, hDC, n, hplace, hcone,
    hz, hL1, hL2, α, μ, w₀, hu⟩ := h
  obtain ⟨e, he, -, -, -, -⟩ := PairedFunctional.pairedFunctionalHeightOne_proof P hP hne CU C' C
    Z j c z pd1 pd2 pd3 ε ε' V m A Cm D hDC n hplace hcone hz hL1 hL2
  exact ⟨_, (hu e he).symm⟩

end HeightOne

/-- **RC16's height-one switching process at `𝔭`, terminal step through batch 3's paired
functional** (tex 4976–5191). The fields `Stage`, `fiberDim`, `mixed`, `coord`, `pos`,
`switch_mixed`, `switch_single` are those of RC16's `RegularitySwitchProcess (RegularAtPrime 𝔭)`
verbatim (ELLIOT steps; their algebra is RC16's `KernelDetection`, `Switch`, `QuadraticCase`); the
field `terminal` is `TerminalPairedFunctional 𝔭 (coord S)` in place of RC16's `Reg (coord S)`. -/
structure RegularitySwitchProcessPF (P : Ideal Lambda) [P.IsPrime] where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The fiber dimension `s = dim_k H¹(C ⊗_R k)`. -/
  fiberDim : Stage → ℕ
  /-- Both cohomology signs occur (or the specialization is nonquadratic). -/
  mixed : Stage → Prop
  /-- The class-functional coordinate of the actual class. -/
  coord : Stage → FractionRing Lambda
  /-- tex 4986–4992, 5154–5157: `s ≥ 1`. -/
  pos : ∀ S, 1 ≤ fiberDim S
  /-- tex 4997–5003, 5116–5122 (switch factor in `R`: valuation preservation, 5137–5153): mixed
  signs, one switch lowers `s` by two. -/
  switch_mixed : ∀ S, mixed S → 1 < fiberDim S →
    ∃ S', fiberDim S' + 2 = fiberDim S ∧ ∃ w, RegularAtPrime P w ∧ coord S = w * coord S'
  /-- tex 5123–5136 (switch factor in `R`, 5137–5153): one sign only, the first switch introduces
  the other sign, same `s`. -/
  switch_single : ∀ S, ¬ mixed S → 1 < fiberDim S →
    ∃ S', fiberDim S' = fiberDim S ∧ mixed S' ∧ ∃ w, RegularAtPrime P w ∧ coord S = w * coord S'
  /-- tex 5159–5189: the terminal step through the paired functional. -/
  terminal : ∀ S, fiberDim S = 1 → TerminalPairedFunctional P (coord S)

/-- RC16's `RegularitySwitchProcess (RegularAtPrime 𝔭)` from the refined process, at a height-one
prime `𝔭 ≠ (2)`; the terminal field is `regularAtPrime_of_terminalPairedFunctional`.
Kind: PROVED. -/
def RegularitySwitchProcessPF.toProcess {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2}) (Pr : RegularitySwitchProcessPF P) :
    RegularitySwitchProcess (RegularAtPrime P) where
  Stage := Pr.Stage
  fiberDim := Pr.fiberDim
  mixed := Pr.mixed
  coord := Pr.coord
  pos := Pr.pos
  switch_mixed := Pr.switch_mixed
  switch_single := Pr.switch_single
  terminal := fun S hS => regularAtPrime_of_terminalPairedFunctional hP hne (Pr.terminal S hS)

/-- **The height-one regularity inputs for a coordinate `u ∈ Frac Λ`** (tex 4976–5200): either
`u = 0` ("If its actual generic class is zero, its coordinate is zero", tex 5196–5197), or at every
height-one prime `𝔭 ≠ (2)` of `Λ` a refined switching process starts at `u` ("use the actual
primitive scalar Selmer complex over `R`", tex 4976–4980; also at the unknown base, tex 5196–5200).
Kind: ELLIOT (the processes; see `RegularitySwitchProcessPF`). -/
def RegularityInputs (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ (Pr : RegularitySwitchProcessPF P) (S₀ : Pr.Stage), Pr.coord S₀ = u

/-- `RegularityInputs u` is the hypothesis `regular` of RC16's `mem_lambdaHalf_of_regularity` and
`exLimitsUniformLowerBound`, with RC16's processes. Kind: PROVED. -/
theorem RegularityInputs.rc16 {u : FractionRing Lambda} (h : RegularityInputs u) :
    u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u := by
  rcases h with h0 | h
  · exact Or.inl h0
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Pr, S₀, hS₀⟩ := h P hP hne
    exact ⟨Pr.toProcess hP hne, S₀, hS₀⟩

/-- **`u ∈ Λ[1/2]` from the regularity inputs** (tex 4976–5200): RC16's
`mem_lambdaHalf_of_regularity` (the descent `regular_of_switchProcess` at every height-one prime and
the intersection formula `Λ[1/2] = ⋂_{𝔭 ≠ (2)} Λ_𝔭`, tex 5190–5194). Kind: PROVED from the
inputs. -/
theorem RegularityInputs.mem_lambdaHalf {u : FractionRing Lambda} (h : RegularityInputs u) :
    u ∈ lambdaHalfToFrac.range :=
  mem_lambdaHalf_of_regularity u h.rc16

/-! ## (a) `HeightOneTarget` -/

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **(a), the algebra: `ũ_x ∈ Λ[1/2]` from `u_{prim,x} ∈ Λ[1/2]` and (4.7)** (tex 4142–4152,
5192–5194, 5703–5704: "Both `ũ_x` and `ũ_0` lie in `Λ[1/2]` by the height-one argument above").
By (4.7) (`CommonCoordinateTarget D`, Lemma `ex:arith-common-coordinate`), `ũ_x = ε_x u_{prim,x}`
with `ε_x ∈ Λ^×`, and a `Λ`-multiple of an element of `Λ[1/2]` lies in `Λ[1/2]`
(`inLamHalf_lamUnit_mul`). Kind: PROVED. -/
theorem heightOneTarget_of_prim
    (hprim : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x))
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D := by
  intro Co Ce F hF x
  obtain ⟨ε, hε, hu⟩ := h47 Co Ce F hF x
  rw [hu]
  exact inLamHalf_lamUnit_mul hε (hprim Co Ce F hF x)

/-- **RC16's remaining hypotheses for the primitive coordinates of the final families**
(height-one regularity, Proposition `ex:limits-uniform-lower-bound`, tex 4976–5200, at the ring
instances `(h_x, k)` of the final field `K = ℚ(√k)`; at `x = 0`, the unknown full-corank-one base,
tex 5196–5200). For every final family `F` (any `C_o, C_e`) and every address `x` there is
`u ∈ Frac Λ` with the following conjuncts (tex; kind; owner):

1. `IsTExpansion u (D.uPrim F x)`: the interface's `u_{prim,x} ∈ ℚ₂[[t]]` is the `t`-expansion of
   the generic class-functional coordinate `u ∈ Frac Λ` of the actual primitive constituent at
   `x`. Tex 3877–3892 (the coordinate), 3895–3985 (regular at the centre); GLUE (interface
   identification); owner RC0 (interface data), with RC15 (`Central.coord_specializes`).
2. `RegularityInputs u`, i.e. one of:
   * `u = 0` (the actual generic class is zero). Tex 5196–5197; ELLIOT; owner RC15 / RC16.
   * at every height-one prime `𝔭 ≠ (2)`, a `RegularitySwitchProcessPF 𝔭` starting at `u` (the
     actual primitive scalar Selmer complex over `R = Λ_𝔭`). Tex 4976–4980; ELLIOT; owner RC16
     (algebra) and batch 3 (Selmer complexes). Its fields:
     - `pos`, `s ≥ 1`. Tex 4986–4992, 5154–5157; ELLIOT; owner batch 3 (HeegnerCohomology),
       RC16.
     - `switch_mixed`, `s ↦ s − 2` with switch factor in `R`. Tex 4997–5003, 5116–5122,
       5137–5153; ELLIOT; owner batch 3, with RC16's algebra (`KernelDetection`,
       `Switch.relaxed_image_eq_span`, `Switch.switch_equal_valuation`).
     - `switch_single`, one sign: `s` kept, the next configuration mixed, switch factor in `R`.
       Tex 5123–5136, 5137–5153; ELLIOT; owner batch 3, with RC16's algebra (`QuadraticCase`).
     - `terminal`, first part: the cone hypothesis of `PairedFunctionalHeightOne` (primitive
       places, cone = sum of the local models, `z` a cocycle, Leibniz rules). Tex 3755–3760,
       3842–3846, 5162–5187; ELLIOT/GLUE (Nekovář 6.2.5–6.2.8, Thm 6.3.4, UNVERIFIED); owner
       batch 3 (Duality, HeegnerCohomology).
     - `terminal`, second part: `u_S = α · λ_z(w₀) · μ` for every integral inverse of `j`. Tex
       5159–5162, 5188–5189; definition + ELLIOT; owner RC16 / RC15.

Discharged here (not inputs): the integrality of the paired functional over `Λ_𝔭` (batch 3,
`pairedFunctionalHeightOne_proof`), the descent and the intersection formula (RC16,
`mem_lambdaHalf_of_regularity`), and the transfer to `ℚ₂[[t]]` (`inLamHalf_of_isTExpansion`).
Non-vacuity: `primRegularityInputs_iff`. -/
def PrimRegularityInputs : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputs u

/-- **(a), the primitive clause: `u_{prim,x} ∈ Λ[1/2]`** at every address of every final family
(tex 4976–5200), from `PrimRegularityInputs D`: RC16's `mem_lambdaHalf_of_regularity` (with batch
3's `pairedFunctionalHeightOne_proof` at the terminal step), then `inLamHalf_of_isTExpansion`.
Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputs (h : PrimRegularityInputs D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **(a): `RCSteps.height_one`** (tex 4909–5205, 5703–5704) from `PrimRegularityInputs D` and
(4.7). Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputs (h : PrimRegularityInputs D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputs D h) h47

end HeightOneTarget

/-! ## The outer switching process with an integral terminal functional -/

/-- **RC16's outer switching process, terminal functional in integral form** (tex 4927–4964). The
fields `Stage`, `outerDim`, `coord`, `pos`, `switch` are those of RC16's `OuterSwitchProcess`
verbatim (ELLIOT: tex 4938–4940 and 4950–4952; 4940–4950). In the field `terminal` (tex
4957–4961) the functional coefficient `β_j` of the Schur/Cramer formula `u_j Δ_j = ±α_j β_j` is the
value `φ_j(λ_j(x_j))` of an integral functional `λ_j : X_j → R_j` (the integral representative of
the paired functional, exponent `a = 0`, tex 3864–3869), with `φ_j : R_j → K` landing in the
valuation ring; RC16's hypothesis `hβ` (`v β_j ≥ −a`, gap B2-b) is then batch 3's
`functionalExponentBound_proof` (`OuterSwitchProcessPF.toProcess`). -/
structure OuterSwitchProcessPF {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {ι : Type}
    (𝒰 : Ultrafilter ι) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The outer kernel dimension `s` of a configuration. -/
  outerDim : Stage → ℕ
  /-- The inner class-functional coordinates `u_j` of a configuration. -/
  coord : Stage → ι → K
  /-- tex 4938–4940, 4950–4952: the outer kernel dimension is at least one. -/
  pos : ∀ S, 1 ≤ outerDim S
  /-- tex 4940–4950: a switch lowers the outer dimension by two and keeps the inner valuations. -/
  switch : ∀ S, 1 < outerDim S → ∃ S', outerDim S' + 2 = outerDim S ∧
    ∀ᶠ j in (𝒰 : Filter ι), v (coord S' j) = v (coord S j)
  /-- tex 4957–4961: the terminal Schur/Cramer data, with an integral functional coefficient. -/
  terminal : ∀ S, outerDim S = 1 → ∃ (α Δ s : ι → K), (∀ j, s j = 1 ∨ s j = -1) ∧
    (∃ (R : ι → Type) (_ : ∀ j, CommRing (R j)) (φ : ∀ j, R j →+* K),
      (∀ j r, (0 : WithTop ℤ) ≤ v (φ j r)) ∧
      ∃ (X : ι → Type) (_ : ∀ j, AddCommGroup (X j)) (_ : ∀ j, Module (R j) (X j))
        (lam : ∀ j, X j →ₗ[R j] R j) (x : ∀ j, X j),
        ∀ᶠ j in (𝒰 : Filter ι), coord S j * Δ j = s j * (α j * φ j (lam j (x j)))) ∧
    (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j)) ∧
    (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j)) ∧
    ¬ OuterNegligible v 𝒰 Δ

/-- RC16's `OuterSwitchProcess v 𝒰 a` (for every exponent `a`) from the refined process: the
hypothesis `hβ` of the terminal field is batch 3's `functionalExponentBound_proof`.
Kind: PROVED. -/
def OuterSwitchProcessPF.toProcess {K : Type} [Field K] {v : AddValuation K (WithTop ℤ)}
    {ι : Type} {𝒰 : Ultrafilter ι} (P : OuterSwitchProcessPF v 𝒰) (a : ℕ) :
    OuterSwitchProcess v 𝒰 a where
  Stage := P.Stage
  outerDim := P.outerDim
  coord := P.coord
  pos := P.pos
  switch := P.switch
  terminal := fun S hS => by
    obtain ⟨α, Δ, s, hs, ⟨R, _, φ, hφ, X, _, _, lam, x, hcr⟩, hα, hΔi, hΔ⟩ := P.terminal S hS
    exact ⟨α, fun j => φ j (lam j (x j)), Δ, s, hs, hcr, hα,
      PairedFunctional.functionalExponentBound_proof K v ι 𝒰 R φ hφ X lam x a, hΔi, hΔ⟩

/-! ## (b) `Eq35Target` -/

/-- **A ring instance of (3.5) with `ω(k') ≤ A`** (tex 2403–2446): a known simple zero `h` of the
prepared filter and a rough companion `k'` of `h` (the form of lane RC13's `roughCompanion`) with
`ω(k') ≤ A`. Kind: definition. -/
structure CompanionPair {ℓ : ℕ} (W : WData ℓ) (A : ℕ) : Type where
  /-- the known simple zero `h` -/
  h : ℤ
  /-- the rough companion `k'` -/
  k : ℤ
  /-- `h` lies in the prepared filter -/
  prepared : W.prepared h
  /-- `ord_{s=1} L(E^{(h)}, s) = 1` -/
  simpleZero : AnalyticRank (Etw ℓ h) 1
  /-- `k'` is a rough companion of `h` -/
  rough : W.IsRoughCompanion h k
  /-- `ω(k') ≤ A` -/
  omega_le : (omega k : ℤ) ≤ A

section Eq35

variable {ℓ : ℕ} (W : WData ℓ)

/-- **RC16's remaining hypotheses for (3.5)** (Proposition `ex:limits-uniform-lower-bound`, tex
4909–5202, at the ring instances `(h, k')` of Proposition `ex:sec7-genus-lower`, tex 2418–2446:
`h` a known simple zero of the prepared filter, `k'` a rough companion, `K' = ℚ(√k')`).
Conjuncts (tex; kind; owner):

1. A field `K = Frac 𝒪`, the valuation `v = v₂` of `𝒪 = (Λ_(2))^` and `ι : Frac Λ → K` with
   `ValuationOfO v ι` (on `Frac Λ`, `v` is the valuation of the DVR `Λ_(2)`, `v 2 = 1`). Tex
   3727–3728, 4918; GLUE (Matsumura, Commutative Ring Theory, Thm 11.5, UNVERIFIED); owner
   RC16 / RC6.
2. Data `uprim h k' ∈ Frac Λ`: the generic primitive class-functional coordinate of the ring
   instance `(h, k')`. Tex 3877–3892, 4911–4913; definition (data); owner RC15.
3. Data `C₀`: the error of (4.6), independent of `(h, k')` (and of `A`). Tex 3999–4000;
   definition (data); owner RC15.
4. Regularity: `RegularityInputs (uprim h k')` at every companion pair (fields as in
   `PrimRegularityInputs`). Tex 4976–5194; ELLIOT, and ELLIOT/GLUE for the cone; owner RC16,
   batch 3.
5. (4.6) at every companion pair: for the element `uh ∈ Λ[1/2]` representing `uprim h k'`,
   `v₂ uh(0) = 2 j_rc(h, k') − 4ω(h) − s(h) − s(hk') − Σ_{p ∣ k'} t_p + err` with `|err| ≤ C₀`.
   Tex 3987–4047 (statement 3987–4004, display 4045); ELLIOT, resting on GLUE (Kolyvagin Thm 1,
   cited statement) and PRINTs (Milne ADT I.7.3, Edixhoven Thm 5.3); owner RC15
   (`Central.calibration_46`), RC9. It contains:
   * `t_p ≤ 2` (`t : ℕ → ℕ`, so `0 ≤ t_p`). Tex 4000–4001, 4039; ELLIOT; owner RC15.
   * `uh(0) ≠ 0` (`v₂` is finite, `v2 0 = ⊤`): the central class is nonzero at a known simple
     zero. Tex 4928–4930; ELLIOT; owner RC15.
   * the link of RC16's integers `j_rc, ω, s(h), s(hk')` with `W.jrc h k'`, `omega h`,
     `sFun ℓ h`, `sFun ℓ (h * k')`, and of RC16's finset `P` with the primes of `k'`
     (`|P| = ω(k') ≤ A`, `card_primeFactors_natAbs`). Tex 2411–2416, 1828–1830; definition (no
     hypothesis); owner RC0 (interface).
6. Outer processes: for every `A` and every sequence of companion pairs with `ω(k') ≤ A`, an
   `OuterSwitchProcessPF v (hyperfilter ℕ)` whose starting inner coordinates have the valuations
   of `ι (uprim h_j k'_j)` on an outer-large set. Tex 4927–4964 (with (5.1) 4453–4648, (5.3)
   4724, (5.4) 4823, the switch lemma 4834–4907); ELLIOT; owner RC6 (outer DVR, (5.1)), batch 3
   (RankCounts, HeegnerCohomology), RC16 (algebra). Its field `terminal` has an integral
   functional coefficient (exponent `a = 0`): tex 4957–4961, 3864–3869; ELLIOT; owner batch 3
   (PairedFunctional).

The hypotheses of (4.6) hold at a companion pair: every prime of `h` splits in `ℚ(√k')` and
`L(E^{(hk')}, 1) ≠ 0` (`W.IsRoughCompanion h k'`), and `h` is a known simple zero. Discharged
here (not inputs): `hβ` (batch 3, `functionalExponentBound_proof`), the height-one terminal
integrality (batch 3, `pairedFunctionalHeightOne_proof`), (5.5), `u_prim ∈ Λ[1/2]` and
(5.5) + (4.6) ⇒ (3.5) (RC16, `exLimitsUniformLowerBound`). -/
def Eq35Inputs : Prop :=
  ∃ (K : Type) (_ : Field K) (v : AddValuation K (WithTop ℤ)) (ι : FractionRing Lambda →+* K),
    ValuationOfO v ι ∧
    ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
      (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
        RegularityInputs (uprim h k')) ∧
      (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
        ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
          ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
            v2 (centralSpecialization uh) =
              ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
                ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
      (∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
        ∃ (P : OuterSwitchProcessPF v (Filter.hyperfilter ℕ)) (S₀ : P.Stage),
          ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
            v (P.coord S₀ j) = v (ι (uprim (inst j).h (inst j).k)))

/-- `v₂ c` equals an integer `n` iff `c ≠ 0` and `v₂(c) = n`. Kind: PROVED. -/
theorem v2_eq_coe_iff {c : ℚ_[2]} {n : ℤ} :
    v2 c = (n : WithTop ℤ) ↔ c ≠ 0 ∧ Padic.valuation c = n := by
  constructor
  · intro h
    have hc : c ≠ 0 := by
      rintro rfl
      rw [v2, AddValuation.map_zero] at h
      exact WithTop.top_ne_coe h
    refine ⟨hc, ?_⟩
    rw [v2, Padic.addValuation.apply hc] at h
    exact_mod_cast h
  · rintro ⟨hc, h⟩
    rw [v2, Padic.addValuation.apply hc, h]

/-- `|{p prime : p ∣ k}| = ω(k)`. Kind: PROVED. -/
theorem card_primeFactors_natAbs (k : ℤ) : k.natAbs.primeFactors.card = omega k := by
  unfold ZInQ.Manuscript.RC.omega
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- **(b): (3.5) for each fixed `A` at the rough companions** (tex 2441–2446, 5200–5202), the form
of batch 3's `FinalFamilyField` input, from `Eq35Inputs W`. For each `A`, RC16's
`exLimitsUniformLowerBound` over the instances `CompanionPair W A` (outer processes via
`OuterSwitchProcessPF.toProcess`, regularity via `RegularityInputs.rc16`) gives (5.5) with a
constant `C` and, with (4.6), (3.5) with `C_R(E, A) = C + C₀ + 2A` (Elliot's route through
`Σ_{p ∣ k'} t_p ≤ 2A`). Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputs (hin : Eq35Inputs W) : Eq35Target W := by
  obtain ⟨K, _, v, ι, hO, uprim, C₀, hreg, h46, houter⟩ := hin
  intro A
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound v ι hO A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => by
      obtain ⟨P, S₀, hS₀⟩ := houter A inst
      exact ⟨0, P.toProcess 0, S₀, hS₀⟩)
    (fun i => (hreg i.h i.k i.prepared i.simpleZero i.rough).rc16)
  refine ⟨(C : ℤ) + (C₀ + 2 * (A : ℤ)), ?_⟩
  intro h k' hprep hrank hrough hω
  obtain ⟨uh, huh, -, h35⟩ := hC ⟨h, k', hprep, hrank, hrough, hω⟩
  obtain ⟨t, err, ht, herr, hv⟩ := h46 h k' hprep hrank hrough uh huh
  obtain ⟨hne, hval⟩ := v2_eq_coe_iff.mp hv
  have hcard : k'.natAbs.primeFactors.card ≤ A := by
    have := card_primeFactors_natAbs k'
    omega
  have h46' : |Padic.valuation (centralSpecialization uh) -
      (2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
        ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ))| ≤ C₀ := by
    rw [hval]
    convert herr using 2
    ring
  have key := h35 (W.jrc h k') (omega h : ℤ) (sFun ℓ h) (sFun ℓ (h * k')) C₀
    k'.natAbs.primeFactors (fun p => (t p : ℤ)) hne
    (fun p _ => ⟨Int.natCast_nonneg _, by exact_mod_cast ht p⟩) hcard h46'
  linarith

end Eq35

/-! ## Non-vacuity

The refined inputs are satisfiable whenever their conclusions hold (so they are not contradictory),
and the refined terminal step is equivalent to RC16's: at a height-one prime `𝔭 ≠ (2)`,
`TerminalPairedFunctional 𝔭 u ↔ RegularAtPrime 𝔭 u` (`terminalPairedFunctional_iff`). The witness
for `←` is the model with `R` in degree one (`C' = C = Z`, `j = c = 𝟙`), `R` in degree two
(`C_U`), `PD₂` the multiplication and no places; the value of `λ_z` does not depend on the integral
inverse by batch 3's `pairedFunctional_sub_eq_coboundary`. In particular
`RegularityInputs u ↔ u ∈ Λ[1/2]` (`regularityInputs_iff`, one-stage processes) and
`PrimRegularityInputs D` holds exactly when every `u_{prim,x}` of every final family lies in
`Λ[1/2]` (`primRegularityInputs_iff`). As for RC16's own process structures, these are abstract
interfaces: their content is the form in which the switching steps are discharged, not extra
logical strength. `OuterSwitchProcessPF` is inhabited (`trivialOuterSwitchProcessPF`). The GLUE
`ValuationOfO` of `Eq35Inputs` is the genuine `2`-adic valuation of `Λ_(2)`, which is not
constructed in Lean (Mathlib has no `ℤ`-valued valuation of `Λ_(2)`); so the
satisfiability of `Eq35Inputs` as a whole is not checked here. -/

section NonVacuity

open CategoryTheory CategoryTheory.Limits

/-- The complex with `R = Λ_𝔭` in degree `d` and zero elsewhere (for the non-vacuity model).
Kind: definition. -/
abbrev singleAtPrime (P : Ideal Lambda) [P.IsPrime] (d : ℤ) :
    CochainComplex (ModuleCat.{0} (Localization.AtPrime P)) ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} (Localization.AtPrime P)) (ComplexShape.up ℤ) d).obj
    (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P))

/-- Its degree-`d` term is `R`. Kind: definition. -/
abbrev singleAtPrimeIso (P : Ideal Lambda) [P.IsPrime] (d : ℤ) :
    (singleAtPrime P d).X d ≅ ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) d _

variable {P : Ideal Lambda} [P.IsPrime]

/-- **The refined terminal step holds at every regular coordinate** (non-vacuity of
`TerminalPairedFunctional`): at a height-one prime `𝔭 ≠ (2)`, every `u ∈ Λ_𝔭` satisfies it, with
the model described above. Kind: PROVED. -/
theorem terminalPairedFunctional_of_regularAtPrime (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    {u : FractionRing Lambda} (hu : RegularAtPrime P u) : TerminalPairedFunctional P u := by
  obtain ⟨r, rfl⟩ := hu
  let R := Localization.AtPrime P
  let pd2 : (singleAtPrime P 2).X 2 →ₗ[R] (singleAtPrime P 1).X 1 →ₗ[R] R :=
    (LinearMap.mul R R).compl₁₂ (singleAtPrimeIso P 2).hom.hom (singleAtPrimeIso P 1).hom.hom
  have hpd2 : ∀ w y, pd2 w y =
      (singleAtPrimeIso P 2).hom.hom w * (singleAtPrimeIso P 1).hom.hom y := fun _ _ => rfl
  have hL2 : ∀ (w : (singleAtPrime P 2).X 2) (y : (singleAtPrime P 1).X 0),
      pd2 w (((singleAtPrime P 1).d 0 1).hom y) =
        (0 : R) * (0 : (singleAtPrime P 2).X 3 →ₗ[R] (singleAtPrime P 1).X 0 →ₗ[R] R)
          (((singleAtPrime P 2).d 2 3).hom w) y := by
    intro w y
    rw [HomologicalComplex.single_obj_d]
    simp
  refine ⟨singleAtPrime P 2, singleAtPrime P 1, singleAtPrime P 1, singleAtPrime P 1, 𝟙 _, 𝟙 _,
    (singleAtPrimeIso P 1).inv.hom (1 : R), 0, pd2, 0, 0, 0, PEmpty, inferInstance, fun _ => 0,
    fun v => v.elim, fun v => v.elim, fun v => v.elim, fun v => v.elim, fun v => v.elim,
    fun v => v.elim, ?_, ?_, ?_, hL2, r, 1, (singleAtPrimeIso P 2).inv.hom (1 : R), ?_⟩
  · exact PairedFunctional.heightOne_cone_hypothesis_satisfiable P hP hne _ PEmpty (fun _ => 0)
      (fun v => v.elim) (fun v => v.elim) (fun v => v.elim) (fun v => v.elim) (fun v => v.elim)
      (fun v => v.elim)
  · rw [HomologicalComplex.single_obj_d]
    rfl
  · intro w y
    rw [HomologicalComplex.single_obj_d]
    simp
  · intro e he
    have hcz : ((singleAtPrime P 1).d 1 2).hom
        (((𝟙 (singleAtPrime P 1) : singleAtPrime P 1 ⟶ singleAtPrime P 1).f 1).hom
          ((singleAtPrimeIso P 1).inv.hom (1 : R))) = 0 := by
      rw [HomologicalComplex.single_obj_d]
      rfl
    obtain ⟨y, hy⟩ := PairedFunctional.pairedFunctional_sub_eq_coboundary pd2 0 0 hL2 e
      (HomotopyEquiv.refl _) he hcz
    have h1 := hy ((singleAtPrimeIso P 2).inv.hom (1 : R))
    simp only [LinearMap.zero_apply, mul_zero, sub_eq_zero] at h1
    rw [h1]
    simp [PairedFunctional.pairedFunctional_apply, HomotopyEquiv.refl, hpd2]

/-- **The refined terminal step is equivalent to RC16's** at a height-one prime `𝔭 ≠ (2)`.
Kind: PROVED (`→`: batch 3's `pairedFunctionalHeightOne_proof`; `←`: the model above). -/
theorem terminalPairedFunctional_iff (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (u : FractionRing Lambda) : TerminalPairedFunctional P u ↔ RegularAtPrime P u :=
  ⟨regularAtPrime_of_terminalPairedFunctional hP hne,
    terminalPairedFunctional_of_regularAtPrime hP hne⟩

/-- The one-stage refined process at a coordinate `u ∈ Λ_𝔭` (fiber dimension one).
Kind: definition (non-vacuity). -/
def RegularitySwitchProcessPF.ofRegular (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (u : FractionRing Lambda) (hu : RegularAtPrime P u) : RegularitySwitchProcessPF P where
  Stage := Unit
  fiberDim := fun _ => 1
  mixed := fun _ => True
  coord := fun _ => u
  pos := fun _ => le_rfl
  switch_mixed := fun _ _ h => absurd h (lt_irrefl 1)
  switch_single := fun _ _ h => absurd h (lt_irrefl 1)
  terminal := fun _ _ => terminalPairedFunctional_of_regularAtPrime hP hne hu

/-- **`RegularityInputs u ↔ u ∈ Λ[1/2]`** (non-vacuity of the regularity inputs). Kind: PROVED
(`→`: RC16's `mem_lambdaHalf_of_regularity`; `←`: one-stage processes, using RC16's intersection
formula `mem_range_lambdaHalf_iff_forall_height_one`). -/
theorem regularityInputs_iff (u : FractionRing Lambda) :
    RegularityInputs u ↔ u ∈ lambdaHalfToFrac.range := by
  refine ⟨fun h => h.mem_lambdaHalf, fun hu => Or.inr fun P _ hP hne => ?_⟩
  have hreg : RegularAtPrime P u := (mem_range_lambdaHalf_iff_forall_height_one u).mp hu P hP hne
  exact ⟨RegularitySwitchProcessPF.ofRegular hP hne u hreg, (), rfl⟩

/-- Every element of `Λ[1/2]` in `ℚ₂[[t]]` is the `t`-expansion of an element of `Λ[1/2] ⊂ Frac Λ`.
Kind: PROVED. -/
theorem exists_isTExpansion_of_inLamHalf {U : PowerSeries ℚ_[2]} (hU : InLamHalf U) :
    ∃ u : FractionRing Lambda, IsTExpansion u U ∧ u ∈ lambdaHalfToFrac.range := by
  obtain ⟨e, G, rfl⟩ := (inLamHalf_iff U).mp hU
  set w : LambdaHalf := IsLocalization.Away.invSelf (2 : Lambda)
  have hw : algebraMap Lambda LambdaHalf 2 * w = 1 := IsLocalization.Away.mul_invSelf 2
  have hkey : algebraMap Lambda LambdaHalf G * w ^ e * algebraMap Lambda LambdaHalf (2 ^ e) =
      algebraMap Lambda LambdaHalf G := by
    rw [map_pow, mul_assoc, ← mul_pow, mul_comm w, hw, one_pow, mul_one]
  refine ⟨lambdaHalfToFrac (algebraMap Lambda LambdaHalf G * w ^ e),
    ⟨G, 2 ^ e, pow_ne_zero _ prime_two_lambda.ne_zero, ?_, ?_⟩, ⟨_, rfl⟩⟩
  · rw [← AlgHom.commutes lambdaHalfToFrac (2 ^ e), ← AlgHom.commutes lambdaHalfToFrac G,
      ← map_mul, hkey]
  · rw [lamIncl_two_pow, mul_comm, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), map_one, one_mul]

/-- **`PrimRegularityInputs D` holds exactly when every primitive coordinate of every final family
lies in `Λ[1/2]`** (non-vacuity of (a)'s inputs). Kind: PROVED. -/
theorem primRegularityInputs_iff {ℓ : ℕ} (D : RCData ℓ) :
    PrimRegularityInputs D ↔ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, InLamHalf (D.uPrim F x) := by
  refine ⟨primLambdaHalf_of_inputs D, fun h Co Ce F hF x => ?_⟩
  obtain ⟨u, hT, hu⟩ := exists_isTExpansion_of_inLamHalf (h Co Ce F hF x)
  exact ⟨u, hT, (regularityInputs_iff u).mpr hu⟩

end NonVacuity

/-- `v₂ ≥ 0` on `ℤ₂`. Kind: PROVED. -/
theorem zero_le_addValuation_coe (r : ℤ_[2]) :
    (0 : WithTop ℤ) ≤ Padic.addValuation (r : ℚ_[2]) := by
  by_cases hr : (r : ℚ_[2]) = 0
  · rw [hr, AddValuation.map_zero]
    exact le_top
  · rw [Padic.addValuation.apply hr]
    have h0 : (0 : ℤ) ≤ (r : ℚ_[2]).valuation := PadicInt.valuation_coe_nonneg
    exact_mod_cast h0

/-- **Non-vacuity of `OuterSwitchProcessPF`**: over `ℚ₂` with its `2`-adic valuation, the
one-configuration process with outer dimension one, coordinate `1`, terminal data
`α = Δ = s = 1` and the functional `id : ℤ₂ → ℤ₂` at `1` (with `ℤ₂ ⊂ ℚ₂`). Kind: PROVED. -/
def trivialOuterSwitchProcessPF {ι : Type} (𝒰 : Ultrafilter ι) :
    OuterSwitchProcessPF (Padic.addValuation (p := 2)) 𝒰 where
  Stage := Unit
  outerDim := fun _ => 1
  coord := fun _ _ => 1
  pos := fun _ => le_rfl
  switch := fun _ h => absurd h (lt_irrefl 1)
  terminal := fun _ _ => by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => Or.inl rfl,
      ⟨fun _ => ℤ_[2], fun _ => inferInstance, fun _ => PadicInt.Coe.ringHom,
        fun _ r => zero_le_addValuation_coe r, fun _ => ℤ_[2], fun _ => inferInstance,
        fun _ => inferInstance, fun _ => LinearMap.id, fun _ => 1,
        Eventually.of_forall fun _ => ?_⟩, ?_, ?_, ?_⟩
    · simp
    · exact Eventually.of_forall (fun _ => by rw [AddValuation.map_one])
    · exact Eventually.of_forall (fun _ => by rw [AddValuation.map_one])
    · intro h
      obtain ⟨j, hj⟩ := (h 1).exists
      rw [AddValuation.map_one] at hj
      exact absurd hj (by exact_mod_cast (by norm_num : ¬ (1 : ℤ) ≤ 0))

end ZInQ.Manuscript.RC.Wiring
