import ZInQKernel.Contrib.RC53Assist.TateReduction.Comparison
import ZInQKernel.Contrib.RC53Assist.DetDegree.Reduction
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# The global good-reduction trace reading

This module proves `GlobalGoodReductionTraceReading` of `NewformGlueG0/GaloisCompletion.lean`
exactly as stated (`globalGoodReductionTraceReading_proved`). Let `E/ℚ` be an elliptic curve with
good reduction at a prime `p`, and let `ℓ ≠ p` be prime. Then:

* every element of the inertia group of every place of `\bar ℚ` above `p` acts trivially on the
  actual rational Tate module `ℚ_ℓ ⊗ T_ℓ(E/\bar ℚ)` (Silverman, *The Arithmetic of Elliptic
  Curves*, VII.4.1 and the easy direction of VII.7.1);
* every integral-closure Frobenius `g` at `p` acts on it with trace `a_p(E)` (the existing
  `WeierstrassCurve.LFunction` coefficient) and determinant `p` (Silverman V.2.3.1 and VII.7.1).

## Route

The global Galois action is compared with reduction directly at a place `v` of `\bar ℚ` above
`p`, a valuation subring of `\bar ℚ`, rather than through an embedding into `\bar ℚ_p`: the residue
field of `v` is an algebraic closure of `𝔽_p`, the decomposition group of `v` acts on it, and
reduction of points at `v` is defined over `\bar ℚ` once `E` has a good integral model with
*rational* coefficients. This avoids identifying decomposition groups of `\bar ℚ` with
`Gal(\bar ℚ_p / ℚ_p)`.

1. *A rational model with the minimal reduction* (`exists_rationalModel`): density of `ℚ` in
   `ℚ_p` approximates the minimal change of variables over `ℚ_p` by a rational one, up to an
   integral change of variables reducing to the identity.
2. *Reduction at a place* (`placeReductionHom`): a bijection on prime-to-`p` torsion
   (`placeReductionHom_bijOn`, from the proved `ModularWeil.reduceHom_bijOn_torsion`), carrying an
   arithmetic Frobenius at `v` to the `p`-power Frobenius (`placeReductionHom_frobenius`) and
   unchanged by inertia (`placeReductionHom_inertia`).
3. *Tate modules* (`placeTateEquiv`): inertia acts trivially
   (`integralTateRep_eq_one_of_mem_inertiaSubgroup`), and the proved determinant form
   `DetDegree.frobeniusTateDetFormOne_proved` of the `p`-power Frobenius on `T_ℓ(Ẽ/\bar 𝔽_p)`
   transfers to the global Frobenius (`integralTateRep_trace_det`, `rationalTateRep_trace_det`).

The local dictionary premise `GoodReductionFrobeniusTraceDictionaryQ` of the reading is not needed
by this proof; its own ingredients (the generic residue-field lemmas of
`TateReduction/Comparison.lean`, the reduction library and the determinant form) are reused at the
global place. The excluded invariant-space representation assembly is recorded only as
historical text in `docs/research/g0-representation-route-invariants.md`; none of its false
local readings is used by the good-prime proofs here.

## Classification

Definitions and PROVED; no prints and no new inputs. Infrastructure: Mathlib (minimal models,
changes of variables, completions, valuation subrings, decomposition and inertia groups), the
vendored Tau Ceti library (Tate modules and their Galois representation, points under a change of
variables and along algebra equivalences), and the reduction library used in
`ModularWeil/ReductionInjective.lean`.
-/


noncomputable section

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve IsLocalRing
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped WithZero Topology

/-!
## Part 1. A rational Weierstrass model with the minimal reduction at a prime

Let `E/ℚ` be a Weierstrass curve and `p` a prime. The minimal model of `E` over `ℤ_p`
(Mathlib's `WeierstrassCurve.minimal`, Silverman VII.1) is obtained by a change of variables
`C = (u, r, s, t)` with coefficients in `ℚ_p`. This part proves that a change of variables
`C'` with *rational* coefficients does as well: the curve `C' • E` over `ℚ` has, after base change
to `ℚ_p`, an integral model over `ℤ_p` whose reduction is exactly the minimal reduction
`reducedCurveQ E p` (`exists_rationalModel`).

### The argument

The rationals are dense in `ℚ_p` (`exists_rat_valued_sub_lt`). Choose rationals `a, b, c, d`
with `|a - u| < |u|`, `|b - r| < |u|²`, `|c - s| < |u|` and `|d - t - s (b - r)| < |u|³`, and put
`C' = (a, b, c, d)`. Then `C' = D * C` for the change of variables
`D = (a u⁻¹, (b - r) u⁻², (c - s) u⁻¹, (d - t - s (b - r)) u⁻³)`, whose coefficients are
integral, with `a u⁻¹ ≡ 1` and the other three `≡ 0` modulo the maximal ideal. Hence `D` is an
integral change of variables reducing to the identity, and
`C' • E = D • (C • E)` has the integral model `D • W` (with `W` the integral minimal model), whose
reduction is that of `W`.

### Classification

Definitions and PROVED; no prints. Infrastructure: Mathlib (minimal models, changes of variables
and their action, density of a global field in its completion, the valuation topology).
Reference: Silverman, *The Arithmetic of Elliptic Curves*, VII.1 (minimal equations, changes of
coordinates preserving integrality).
-/

section RationalModel

variable (p : ℕ) (hp : p.Prime)

/-- **PROVED**, density of the rationals in the completion at `p`, as a strict valuation bound:
every `y ∈ ℚ_p` has a rational approximation `x` with `|x - y| < |c|` for any `c ≠ 0`.
Locators: Mathlib `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`,
`Valued.mem_nhds` and `Valuation.restrict_lt_iff`. -/
theorem exists_rat_valued_sub_lt (y c : (primeIdealQ p hp).adicCompletion ℚ) (hc : c ≠ 0) :
    ∃ x : ℚ, Valued.v (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) x - y) <
      Valued.v c := by
  have h' : (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰).restrict c ≠ 0 := by
    simp [hc]
  have hn : {t : (primeIdealQ p hp).adicCompletion ℚ |
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰).restrict (t - y) <
        (Units.mk0 _ h').1} ∈ 𝓝 y :=
    Valued.mem_nhds.mpr ⟨Units.mk0 _ h', fun _ h => h⟩
  obtain ⟨x, hx⟩ := (denseRange_algebraMap ℚ (primeIdealQ p hp)).mem_nhds hn
  refine ⟨x, ?_⟩
  rw [Set.mem_ofPred_eq, Units.val_mk0, eq_ratCast] at hx
  rw [eq_ratCast]
  exact (Valuation.restrict_lt_iff _).mp hx

/-- **PROVED**, a quotient bound in the value group: `|x| < |c|` gives `|x c⁻¹| < 1`.
Locator: Mathlib `div_lt_one₀`. -/
theorem valued_mul_inv_lt_one {x c : (primeIdealQ p hp).adicCompletion ℚ} (hc : c ≠ 0)
    (h : Valued.v x < Valued.v c) : Valued.v (x * c⁻¹) < 1 := by
  have hc' : (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) c ≠ 0 := by
    simpa using hc
  rw [map_mul, map_inv₀, ← div_eq_mul_inv]
  exact (div_lt_one₀ (zero_lt_iff.mpr hc')).mpr h

/-- **PROVED**, an element of the open unit ball lies in `ℤ_p`. Locator: Mathlib
`mem_adicCompletionIntegers`. -/
theorem mem_integers_of_valued_lt_one {x : (primeIdealQ p hp).adicCompletion ℚ}
    (h : Valued.v x < 1) : x ∈ (primeIdealQ p hp).adicCompletionIntegers ℚ :=
  (mem_adicCompletionIntegers _ _ _).mpr h.le

/-- **PROVED**, an element of the open unit ball has residue zero. Locators:
`NewformPeriodsDictionary.mem_maximalIdeal_completion_iff`, Mathlib `residue_eq_zero_iff`. -/
theorem residue_eq_zero_of_valued_lt_one (x : (primeIdealQ p hp).adicCompletionIntegers ℚ)
    (h : Valued.v (x : (primeIdealQ p hp).adicCompletion ℚ) < 1) :
    residue ((primeIdealQ p hp).adicCompletionIntegers ℚ) x = 0 :=
  (residue_eq_zero_iff x).mpr ((mem_maximalIdeal_completion_iff _ x).mpr h)

variable (E : WeierstrassCurve ℚ)

/-- **PROVED**, a rational change of variables with the minimal reduction (Silverman VII.1):
for every Weierstrass curve `E/ℚ` and prime `p` there are a change of variables `C'` over `ℚ` and a
Weierstrass curve `W` over `ℤ_p` such that `C' • E` base changed to `ℚ_p` is `W` base changed to
`ℚ_p`, and the reduction of `W` is the minimal reduction `reducedCurveQ E p`. The proof
approximates the minimal change of variables `TateReduction.minimalChange` by rationals, as in the
module documentation. -/
theorem exists_rationalModel :
    ∃ (C' : VariableChange ℚ) (W : WeierstrassCurve ((primeIdealQ p hp).adicCompletionIntegers ℚ)),
      (C' • E).baseChange ((primeIdealQ p hp).adicCompletion ℚ) =
          W.baseChange ((primeIdealQ p hp).adicCompletion ℚ) ∧
        W.map (residue ((primeIdealQ p hp).adicCompletionIntegers ℚ)) =
          reducedCurveQ E (primeIdealQ p hp) := by
  classical
  let C := TateReduction.minimalChange E p hp
  have hu0 : (C.u : (primeIdealQ p hp).adicCompletion ℚ) ≠ 0 := C.u.ne_zero
  obtain ⟨a, ha⟩ := exists_rat_valued_sub_lt p hp (C.u : (primeIdealQ p hp).adicCompletion ℚ)
    (C.u : (primeIdealQ p hp).adicCompletion ℚ) hu0
  obtain ⟨b, hb⟩ := exists_rat_valued_sub_lt p hp C.r
    ((C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 2) (pow_ne_zero 2 hu0)
  obtain ⟨c, hc⟩ := exists_rat_valued_sub_lt p hp C.s
    (C.u : (primeIdealQ p hp).adicCompletion ℚ) hu0
  obtain ⟨d, hd⟩ := exists_rat_valued_sub_lt p hp
    (C.t + C.s * (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) b - C.r))
    ((C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 3) (pow_ne_zero 3 hu0)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg] at ha
    exact lt_irrefl _ ha
  -- the four coefficients of the integral change of variables `D`
  let du : (primeIdealQ p hp).adicCompletion ℚ :=
    algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) a *
      (C.u : (primeIdealQ p hp).adicCompletion ℚ)⁻¹
  let dr : (primeIdealQ p hp).adicCompletion ℚ :=
    (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) b - C.r) *
      ((C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 2)⁻¹
  let ds : (primeIdealQ p hp).adicCompletion ℚ :=
    (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) c - C.s) *
      (C.u : (primeIdealQ p hp).adicCompletion ℚ)⁻¹
  let dt : (primeIdealQ p hp).adicCompletion ℚ :=
    (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) d -
        (C.t + C.s * (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) b - C.r))) *
      ((C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 3)⁻¹
  have hdu : Valued.v (du - 1) < 1 := by
    have : du - 1 = (algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) a -
        (C.u : (primeIdealQ p hp).adicCompletion ℚ)) *
          (C.u : (primeIdealQ p hp).adicCompletion ℚ)⁻¹ := by
      simp only [du]
      field_simp
    rw [this]
    exact valued_mul_inv_lt_one p hp hu0 ha
  have hdr : Valued.v dr < 1 := valued_mul_inv_lt_one p hp (pow_ne_zero 2 hu0) hb
  have hds : Valued.v ds < 1 := valued_mul_inv_lt_one p hp hu0 hc
  have hdt : Valued.v dt < 1 := valued_mul_inv_lt_one p hp (pow_ne_zero 3 hu0) hd
  have hdu1 : Valued.v du = 1 := by
    have h := Valuation.map_eq_of_sub_lt (Valued.v : Valuation
      ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) (x := 1) (y := du) (by rwa [map_one])
    rwa [map_one] at h
  have hduI : du ∈ (primeIdealQ p hp).adicCompletionIntegers ℚ :=
    (mem_adicCompletionIntegers _ _ _).mpr hdu1.le
  have hUnit : IsUnit (⟨du, hduI⟩ : (primeIdealQ p hp).adicCompletionIntegers ℚ) :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hdu1
  let D : VariableChange ((primeIdealQ p hp).adicCompletionIntegers ℚ) :=
    ⟨hUnit.unit, ⟨dr, mem_integers_of_valued_lt_one p hp hdr⟩,
      ⟨ds, mem_integers_of_valued_lt_one p hp hds⟩, ⟨dt, mem_integers_of_valued_lt_one p hp hdt⟩⟩
  let C' : VariableChange ℚ := ⟨Units.mk0 a ha0, b, c, d⟩
  -- `C' = D * C` over `ℚ_p`
  have hfac : C'.baseChange ((primeIdealQ p hp).adicCompletion ℚ) =
      D.baseChange ((primeIdealQ p hp).adicCompletion ℚ) * C := by
    apply VariableChange.ext
    · apply Units.ext
      change algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) a =
        du * (C.u : (primeIdealQ p hp).adicCompletion ℚ)
      simp only [du]
      field_simp
    · change algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) b =
        dr * (C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 2 + C.r
      simp only [dr]
      field_simp
      ring
    · change algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) c =
        (C.u : (primeIdealQ p hp).adicCompletion ℚ) * ds + C.s
      simp only [ds]
      field_simp
      ring
    · change algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) d =
        dt * (C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 3 +
          dr * C.s * (C.u : (primeIdealQ p hp).adicCompletion ℚ) ^ 2 + C.t
      simp only [dt, dr]
      field_simp
      ring
  -- `D` reduces to the identity
  have hDres : D.map (residue ((primeIdealQ p hp).adicCompletionIntegers ℚ)) = 1 := by
    apply VariableChange.ext
    · apply Units.ext
      change residue ((primeIdealQ p hp).adicCompletionIntegers ℚ) (hUnit.unit :
        (primeIdealQ p hp).adicCompletionIntegers ℚ) = 1
      rw [IsUnit.unit_spec, ← sub_eq_zero, ← map_one (residue _), ← map_sub]
      exact residue_eq_zero_of_valued_lt_one p hp _ hdu
    · exact residue_eq_zero_of_valued_lt_one p hp _ hdr
    · exact residue_eq_zero_of_valued_lt_one p hp _ hds
    · exact residue_eq_zero_of_valued_lt_one p hp _ hdt
  let Wm := (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
    ((primeIdealQ p hp).adicCompletionIntegers ℚ)
  let Wi := integralModel ((primeIdealQ p hp).adicCompletionIntegers ℚ) Wm
  have hWi : Wi.baseChange ((primeIdealQ p hp).adicCompletion ℚ) = Wm :=
    baseChange_integralModel_eq _ Wm
  refine ⟨C', D • Wi, ?_, ?_⟩
  · rw [← baseChange_smul_baseChange, hfac, mul_smul, ← baseChange_smul_baseChange, hWi]
    rfl
  · rw [← map_variableChange, hDres, one_smul]
    rfl

end RationalModel

/-!
## Part 2. Reduction of points at a place of the algebraic closure of the rationals

Let `E/ℚ` have good reduction at `p` and let `v` be a valuation subring of `\bar ℚ` with `p` in
its maximal ideal (a place of `\bar ℚ` above `p`, in the sense of
`NewformGlueG0.Completion.Arithmetic.LiesOver`). This part constructs the reduction of points
`E(\bar ℚ) → Ẽ(\bar 𝔽_p)` at `v` directly over `\bar ℚ`, without passing through `\bar ℚ_p`, and
proves its three properties used for the global Tate action:

* it is a bijection on `N`-torsion for `N` prime to `p` (`placeReductionHom_bijOn`, Silverman
  VII.3.1);
* it carries an arithmetic Frobenius at `v` to the `p`-power Frobenius
  (`placeReductionHom_frobenius`, Silverman VII.7);
* it is unchanged by an element of the inertia group of `v` (`placeReductionHom_inertia`), so
  inertia fixes every prime-to-`p` torsion point (`map_eq_self_of_mem_inertiaSubgroup`, Silverman
  VII.4.1 and the easy direction of VII.7.1).

### Construction

1. *A rational integral model.* `exists_rationalModel` (Part 1) gives a rational
   change of variables `C'` with `C' • E` integral at `p` and reducing to the minimal reduction.
   Its rational coefficients are `p`-integral, so they lie in `v`
   (`algebraMap_mem_place`): a rational number with denominator prime to `p` has denominator a unit
   of `v`, since `p` and the denominator generate the unit ideal. This gives the model
   `placeModel` over `v`, with generic fibre `C' • E` over `\bar ℚ` (`placeModel_map_subtype`).
2. *Its special fibre.* Residues of `p`-integral rationals are computed as `num / den` both in
   the residue field of `v` and in `𝔽_p` (`residue_place_algebraMap`,
   `residueFieldEquivZModQ_residue`), so the special fibre is `reducedCurveModP E p` base changed to
   the residue field `k_v` (`placeModel_map_residue`), which has good reduction.
3. *The residue field.* `k_v` is algebraically closed (`TateReduction.isAlgClosed_residueField`)
   and algebraic over `𝔽_p` (`isAlgebraic_residueField_place`: an element of `v` is a root of a
   primitive integer polynomial, whose reduction mod `p` is nonzero), hence `k_v ≅ \bar 𝔽_p`
   (`placeResidueEquiv`).
4. *Reduction* `placeReductionHom` is the composite of the change of variables `C'`, the vendored
   reduction homomorphism `reduceHom` of the model, and transport along `k_v ≅ \bar 𝔽_p`.

### Classification

Definitions and PROVED; no prints. Infrastructure: Mathlib, the vendored Tau Ceti library (points
under a change of variables and along algebra equivalences) and the reduction library used in
`ModularWeil/ReductionInjective.lean`. Reference: Silverman, *The Arithmetic of Elliptic Curves*,
VII.2–VII.4 and VII.7.
-/

open Polynomial

section Rationals

variable {p : ℕ} (hp : p.Prime)

/-- **PROVED**, a rational number integral at `p` has denominator prime to `p`.
Locator: Mathlib `Rat.valuation_le_one_iff_den`. -/
theorem not_dvd_den_of_valuation_le_one {x : ℚ}
    (hx : (primeIdealQ p hp).valuation ℚ x ≤ 1) : ¬ p ∣ x.den := by
  rintro ⟨k, hk⟩
  apply Rat.valuation_le_one_iff_den.mp hx
  change ((x.den : ℕ) : NumberField.RingOfIntegers ℚ) ∈
    Ideal.span {((p : ℕ) : NumberField.RingOfIntegers ℚ)}
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable (v : ValuationSubring (AlgebraicClosure ℚ))
  (hv : ((p : ℕ) : AlgebraicClosure ℚ) ∈ v.nonunits)

include hp hv in
/-- **PROVED**, the residue field of a place above `p` has characteristic `p`. Locator: the
vendored `ValuationSubring.charP_residueField_of_liesOverPrime_def`. -/
theorem charP_residueField_place : CharP (ResidueField v) p :=
  ValuationSubring.charP_residueField_of_liesOverPrime_def hp
    (ValuationSubring.liesOverPrime_iff.mpr hv)

include hp hv in
/-- **PROVED**, a natural number prime to `p` is a unit at a place above `p`: its residue is
nonzero in characteristic `p`. Locators: `charP_residueField_place`, Mathlib
`CharP.cast_eq_zero_iff`. -/
theorem natCast_notMem_nonunits_place {d : ℕ} (hd : ¬ p ∣ d) :
    ((d : ℕ) : AlgebraicClosure ℚ) ∉ v.nonunits := by
  have := charP_residueField_place hp v hv
  intro h
  have hres : residue v ⟨(d : AlgebraicClosure ℚ), ValuationSubring.natCast_mem' v d⟩ = 0 :=
    (v.coe_mem_nonunits_iff_residue_eq_zero _).mp h
  have hcast : ((d : ℕ) : ResidueField v) = 0 := by
    rw [← hres]
    have : (⟨(d : AlgebraicClosure ℚ), ValuationSubring.natCast_mem' v d⟩ : v) = (d : v) :=
      Subtype.ext (by simp)
    rw [this, map_natCast]
  exact hd ((CharP.cast_eq_zero_iff (ResidueField v) p d).mp hcast)

include hv in
/-- **PROVED**, a rational number integral at `p` lies in every place above `p`.
Locators: `not_dvd_den_of_valuation_le_one`, `natCast_notMem_nonunits_place`, the vendored
`ValuationSubring.div_mem_of_mem_of_notMem_nonunits`. -/
theorem algebraMap_mem_place {x : ℚ} (hx : (primeIdealQ p hp).valuation ℚ x ≤ 1) :
    algebraMap ℚ (AlgebraicClosure ℚ) x ∈ v := by
  rw [eq_ratCast, Rat.cast_def]
  exact v.div_mem_of_mem_of_notMem_nonunits (intCast_mem v.toSubring x.num)
    (natCast_notMem_nonunits_place hp v hv (not_dvd_den_of_valuation_le_one hp hx))

include hv in
/-- **PROVED**, the residue of a `p`-integral rational number at a place above `p` is
`num / den`. Locator: the vendored `ValuationSubring.residue_eq_div_of_eq_div`. -/
theorem residue_place_algebraMap {x : ℚ} (hx : (primeIdealQ p hp).valuation ℚ x ≤ 1) :
    residue v ⟨algebraMap ℚ (AlgebraicClosure ℚ) x, algebraMap_mem_place hp v hv hx⟩ =
      (x.num : ResidueField v) / (x.den : ResidueField v) := by
  have hd := natCast_notMem_nonunits_place hp v hv (not_dvd_den_of_valuation_le_one hp hx)
  rw [v.residue_eq_div_of_eq_div _ (intCast_mem v.toSubring x.num)
    (ValuationSubring.natCast_mem' v x.den) hd (by rw [eq_ratCast, Rat.cast_def])]
  have hn : (⟨((x.num : ℤ) : AlgebraicClosure ℚ), intCast_mem v.toSubring x.num⟩ : v) =
      ((x.num : ℤ) : v) := Subtype.ext (by simp)
  have hd' : (⟨((x.den : ℕ) : AlgebraicClosure ℚ), ValuationSubring.natCast_mem' v x.den⟩ : v) =
      ((x.den : ℕ) : v) := Subtype.ext (by simp)
  rw [hn, hd', map_intCast, map_natCast]

/-- **PROVED**, the residue in `𝔽_p` of an element of `ℤ_p` equal to a rational number `x`,
multiplied by the denominator of `x`, is the numerator of `x`. Locator:
`NewformPeriodsDictionary.residueFieldEquivZModQ`. -/
theorem residueFieldEquivZModQ_residue {x : ℚ}
    (y : (primeIdealQ p hp).adicCompletionIntegers ℚ)
    (hxy : algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) x =
      (y : (primeIdealQ p hp).adicCompletion ℚ)) :
    residueFieldEquivZModQ p hp (residue _ y) * (x.den : ZMod p) = (x.num : ZMod p) := by
  have hy : y * (x.den : (primeIdealQ p hp).adicCompletionIntegers ℚ) =
      ((x.num : ℤ) : (primeIdealQ p hp).adicCompletionIntegers ℚ) := by
    apply Subtype.ext
    push_cast
    rw [← hxy, eq_ratCast]
    have hd0 : ((x.den : ℕ) : (primeIdealQ p hp).adicCompletion ℚ) ≠ 0 := by
      exact_mod_cast x.den_ne_zero
    rw [Rat.cast_def, div_mul_cancel₀ _ hd0]
  calc residueFieldEquivZModQ p hp (residue _ y) * (x.den : ZMod p)
      = residueFieldEquivZModQ p hp (residue _
          (y * (x.den : (primeIdealQ p hp).adicCompletionIntegers ℚ))) := by
        rw [map_mul, map_mul, map_natCast, map_natCast]
    _ = (x.num : ZMod p) := by rw [hy, map_intCast, map_intCast]

include hv in
/-- **PROVED**, residues of a `p`-integral rational number agree at a place above `p` and in
`ℤ_p`, through any `𝔽_p`-algebra structure on the residue field of the place. Locators:
`residue_place_algebraMap`, `residueFieldEquivZModQ_residue`. -/
theorem residue_place_eq_algebraMap [Algebra (ZMod p) (ResidueField v)] {x : ℚ}
    (hx : (primeIdealQ p hp).valuation ℚ x ≤ 1)
    (y : (primeIdealQ p hp).adicCompletionIntegers ℚ)
    (hxy : algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) x =
      (y : (primeIdealQ p hp).adicCompletion ℚ)) :
    residue v ⟨algebraMap ℚ (AlgebraicClosure ℚ) x, algebraMap_mem_place hp v hv hx⟩ =
      algebraMap (ZMod p) (ResidueField v) (residueFieldEquivZModQ p hp (residue _ y)) := by
  have := charP_residueField_place hp v hv
  have hd : (x.den : ResidueField v) ≠ 0 := fun h =>
    not_dvd_den_of_valuation_le_one hp hx ((CharP.cast_eq_zero_iff (ResidueField v) p x.den).mp h)
  rw [residue_place_algebraMap hp v hv hx, div_eq_iff hd]
  have h := congrArg (algebraMap (ZMod p) (ResidueField v))
    (residueFieldEquivZModQ_residue hp y hxy)
  rw [map_mul, map_natCast, map_intCast] at h
  exact h.symm

/-- **PROVED**, a rational number equal in `ℚ_p` to an element of `ℤ_p` is integral at `p`.
Locators: `NewformPeriodsDictionary.valued_algebraMap_Q`, Mathlib `mem_adicCompletionIntegers`. -/
theorem valuation_le_one_of_eq_integer {x : ℚ}
    (y : (primeIdealQ p hp).adicCompletionIntegers ℚ)
    (hxy : algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) x =
      (y : (primeIdealQ p hp).adicCompletion ℚ)) :
    (primeIdealQ p hp).valuation ℚ x ≤ 1 := by
  rw [← valued_algebraMap_Q, hxy]
  exact (mem_adicCompletionIntegers _ _ _).mp y.2

end Rationals

section Model

variable (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime)

/-- **DEFINITION**, the rational change of variables of `exists_rationalModel`. -/
def ratChange : VariableChange ℚ :=
  (exists_rationalModel p hp E).choose

/-- **DEFINITION**, the integral model over `ℤ_p` of `exists_rationalModel`. -/
def ratIntegralModel : WeierstrassCurve ((primeIdealQ p hp).adicCompletionIntegers ℚ) :=
  (exists_rationalModel p hp E).choose_spec.choose

/-- **PROVED**, the rational model and the integral model agree over `ℚ_p`. Locator:
`exists_rationalModel`. -/
theorem ratChange_baseChange :
    (ratChange E hp • E).baseChange ((primeIdealQ p hp).adicCompletion ℚ) =
      (ratIntegralModel E hp).baseChange ((primeIdealQ p hp).adicCompletion ℚ) :=
  (exists_rationalModel p hp E).choose_spec.choose_spec.1

/-- **PROVED**, the integral model reduces to the minimal reduction. Locator:
`exists_rationalModel`. -/
theorem ratIntegralModel_map_residue :
    (ratIntegralModel E hp).map (residue ((primeIdealQ p hp).adicCompletionIntegers ℚ)) =
      reducedCurveQ E (primeIdealQ p hp) :=
  (exists_rationalModel p hp E).choose_spec.choose_spec.2

/-- **PROVED**, `reducedCurveModP` is the integral model reduced through `ℤ_p → 𝔽_p`.
Locators: the definition `reducedCurveModP`, `ratIntegralModel_map_residue`. -/
theorem reducedCurveModP_eq_map :
    reducedCurveModP E p hp = (ratIntegralModel E hp).map
      ((residueFieldEquivZModQ p hp).toRingHom.comp
        (residue ((primeIdealQ p hp).adicCompletionIntegers ℚ))) := by
  rw [reducedCurveModP, ← ratIntegralModel_map_residue, WeierstrassCurve.map_map]

/-- **PROVED**, each rational coefficient equals in `ℚ_p` the corresponding integral one.
Locator: `ratChange_baseChange`. -/
theorem ratChange_coeffs :
    algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) (ratChange E hp • E).a₁ =
        ((ratIntegralModel E hp).a₁ : (primeIdealQ p hp).adicCompletion ℚ) ∧
      algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) (ratChange E hp • E).a₂ =
        ((ratIntegralModel E hp).a₂ : (primeIdealQ p hp).adicCompletion ℚ) ∧
      algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) (ratChange E hp • E).a₃ =
        ((ratIntegralModel E hp).a₃ : (primeIdealQ p hp).adicCompletion ℚ) ∧
      algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) (ratChange E hp • E).a₄ =
        ((ratIntegralModel E hp).a₄ : (primeIdealQ p hp).adicCompletion ℚ) ∧
      algebraMap ℚ ((primeIdealQ p hp).adicCompletion ℚ) (ratChange E hp • E).a₆ =
        ((ratIntegralModel E hp).a₆ : (primeIdealQ p hp).adicCompletion ℚ) := by
  have h := ratChange_baseChange E hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg WeierstrassCurve.a₁ h
  · exact congrArg WeierstrassCurve.a₂ h
  · exact congrArg WeierstrassCurve.a₃ h
  · exact congrArg WeierstrassCurve.a₄ h
  · exact congrArg WeierstrassCurve.a₆ h

variable (v : ValuationSubring (AlgebraicClosure ℚ))
  (hv : ((p : ℕ) : AlgebraicClosure ℚ) ∈ v.nonunits)

/-- **DEFINITION**, the integral model of `ratChange E p • E` over a place `v` above `p`: its
rational coefficients, which lie in `v` by `algebraMap_mem_place`. -/
def placeModel : WeierstrassCurve v where
  a₁ := ⟨_, algebraMap_mem_place hp v hv
    (valuation_le_one_of_eq_integer hp _ (ratChange_coeffs E hp).1)⟩
  a₂ := ⟨_, algebraMap_mem_place hp v hv
    (valuation_le_one_of_eq_integer hp _ (ratChange_coeffs E hp).2.1)⟩
  a₃ := ⟨_, algebraMap_mem_place hp v hv
    (valuation_le_one_of_eq_integer hp _ (ratChange_coeffs E hp).2.2.1)⟩
  a₄ := ⟨_, algebraMap_mem_place hp v hv
    (valuation_le_one_of_eq_integer hp _ (ratChange_coeffs E hp).2.2.2.1)⟩
  a₆ := ⟨_, algebraMap_mem_place hp v hv
    (valuation_le_one_of_eq_integer hp _ (ratChange_coeffs E hp).2.2.2.2)⟩

/-- **PROVED**, the generic fibre of `placeModel` is `ratChange E p • E` over `\bar ℚ`.
Locator: the definition `placeModel`, coefficientwise. -/
theorem placeModel_map_subtype :
    (placeModel E hp v hv).map v.subtype =
      (ratChange E hp • E).baseChange (AlgebraicClosure ℚ) := by
  ext <;> rfl

/-- **PROVED**, the special fibre of `placeModel` is `reducedCurveModP E p` base changed to the
residue field of the place, for any `𝔽_p`-algebra structure on it. Locators:
`residue_place_eq_algebraMap`, `reducedCurveModP_eq_map`. -/
theorem placeModel_map_residue [Algebra (ZMod p) (ResidueField v)] :
    (placeModel E hp v hv).map (residue v) =
      (reducedCurveModP E p hp).baseChange (ResidueField v) := by
  rw [reducedCurveModP_eq_map E hp]
  have hc := ratChange_coeffs E hp
  ext
  · exact residue_place_eq_algebraMap hp v hv
      (valuation_le_one_of_eq_integer hp _ hc.1) _ hc.1
  · exact residue_place_eq_algebraMap hp v hv
      (valuation_le_one_of_eq_integer hp _ hc.2.1) _ hc.2.1
  · exact residue_place_eq_algebraMap hp v hv
      (valuation_le_one_of_eq_integer hp _ hc.2.2.1) _ hc.2.2.1
  · exact residue_place_eq_algebraMap hp v hv
      (valuation_le_one_of_eq_integer hp _ hc.2.2.2.1) _ hc.2.2.2.1
  · exact residue_place_eq_algebraMap hp v hv
      (valuation_le_one_of_eq_integer hp _ hc.2.2.2.2) _ hc.2.2.2.2

/-- **PROVED**, the integral model over the place has good reduction. Locators:
`placeModel_map_residue`, `NewformPeriodsDictionary.reducedCurveModP_isElliptic`. -/
theorem placeModel_Δ_ne_zero [Algebra (ZMod p) (ResidueField v)]
    (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    ((placeModel E hp v hv).map (residue v)).Δ ≠ 0 := by
  rw [placeModel_map_residue]
  have := reducedCurveModP_isElliptic E p hp hgood
  exact ((reducedCurveModP E p hp).baseChange _).isUnit_Δ.ne_zero

end Model

section ResidueField

variable {p : ℕ} (hp : p.Prime) (v : ValuationSubring (AlgebraicClosure ℚ))

include hp in
/-- **PROVED**, the residue field of a place of `\bar ℚ` is algebraic over `𝔽_p`. An element of
the place is a root of a primitive integer polynomial; its reduction mod `p` is nonzero, since a
primitive polynomial has a coefficient prime to `p`, and it vanishes at the residue. Locators:
Mathlib `Polynomial.isPrimitive_primPart`, `Polynomial.eq_C_content_mul_primPart`,
`Polynomial.aeval_algHom_apply`. -/
theorem isAlgebraic_residueField_place [Algebra (ZMod p) (ResidueField v)] :
    Algebra.IsAlgebraic (ZMod p) (ResidueField v) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨f, hf0, hfx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : AlgebraicClosure ℚ))
  have hc0 : (f.content : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (mt Polynomial.content_eq_zero_iff.mp hf0)
  have hgx : aeval (x : AlgebraicClosure ℚ) f.primPart = 0 := by
    have h := hfx
    rw [Polynomial.eq_C_content_mul_primPart f, map_mul, aeval_C, eq_intCast] at h
    exact (mul_eq_zero.mp h).resolve_left hc0
  have hgx' : aeval x f.primPart = 0 := by
    apply Subtype.ext
    have h := Polynomial.aeval_algHom_apply v.subtype.toIntAlgHom x f.primPart
    simp only [RingHom.toIntAlgHom_apply] at h
    rw [ZeroMemClass.coe_zero]
    change v.subtype (aeval x f.primPart) = 0
    rw [← h]
    exact hgx
  refine ⟨f.primPart.map (algebraMap ℤ (ZMod p)), fun h => ?_, ?_⟩
  · have hdvd : ∀ i, (p : ℤ) ∣ f.primPart.coeff i := by
      intro i
      have hi := congrArg (fun q => q.coeff i) h
      simp only [coeff_map, coeff_zero, algebraMap_int_eq, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hi
    have hu := Polynomial.isPrimitive_primPart f (p : ℤ)
      ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit hu
  · rw [aeval_def, eval₂_map, RingHom.ext_int ((algebraMap (ZMod p) (ResidueField v)).comp
      (algebraMap ℤ (ZMod p))) (algebraMap ℤ (ResidueField v)), ← aeval_def]
    have h := Polynomial.aeval_algHom_apply (residue v).toIntAlgHom x f.primPart
    simp only [RingHom.toIntAlgHom_apply] at h
    exact h.trans (by rw [hgx', map_zero])

include hp in
/-- **PROVED**, the residue field of a place of `\bar ℚ` above `p` is an algebraic closure of
`𝔽_p`. Locators: `TateReduction.isAlgClosed_residueField`, `isAlgebraic_residueField_place`. -/
theorem isAlgClosure_residueField_place [Fact p.Prime] [Algebra (ZMod p) (ResidueField v)] :
    IsAlgClosure (ZMod p) (ResidueField v) :=
  IsAlgClosure.mk (TateReduction.isAlgClosed_residueField v) (isAlgebraic_residueField_place hp v)

/-- **DEFINITION**, an identification of the residue field of a place of `\bar ℚ` above `p` with
`\bar 𝔽_p`: uniqueness of algebraic closures. Locator: Mathlib `IsAlgClosure.equiv`. -/
def placeResidueEquiv [Fact p.Prime] [Algebra (ZMod p) (ResidueField v)] :
    ResidueField v ≃ₐ[ZMod p] AlgebraicClosure (ZMod p) :=
  haveI := isAlgClosure_residueField_place hp v
  IsAlgClosure.equiv (ZMod p) _ _

end ResidueField

section Reduction

open scoped Classical

variable (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) (v : ValuationSubring (AlgebraicClosure ℚ))
  (hv : ((p : ℕ) : AlgebraicClosure ℚ) ∈ v.nonunits) [Fact p.Prime]
  [Algebra (ZMod p) (ResidueField v)]

/-- **DEFINITION**, reduction of points at a place `v` of `\bar ℚ` above `p` (Silverman VII.2):
from `E(\bar ℚ)` to the points of `reducedCurveModP E p` over `\bar 𝔽_p`, through the rational
change of variables `ratChange`, the integral model `placeModel` over `v`, the vendored reduction
homomorphism `reduceHom`, and the identification `placeResidueEquiv` of the residue field. -/
def placeReductionHom (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point →+
      ((reducedCurveModP E p hp).baseChange (AlgebraicClosure (ZMod p))).toAffine.Point :=
  haveI := reducedCurveModP_isElliptic E p hp hgood
  (Affine.Point.mapEquiv (reducedCurveModP E p hp) (placeResidueEquiv hp v)).toAddMonoidHom.comp
    ((AddEquiv.cast (M := fun V : WeierstrassCurve (ResidueField v) => V.toAffine.Point)
        (placeModel_map_residue E hp v hv)).toAddMonoidHom.comp
      ((reduceHom (placeModel_Δ_ne_zero E hp v hv hgood)).comp
        ((AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure ℚ) => V.toAffine.Point)
            (placeModel_map_subtype E hp v hv).symm).toAddMonoidHom.comp
          (E.pointEquivVariableChange (AlgebraicClosure ℚ) (ratChange E hp)).symm.toAddMonoidHom)))

/-- **PROVED**, reduction at the place is a bijection on prime-to-`p` torsion (Silverman VII.3.1):
every step is a group isomorphism except the reduction of the integral model, which is a bijection
on `N`-torsion for `N` invertible in the residue field over the algebraically closed field `\bar ℚ`
of characteristic zero (`ModularWeil.reduceHom_bijOn_torsion`). -/
theorem placeReductionHom_bijOn (hgood : GoodReductionAt E (primeIdealQ p hp)) {N : ℕ}
    (hN : (N : ResidueField v) ≠ 0) :
    Set.BijOn (placeReductionHom E hp v hv hgood) {P | N • P = 0} {Q | N • Q = 0} := by
  rw [placeReductionHom]
  simp only [AddMonoidHom.coe_comp]
  exact (TateReduction.bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
    ((TateReduction.bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
      ((CloudB3RC53.ModularWeil.reduceHom_bijOn_torsion _ hN).comp
        ((TateReduction.bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
          (TateReduction.bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N))))

/-- **PROVED**, a point of the rational model whose abscissa is not in `v` reduces to the point at
infinity. Locator: the vendored `reducePoint_some_of_notMem`. -/
theorem placeReductionHom_some_of_notMem (hgood : GoodReductionAt E (primeIdealQ p hp))
    {x y : AlgebraicClosure ℚ}
    (h : ((ratChange E hp • E).baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hx : x ∉ v) :
    placeReductionHom E hp v hv hgood
        (E.pointEquivVariableChange (AlgebraicClosure ℚ) (ratChange E hp) (.some x y h)) = 0 := by
  simp only [placeReductionHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, Affine.Point.mapEquiv_apply]
  rw [AddEquiv.cast_apply (placeModel_map_subtype E hp v hv).symm,
    Affine.Point.cast_some (placeModel_map_subtype E hp v hv).symm,
    TateReduction.reduceHom_apply, reducePoint_some_of_notMem _ _ hx, map_zero, map_zero]

/-- **PROVED**, reduction at the place carries an arithmetic Frobenius at `v` to the `p`-power
Frobenius (Silverman VII.7, as in the proof of VII.7.1). An element `g` of the decomposition group
of `v` with `g x ≡ x^p` modulo the maximal ideal for `x ∈ v` acts on the residue field as
`z ↦ z^p`; the change of variables `ratChange` is rational, so it commutes with `g`; integral
points reduce coordinatewise and the others to infinity, before and after `g`; and the
identification of the residue field with `\bar 𝔽_p` commutes with `p`-th powers. -/
theorem placeReductionHom_frobenius (hgood : GoodReductionAt E (primeIdealQ p hp))
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hdec : g ∈ v.decompositionSubgroup ℚ)
    (hfr : ∀ x ∈ v, g x - x ^ p ∈ v.nonunits)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    placeReductionHom E hp v hv hgood (Affine.Point.map (W' := E) g.toAlgHom P) =
      Affine.Point.map (W' := reducedCurveModP E p hp)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
        (placeReductionHom E hp v hv hgood P) := by
  have hfrob : ∀ (z : AlgebraicClosure ℚ) (hz : z ∈ v) (hgz : g z ∈ v),
      residue v ⟨g z, hgz⟩ = residue v ⟨z, hz⟩ ^ p := by
    intro z hz hgz
    rw [← map_pow]
    exact (v.residue_eq_residue_iff_sub_mem_nonunits hgz (pow_mem hz p)).mpr (hfr z hz)
  obtain ⟨Q, rfl⟩ := (E.pointEquivVariableChange (AlgebraicClosure ℚ) (ratChange E hp)).surjective P
  rw [map_pointEquivVariableChange]
  rcases Q with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · have h₁ := (Affine.baseChange_nonsingular (ratChange E hp • E)
      (f := g.toAlgHom) g.injective x y).mpr h
    rw [Affine.Point.map_some]
    by_cases hx : x ∈ v
    · have hgx : g.toAlgHom x ∈ v :=
        ValuationSubring.smul_mem_of_mem_decompositionSubgroup _ hdec hx
      have h₂ : ((placeModel E hp v hv).map v.subtype).toAffine.Nonsingular x y := by
        rw [placeModel_map_subtype]
        exact h
      have h₃ : ((placeModel E hp v hv).map v.subtype).toAffine.Nonsingular
          (g.toAlgHom x) (g.toAlgHom y) := by
        rw [placeModel_map_subtype]
        exact h₁
      have hy : y ∈ v := Affine.Y_mem_of_X_mem _ h₂.1 hx
      have hgy : g.toAlgHom y ∈ v := Affine.Y_mem_of_X_mem _ h₃.1 hgx
      have hx' : residue v ⟨g.toAlgHom x, hgx⟩ = residue v ⟨x, hx⟩ ^ p := hfrob x hx hgx
      have hy' : residue v ⟨g.toAlgHom y, hgy⟩ = residue v ⟨y, hy⟩ ^ p := hfrob y hy hgy
      simp only [placeReductionHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply, Affine.Point.mapEquiv_apply]
      rw [AddEquiv.cast_apply (placeModel_map_subtype E hp v hv).symm,
        Affine.Point.cast_some (placeModel_map_subtype E hp v hv).symm,
        AddEquiv.cast_apply (placeModel_map_subtype E hp v hv).symm,
        Affine.Point.cast_some (placeModel_map_subtype E hp v hv).symm,
        TateReduction.reduceHom_apply, TateReduction.reduceHom_apply,
        reducePoint_some_of_mem _ _ hx, reducePoint_some_of_mem _ _ hgx,
        AddEquiv.cast_apply (placeModel_map_residue E hp v hv),
        Affine.Point.cast_some (placeModel_map_residue E hp v hv),
        AddEquiv.cast_apply (placeModel_map_residue E hp v hv),
        Affine.Point.cast_some (placeModel_map_residue E hp v hv),
        Affine.Point.map_some, Affine.Point.map_some, Affine.Point.map_some]
      simp only [FiniteField.frobeniusAlgHom_apply, ZMod.card, hx', hy', map_pow]
    · have hgx : g.toAlgHom x ∉ v := fun hmem => hx (by
        simpa using ValuationSubring.smul_mem_of_mem_decompositionSubgroup _ (inv_mem hdec) hmem)
      rw [placeReductionHom_some_of_notMem E hp v hv hgood h hx,
        placeReductionHom_some_of_notMem E hp v hv hgood h₁ hgx, map_zero]

/-- **PROVED**, reduction at the place is unchanged by an element of the inertia group of `v`
(Silverman VII.4.1): such an element preserves `v` and acts trivially on its residue field, and
the change of variables `ratChange` is rational. Locator: the vendored
`reducePoint_some_apply_of_mem_inertia`. -/
theorem placeReductionHom_inertia (hgood : GoodReductionAt E (primeIdealQ p hp))
    (s : v.decompositionSubgroup ℚ) (hs : s ∈ v.inertiaSubgroup ℚ)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    placeReductionHom E hp v hv hgood
        (Affine.Point.map (W' := E) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P) =
      placeReductionHom E hp v hv hgood P := by
  obtain ⟨Q, rfl⟩ := (E.pointEquivVariableChange (AlgebraicClosure ℚ) (ratChange E hp)).surjective P
  rw [map_pointEquivVariableChange]
  rcases Q with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · have h₁ := (Affine.baseChange_nonsingular (ratChange E hp • E)
      (f := (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
      (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).injective x y).mpr h
    rw [Affine.Point.map_some]
    have h₂ : ((placeModel E hp v hv).map v.subtype).toAffine.Nonsingular x y := by
      rw [placeModel_map_subtype]
      exact h
    have h₃ : ((placeModel E hp v hv).map v.subtype).toAffine.Nonsingular
        ((s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x)
        ((s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y) := by
      rw [placeModel_map_subtype]
      exact h₁
    simp only [placeReductionHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply]
    rw [AddEquiv.cast_apply (placeModel_map_subtype E hp v hv).symm,
      Affine.Point.cast_some (placeModel_map_subtype E hp v hv).symm,
      AddEquiv.cast_apply (placeModel_map_subtype E hp v hv).symm,
      Affine.Point.cast_some (placeModel_map_subtype E hp v hv).symm,
      TateReduction.reduceHom_apply, TateReduction.reduceHom_apply]
    erw [reducePoint_some_apply_of_mem_inertia _ s.2 hs h₂ h₃]

include hv in
/-- **PROVED**, inertia fixes prime-to-`p` torsion at good reduction (Silverman VII.4.1, the
easy direction of the criterion of Néron, Ogg and Shafarevich, VII.7.1): an element of the inertia
group of `v` fixes every point of `E(\bar ℚ)[N]` for `N` invertible in the residue field. It does
not change reductions (`placeReductionHom_inertia`), and reduction is injective on `N`-torsion
(`placeReductionHom_bijOn`). -/
theorem map_eq_self_of_mem_inertiaSubgroup (hgood : GoodReductionAt E (primeIdealQ p hp))
    (s : v.decompositionSubgroup ℚ) (hs : s ∈ v.inertiaSubgroup ℚ) {N : ℕ}
    (hN : (N : ResidueField v) ≠ 0) {P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point}
    (hP : N • P = 0) :
    Affine.Point.map (W' := E) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P = P := by
  refine (placeReductionHom_bijOn E hp v hv hgood hN).injOn ?_ hP
    (placeReductionHom_inertia E hp v hv hgood s hs P)
  change N • Affine.Point.map _ P = 0
  rw [← map_nsmul, hP, map_zero]

end Reduction

/-!
## Part 3. The global Tate action at a good prime

Reduction at a place gives an isomorphism of Tate modules `placeTateEquiv`, through which inertia
acts trivially and an arithmetic Frobenius acts as the `p`-power Frobenius of the reduction. The
proved determinant form on the reduction then gives trace and determinant on the actual integral
and rational Tate modules of `NewformGlueG0/GaloisCompletion.lean`.
-/

section Tate

open scoped Classical
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion

variable (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) (v : ValuationSubring (AlgebraicClosure ℚ))
  (hv : ((p : ℕ) : AlgebraicClosure ℚ) ∈ v.nonunits) [Fact p.Prime]
  [Algebra (ZMod p) (ResidueField v)] (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fact p.Prime] [Algebra (ZMod p) (ResidueField v)] in
include hp hv in
/-- **PROVED**, powers of a prime `ℓ ≠ p` are invertible in the residue field of a place above
`p`. Locators: `charP_residueField_place`, Mathlib `CharP.cast_eq_zero_iff`. -/
theorem natCast_pow_ne_zero_residue (hℓ : ℓ ≠ p) (n : ℕ) :
    ((ℓ ^ n : ℕ) : ResidueField v) ≠ 0 := by
  have := charP_residueField_place hp v hv
  intro h
  rw [CharP.cast_eq_zero_iff _ p] at h
  exact hℓ ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h)).symm

/-- **DEFINITION WITH PROVED BIJECTIVITY**, the `ℤ_ℓ`-linear isomorphism
`T_ℓ(E/\bar ℚ) ≅ T_ℓ(Ẽ/\bar 𝔽_p)` induced by reduction at the place `v` (Silverman VII.3.1 and
III.7). Locators: `placeReductionHom_bijOn`, `TateReduction.tateLinearEquivOfBijOn`. -/
def placeTateEquiv (hgood : GoodReductionAt E (primeIdealQ p hp)) (hℓ : ℓ ≠ p) :
    TauCeti.TateModule ℓ (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point ≃ₗ[ℤ_[ℓ]]
      CloudB3RC53.ModularWeil.redTate p (reducedCurveModP E p hp) ℓ :=
  TateReduction.tateLinearEquivOfBijOn (placeReductionHom E hp v hv hgood)
    (fun n => placeReductionHom_bijOn E hp v hv hgood (natCast_pow_ne_zero_residue hp v hv ℓ hℓ n))

/-- **PROVED**, the reduction isomorphism of Tate modules carries an arithmetic Frobenius at `v`,
acting through the global Galois representation, to the `p`-power Frobenius `frobTate` (Silverman
VII.7.1). Locator: `placeReductionHom_frobenius`, through `TauCeti.TateModule.map_comp`. -/
theorem placeTateEquiv_frobenius (hgood : GoodReductionAt E (primeIdealQ p hp)) (hℓ : ℓ ≠ p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hdec : g ∈ v.decompositionSubgroup ℚ)
    (hfr : ∀ x ∈ v, g x - x ^ p ∈ v.nonunits)
    (x : TauCeti.TateModule ℓ (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    placeTateEquiv E hp v hv ℓ hgood hℓ (E.tateModuleGaloisRepresentation ℓ g x) =
      CloudB3RC53.ModularWeil.frobTate p (reducedCurveModP E p hp) ℓ
        (placeTateEquiv E hp v hv ℓ hgood hℓ x) := by
  have key : (placeReductionHom E hp v hv hgood).comp (Affine.Point.map (W' := E) g.toAlgHom) =
      (Affine.Point.map (W' := reducedCurveModP E p hp)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))).comp
        (placeReductionHom E hp v hv hgood) :=
    AddMonoidHom.ext fun P => placeReductionHom_frobenius E hp v hv hgood g hdec hfr P
  rw [placeTateEquiv, TateReduction.tateLinearEquivOfBijOn_apply,
    TateReduction.tateLinearEquivOfBijOn_apply, WeierstrassCurve.tateModuleGaloisRepresentation_apply]
  change TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x) =
    TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x)
  rw [← AddMonoidHom.comp_apply (TauCeti.TateModule.map _), ← TauCeti.TateModule.map_comp, key,
    TauCeti.TateModule.map_comp, AddMonoidHom.comp_apply]

include hv in
/-- **PROVED**, the inertia group of a place above a good prime `p ≠ ℓ` acts trivially on the
actual integral Tate module `T_ℓ(E/\bar ℚ)` (Silverman VII.4.1 and VII.7.1, good reduction implies
unramified). Locators: `map_eq_self_of_mem_inertiaSubgroup`,
`WeierstrassCurve.tateModuleGaloisRepresentation_eq_one_iff`. -/
theorem integralTateRep_eq_one_of_mem_inertiaSubgroup [E.IsElliptic]
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (hℓ : ℓ ≠ p)
    (s : v.decompositionSubgroup ℚ) (hs : s ∈ v.inertiaSubgroup ℚ) :
    integralTateRep E ℓ (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 := by
  have hℓQ : (ℓ : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  change E.tateModuleGaloisRepresentation ℓ (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1
  refine (E.tateModuleGaloisRepresentation_eq_one_iff hℓQ).mpr fun k P hP => ?_
  exact map_eq_self_of_mem_inertiaSubgroup E hp v hv hgood s hs
    (natCast_pow_ne_zero_residue hp v hv ℓ hℓ k) hP

include hv in
/-- **PROVED**, trace and determinant of an arithmetic Frobenius at `v` on the actual integral
Tate module `T_ℓ(E/\bar ℚ)`, at a good prime `p ≠ ℓ` (Silverman V.2.3.1 and VII.7.1): trace
`p + 1 - #Ẽ(𝔽_p)` and determinant `p`. Conjugating by `placeTateEquiv` turns the proved
determinant form `DetDegree.frobeniusTateDetFormOne_proved` of `frobTate` into
`det(1 - n ρ(g)) = 1 - a n + p n²`, and `ModularWeil.trace_det_of_detFormOne` reads off the trace
and the determinant. -/
theorem integralTateRep_trace_det [E.IsElliptic] (hgood : GoodReductionAt E (primeIdealQ p hp))
    (hℓ : ℓ ≠ p) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hdec : g ∈ v.decompositionSubgroup ℚ) (hfr : ∀ x ∈ v, g x - x ^ p ∈ v.nonunits) :
    LinearMap.trace ℤ_[ℓ] (integralTate E ℓ) (integralTateRep E ℓ g) =
        (((p : ℤ) + 1 - (Nat.card (reducedCurveModP E p hp).toAffine.Point : ℤ) : ℤ) : ℤ_[ℓ]) ∧
      LinearMap.det (integralTateRep E ℓ g) = (p : ℤ_[ℓ]) := by
  let e := placeTateEquiv E hp v hv ℓ hgood hℓ
  let ρ : Module.End ℤ_[ℓ] (integralTate E ℓ) := integralTateRep E ℓ g
  have hρ : ∀ x, ρ x = E.tateModuleGaloisRepresentation ℓ g x := fun x => rfl
  have hconj : CloudB3RC53.ModularWeil.frobTate p (reducedCurveModP E p hp) ℓ =
      (e : _ →ₗ[ℤ_[ℓ]] _) ∘ₗ ρ ∘ₗ (e.symm : _ →ₗ[ℤ_[ℓ]] _) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hρ]
    exact (placeTateEquiv_frobenius E hp v hv ℓ hgood hℓ g hdec hfr x).symm
  let b := integralTateBasis E ℓ
  have hA := CloudB3RC53.ModularWeil.trace_det_of_detFormOne (LinearMap.toMatrix b b ρ)
    (((p : ℤ) + 1 - (Nat.card (reducedCurveModP E p hp).toAffine.Point : ℤ) : ℤ) : ℤ_[ℓ])
    (p : ℤ_[ℓ]) (fun n => by
      have hm : (1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) - (n : ℤ_[ℓ]) • LinearMap.toMatrix b b ρ =
          LinearMap.toMatrix b b ((1 : Module.End ℤ_[ℓ] _) - (n : ℤ_[ℓ]) • ρ) := by
        rw [map_sub, map_smul, LinearMap.toMatrix_one]
      rw [hm, LinearMap.det_toMatrix]
      have hc : (1 : Module.End ℤ_[ℓ]
          (CloudB3RC53.ModularWeil.redTate p (reducedCurveModP E p hp) ℓ)) -
          (n : ℤ_[ℓ]) • CloudB3RC53.ModularWeil.frobTate p (reducedCurveModP E p hp) ℓ =
          (e : _ →ₗ[ℤ_[ℓ]] _) ∘ₗ ((1 : Module.End ℤ_[ℓ] _) - (n : ℤ_[ℓ]) • ρ) ∘ₗ
            (e.symm : _ →ₗ[ℤ_[ℓ]] _) := by
        rw [hconj]
        refine LinearMap.ext fun y => ?_
        simp
      have hFD := DetDegree.frobeniusTateDetFormOne_proved p (reducedCurveModP E p hp)
        (reducedCurveModP_isElliptic E p hp hgood) ℓ hℓ n
      rw [hc, LinearMap.det_conj] at hFD
      exact hFD)
  refine ⟨?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b]
    exact hA.1
  · rw [← LinearMap.det_toMatrix b]
    exact hA.2

include hv in
/-- **PROVED**, trace and determinant of an arithmetic Frobenius at `v` on the actual rational
Tate module `ℚ_ℓ ⊗ T_ℓ(E/\bar ℚ)` at a good prime `p ≠ ℓ`: trace `a_p(E)` (the existing
`WeierstrassCurve.LFunction` coefficient) and determinant `p`. Locators:
`integralTateRep_trace_det`, Mathlib `LinearMap.trace_baseChange`, `LinearMap.det_baseChange`, and
`NewformPeriodsDictionary.lFunction_prime_eq_card_ZMod`. -/
theorem rationalTateRep_trace_det [E.IsElliptic] (hgood : GoodReductionAt E (primeIdealQ p hp))
    (hℓ : ℓ ≠ p) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hdec : g ∈ v.decompositionSubgroup ℚ) (hfr : ∀ x ∈ v, g x - x ^ p ∈ v.nonunits) :
    LinearMap.trace ℚ_[ℓ] (rationalTate E ℓ) (rationalTateRep E ℓ g) = (E.LFunction p : ℚ_[ℓ]) ∧
      LinearMap.det (rationalTateRep E ℓ g) = (p : ℚ_[ℓ]) := by
  obtain ⟨ht, hd⟩ := integralTateRep_trace_det E hp v hv ℓ hgood hℓ g hdec hfr
  have : Module.Free ℤ_[ℓ] (integralTate E ℓ) := Module.Free.of_basis (integralTateBasis E ℓ)
  have : Module.Finite ℤ_[ℓ] (integralTate E ℓ) := Module.Finite.of_basis (integralTateBasis E ℓ)
  rw [rationalTateRep, Representation.baseChange_apply, LinearMap.trace_baseChange,
    LinearMap.det_baseChange, ht, hd, lFunction_prime_eq_card_ZMod E p hp hgood]
  refine ⟨?_, ?_⟩
  · rw [map_intCast]
  · rw [map_natCast]

end Tate

section Main

open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion

/-- **PROVED**, `GlobalGoodReductionTraceReading` of `NewformGlueG0/GaloisCompletion.lean`, exactly
as stated (Silverman VII.4.1, VII.7.1 and V.2.3.1). Let `E/ℚ` be elliptic with good reduction at
`p ≠ ℓ`.

* *Inertia.* For every place `D.place` of `\bar ℚ` above `p` and every `i` in its inertia group,
  `i` fixes all `ℓ`-power torsion of `E(\bar ℚ)` (`map_eq_self_of_mem_inertiaSubgroup`, through
  reduction at that place), so it acts trivially on `T_ℓ(E)` and on `ℚ_ℓ ⊗ T_ℓ(E)`.
* *Frobenius.* An integral-closure Frobenius `g` at `p` is an arithmetic Frobenius at an actual
  place of `\bar ℚ` above `p` (`Completion.Arithmetic.place_of_isFrobAt`), and
  `rationalTateRep_trace_det` gives trace `a_p(E)` and determinant `p`.

The premise `GoodReductionFrobeniusTraceDictionaryQ` of the reading is not used: the global
statement is proved directly from reduction at a place of `\bar ℚ`, the proved determinant form
`DetDegree.frobeniusTateDetFormOne_proved` and the proved rational integral model
`exists_rationalModel`. -/
theorem globalGoodReductionTraceReading_proved : GlobalGoodReductionTraceReading := by
  intro _ E _ ℓ _ p hp hpℓ hgood
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun D i hi => ?_, fun g hg => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hi
    have hv : ((p : ℕ) : AlgebraicClosure ℚ) ∈ D.place.nonunits := D.liesOver
    have := charP_residueField_place hp D.place hv
    let _ : Algebra (ZMod p) (ResidueField D.place) :=
      (ZMod.castHom dvd_rfl (ResidueField D.place)).toAlgebra
    have h1 := integralTateRep_eq_one_of_mem_inertiaSubgroup E hp D.place hv ℓ hgood hpℓ.symm s hs
    change Representation.baseChange ℚ_[ℓ] (integralTateRep E ℓ) _ = 1
    rw [Representation.baseChange_apply, Subgroup.coe_subtype, h1, LinearMap.baseChange_one]
  · obtain ⟨v, hv, hfr⟩ := Arithmetic.place_of_isFrobAt g p hp hg
    have := charP_residueField_place hp v hv
    let _ : Algebra (ZMod p) (ResidueField v) := (ZMod.castHom dvd_rfl (ResidueField v)).toAlgebra
    exact rationalTateRep_trace_det E hp v hv ℓ hgood hpℓ.symm g hfr.1 hfr.2

/-- **PROVED**, the actual good local Tate polynomial is the minimal-reduction polynomial, with no
remaining reading. Locators: `Completion.localTatePolynomial_of_good` and
`globalGoodReductionTraceReading_proved`. -/
theorem localTatePolynomial_of_good_proved (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
    [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (D : LocalArithmeticFrobenius p) :
    localTatePolynomial E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) :=
  localTatePolynomial_of_good globalGoodReductionTraceReading_proved E ℓ p hp hpℓ hgood D

end Main

end ZInQ.Contrib.RC53Assist.GlobalTrace
