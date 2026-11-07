import ZInQKernel.Multiplication.Local.FormalLogarithm

/-!
# The formal group law of `y² = x³ + A x`

Blueprint: `multiplication/local/formal-group-law.md`, part 2.

`formalAdd A` is a commutative formal group law with inverse `-T` (`formalGroupLaw_exists`).
Over a field `F` of characteristic `0` the identities follow from
`log(F(T₁, T₂)) = log(T₁) + log(T₂)` (`formalLog_formalAdd_aux`): `log` has a compositional
inverse (Mathlib's `PowerSeries.substInvOfIsUnit`, as its linear coefficient is `1`), so
`f ↦ log(f)` is injective on series without constant term (`subst_formalLog_injective`), and
both sides of each identity have the same logarithm (`log` is odd for the inverse). Over the
valuation ring `𝒪 ⊂ K` the identities follow by mapping to `K` (coefficientwise injective,
and compatible with substitution, `MvPowerSeries.map_subst`). The evaluation
`z(P + Q) = F(z(P), z(Q))` is `hasSum_formalAdd`.
-/

namespace ZInQ.Mult

open MvPowerSeries WithZero

/-! ### Over a field of characteristic `0` -/

section Field

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem constantCoeff_formalLog (A : F) : PowerSeries.constantCoeff (formalLog A) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalLog, PowerSeries.coeff_mk,
    logCoeffA_zero]

omit [CharZero F] in
theorem coeff_one_formalLog (A : F) : PowerSeries.coeff 1 (formalLog A) = 1 := by
  rw [formalLog, PowerSeries.coeff_mk, logCoeffA_one]

omit [CharZero F] in
/-- `f ↦ log(f)` is injective on power series without constant term. -/
theorem subst_formalLog_injective (A : F) {σ : Type*} {f g : MvPowerSeries σ F}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : PowerSeries.subst f (formalLog A) = PowerSeries.subst g (formalLog A)) : f = g := by
  have hu : IsUnit (PowerSeries.coeff 1 (formalLog A)) := by
    rw [coeff_one_formalLog]; exact isUnit_one
  have hE := PowerSeries.subst_substInvOfIsUnit_left (formalLog A) (constantCoeff_formalLog A) hu
  have hL : PowerSeries.HasSubst (formalLog A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalLog A)
  have key : ∀ {k : MvPowerSeries σ F}, constantCoeff k = 0 →
      k = PowerSeries.subst (PowerSeries.subst k (formalLog A))
        (PowerSeries.substInvOfIsUnit (formalLog A) hu) := by
    intro k hk
    have hk' := PowerSeries.HasSubst.of_constantCoeff_zero hk
    rw [← PowerSeries.subst_comp_subst_apply hL hk', hE, PowerSeries.subst_X hk']
  rw [key hf, key hg, h]

omit [CharZero F] in
theorem hasSubst_pair {σ : Type*} {a b : MvPowerSeries σ F} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : MvPowerSeries.HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb]

theorem constantCoeff_subst_formalAdd {R : Type*} [CommRing R] (A : R) {σ : Type*}
    {a b : MvPowerSeries σ R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (MvPowerSeries.subst ![a, b] (formalAdd A)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i <;> simp [ha, hb]) (fun i => by fin_cases i <;> simp [ha, hb])
    (constantCoeff_formalAdd A)

/-- `log(F(a, b)) = log(a) + log(b)`. -/
theorem subst_formalLog_subst_formalAdd (A : F) {σ : Type*} {a b : MvPowerSeries σ F}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![a, b] (formalAdd A)) (formalLog A) =
      PowerSeries.subst a (formalLog A) + PowerSeries.subst b (formalLog A) := by
  have hab := hasSubst_pair ha hb
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_formalAdd A)
  have h0 := (PowerSeries.HasSubst.X (S := F) (0 : Fin 2)).const
  have h1 := (PowerSeries.HasSubst.X (S := F) (1 : Fin 2)).const
  calc PowerSeries.subst (MvPowerSeries.subst ![a, b] (formalAdd A)) (formalLog A)
      = MvPowerSeries.subst ![a, b] (PowerSeries.subst (formalAdd A) (formalLog A)) := by
        rw [PowerSeries.subst_def, PowerSeries.subst_def,
          MvPowerSeries.subst_comp_subst_apply hF.const hab]
    _ = MvPowerSeries.subst ![a, b]
          (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalLog A) +
            PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (formalLog A)) := by
        rw [formalLog_formalAdd_aux]
    _ = _ := by
        rw [MvPowerSeries.subst_add hab, PowerSeries.subst_def, PowerSeries.subst_def,
          MvPowerSeries.subst_comp_subst_apply h0 hab, MvPowerSeries.subst_comp_subst_apply h1 hab,
          PowerSeries.subst_def, PowerSeries.subst_def]
        simp only [MvPowerSeries.subst_X hab]
        rfl

local notation "Y₀" => (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) F)
local notation "Y₁" => (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) F)
local notation "Y₂" => (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) F)

theorem formalAdd_assoc_field (A : F) :
    (formalAdd A).subst ![(formalAdd A).subst ![Y₀, Y₁], Y₂] =
      (formalAdd A).subst ![Y₀, (formalAdd A).subst ![Y₁, Y₂]] := by
  have c01 := constantCoeff_subst_formalAdd A (constantCoeff_X (R := F) (0 : Fin 3))
    (constantCoeff_X 1)
  have c12 := constantCoeff_subst_formalAdd A (constantCoeff_X (R := F) (1 : Fin 3))
    (constantCoeff_X 2)
  refine subst_formalLog_injective A (constantCoeff_subst_formalAdd A c01 (constantCoeff_X 2))
    (constantCoeff_subst_formalAdd A (constantCoeff_X 0) c12) ?_
  rw [subst_formalLog_subst_formalAdd A c01 (constantCoeff_X 2),
    subst_formalLog_subst_formalAdd A (constantCoeff_X 0) c12,
    subst_formalLog_subst_formalAdd A (constantCoeff_X 0) (constantCoeff_X 1),
    subst_formalLog_subst_formalAdd A (constantCoeff_X 1) (constantCoeff_X 2)]
  ring

theorem formalAdd_comm_field (A : F) :
    formalAdd A = (formalAdd A).subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] := by
  refine subst_formalLog_injective A (constantCoeff_formalAdd A)
    (constantCoeff_subst_formalAdd A (constantCoeff_X 1) (constantCoeff_X 0)) ?_
  rw [subst_formalLog_subst_formalAdd A (constantCoeff_X 1) (constantCoeff_X 0),
    formalLog_formalAdd_aux]
  ring

omit [CharZero F] in
/-- `log` is odd: `log(-T) = -log(T)`. -/
theorem subst_neg_X_formalLog (A : F) :
    PowerSeries.subst (-PowerSeries.X : PowerSeries F) (formalLog A) = -formalLog A := by
  rw [show (-PowerSeries.X : PowerSeries F) = (-1 : F) • PowerSeries.X by simp,
    ← PowerSeries.rescale_eq_subst]
  ext n
  rw [PowerSeries.coeff_rescale, map_neg, formalLog, PowerSeries.coeff_mk]
  rcases Nat.even_or_odd n with hn | hn
  · rw [logCoeffA_eq_zero_of_even hn]; simp
  · rw [hn.neg_one_pow]; ring

theorem formalAdd_inv_field (A : F) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries F), -PowerSeries.X] (formalAdd A) = 0 := by
  have hX : constantCoeff (PowerSeries.X : PowerSeries F) = 0 := PowerSeries.constantCoeff_X
  have hnX : constantCoeff (-PowerSeries.X : PowerSeries F) = 0 := by
    rw [map_neg]; exact neg_eq_zero.mpr hX
  refine subst_formalLog_injective A (constantCoeff_subst_formalAdd A hX hnX) (map_zero _) ?_
  rw [subst_formalLog_subst_formalAdd A hX hnX, PowerSeries.subst_zero_of_constantCoeff_zero
    (constantCoeff_formalLog A)]
  have h1 : PowerSeries.subst (PowerSeries.X : PowerSeries F) (formalLog A) = formalLog A :=
    PowerSeries.X_subst _
  have h2 := subst_neg_X_formalLog A
  rw [show (PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit F) (formalLog A) :
      MvPowerSeries Unit F) = formalLog A from h1]
  rw [show (PowerSeries.subst (-PowerSeries.X : MvPowerSeries Unit F) (formalLog A) :
      MvPowerSeries Unit F) = -formalLog A from h2]
  ring

end Field

/-! ### Change of coefficients -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)

theorem map_chordSlope (A : R) : MvPowerSeries.map h (chordSlope A) = chordSlope (h A) := by
  ext n; rw [coeff_map, coeff_chordSlope, coeff_chordSlope, omegaCoeff_map]

theorem map_omegaFst (A : R) : MvPowerSeries.map h (omegaFst A) = omegaFst (h A) := by
  ext n; rw [coeff_map, coeff_omegaFst, coeff_omegaFst]; split_ifs <;> simp [omegaCoeff_map]

theorem map_chordInv (A : R) : MvPowerSeries.map h (chordInv A) = chordInv (h A) := by
  have e1 := congrArg (MvPowerSeries.map h) (chordInv_mul A)
  rw [map_mul, map_one, map_add, map_one, map_mul, map_C, map_pow, map_chordSlope] at e1
  have e2 := chordInv_mul (h A)
  calc MvPowerSeries.map h (chordInv A)
      = MvPowerSeries.map h (chordInv A) *
          ((1 + MvPowerSeries.C (h A) * chordSlope (h A) ^ 2) * chordInv (h A)) := by
        rw [mul_comm (1 + _), e2, mul_one]
    _ = chordInv (h A) := by rw [← mul_assoc, e1, one_mul]

theorem map_formalAdd (A : R) : MvPowerSeries.map h (formalAdd A) = formalAdd (h A) := by
  rw [formalAdd_eq, formalAdd_eq]
  simp only [map_add, map_mul, map_sub, map_X, map_C, map_ofNat, map_chordSlope, map_omegaFst,
    map_chordInv]

theorem map_injective_of_injective {σ : Type*} {h : R →+* S} (hi : Function.Injective h) :
    Function.Injective (MvPowerSeries.map (σ := σ) h) := fun f g e => by
  ext n; exact hi (by rw [← coeff_map, ← coeff_map, e])

theorem comp_pair {X Y : Type*} (f : X → Y) (a b : X) : (fun i => f (![a, b] i)) = ![f a, f b] := by
  funext i; fin_cases i <;> rfl

theorem map_subst_pair {σ : Type*} {a b : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.map h (f.subst ![a, b]) =
      (MvPowerSeries.map h f).subst ![MvPowerSeries.map h a, MvPowerSeries.map h b] := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb]),
    comp_pair]

/-- The linear coefficients of `formalAdd A` are `1`. -/
theorem coeff_single_formalAdd (A : R) (i : Fin 2) :
    coeff (Finsupp.single i 1) (formalAdd A) = 1 := by
  classical
  rw [formalAdd_eq, map_add, map_add]
  have hT : coeff (Finsupp.single i 1) (2 * MvPowerSeries.C A * chordSlope A *
      (omegaFst A - chordSlope A * MvPowerSeries.X 0) * chordInv A) = 0 := by
    apply coeff_of_lt_order
    have h1 : (1 : ℕ∞) ≤ (2 * MvPowerSeries.C A * chordSlope A).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp [constantCoeff_chordSlope])
    have h2 : (1 : ℕ∞) ≤ (omegaFst A - chordSlope A * MvPowerSeries.X 0).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp [constantCoeff_omegaFst])
    calc (((Finsupp.single i 1).degree : ℕ) : ℕ∞) = 1 := by simp [Finsupp.degree_single]
      _ < 1 + 1 := by norm_num
      _ ≤ _ := add_le_add h1 h2
      _ ≤ _ := le_order_mul
      _ ≤ _ := le_self_add
      _ ≤ _ := le_order_mul
  rw [hT, add_zero]
  fin_cases i <;> simp [coeff_X, Finsupp.single_eq_single_iff]

end Map

/-! ### Over the valuation ring -/

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [DecidableEq K]

omit [DecidableEq K] in
theorem vK_integer_nonneg (A : Valued.integer K) : 0 ≤ vK K (A : K) := by
  exact (le_ordOf_iff (Valued.v : Valuation K ℤᵐ⁰) (A : K) 0).mpr (by
    rw [neg_zero, exp_zero]; exact A.2)

/-- **The formal group law.** For `A` in the valuation ring `𝒪` of a complete `ℤᵐ⁰`-valued field
`K` of characteristic `0`, the chord series `formalAdd A ∈ 𝒪⟦T₁, T₂⟧` is a commutative formal
group law `F(T₁, T₂) = T₁ + T₂ + ⋯` with formal inverse `i(T) = -T` (`F(T, -T) = 0`), and
`z(P + Q) = F(z(P), z(Q))` for `P, Q ∈ W₁(K)`, the double series converging. -/
theorem formalGroupLaw_exists [CompleteSpace K] [CharZero K] (A : Valued.integer K) :
    ∃ F : FormalGroup (Valued.integer K), F.toPowerSeries = formalAdd A ∧ F.IsComm ∧
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (Valued.integer K)), -PowerSeries.X]
        F.toPowerSeries = 0 ∧
      ∀ P ∈ W1 (vK K) (A : K), ∀ Q ∈ W1 (vK K) (A : K),
        HasSum (fun n : Fin 2 →₀ ℕ =>
          ((MvPowerSeries.coeff n F.toPowerSeries : Valued.integer K) : K) *
            zCoord P ^ n 0 * zCoord Q ^ n 1) (zCoord (P + Q)) := by
  set ι : Valued.integer K →+* K := (Valued.integer K).subtype with hιdef
  have hι : Function.Injective ι := Subtype.val_injective
  have hmap : MvPowerSeries.map ι (formalAdd A) = formalAdd (A : K) := map_formalAdd ι A
  have cX : ∀ {n : ℕ} (i : Fin n),
      constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin n) (Valued.integer K)) = 0 :=
    fun i => constantCoeff_X i
  let F : FormalGroup (Valued.integer K) :=
    { toPowerSeries := formalAdd A
      zero_constantCoeff := constantCoeff_formalAdd A
      lin_coeff_X := coeff_single_formalAdd A 0
      lin_coeff_Y := coeff_single_formalAdd A 1
      assoc := by
        apply map_injective_of_injective hι
        rw [map_subst_pair ι (constantCoeff_subst_formalAdd A (cX 0) (cX 1)) (cX 2),
          map_subst_pair ι (cX 0) (constantCoeff_subst_formalAdd A (cX 1) (cX 2)),
          map_subst_pair ι (cX 0) (cX 1), map_subst_pair ι (cX 1) (cX 2)]
        simp only [map_X, hmap]
        exact formalAdd_assoc_field (A : K) }
  refine ⟨F, rfl, ⟨?_⟩, ?_, ?_⟩
  · apply map_injective_of_injective hι
    show MvPowerSeries.map ι (formalAdd A) = MvPowerSeries.map ι ((formalAdd A).subst
      ![MvPowerSeries.X 1, MvPowerSeries.X 0])
    rw [map_subst_pair ι (cX 1) (cX 0)]
    simp only [map_X, hmap]
    exact formalAdd_comm_field (A : K)
  · apply map_injective_of_injective hι
    have hX : constantCoeff (PowerSeries.X : PowerSeries (Valued.integer K)) = 0 :=
      PowerSeries.constantCoeff_X
    have hnX : constantCoeff (-PowerSeries.X : PowerSeries (Valued.integer K)) = 0 := by
      rw [map_neg]; exact neg_eq_zero.mpr hX
    show MvPowerSeries.map ι (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries _),
      -PowerSeries.X] (formalAdd A)) = MvPowerSeries.map ι 0
    have hmX : MvPowerSeries.map ι (PowerSeries.X : PowerSeries (Valued.integer K)) =
        (PowerSeries.X : PowerSeries K) := map_X ι ()
    rw [map_subst_pair ι hX hnX, map_neg, map_zero, hmap, hmX]
    exact formalAdd_inv_field (A : K)
  · intro P hP Q hQ
    have := hasSum_formalAdd (vK_integer_nonneg A) hP hQ
    rw [← hmap] at this
    convert this using 2 with n
    rw [coeff_map, monoVal, mul_assoc]
    rfl

end ZInQ.Mult
