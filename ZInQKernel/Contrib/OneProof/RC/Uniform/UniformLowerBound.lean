import ZInQKernel.Contrib.OneProof.RC.Uniform.Determinant
import ZInQKernel.Contrib.OneProof.RC.Uniform.Switch
import ZInQKernel.Contrib.OneProof.RC.Uniform.QuadraticCase
import ZInQKernel.Contrib.OneProof.RC.Uniform.KernelDetection
import ZInQKernel.Contrib.OneProof.RC.Uniform.LambdaHalf
import ZInQKernel.Contrib.OneProof.RC.Uniform.OuterContradiction
import ZInQKernel.Contrib.OneProof.RC.Uniform.HeightOneRegularity

/-!
# Lane RC16: Proposition `ex:limits-uniform-lower-bound` (uniform ring lower bound and height-one
regularity), assembled

Manuscript (11/5), tex lines 4909–4925 (statement):

> Fix `E, π`, the old local types and a bound `A`. For every ring instance satisfying the hypotheses
> of Proposition `ex:arith-central-calibration` and `ω(k) ≤ A`, the actual primitive coordinate
> satisfies `v₂u_prim ≥ −C(E,A)`, `u_prim ∈ Λ[1/2]`, where the first valuation is that of `𝒪` and the
> constant is independent of the active support and companion field. Consequently its central
> specialization and (4.6) imply (3.5).
>
> The regularity assertion also holds at the unknown full-corank-one base used in
> Lemma `ex:arith-base-zero`. The uniform numerical lower bound here is asserted only for the known
> simple-zero ring instances; it is not asserted at that unknown base.

This file assembles the three conclusions from the lane's `PROVED` algebra and Elliot's steps, which
enter as the inputs named below (each with its tex lines):

* (5.5): `uniform_lower_bound_of_switchProcess` (`OuterContradiction.lean`) applied to the outer
  switching processes (inputs: (5.1) bounded models, (5.3) outer DVR, (5.4) and the kernel detection,
  the switch lemma; fields of `OuterSwitchProcess`). The terminal Schur/Cramer data are produced from
  the minimal-model matrices by `terminalData_of_minimalModels` below, using `Determinant.lean`.
  The bounded size is fixed on an outer-large set by `exists_eventually_size_eq` from (5.1).
* `u_prim ∈ Λ[1/2]`: `regular_of_switchProcess` (`HeightOneRegularity.lean`) at every height-one
  prime `𝔭 ≠ (2)`, then the intersection formula `mem_range_lambdaHalf_iff_forall_height_one`
  (`LambdaHalf.lean`).
* (3.5): the central specialization and (4.6), `eq35_of_lambdaHalf` (`LambdaHalf.lean`), after the
  identification of the `𝒪`-valuation on `Λ[1/2]` (`GLUE`, `ValuationOfO` below).
-/

namespace ZInQ.Manuscript.RC.Uniform

open Filter Matrix

/-! ## Regularity at a principal prime of `Λ` -/

/-- Membership in the localization `Λ_(p)` inside `Frac Λ`, in the form of `LambdaHalf.lean`:
`x · s ∈ Λ` for some `s ∉ (p)`. For `p` prime this is `x ∈ Λ_(p)` (`mem_range_atPrime_iff`).
Kind: definition. -/
def RegularAt (p : Lambda) (x : FractionRing Lambda) : Prop :=
  ∃ a s : Lambda, s ∉ Ideal.span {p} ∧
    x * algebraMap Lambda (FractionRing Lambda) s = algebraMap Lambda (FractionRing Lambda) a

/-- `Λ_(p)` is closed under products (`p` prime). Kind: PROVED. -/
theorem regularAt_mul {p : Lambda} (hp : Prime p) {x y : FractionRing Lambda}
    (hx : RegularAt p x) (hy : RegularAt p y) : RegularAt p (x * y) := by
  obtain ⟨a, s, hs, hxs⟩ := hx
  obtain ⟨b, r, hr, hyr⟩ := hy
  have hprime : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨a * b, s * r, fun h => ?_, ?_⟩
  · rcases hprime.mem_or_mem h with h' | h'
    · exact hs h'
    · exact hr h'
  · rw [map_mul, map_mul]
    calc x * y * ((algebraMap Lambda (FractionRing Lambda)) s *
          (algebraMap Lambda (FractionRing Lambda)) r)
        = (x * (algebraMap Lambda (FractionRing Lambda)) s) *
          (y * (algebraMap Lambda (FractionRing Lambda)) r) := by ring
      _ = _ := by rw [hxs, hyr]

/-- Membership in the genuine localization `Λ_𝔭 = Localization.AtPrime 𝔭` inside `Frac Λ`, for a prime
`𝔭` of `Λ`: the ring `R` of the height-one paragraph ("put `R = Λ_𝔭`", tex 4977–4978).
Kind: definition. -/
def RegularAtPrime (P : Ideal Lambda) [P.IsPrime] (x : FractionRing Lambda) : Prop :=
  x ∈ (Localization.mapToFractionRing (FractionRing Lambda) P.primeCompl
    (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)).range

/-- **Height-one regularity gives `u_prim ∈ Λ[1/2]`** (tex 4976–5197). For an element `u` of `Frac Λ`
(the generic class-functional coordinate of the actual primitive class), suppose either `u = 0` (the
actual generic class is zero, tex 5196–5197) or, at every height-one prime `𝔭 ≠ (2)` of `Λ`, the
switching process of `HeightOneRegularity.lean` over `R = Λ_𝔭` starts at `u` (its steps are Elliot's,
tex 4976–5193; their algebra is in `QuadraticCase.lean`, `Switch.lean`, `KernelDetection.lean`).
Then, by the intersection formula `Λ[1/2] = ⋂_{𝔭 ≠ (2)} Λ_𝔭` (`mem_range_lambdaHalf_iff_forall_height_one`,
"the normal-domain intersection formula", tex 5194–5195), `u` lies in the image of the genuine
`Λ[1/2]`. This applies verbatim at the unknown full-corank-one base: "This requires no uniform outer
valuation bound at that base" (tex 5199–5200). Kind: PROVED from the inputs. -/
theorem mem_lambdaHalf_of_regularity (u : FractionRing Lambda)
    (hreg : u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u) :
    u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hht hne
  rcases hreg with rfl | hreg
  · exact Subalgebra.zero_mem _
  · obtain ⟨Pr, S₀, hS₀⟩ := hreg P hht hne
    rw [← hS₀]
    exact regular_of_switchProcess (fun x y hx hy => Subalgebra.mul_mem _ hx hy) Pr S₀

/-! ## The bounded size on an outer-large set, and the terminal Cramer data -/

/-- "fixing the bounded `n` on an outer-large set" (tex 4936–4938): if the ranks `n_j` of the minimal
completed models are bounded by `N` (the bound (5.1), `N(E,A,j) ≤ 56ω(2N)+8A+56j+70`, lane RC6), one
value `n` is taken on an outer-large set. Kind: PROVED. -/
theorem exists_eventually_size_eq {ι : Type*} (𝒰 : Ultrafilter ι) (size : ι → ℕ) (N : ℕ)
    (hN : ∀ j, size j ≤ N) : ∃ n ≤ N, ∀ᶠ j in (𝒰 : Filter ι), size j = n := by
  induction N generalizing size with
  | zero => exact ⟨0, le_rfl, Eventually.of_forall (fun j => Nat.le_zero.mp (hN j))⟩
  | succ N ih =>
    rcases (Ultrafilter.eventually_or).1
        (Eventually.of_forall (fun j => em (size j = N + 1)) :
          ∀ᶠ j in (𝒰 : Filter ι), size j = N + 1 ∨ ¬ size j = N + 1) with h | h
    · exact ⟨N + 1, le_rfl, h⟩
    · -- restrict to the outer-large set where `size j ≤ N`
      have h' : ∀ᶠ j in (𝒰 : Filter ι), size j ≤ N := by
        filter_upwards [h] with j hj
        have := hN j
        omega
      -- replace `size` by a function bounded by `N` agreeing with it there
      obtain ⟨n, hn, hne⟩ := ih (fun j => min (size j) N) (fun j => min_le_right _ _)
      refine ⟨n, le_trans hn (Nat.le_succ N), ?_⟩
      filter_upwards [hne, h'] with j hj1 hj2
      rw [← hj1, min_eq_left hj2]

variable {K : Type*} [Field K]

/-- **The terminal data from the minimal models** (tex 4957–4961): at terminal outer dimension one,
the inner minimal models `[K^{n+1} --D_j--> K^{n+1}]` (one fixed size on an outer-large set), inner
cycles `z_j` and closed functionals `λ_j`, the inner class-functional coordinates computed through
any admissible complements, and one maximal minor position `(k₀, j₀)` whose inner minors `Δ_j` are
nonzero, satisfy the Schur/Cramer relation `u_j Δ_j = ±z_j(j₀) λ_j(k₀)` (`classFunctionalCoord_cramer`
in `Determinant.lean`). If moreover `z_j` is integral, `2^a λ_j` is integral and the minors are
integral and nonzero in `𝒪_∞`, this is exactly the `terminal` field of `OuterSwitchProcess`.
Kind: PROVED. -/
theorem terminalData_of_minimalModels (v : AddValuation K (WithTop ℤ)) {ι : Type*}
    (𝒰 : Ultrafilter ι) (a n : ℕ) (D : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : ι → Fin (n + 1) → K) (w : ι → Fin n → Fin (n + 1) → K) (y : ι → Fin (n + 1) → K)
    (k0 j0 : Fin (n + 1))
    (hz : ∀ j, D j *ᵥ z j = 0) (hlam : ∀ j, lam j ᵥ* D j = 0)
    (hden : ∀ j, detCols (colsDWY (D j) (w j) (y j)) ≠ 0)
    (hΔ0 : ∀ j, ((D j).submatrix k0.succAbove j0.succAbove).det ≠ 0)
    (hα : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (z j j0))
    (hβ : ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (lam j k0))
    (hΔint : ∀ᶠ j in (𝒰 : Filter ι),
      (0 : WithTop ℤ) ≤ v (((D j).submatrix k0.succAbove j0.succAbove).det))
    (hΔ : ¬ OuterNegligible v 𝒰 (fun j => ((D j).submatrix k0.succAbove j0.succAbove).det)) :
    ∃ (α β Δ s : ι → K), (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ᶠ j in (𝒰 : Filter ι),
        classFunctionalCoordWith (D j) (z j) (lam j) (w j) (y j) * Δ j = s j * (α j * β j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j)) ∧
      ¬ OuterNegligible v 𝒰 Δ := by
  refine ⟨fun j => z j j0, fun j => lam j k0,
    fun j => ((D j).submatrix k0.succAbove j0.succAbove).det,
    fun _ => (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)), fun _ => cramerSign_eq_or n j0 k0,
    Eventually.of_forall (fun j => ?_), hα, hβ, hΔint, hΔ⟩
  exact (classFunctionalCoord_cramer (D j) (z j) (lam j) (hz j) (hlam j) k0 j0 (hΔ0 j)
    (w j) (y j) (hden j)).1

/-! ## The valuation of `𝒪` on `Λ[1/2]` -/

/-- `Λ_(2) ∩ Λ[1/2] = Λ` inside `Frac Λ`: an element of `Λ[1/2]` that is regular at `(2)` lies in `Λ`
(because `2` is prime in `Λ`). Kind: PROVED. -/
theorem mem_lambda_of_regularAt_two {x : FractionRing Lambda} (hx : RegularAt 2 x)
    (hx' : ∃ a : Lambda, ∃ m : ℕ, x * algebraMap Lambda (FractionRing Lambda) (2 ^ m) =
      algebraMap Lambda (FractionRing Lambda) a) :
    ∃ c : Lambda, x = algebraMap Lambda (FractionRing Lambda) c := by
  obtain ⟨b, s, hs, hxs⟩ := hx
  obtain ⟨a, m, hxa⟩ := hx'
  have hinj := IsFractionRing.injective Lambda (FractionRing Lambda)
  -- `a s = b 2^m` in `Λ`
  have hab : a * s = b * 2 ^ m := by
    apply hinj
    rw [map_mul, map_mul, ← hxa, ← hxs]
    ring
  -- `2^m ∣ a`, since `2 ∤ s`
  have hs2 : ¬ (2 : Lambda) ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)
  have hdvd : (2 : Lambda) ^ m ∣ a := by
    have h1 : (2 : Lambda) ^ m ∣ a * s := ⟨b, by rw [hab, mul_comm]⟩
    exact (Prime.pow_dvd_of_dvd_mul_right prime_two_lambda m hs2 h1)
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, ?_⟩
  have h2m : algebraMap Lambda (FractionRing Lambda) (2 ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m prime_two_lambda.ne_zero)
  apply mul_right_cancel₀ h2m
  rw [hxa, hc, map_mul, mul_comm]

/-- The identification of the valuation of `𝒪` on `Frac Λ` (`GLUE`). `𝒪 = (Λ_(2))^` is the completion of
the discrete valuation ring `Λ_(2)` (tex 3729–3730; `Λ` is a UFD, `lambda_ufd`, and `(2)` is a
height-one prime, so `Λ_(2)` is a DVR with uniformizer `2`: Matsumura, *Commutative Ring Theory*,
Thm 11.5 (UNVERIFIED locator)). For the embedding `ι : Frac Λ → K = Frac 𝒪` and the valuation `v` of
`𝒪`, an element is `𝒪`-integral iff it lies in `Λ_(2)`, and `v 2 = 1`. Kind: GLUE (a property of the
genuine `v₂`, not constructed here). -/
structure ValuationOfO (v : AddValuation K (WithTop ℤ)) (ι : FractionRing Lambda →+* K) : Prop where
  /-- `𝒪 ∩ Frac Λ = Λ_(2)`. -/
  integral_iff : ∀ x, (0 : WithTop ℤ) ≤ v (ι x) ↔ RegularAt 2 x
  /-- `2` is a uniformizer. -/
  val_two : v (ι 2) = 1

/-- (5.5) in integral form on `Λ[1/2]`: from `v₂ u ≥ −C` in `𝒪` and `u ∈ Λ[1/2]` one gets
`2^C u ∈ Λ`. Kind: PROVED from the GLUE identification `ValuationOfO`. -/
theorem integral_form_of_valuation_bound (v : AddValuation K (WithTop ℤ))
    (ι : FractionRing Lambda →+* K) (hO : ValuationOfO v ι) (C : ℕ) (u : LambdaHalf)
    (hC : (((-C : ℤ)) : WithTop ℤ) ≤ v (ι (lambdaHalfToFrac u))) :
    (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range := by
  set x := lambdaHalfToFrac u with hxdef
  -- `v (2^C x) ≥ 0`
  have h1 : (0 : WithTop ℤ) ≤ v (ι (2 ^ C * x)) := by
    rw [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow, hO.val_two]
    induction hvx : v (ι x) using WithTop.recTopCoe with
    | top => simp
    | coe m =>
      rw [hvx] at hC
      have hm : -(C : ℤ) ≤ m := by exact_mod_cast hC
      have : (0 : ℤ) ≤ C • (1 : ℤ) + m := by simp; omega
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.coe_add]
      exact_mod_cast this
  have hreg : RegularAt 2 (2 ^ C * x) := (hO.integral_iff _).mp h1
  -- `2^C x ∈ Λ[1/2]`
  have hmem : 2 ^ C * x ∈ lambdaHalfToFrac.range :=
    ⟨2 ^ C * u, by rw [map_mul, map_pow, map_ofNat]; rfl⟩
  rw [mem_range_lambdaHalf_iff_forall_prime] at hmem
  have hx' : ∃ a : Lambda, ∃ m : ℕ, (2 ^ C * x) * algebraMap Lambda (FractionRing Lambda) (2 ^ m) =
      algebraMap Lambda (FractionRing Lambda) a :=
    (mem_lambdaHalf_iff_forall_prime _).mpr hmem
  obtain ⟨c, hc⟩ := mem_lambda_of_regularAt_two hreg hx'
  refine ⟨c, lambdaHalfToFrac_injective ?_⟩
  rw [map_mul, map_pow, map_ofNat, hc]
  exact lambdaHalfToFrac.commutes c

/-! ## The proposition -/

/-- **Proposition `ex:limits-uniform-lower-bound`** (tex 4909–5202), assembled.

Data: the field `K = Frac 𝒪` with the valuation `v = v₂` of `𝒪` and `ι : Frac Λ → K`, identified on
`Frac Λ` by the GLUE `ValuationOfO`; the known simple-zero ring instances `Inst` with `ω(k) ≤ A`, with
primitive coordinates `uprim i ∈ Frac Λ`.

Inputs (`ELLIOT`, the steps of the proof; their algebra is `PROVED` in this lane):
* `outer`: for every sequence of instances, the outer switching process along the fixed nonprincipal
  ultrafilter starts at the primitive coordinates (tex 4927–4964; fields of `OuterSwitchProcess`);
* `regular`: at every height-one prime `𝔭 ≠ (2)` of `Λ`, the height-one switching process over
  `R = Λ_𝔭` starts at the primitive coordinate, or the coordinate is zero (tex 4976–5197; fields of
  `RegularitySwitchProcess`).

Conclusions (PROVED from the inputs):
1. (5.5): `∃ C, ∀ i, v₂ u_prim(i) ≥ −C`, `C` independent of the active support and companion field;
2. `u_prim(i) ∈ Λ[1/2]` for every instance;
3. (3.5), by Elliot's route "(5.5) [...] with (4.6) and `Σ_{p|k} t_p ≤ 2A`" (tex 5200–5202): for an
   instance with `u_prim(0) ≠ 0` satisfying (4.6) with error `C₀`, `0 ≤ t_p ≤ 2` and `ω(k) ≤ A`,
   `2 j_rc ≥ 4ω(h) + s(h) + s(hk) − C_R(E,A)`, `C_R(E,A) = C + C₀ + 2A` (the sharper constant `C + C₀`,
   which needs only `t_p ≥ 0`, is `eq35_of_lambdaHalf`).

The unknown-base regularity is `mem_lambdaHalf_of_regularity`, which uses no lower bound. -/
theorem exLimitsUniformLowerBound (v : AddValuation K (WithTop ℤ))
    (ι : FractionRing Lambda →+* K) (hO : ValuationOfO v ι) (A : ℕ)
    {Inst : Type*} (uprim : Inst → FractionRing Lambda)
    (outer : ∀ inst : ℕ → Inst, ∃ (a : ℕ) (P : OuterSwitchProcess v (Filter.hyperfilter ℕ) a)
      (S₀ : P.Stage), ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        v (P.coord S₀ j) = v (ι (uprim (inst j))))
    (regular : ∀ i, uprim i = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 →
      P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = uprim i) :
    ∃ C : ℕ,
      (∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ v (ι (uprim i))) ∧
      (∀ i, ∃ uh : LambdaHalf, lambdaHalfToFrac uh = uprim i ∧
        (2 : LambdaHalf) ^ C * uh ∈ (algebraMap Lambda LambdaHalf).range ∧
        ∀ (j_rc ω sh shk C₀ : ℤ) (P : Finset ℕ) (t : ℕ → ℤ),
          centralSpecialization uh ≠ 0 → (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) → P.card ≤ A →
          |Padic.valuation (centralSpecialization uh) -
              (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀ →
          2 * j_rc ≥ 4 * ω + sh + shk - ((C : ℤ) + (C₀ + 2 * A))) := by
  obtain ⟨C, hC⟩ := uniform_lower_bound_of_switchProcess v (fun i => ι (uprim i)) outer
  refine ⟨C, hC, fun i => ?_⟩
  obtain ⟨uh, huh0⟩ := mem_lambdaHalf_of_regularity (uprim i) (regular i)
  have huh : lambdaHalfToFrac uh = uprim i := huh0
  have hint := integral_form_of_valuation_bound v ι hO C uh (by rw [huh]; exact hC i)
  exact ⟨uh, huh, hint, fun j_rc ω sh shk C₀ P t hu0 ht hP h46 =>
    eq35_of_eq55_eq46_absorbed ht hP h46 ((valuation_central_ge C uh hint).resolve_left hu0)⟩

end ZInQ.Manuscript.RC.Uniform
