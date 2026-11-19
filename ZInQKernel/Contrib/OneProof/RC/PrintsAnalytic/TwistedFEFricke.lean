import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Twist.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Sign

/-!
# Lane RC33: the Fricke relation of a quadratic twist and its functional equation

Steps (2) and (3) of the classical proof of the twisted functional equation (the route of
Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Proposition 3.64, and
Atkin–Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*, Invent. Math. 48 (1978),
Theorem 3.1; locators UNVERIFIED, not re-read here; the Lean proof does not depend on them).
Everything in this file is PROVED, over the vendored Tau Ceti theory of the twist
`CuspForm.twist` (`f ⊗ Φ = M⁻¹ ∑_{a mod M} 𝓕Φ(a) f|[1, a/M; 0, 1]`, a cusp form on `Γ₁(L)` for
`N M ∣ L`, `M² ∣ L`) and of the Fricke completion `CuspForm.frickeCompletedL`.

Let `M ≥ 1`, `N ≥ 1` be coprime, `L = M² N`, `W_Q = [0, -1; Q, 0]` (`TauCeti.frickeGL`), and let
`F : ℍ → ℂ` satisfy `F|γ = F` for `γ ∈ Γ₀(N)` and `(√N)^{2-k} F|W_N = ε F`.

* `upperRightHom_mul_frickeGL` (the matrix identity): for integers `a, v, w` with
  `M w = 1 + N a v`, `[1, a/M; 0, 1] W_L = W_N γ [1, v/M; 0, 1] (M · 1)` with
  `γ = [M, -v; -N a, w] ∈ Γ₀(N)` (`twistGamma`).
* `slash_upperRightHom_slash_frickeGL`: hence `(√L)^{2-k} (F|[1, a/M; 0, 1])|W_L =
  ε F|[1, v/M; 0, 1]` (the scalar matrix `M · 1` acts by `M^{k-2}`, Tau Ceti's
  `ModularForm.slash_scalar`, and `(√L)^{2-k} = M^{2-k} (√N)^{2-k}`).
* `twistSum_slash_frickeGL`: for a quadratic Dirichlet character `χ` modulo `M`, the sum
  `S = ∑_a χ(a) F|[1, a/M; 0, 1]` (`twistSum`) satisfies `(√L)^{2-k} S|W_L = ε χ(-N) S`: only
  units `u` contribute, `v ≡ -(N u)⁻¹ (mod M)` (`frickeInvol`, an involution of `(ℤ/M)ˣ`), and
  `χ(-(N u)⁻¹) = χ(-N) χ(u)`.
* `coe_twist_eq_smul_twistSum`: for primitive quadratic `χ`, `f ⊗ χ = (χ(-1) G(χ)/M) S`, from
  Mathlib's `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`
  (`𝓕χ(a) = χ⁻¹(-a) G(χ)`, which vanishes off the units).
* `twist_slash_frickeGL`, `twist_frickeCompletedL_sub`: the Fricke relation
  `(√L)^{2-k} (f ⊗ χ)|W_L = ε χ(-N) (f ⊗ χ)` and the functional equation
  `Λ_L(k - s, f ⊗ χ) = i^k ε χ(-N) Λ_L(s, f ⊗ χ)` for every `s` (Tau Ceti's two-form equation
  `CuspForm.frickeCompletedL_sub_eq_I_zpow_mul`, which needs no hypothesis on the forms).
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.PrintsAnalytic.TwistedFE

variable {M N : ℕ} {k : ℤ}

/-! ### The matrix identity -/

/-- **The matrix `γ = [M, -v; -N a, w]` of `SL(2, ℤ)`** (PROVED determinant `1`), for integers
with `M w = 1 + N a v`. -/
def twistGamma (M N : ℕ) (a v w : ℤ) (hw : (M : ℤ) * w = 1 + N * a * v) : SL(2, ℤ) :=
  ⟨!![(M : ℤ), -v; -(N * a), w], by
    rw [Matrix.det_fin_two_of]; linear_combination hw⟩

/-- The entries of `twistGamma` (PROVED). -/
theorem twistGamma_coe (M N : ℕ) (a v w : ℤ) (hw : (M : ℤ) * w = 1 + N * a * v) :
    ((twistGamma M N a v w hw : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(M : ℤ), -v; -(N * a), w] := rfl

/-- **`γ ∈ Γ₀(N)`** (PROVED): its lower-left entry `-N a` is divisible by `N`. -/
theorem twistGamma_mem_Gamma0 (M N : ℕ) (a v w : ℤ) (hw : (M : ℤ) * w = 1 + N * a * v) :
    twistGamma M N a v w hw ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp [twistGamma_coe]

/-- The translation matrix `[1, x; 0, 1]` (PROVED). -/
theorem coe_upperRightHom (x : ℝ) :
    ((upperRightHom x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := rfl

/-- The image of `twistGamma` in `GL(2, ℝ)` (PROVED). -/
theorem coe_mapGL_twistGamma (M N : ℕ) (a v w : ℤ) (hw : (M : ℤ) * w = 1 + N * a * v) :
    ((mapGL ℝ (twistGamma M N a v w hw) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(M : ℝ), -v; -(N * a), w] := by
  rw [mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistGamma_coe]

/-- The scalar matrix `u · 1` of `GL(2, ℝ)` (PROVED). -/
theorem coe_scalar_two (u : ℝˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(u : ℝ), 0; 0, u] := by
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The matrix identity** (PROVED): if `M w = 1 + N a v`, then in `GL(2, ℝ)`
`[1, a/M; 0, 1] W_{M²N} = W_N γ [1, v/M; 0, 1] (M · 1)` with `γ = twistGamma M N a v w`. Both
sides are `[N M a, -1; M² N, 0]`. -/
theorem upperRightHom_mul_frickeGL [NeZero M] [NeZero N] (a v w : ℤ)
    (hw : (M : ℤ) * w = 1 + N * a * v) :
    upperRightHom ((a : ℝ) / M) * TauCeti.frickeGL ℝ (M ^ 2 * N) =
      TauCeti.frickeGL ℝ N * mapGL ℝ (twistGamma M N a v w hw) * upperRightHom ((v : ℝ) / M) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M : ℝ) (NeZero.ne _)) := by
  have hM : (M : ℝ) ≠ 0 := NeZero.ne _
  have hwR : (M : ℝ) * w = 1 + N * a * v := by exact_mod_cast hw
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_upperRightHom, coe_upperRightHom, TauCeti.coe_frickeGL, TauCeti.coe_frickeGL,
    coe_mapGL_twistGamma, coe_scalar_two]
  simp only [Matrix.mul_fin_two, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  all_goals first | linear_combination hwR | simp

/-! ### One translate under the Fricke matrix -/

/-- A translation matrix has positive determinant (PROVED). -/
theorem det_upperRightHom_pos (x : ℝ) :
    0 < ((upperRightHom x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [coe_upperRightHom, Matrix.det_fin_two_of]; norm_num

/-- The Fricke matrix has positive determinant (PROVED). -/
theorem det_frickeGL_pos [NeZero N] :
    0 < ((TauCeti.frickeGL ℝ N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have := TauCeti.val_det_frickeGL_pos (K := ℝ) (N := N)
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at this

/-- The image of `SL(2, ℤ)` in `GL(2, ℝ)` has positive determinant (PROVED). -/
theorem det_mapGL_pos (γ : SL(2, ℤ)) :
    0 < ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have h : ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    simp
  rw [h]
  exact one_pos

/-- **The normalizing constant at level `M² N`** (PROVED): `(√(M² N))^{2-k} = M^{2-k} (√N)^{2-k}`
(Tau Ceti's `atkinLehnerNormalizer`). -/
theorem atkinLehnerNormalizer_sq_mul (M N : ℕ) (k : ℤ) :
    TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k =
      (M : ℂ) ^ (2 - k) * TauCeti.atkinLehnerNormalizer N k := by
  rw [TauCeti.atkinLehnerNormalizer_mul, TauCeti.atkinLehnerNormalizer_def (M ^ 2)]
  congr 2
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg M)]
  simp

/-- **One translate under `W_{M²N}`** (PROVED). If `F|γ = F` for every `γ ∈ Γ₀(N)` and
`(√N)^{2-k} F|W_N = ε F`, and `M w = 1 + N a v`, then
`(√(M²N))^{2-k} (F|[1, a/M; 0, 1])|W_{M²N} = ε F|[1, v/M; 0, 1]`: by the matrix identity
`upperRightHom_mul_frickeGL`, with `γ = twistGamma M N a v w ∈ Γ₀(N)`, and the scalar `M · 1`
acting by `M^{k-2}`. -/
theorem slash_upperRightHom_slash_frickeGL [NeZero M] [NeZero N] {F : ℍ → ℂ}
    (hF0 : ∀ g : Gamma0 N, F ∣[k] mapGL ℝ (g : SL(2, ℤ)) = F) {ε : ℂ}
    (hFW : TauCeti.atkinLehnerNormalizer N k • (F ∣[k] TauCeti.frickeGL ℝ N) = ε • F)
    (a v w : ℤ) (hw : (M : ℤ) * w = 1 + N * a * v) :
    TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
        ((F ∣[k] upperRightHom ((a : ℝ) / M)) ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) =
      ε • (F ∣[k] upperRightHom ((v : ℝ) / M)) := by
  have hn : TauCeti.atkinLehnerNormalizer N k ≠ 0 :=
    TauCeti.atkinLehnerNormalizer_ne_zero (NeZero.ne N) k
  have hM : (M : ℂ) ≠ 0 := NeZero.ne _
  have hFW' : F ∣[k] TauCeti.frickeGL ℝ N =
      ((TauCeti.atkinLehnerNormalizer N k)⁻¹ * ε) • F := by
    rw [mul_smul, ← hFW, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [← SlashAction.slash_mul, upperRightHom_mul_frickeGL a v w hw, SlashAction.slash_mul,
    SlashAction.slash_mul, SlashAction.slash_mul, ModularForm.slash_scalar, hFW',
    ModularForm.smul_slash_of_det_pos k (det_mapGL_pos _),
    hF0 ⟨_, twistGamma_mem_Gamma0 M N a v w hw⟩,
    ModularForm.smul_slash_of_det_pos k (det_upperRightHom_pos _), smul_smul, smul_smul,
    atkinLehnerNormalizer_sq_mul]
  congr 1
  have h1 : (M : ℂ) ^ (2 - k) * (M : ℂ) ^ (k - 2) = 1 := by
    rw [← zpow_add₀ hM]
    simp
  rw [Units.val_mk0, Complex.ofReal_natCast]
  calc _ = ((M : ℂ) ^ (2 - k) * (M : ℂ) ^ (k - 2)) *
        (TauCeti.atkinLehnerNormalizer N k * (TauCeti.atkinLehnerNormalizer N k)⁻¹) * ε := by
        ring
    _ = ε := by rw [h1, mul_inv_cancel₀ hn, one_mul, one_mul]

/-! ### The involution `u ↦ -(N u)⁻¹` of `(ℤ/M)ˣ` -/

/-- **The involution `u ↦ -(N u)⁻¹`** of `(ℤ/M)ˣ`, for `N` prime to `M`: the residue `v` of
the matrix identity, `N u v ≡ -1 (mod M)`. -/
def frickeInvol (hNM : N.Coprime M) (u : (ZMod M)ˣ) : (ZMod M)ˣ :=
  -(ZMod.unitOfCoprime N hNM * u)⁻¹

/-- `frickeInvol` is an involution (PROVED). -/
theorem frickeInvol_frickeInvol (hNM : N.Coprime M) (u : (ZMod M)ˣ) :
    frickeInvol hNM (frickeInvol hNM u) = u := by
  simp only [frickeInvol, mul_neg, inv_neg, neg_neg, mul_inv, inv_inv]
  group

/-- **`N u v = -1` in `ℤ/M`** for `v = frickeInvol u` (PROVED). -/
theorem natCast_mul_mul_frickeInvol (hNM : N.Coprime M) (u : (ZMod M)ˣ) :
    (N : ZMod M) * (u : ZMod M) * (frickeInvol hNM u : ZMod M) = -1 := by
  have h := (ZMod.unitOfCoprime N hNM * u).mul_inv
  rw [Units.val_mul, ZMod.coe_unitOfCoprime] at h
  simp only [frickeInvol, Units.val_neg, mul_neg, h]

/-- **A character sum runs over the units** (PROVED): `∑_{a mod M} χ(a) G(a) = ∑_u χ(u) G(u)`,
since `χ` vanishes off the units. -/
theorem sum_eq_sum_units [NeZero M] {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (χ : DirichletCharacter ℂ M) (G : ZMod M → V) :
    ∑ a : ZMod M, χ a • G a = ∑ u : (ZMod M)ˣ, χ u • G u := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun u _ _ => (u : ZMod M)) (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ _ _ _ _ h => Units.ext h) (fun b _ hb => ?_) (fun _ _ _ => rfl)
  have hu : IsUnit b := by
    by_contra hnu
    exact hb (by rw [MulChar.map_nonunit χ hnu, zero_smul])
  exact ⟨hu.unit, Finset.mem_univ _, by rwa [IsUnit.unit_spec], hu.unit_spec⟩

/-! ### The character sum under the Fricke matrix -/

/-- **The character sum** `S = ∑_{a mod M} χ(a) F|[1, a/M; 0, 1]` of a function `F : ℍ → ℂ`
(the twist without its normalizing constant; translation by the representative `a.val`). -/
noncomputable def twistSum [NeZero M] (χ : DirichletCharacter ℂ M) (k : ℤ) (F : ℍ → ℂ) :
    ℍ → ℂ :=
  ∑ a : ZMod M, χ a • (F ∣[k] upperRightHom ((a.val : ℝ) / M))

/-- A quadratic character takes the same value at `u` and `u⁻¹` (PROVED). -/
theorem apply_inv_of_isQuadratic {χ : DirichletCharacter ℂ M} (hχ : χ.IsQuadratic)
    (u : (ZMod M)ˣ) : χ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = χ u := by
  have h1 : χ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * χ u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rcases hχ u with h | h | h
  · rw [h, mul_zero] at h1
    exact absurd h1 zero_ne_one
  · rw [h, mul_one] at h1
    rw [h1, h]
  · rw [h] at h1 ⊢
    linear_combination -h1

/-- A quadratic character squares to `1` on units (PROVED). -/
theorem apply_mul_self_of_isQuadratic {χ : DirichletCharacter ℂ M} (hχ : χ.IsQuadratic)
    (u : (ZMod M)ˣ) : χ u * χ u = 1 := by
  have h1 : χ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * χ u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rwa [apply_inv_of_isQuadratic hχ] at h1

/-- `χ(-N)² = 1` for `N` prime to `M` and quadratic `χ` (PROVED). -/
theorem apply_neg_natCast_mul_self {χ : DirichletCharacter ℂ M} (hχ : χ.IsQuadratic)
    (hNM : N.Coprime M) : χ (-(N : ZMod M)) * χ (-(N : ZMod M)) = 1 := by
  have h := apply_mul_self_of_isQuadratic hχ (-(ZMod.unitOfCoprime N hNM))
  rwa [Units.val_neg, ZMod.coe_unitOfCoprime] at h

/-- **`χ(-(N u)⁻¹) = χ(-N) χ(u)`** for quadratic `χ` (PROVED). -/
theorem apply_frickeInvol {χ : DirichletCharacter ℂ M} (hχ : χ.IsQuadratic)
    (hNM : N.Coprime M) (u : (ZMod M)ˣ) :
    χ (frickeInvol hNM u : ZMod M) = χ (-(N : ZMod M)) * χ u := by
  simp only [frickeInvol, Units.val_neg]
  rw [neg_eq_neg_one_mul, map_mul, apply_inv_of_isQuadratic hχ, Units.val_mul, map_mul,
    ZMod.coe_unitOfCoprime, neg_eq_neg_one_mul (N : ZMod M), map_mul]
  ring

/-- **The Fricke relation of the character sum** (PROVED). Let `χ` be a quadratic Dirichlet
character modulo `M`, `N` prime to `M`, and `F : ℍ → ℂ` with `F|γ = F` on `Γ₀(N)` and
`(√N)^{2-k} F|W_N = ε F`. Then `(√(M²N))^{2-k} S|W_{M²N} = ε χ(-N) S` for
`S = ∑_a χ(a) F|[1, a/M; 0, 1]`. Each unit `u` goes to `ε F|[1, v/M; 0, 1]` with
`v = frickeInvol u` (`slash_upperRightHom_slash_frickeGL`); reindexing by the involution and
`χ(v) = χ(-N) χ(u)`, `χ(-N)² = 1` give the claim. -/
theorem twistSum_slash_frickeGL [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M}
    (hχ : χ.IsQuadratic) (hNM : N.Coprime M) {F : ℍ → ℂ}
    (hF0 : ∀ g : Gamma0 N, F ∣[k] mapGL ℝ (g : SL(2, ℤ)) = F) {ε : ℂ}
    (hFW : TauCeti.atkinLehnerNormalizer N k • (F ∣[k] TauCeti.frickeGL ℝ N) = ε • F) :
    TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
        (twistSum χ k F ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) =
      (ε * χ (-(N : ZMod M))) • twistSum χ k F := by
  set h : ZMod M → ℍ → ℂ := fun a => F ∣[k] upperRightHom ((a.val : ℝ) / M) with hh
  have hterm : ∀ u : (ZMod M)ˣ, TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
      (h u ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) = ε • h (frickeInvol hNM u) := by
    intro u
    have hdvd : (M : ℤ) ∣ 1 + N * (((u : ZMod M).val : ℕ) : ℤ) *
        ((((frickeInvol hNM u : (ZMod M)ˣ) : ZMod M).val : ℕ) : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, natCast_mul_mul_frickeInvol]
      ring
    obtain ⟨w, hw⟩ := hdvd
    have := slash_upperRightHom_slash_frickeGL hF0 hFW _ _ w hw.symm
    simpa only [Int.cast_natCast] using this
  have hL : ∀ a : ZMod M, TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
      ((χ a • h a) ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) =
        χ a • (TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
          (h a ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N))) := by
    intro a
    rw [ModularForm.smul_slash_of_det_pos k det_frickeGL_pos, smul_comm]
  unfold twistSum
  rw [SlashAction.sum_slash, Finset.smul_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun a _ => hL a]
  rw [sum_eq_sum_units χ (fun a => TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
      (h a ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)))]
  have hR : ∑ x : ZMod M, (ε * χ (-(N : ZMod M))) • χ x • h x =
      ∑ u : (ZMod M)ˣ, (ε * χ (-(N : ZMod M))) • χ u • h u := by
    rw [← Finset.smul_sum, ← Finset.smul_sum, sum_eq_sum_units χ h]
  rw [show (∑ x : ZMod M, (ε * χ (-(N : ZMod M))) • χ x •
      (F ∣[k] upperRightHom ((x.val : ℝ) / M))) =
      ∑ x : ZMod M, (ε * χ (-(N : ZMod M))) • χ x • h x from rfl, hR]
  simp_rw [hterm]
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ (frickeInvol_frickeInvol hNM)) _ _
    (fun u => ?_)
  show χ u • ε • h (frickeInvol hNM u) = (ε * χ (-(N : ZMod M))) •
    χ (frickeInvol hNM u : ZMod M) • h (frickeInvol hNM u)
  rw [apply_frickeInvol hχ hNM, smul_smul, smul_smul]
  congr 1
  linear_combination (-(ε * χ u)) * apply_neg_natCast_mul_self hχ hNM

/-! ### The twisted cusp form -/

/-- **The twist through the character sum** (PROVED): for a primitive quadratic Dirichlet
character `χ` modulo `M`, Tau Ceti's twist is `f ⊗ χ = (M⁻¹ χ(-1) G(χ)) S`, with
`S = twistSum χ k f` and `G(χ)` the Gauss sum: `𝓕χ(a) = χ⁻¹(-a) G(χ)` (Mathlib's
`DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`), and `χ⁻¹ = χ`. -/
theorem coe_twist_eq_smul_twistSum [NeZero M] {N L : ℕ} {χ : DirichletCharacter ℂ M}
    (hprim : χ.IsPrimitive) (hχ : χ.IsQuadratic) (hNL : N * M ∣ L) (hML : M * M ∣ L)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist (⇑χ) hNL hML f) =
      ((M : ℂ)⁻¹ * χ (-1) * gaussSum χ ZMod.stdAddChar) • twistSum χ k ⇑f := by
  funext τ
  rw [CuspForm.twist_apply]
  simp only [twistSum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    TauCeti.ModularForm.slash_upperRightHom_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hprim, hχ.inv,
    neg_eq_neg_one_mul a, map_mul]
  ring

/-- **The Fricke relation of a quadratic twist** (PROVED; step (2) of the route). For a cusp
form `f` on `Γ₁(N)` with `f|γ = f` on `Γ₀(N)` and `(√N)^{2-k} f|W_N = ε f`, and a primitive
quadratic character `χ` modulo `M` prime to `N`, the twist `f ⊗ χ` (a cusp form on `Γ₁(M²N)`)
satisfies `(√(M²N))^{2-k} (f ⊗ χ)|W_{M²N} = ε χ(-N) (f ⊗ χ)`. -/
theorem twist_slash_frickeGL [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M}
    (hprim : χ.IsPrimitive) (hχ : χ.IsQuadratic) (hNM : N.Coprime M)
    (hNL : N * M ∣ M ^ 2 * N) (hML : M * M ∣ M ^ 2 * N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hF0 : ∀ g : Gamma0 N, ⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = ⇑f) {ε : ℂ}
    (hFW : TauCeti.atkinLehnerNormalizer N k • (⇑f ∣[k] TauCeti.frickeGL ℝ N) = ε • ⇑f) :
    TauCeti.atkinLehnerNormalizer (M ^ 2 * N) k •
        (⇑(CuspForm.twist (⇑χ) hNL hML f) ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) =
      (ε * χ (-(N : ZMod M))) • ⇑(CuspForm.twist (⇑χ) hNL hML f) := by
  rw [coe_twist_eq_smul_twistSum hprim hχ, ModularForm.smul_slash_of_det_pos k det_frickeGL_pos,
    smul_comm, twistSum_slash_frickeGL hχ hNM hF0 hFW, smul_comm]

/-- **The functional equation of a quadratic twist** (PROVED; step (3) of the route). Under the
hypotheses of `twist_slash_frickeGL`, the level-`M²N` completion `Λ_{M²N}(s) =` Tau Ceti's
`CuspForm.frickeCompletedL` of `f ⊗ χ` satisfies `Λ_{M²N}(k - s) = i^k ε χ(-N) Λ_{M²N}(s)` for
every `s`: the companion `(√(M²N))^{2-k} (f ⊗ χ)|W_{M²N}` is `ε χ(-N) (f ⊗ χ)`, and Tau Ceti's
`CuspForm.frickeCompletedL_sub_eq_I_zpow_mul` is the Mellin-transform identity for any two
cusp forms related in this way. -/
theorem twist_frickeCompletedL_sub [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M}
    (hprim : χ.IsPrimitive) (hχ : χ.IsQuadratic) (hNM : N.Coprime M)
    (hNL : N * M ∣ M ^ 2 * N) (hML : M * M ∣ M ^ 2 * N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hF0 : ∀ g : Gamma0 N, ⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = ⇑f) {ε : ℂ}
    (hFW : TauCeti.atkinLehnerNormalizer N k • (⇑f ∣[k] TauCeti.frickeGL ℝ N) = ε • ⇑f)
    (s : ℂ) :
    CuspForm.frickeCompletedL (CuspForm.twist (⇑χ) hNL hML f)
        ((M ^ 2 * N).toPNat (NeZero.pos _)) ((k : ℂ) - s) =
      Complex.I ^ k * (ε * χ (-(N : ZMod M))) *
        CuspForm.frickeCompletedL (CuspForm.twist (⇑χ) hNL hML f)
          ((M ^ 2 * N).toPNat (NeZero.pos _)) s := by
  set g := CuspForm.twist (⇑χ) hNL hML f with hg
  have hrel : ⇑((ε * χ (-(N : ZMod M))) • g) =
      ((Real.sqrt ((M ^ 2 * N : ℕ) : ℝ) : ℝ) : ℂ) ^ (2 - k) •
        (⇑g ∣[k] TauCeti.frickeGL ℝ (M ^ 2 * N)) := by
    rw [FunLike.coe_smul, ← TauCeti.atkinLehnerNormalizer_def,
      twist_slash_frickeGL hprim hχ hNM hNL hML f hF0 hFW]
  rw [CuspForm.frickeCompletedL_sub_eq_I_zpow_mul g _ (M ^ 2 * N) hrel s,
    CuspForm.frickeCompletedL_smul]
  ring

end ZInQ.Manuscript.RC.PrintsAnalytic.TwistedFE
