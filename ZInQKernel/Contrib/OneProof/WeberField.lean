import ZInQKernel.Contrib.OneProof.X1Igusa
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Roots
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

/-! # weber-field: the function-field comparison `ℚ(j, f₁) = ℚ(j)(x(P))` (`WeberFieldComparison`), proved

Task weber-field (2026-11-16), report `docs/research/weber-field.md`, scratch `scratch/weber-field/`.

**Target.** `X1Igusa.Weber.WeberFieldComparison`, stated by x1-igusa (`scratch/x1-igusa/WeberComparison.lean`, base
`62d9b7c5`; copied here verbatim with `wOf`, `evAn`, `evAlg`, since that scratch file is not a module): for `N ≥ 2`
some point `P` of exact order `N` of the kernel's `E_j` over `\overline{ℚ(j)}` has the same ideal of polynomial
relations over `ℚ` as Weber's function: `F(j(τ), f₁(τ)) = 0` for all `τ ∈ ℍ` with `g₂(τ)g₃(τ) ≠ 0` iff
`F(j, w(P)) = 0`, where `f₁(τ) = T5Glue.weber ⟨1, τ⟩ (1/N)` and `w(P) = (αx(P) − 3/2)/(g_j − 27)`. With
`adjoin_wOf` (`ℚ(j)(w(P)) = ℚ(j)(x(P)) = fieldX1 P`) this identifies Diamond–Shurman's function field `ℚ(j, f₁)`
of `X₁(N)_alg` with the kernel's `K_N`: the gap x1-igusa §4 named between `AfTateCharPolyPicZero` and DS 9.5.4.

**Proof** (`weberFieldComparison`), all glue, no new hypothesis:
* §A. A prime ideal `I ⊆ ℚ[J][T]` with `I ∩ ℚ[J] = 0` and `I ≠ 0` is `ker(T ↦ θ)` for a root `θ ∈ \overline{ℚ(j)}`
  (`ℚ(j)[T]` is the localization of `ℚ[J][T]` at `ℚ[J]∖0`, a PID; Mathlib's `Polynomial.isLocalization`).
* §B, §C. Mathlib's division polynomial `ΨSqₙ` of the universal curve `y² = x³ − (G/4)x − G/4` over `ℚ[G]`, cleared
  of the denominators of `G = 27J/(J − 1728)`, `x = 46656T/(J − 1728)`, specializes to `ΨSqₙ` of Diamond–Shurman's
  `E_j` over `\overline{ℚ(j)}` and of `E_{j(τ)}` over `ℂ`; Tau Ceti's `eval_ΨSq_eq_zero_iff_zsmul_eq_zero` turns its
  roots into `n`-torsion points on both sides; the vendored uniformization `PeriodPair.isUniformization_toPoint`
  (AnthropicFLT) gives the point `(g₂/g₃)℘(1/N)` of exact order `N` on `ℂ/⟨1, τ⟩`.
* §D. `g₂, g₃` are holomorphic on `ℍ` (Eisenstein series, `T5Glue.G_eq_E`), `Δ ≠ 0` (`disc_ppD_ne_zero`),
  `τ ↦ ℘_τ(1/N)` is holomorphic (locally uniform majorant `≪ ‖(m, n)‖⁻³`), `g₃(i) = 0`, `g₂(ρ) = 0`, so `j` is not
  constant and some `τ` has `g₂g₃ ≠ 0`; the identity theorem makes `I = {F : F(j, f₁) ≡ 0 on ℍ}` prime.
* §E. `I` contains the cleared `ΨSq_N`; §A gives `θ`, §C a point `P` with `w(P) = θ`, `N • P = 0`, and exact order
  `N` because a smaller order `d` would put the cleared `ΨSq_d` in `I`, contradicting `d/N ∉ ⟨1, τ⟩`.

No `sorry`, no `axiom`, no build-time code; axioms `propext`, `Classical.choice`, `Quot.sound`. -/

noncomputable section

namespace X1Igusa.Weber

open LeafModCurves WeierstrassCurve T5Glue

/-- The kernel-model expression of Weber's function at `P`: `w(P) = (α x(P) − 3/2)/(g_j − 27)`. -/
def wOf (P : EjBar.toAffine.Point) : Kbar :=
  (algebraMap Qj Kbar alpha * xCoord P + algebraMap Qj Kbar (-3 / 2)) / algebraMap Qj Kbar (gDS - 27)

/-- `F(J, T)` at `(J, T) = (j, w(P))` in `\overline{ℚ(j)}`. -/
def evAlg (F : Polynomial (Polynomial ℚ)) (P : EjBar.toAffine.Point) : Kbar :=
  (F.map ((algebraMap Qj Kbar).comp (algebraMap (Polynomial ℚ) Qj))).eval (wOf P)

/-! ## A. The algebraic lemma -/

/-- `ℚ[J] → \overline{ℚ(j)}`. -/
abbrev phiK : Polynomial ℚ →+* Kbar := (algebraMap Qj Kbar).comp (algebraMap (Polynomial ℚ) Qj)

/-- Evaluation `ℚ[J][T] → \overline{ℚ(j)}` at `(j, θ)`. -/
def evK (θ : Kbar) : Polynomial (Polynomial ℚ) →+* Kbar := Polynomial.eval₂RingHom phiK θ

theorem evAlg_eq (F : Polynomial (Polynomial ℚ)) (P : EjBar.toAffine.Point) :
    evAlg F P = evK (wOf P) F := by
  simp only [evAlg, evK, Polynomial.eval_map, Polynomial.coe_eval₂RingHom]

section
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- **A prime ideal of `ℚ[J][T]` meeting `ℚ[J]` only in `0` and containing a nonzero element is the kernel of
`T ↦ θ` for some `θ ∈ \overline{ℚ(j)}`.** -/
theorem exists_root_of_isPrime {I : Ideal (Polynomial (Polynomial ℚ))} (hI : I.IsPrime)
    (hdisj : ∀ c : Polynomial ℚ, Polynomial.C c ∈ I → c = 0) {Φ : Polynomial (Polynomial ℚ)}
    (hΦ : Φ ∈ I) (hΦ0 : Φ ≠ 0) : ∃ θ : Kbar, ∀ F, F ∈ I ↔ evK θ F = 0 := by
  set M := (nonZeroDivisors (Polynomial ℚ)).map (Polynomial.C : Polynomial ℚ →+* _) with hM
  have : IsLocalization M (Polynomial Qj) := Polynomial.isLocalization _ _
  have hd : Disjoint (M : Set (Polynomial (Polynomial ℚ))) I := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcI
    exact nonZeroDivisors.ne_zero hc (hdisj c hcI)
  set J := I.map (algebraMap (Polynomial (Polynomial ℚ)) (Polynomial Qj)) with hJdef
  have hJp : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ I hI hd
  have hJI : J.under _ = I := IsLocalization.under_map_of_isPrime_disjoint M _ hI hd
  have hmapinj : Function.Injective (algebraMap (Polynomial (Polynomial ℚ)) (Polynomial Qj)) :=
    Polynomial.map_injective _ (IsFractionRing.injective (Polynomial ℚ) Qj)
  have hJ0 : J ≠ ⊥ := by
    intro h
    have : algebraMap _ (Polynomial Qj) Φ ∈ J := Ideal.mem_map_of_mem _ hΦ
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hmapinj] at this
    exact hΦ0 this
  have hJm : J.IsMaximal := Ideal.IsPrime.isMaximal hJp hJ0
  set p := Submodule.IsPrincipal.generator J with hpdef
  have hJsp : J = Ideal.span {p} := (Ideal.span_singleton_generator J).symm
  have hp0 : p ≠ 0 := by
    intro h; apply hJ0; rw [hJsp, h, Ideal.span_singleton_eq_bot]
  have hpu : ¬ IsUnit p := by
    intro h; apply hJm.ne_top; rw [hJsp, Ideal.span_singleton_eq_top]; exact h
  have hdeg : p.degree ≠ 0 := by
    intro h
    exact hpu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_aeval_eq_zero Kbar p hdeg
  refine ⟨θ, fun F => ?_⟩
  have hker : J = RingHom.ker (Polynomial.aeval θ : Polynomial Qj →ₐ[Qj] Kbar) := by
    apply hJm.eq_of_le
    · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]; exact one_ne_zero
    · rw [hJsp, Ideal.span_le, Set.singleton_subset_iff]; exact hθ
  have h1 : evK θ F = Polynomial.aeval θ (algebraMap _ (Polynomial Qj) F) := by
    rw [Polynomial.aeval_def]
    show _ = Polynomial.eval₂ (algebraMap Qj Kbar) θ (F.map (algebraMap (Polynomial ℚ) Qj))
    rw [Polynomial.eval₂_map]; rfl
  rw [h1, ← RingHom.mem_ker, ← hker, ← hJI, Ideal.mem_comap]

end

/-! ## B. Clearing denominators: `(G, x) ↦ (27J/D, 46656 T/D)` -/

open Polynomial in
/-- `D = J − 1728`, a constant of `ℚ[J][T]`. -/
abbrev DJ : Polynomial (Polynomial ℚ) := C (X - C 1728)

/-- Evaluation `ℚ[G][x] → L` at `(G, x) = (a, b)`. -/
def ev2 {L : Type} [Field L] [CharZero L] (a b : L) : Polynomial (Polynomial ℚ) →+* L :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom L) a) b

open Polynomial in
/-- `Φ = D^k · P(27J/D, 46656T/D)` under every evaluation with `D ≠ 0`. -/
def Clears (P Φ : Polynomial (Polynomial ℚ)) (k : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] (e : Polynomial (Polynomial ℚ) →+* L), e DJ ≠ 0 →
    e Φ = e DJ ^ k * ev2 (27 * e (C X) / e DJ) (46656 * e X / e DJ) P

open Polynomial in
theorem clears_add {P Q Φ Ψ : Polynomial (Polynomial ℚ)} {k l : ℕ} (hP : Clears P Φ k)
    (hQ : Clears Q Ψ l) : Clears (P + Q) (Φ * DJ ^ l + Ψ * DJ ^ k) (k + l) := by
  intro L _ _ e he
  rw [map_add, map_mul, map_mul, map_pow, map_pow, hP L e he, hQ L e he, map_add]
  ring

open Polynomial in
theorem clears_mul {P Q Φ Ψ : Polynomial (Polynomial ℚ)} {k l : ℕ} (hP : Clears P Φ k)
    (hQ : Clears Q Ψ l) : Clears (P * Q) (Φ * Ψ) (k + l) := by
  intro L _ _ e he
  rw [map_mul, hP L e he, hQ L e he, map_mul]
  ring

open Polynomial in
theorem clears_CC (q : ℚ) : Clears (C (C q)) (C (C q)) 0 := by
  intro L _ _ e he
  have h1 : e (C (C q)) = (q : L) := eq_ratCast (e.comp (C.comp C)) q
  simp only [ev2, coe_eval₂RingHom, eval₂_C, pow_zero, one_mul, h1]
  rfl

open Polynomial in
theorem clears_CX : Clears (C X) (C (C 27 * X)) 1 := by
  intro L _ _ e he
  have h27 : e (C (C 27)) = 27 := by
    have := eq_ratCast (e.comp (C.comp C)) 27
    rwa [RingHom.comp_apply, RingHom.comp_apply, Rat.cast_ofNat] at this
  simp only [ev2, coe_eval₂RingHom, eval₂_C, eval₂_X, pow_one, map_mul, h27]
  field_simp

open Polynomial in
theorem clears_X : Clears X (C (C 46656) * X) 1 := by
  intro L _ _ e he
  have h : e (C (C 46656)) = 46656 := by
    have := eq_ratCast (e.comp (C.comp C)) 46656
    rwa [RingHom.comp_apply, RingHom.comp_apply, Rat.cast_ofNat] at this
  simp only [ev2, coe_eval₂RingHom, eval₂_X, pow_one, map_mul, h]
  field_simp

open Polynomial in
theorem exists_clears (P : Polynomial (Polynomial ℚ)) : ∃ Φ k, Clears P Φ k := by
  induction P using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C q => exact ⟨_, _, clears_CC q⟩
    | add a b ha hb =>
      obtain ⟨Φ, k, h1⟩ := ha
      obtain ⟨Ψ, l, h2⟩ := hb
      rw [C_add]; exact ⟨_, _, clears_add h1 h2⟩
    | monomial n q ih =>
      obtain ⟨Φ, k, h1⟩ := ih
      rw [pow_succ, ← mul_assoc, C_mul]; exact ⟨_, _, clears_mul h1 clears_CX⟩
  | add P Q hP hQ =>
    obtain ⟨Φ, k, h1⟩ := hP
    obtain ⟨Ψ, l, h2⟩ := hQ
    exact ⟨_, _, clears_add h1 h2⟩
  | monomial n a ih =>
    obtain ⟨Φ, k, h1⟩ := ih
    rw [pow_succ, ← mul_assoc]; exact ⟨_, _, clears_mul h1 clears_X⟩

/-! ## C. The universal curve `y² = x³ − (G/4)x − G/4` and its two specializations -/

/-- `y² = x³ − (a/4)x − a/4` over a field. -/
def curveG {L : Type*} [Field L] (a : L) : WeierstrassCurve L := ⟨0, 0, 0, -(a / 4), -(a / 4)⟩

open Polynomial in
/-- The universal curve over `ℚ[G]`. -/
def WG : WeierstrassCurve (Polynomial ℚ) := ⟨0, 0, 0, C (-1 / 4) * X, C (-1 / 4) * X⟩

theorem WG_map {L : Type} [Field L] [CharZero L] (a : L) :
    WG.map (Polynomial.eval₂RingHom (Rat.castHom L) a) = curveG a := by
  ext <;> simp [WG, curveG] <;> ring

/-- `ev2 a b ΨSqₙ(WG) = ΨSqₙ(curveG a)(b)`. -/
theorem ev2_ΨSq {L : Type} [Field L] [CharZero L] (a b : L) (n : ℤ) :
    ev2 a b (WG.ΨSq n) = ((curveG a).ΨSq n).eval b := by
  rw [← WG_map, map_ΨSq, Polynomial.eval_map]; rfl

theorem EDSBar_eq : EDSBar = curveG (algebraMap Qj Kbar gDS) := by
  ext <;> simp [EDSBar, EDS, curveG, baseChange, map_div₀, map_ofNat]

theorem evK_CX (θ : Kbar) : evK θ (Polynomial.C Polynomial.X) = algebraMap Qj Kbar RatFunc.X := by
  simp [evK, RatFunc.algebraMap_X]

theorem evK_DJ (θ : Kbar) : evK θ DJ = algebraMap Qj Kbar (RatFunc.X - 1728) := by
  simp [evK, DJ, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem evK_DJ_ne (θ : Kbar) : evK θ DJ ≠ 0 := by
  rw [evK_DJ, ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]; exact X_sub_1728_ne_zero

/-- On the `\overline{ℚ(j)}` side a clearing of `ΨSqₙ(WG)` is `D^k · ΨSqₙ(E_j^{DS})((g_j − 27)θ)`. -/
theorem evK_clears {n : ℤ} {Φ : Polynomial (Polynomial ℚ)} {k : ℕ} (h : Clears (WG.ΨSq n) Φ k)
    (θ : Kbar) : evK θ Φ = evK θ DJ ^ k * (EDSBar.ΨSq n).eval (algebraMap Qj Kbar (gDS - 27) * θ) := by
  have h1 : 27 * evK θ (Polynomial.C Polynomial.X) / evK θ DJ = algebraMap Qj Kbar gDS := by
    rw [evK_CX, evK_DJ, gDS, map_div₀, map_mul, map_ofNat]
  have hX : evK θ Polynomial.X = θ := by simp [evK]
  have h2 : 46656 * evK θ Polynomial.X / evK θ DJ = algebraMap Qj Kbar (gDS - 27) * θ := by
    rw [hX, evK_DJ, gDS_sub, map_div₀, map_mul, map_ofNat, map_ofNat]
    ring
  rw [h Kbar (evK θ) (evK_DJ_ne θ), ev2_ΨSq, EDSBar_eq, h1, h2]


/-! ## C'. Points: the `\overline{ℚ(j)}` side -/

/-- A root `θ` of `ΨSqₙ(E_j^{DS})((g_j − 27)·)` is `w(P)` for a nonzero `n`-torsion point `P` of the kernel's
`E_j`; and `ΨSq_d` vanishes there for every `d` killing `P`. -/
theorem exists_point_of_root {n : ℕ} (θ : Kbar)
    (h : (EDSBar.ΨSq n).eval (algebraMap Qj Kbar (gDS - 27) * θ) = 0) :
    ∃ P : EjBar.toAffine.Point, P ≠ 0 ∧ n • P = 0 ∧ wOf P = θ ∧
      ∀ d : ℕ, d • P = 0 → (EDSBar.ΨSq d).eval (algebraMap Qj Kbar (gDS - 27) * θ) = 0 := by
  obtain ⟨y, hns, hz⟩ := EDSBar.eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero.mp h
  set Q : EDSBar.toAffine.Point := Affine.Point.some _ _ hns with hQdef
  have hQ0 : Q ≠ 0 := Affine.Point.some_ne_zero hns
  have hQn : n • Q = 0 := zsmul_fromAffine_eq_zero_iff.mp hz
  obtain ⟨u, hu2⟩ := exists_u
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap Qj Kbar).injective] at hu2
    exact alpha_ne_zero hu2
  obtain ⟨ψ, hψ⟩ := exists_addEquiv_xCoord EjBar EDSBar (cDS u hu) (cDS_smul u hu2 hu)
  have hP0 : ψ.symm Q ≠ 0 := by rw [ne_eq, AddEquiv.map_eq_zero_iff]; exact hQ0
  refine ⟨ψ.symm Q, hP0, ?_, ?_, ?_⟩
  · rw [← map_nsmul, hQn, map_zero]
  · have hx := hψ (ψ.symm Q) hP0
    rw [AddEquiv.apply_symm_apply] at hx
    have hc : ((cDS u hu).u : Kbar) ^ 2 = algebraMap Qj Kbar alpha := hu2
    have hr : (cDS u hu).r = algebraMap Qj Kbar (-3 / 2) := rfl
    rw [hc, hr] at hx
    have hxQ : xCoord Q = algebraMap Qj Kbar (gDS - 27) * θ := rfl
    have hg : algebraMap Qj Kbar (gDS - 27) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective, gDS_sub]
      exact div_ne_zero (by norm_num) X_sub_1728_ne_zero
    unfold wOf
    rw [← hx, hxQ]
    field_simp
  · intro d hd
    have : d • Q = 0 := by rw [← AddEquiv.apply_symm_apply ψ Q, ← map_nsmul, hd, map_zero]
    exact (EDSBar.eval_ΨSq_eq_zero_iff_zsmul_eq_zero hns d).mpr (zsmul_fromAffine_eq_zero_iff.mpr this)

/-! ## C''. Points: the complex side (the uniformization) -/

/-- `(u, 0, 0, 0) · y² = x³ − (g/4)x − g/4` with `g = g₂³/g₃²`, `u² = g₂/g₃`, is `ℂ/Λ`'s curve. -/
theorem curveC_smul (L : PeriodPair) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (u : ℂ)
    (hu2 : u ^ 2 = L.g₂ / L.g₃) (hu : u ≠ 0) :
    (⟨Units.mk0 u hu, 0, 0, 0⟩ : VariableChange ℂ) • curveG (L.g₂ ^ 3 / L.g₃ ^ 2) =
      L.weierstrassCurve := by
  have hu2' : u ^ 2 * L.g₃ = L.g₂ := by rw [hu2]; field_simp
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, curveG, PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
    PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  all_goals field_simp
  · ring
  · ring
  · ring
  · linear_combination (L.g₂ * (u ^ 2 * L.g₃ + L.g₂)) * hu2'
  · linear_combination ((u ^ 2 * L.g₃) ^ 2 + u ^ 2 * L.g₃ * L.g₂ + L.g₂ ^ 2) * hu2'

/-- `n • toPoint z = toPoint (n z)`. -/
theorem nsmul_toPoint (L : PeriodPair) (hΔ : L.DiscriminantNeZero) (z : ℂ) (n : ℕ) :
    n • L.toPoint hΔ z = L.toPoint hΔ (n * z) := by
  have hU := L.isUniformization_toPoint hΔ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih, ← hU.1]
    congr 1; push_cast; ring

theorem toPoint_eq_zero_iff (L : PeriodPair) (hΔ : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint hΔ z = 0 ↔ z ∈ L.lattice :=
  ⟨(L.isUniformization_toPoint hΔ).2.2 z, L.toPoint_of_mem hΔ⟩

theorem discNeZero_pp (τ : UpperHalfPlane) : (pp τ).DiscriminantNeZero := disc_ppD_ne_zero τ

/-- **The division polynomial at Weber's point.** On `ℂ/⟨1, τ⟩` with `g₂g₃ ≠ 0`, `x = (g₂/g₃)℘(1/N)` is a root of
`ΨSqₙ(y² = x³ − (g/4)x − g/4)`, `g = g₂³/g₃²`, iff `n/N ∈ ⟨1, τ⟩`. -/
theorem eval_ΨSq_weber_eq_zero_iff (τ : UpperHalfPlane) (h2 : (pp τ).g₂ ≠ 0) (h3 : (pp τ).g₃ ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    ((curveG ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)).ΨSq n).eval
        ((pp τ).g₂ / (pp τ).g₃ * (pp τ).weierstrassP (1 / N)) = 0 ↔
      (n : ℂ) * (1 / N) ∈ (pp τ).lattice := by
  set L := pp τ with hL
  have hΔ : L.DiscriminantNeZero := discNeZero_pp τ
  have hz : (1 / (N : ℂ)) ∉ L.lattice := by
    have := div_nat_not_mem τ (a := 1) (N := N) one_pos (by omega)
    rwa [Nat.cast_one] at this
  obtain ⟨u, hu2⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / L.g₃) two_pos
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hu2
    rcases hu2 with h | h
    · exact h2 h
    · exact h3 h
  obtain ⟨e, he⟩ := exists_addEquiv_xCoord L.weierstrassCurve (curveG (L.g₂ ^ 3 / L.g₃ ^ 2)) _
    (curveC_smul L h2 h3 u hu2 hu)
  set Q₀ := L.toPoint hΔ (1 / N) with hQ₀
  have hQ₀0 : Q₀ ≠ 0 := by rw [hQ₀, ne_eq, toPoint_eq_zero_iff]; exact hz
  have hxQ₀ : xCoord Q₀ = L.weierstrassP (1 / N) := by
    rw [hQ₀, L.toPoint_of_notMem hΔ hz]; rfl
  have hQ0 : e Q₀ ≠ 0 := by rw [ne_eq, AddEquiv.map_eq_zero_iff]; exact hQ₀0
  obtain ⟨x, y, hns, hQ⟩ : ∃ x y, ∃ hns : (curveG (L.g₂ ^ 3 / L.g₃ ^ 2)).toAffine.Nonsingular x y,
      e Q₀ = Affine.Point.some x y hns := by
    cases h : e Q₀ with
    | zero => exact absurd h hQ0
    | some x y hns => exact ⟨x, y, hns, rfl⟩
  have hx : x = L.g₂ / L.g₃ * L.weierstrassP (1 / N) := by
    have := he Q₀ hQ₀0
    have h' : xCoord (Affine.Point.some x y hns) = x := rfl
    rw [hQ, hxQ₀, h'] at this
    simpa [hu2] using this
  rw [← hx, eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns, zsmul_fromAffine_eq_zero_iff, ← hQ,
    ← map_nsmul, AddEquiv.map_eq_zero_iff, hQ₀, nsmul_toPoint, toPoint_eq_zero_iff]

open UpperHalfPlane

/-! ## D. Analysis on the upper half plane -/

/-- The upper half plane as a subset of `ℂ`. -/
def Hs : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

/-- Identity theorem on `ℍ`. -/
theorem eq_zero_of_eventually {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) {z₀ : ℂ} (hz₀ : z₀ ∈ Hs)
    (h : f =ᶠ[nhds z₀] 0) : ∀ z ∈ Hs, f z = 0 := fun _ hz =>
  (hf.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ h hz

/-- Holomorphic functions on `ℍ` form a domain. -/
theorem eq_zero_or_eq_zero {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) (hg : DifferentiableOn ℂ g Hs)
    (h : ∀ z ∈ Hs, f z * g z = 0) : (∀ z ∈ Hs, f z = 0) ∨ (∀ z ∈ Hs, g z = 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩ := hc
  have hgc : ContinuousAt g b := (hg.differentiableAt (isOpen_Hs.mem_nhds hb)).continuousAt
  have hev : ∀ᶠ z in nhds b, g z ≠ 0 ∧ z ∈ Hs :=
    (hgc.eventually_ne hgb).and (isOpen_Hs.mem_nhds hb)
  have hf0 : f =ᶠ[nhds b] 0 := hev.mono fun z hz => by
    have := h z hz.2
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hz.1
  exact hfa (eq_zero_of_eventually hf hb hf0 a ha)

theorem ofComplex_coe {z : ℂ} (hz : z ∈ Hs) : ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

/-! ### `g₂`, `g₃`, `Δ`, `j` on `ℍ` -/

def G2f (z : ℂ) : ℂ := (pp (ofComplex z)).g₂
def G3f (z : ℂ) : ℂ := (pp (ofComplex z)).g₃
def Dlf (z : ℂ) : ℂ := discL (pp (ofComplex z))
def Jf (z : ℂ) : ℂ := jL (pp (ofComplex z))

theorem diffOn_E {k : ℕ} (hk : 3 ≤ k) :
    DifferentiableOn ℂ ((ModularForm.E hk : UpperHalfPlane → ℂ) ∘ ofComplex) Hs :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo _)

theorem diffOn_G2f : DifferentiableOn ℂ G2f Hs := by
  have h : G2f = fun z => 60 * (2 * riemannZeta ((4 : ℕ) : ℂ) *
      ((ModularForm.E (k := 4) (by norm_num) : UpperHalfPlane → ℂ) ∘ ofComplex) z) := by
    funext z
    simp only [G2f, PeriodPair.g₂, Function.comp]
    rw [← G_eq_E]; rfl
  rw [h]; exact ((diffOn_E _).const_mul _).const_mul _

theorem diffOn_G3f : DifferentiableOn ℂ G3f Hs := by
  have h : G3f = fun z => 140 * (2 * riemannZeta ((6 : ℕ) : ℂ) *
      ((ModularForm.E (k := 6) (by norm_num) : UpperHalfPlane → ℂ) ∘ ofComplex) z) := by
    funext z
    simp only [G3f, PeriodPair.g₃, Function.comp]
    rw [← G_eq_E]; rfl
  rw [h]; exact ((diffOn_E _).const_mul _).const_mul _

theorem Dlf_eq (z : ℂ) : Dlf z = G2f z ^ 3 - 27 * G3f z ^ 2 := rfl

theorem Dlf_ne (z : ℂ) : Dlf z ≠ 0 := disc_ppD_ne_zero (ofComplex z)

theorem Jf_eq (z : ℂ) : Jf z = 1728 * G2f z ^ 3 / Dlf z := rfl

theorem diffOn_Dlf : DifferentiableOn ℂ Dlf Hs := by
  have : Dlf = fun z => G2f z ^ 3 - 27 * G3f z ^ 2 := rfl
  rw [this]; exact (diffOn_G2f.pow 3).sub ((diffOn_G3f.pow 2).const_mul 27)

theorem diffOn_Jf : DifferentiableOn ℂ Jf Hs := by
  have : Jf = fun z => 1728 * G2f z ^ 3 / Dlf z := rfl
  rw [this]; exact ((diffOn_G2f.pow 3).const_mul 1728).div diffOn_Dlf fun z _ => Dlf_ne z

/-! ### `℘_τ(c)` is holomorphic in `τ` -/

/-- The lattice term `1/(c − ω)² − 1/ω²`, `ω = v₀w + v₁`. -/
def wTerm (c : ℂ) (v : Fin 2 → ℤ) (w : ℂ) : ℂ :=
  1 / (c - ((v 0 : ℂ) * w + v 1)) ^ 2 - 1 / ((v 0 : ℂ) * w + v 1) ^ 2

theorem weierstrassP_pp_eq (τ : UpperHalfPlane) (c : ℂ) :
    (pp τ).weierstrassP c = ∑' v : Fin 2 → ℤ, wTerm c v τ := by
  show (ppD τ).weierstrassP c = _
  rw [PeriodPair.weierstrassP, ← (latEquiv τ).tsum_eq]
  congr 1; funext v; rw [latEquiv_apply]; rfl

theorem lin_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) {w : ℂ} (hw : w ∈ Hs) :
    (v 0 : ℂ) * w + v 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hw' : 0 < w.im := hw
  have h0 : v 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hw'.ne'
  rw [h0] at h
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
  exact hv (by ext i; fin_cases i <;> simp [h0, h])

theorem shift_ne_zero {c : ℝ} (hcZ : ∀ m : ℤ, c ≠ m) (v : Fin 2 → ℤ) {w : ℂ} (hw : w ∈ Hs) :
    (c : ℂ) - ((v 0 : ℂ) * w + v 1) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, Complex.zero_im, zero_sub, neg_eq_zero] at him
  have hw' : 0 < w.im := hw
  have h0 : v 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hw'.ne'
  rw [h0] at h
  simp only [Int.cast_zero, zero_mul, zero_add, sub_eq_zero] at h
  exact hcZ (v 1) (by exact_mod_cast h)

theorem diffOn_wTerm {c : ℝ} (hcZ : ∀ m : ℤ, c ≠ m) (v : Fin 2 → ℤ) :
    DifferentiableOn ℂ (wTerm c v) Hs := by
  by_cases hv : v = 0
  · subst hv
    have : wTerm c 0 = fun _ => 1 / (c : ℂ) ^ 2 := by
      funext w; simp [wTerm]
    rw [this]; exact differentiableOn_const _
  · unfold wTerm
    refine DifferentiableOn.sub ?_ ?_
    · refine (differentiableOn_const _).div ?_ fun w hw => pow_ne_zero 2 (shift_ne_zero hcZ v hw)
      exact ((differentiableOn_const _).sub
        (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _))).pow 2
    · refine (differentiableOn_const _).div ?_ fun w hw => pow_ne_zero 2 (lin_ne_zero hv hw)
      exact (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _)).pow 2

/-- The cancellation estimate `‖1/δ² − 1/ω²‖ ≤ 4(2/a³ + 1/a⁴)` for `δ + ω = c`, `‖c‖ ≤ 1`. -/
theorem key_bound {c ω δ : ℂ} {a : ℝ} (ha : 0 < a) (hω : a ≤ ‖ω‖) (hδ : a ≤ 2 * ‖δ‖)
    (hsum : δ + ω = c) (hc : ‖c‖ ≤ 1) : ‖1 / δ ^ 2 - 1 / ω ^ 2‖ ≤ 4 * (2 / a ^ 3 + 1 / a ^ 4) := by
  have hX : 0 < ‖ω‖ := lt_of_lt_of_le ha hω
  have hY : 0 < ‖δ‖ := by linarith
  have hω0 : ω ≠ 0 := norm_pos_iff.mp hX
  have hδ0 : δ ≠ 0 := norm_pos_iff.mp hY
  have e : 1 / δ ^ 2 - 1 / ω ^ 2 = (2 * ω - c) * c / (δ ^ 2 * ω ^ 2) := by
    rw [← hsum]; field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖2 * ω - c‖ ≤ 2 * ‖ω‖ + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]; norm_num; linarith
  have h2 : ‖2 * ω - c‖ * ‖c‖ ≤ 2 * ‖ω‖ + 1 := by
    calc ‖2 * ω - c‖ * ‖c‖ ≤ (2 * ‖ω‖ + 1) * 1 := by
          gcongr
      _ = 2 * ‖ω‖ + 1 := by ring
  have h3 : (a / 2) ^ 2 * ‖ω‖ ^ 2 ≤ ‖δ‖ ^ 2 * ‖ω‖ ^ 2 := by
    gcongr; linarith
  calc ‖2 * ω - c‖ * ‖c‖ / (‖δ‖ ^ 2 * ‖ω‖ ^ 2) ≤ (2 * ‖ω‖ + 1) / ((a / 2) ^ 2 * ‖ω‖ ^ 2) := by
        gcongr
    _ = 4 * (2 / (a ^ 2 * ‖ω‖) + 1 / (a ^ 2 * ‖ω‖ ^ 2)) := by field_simp; ring
    _ ≤ 4 * (2 / (a ^ 2 * a) + 1 / (a ^ 2 * a ^ 2)) := by gcongr
    _ = 4 * (2 / a ^ 3 + 1 / a ^ 4) := by ring

theorem norm_vec_eq (v : Fin 2 → ℤ) : ‖v‖ = max |(v 0 : ℝ)| |(v 1 : ℝ)| := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp [Nat.cast_natAbs]

theorem one_le_norm_vec {v : Fin 2 → ℤ} (hv : v ≠ 0) : 1 ≤ ‖v‖ := by
  rw [norm_vec_eq]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; exact hv (by ext i; fin_cases i <;> simp [h0, h1])
    have : (1 : ℝ) ≤ |(v 1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h1
    exact le_max_of_le_right this
  · have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
    exact le_max_of_le_left this

/-- `r(τ)‖v‖ ≤ 2‖c − (v₀τ + v₁)‖` for `|c| ≤ 1/2`. -/
theorem shift_bound (τ : UpperHalfPlane) {v : Fin 2 → ℤ} (hv : v ≠ 0) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    EisensteinSeries.r τ * ‖v‖ ≤ 2 * ‖(c : ℂ) - ((v 0 : ℂ) * τ + v 1)‖ := by
  have hr := EisensteinSeries.r_pos τ
  have hn : ‖(c : ℂ) - ((v 0 : ℂ) * τ + v 1)‖ = ‖(v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ)‖ := by
    rw [← norm_neg]; congr 1; push_cast; ring
  rw [hn, norm_vec_eq]
  rcases le_total |(v 1 : ℝ)| |(v 0 : ℝ)| with h | h
  · rw [max_eq_left h]
    have h0 : (v 0 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have h1 : (v 1 : ℝ) = 0 := abs_nonpos_iff.mp h
      have h0' : v 0 = 0 := by exact_mod_cast h0
      have h1' : v 1 = 0 := by exact_mod_cast h1
      exact hv (by ext i; fin_cases i <;> simp [h0', h1'])
    have hb := EisensteinSeries.auxbound1 τ (c := 1) (((v 1 : ℝ) - c) / v 0) (by norm_num)
    have he : (v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ) =
        ((v 0 : ℝ) : ℂ) * (((1 : ℝ) : ℂ) * τ + (((v 1 - c) / v 0 : ℝ) : ℂ)) := by
      have : (v 0 : ℂ) ≠ 0 := by exact_mod_cast h0
      push_cast; field_simp
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |(v 0 : ℝ)| * EisensteinSeries.r τ ≤
        |(v 0 : ℝ)| * ‖((1 : ℝ) : ℂ) * τ + (((v 1 - c) / v 0 : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    nlinarith [abs_nonneg (v 0 : ℝ)]
  · rw [max_eq_right h]
    have h1 : (v 1 : ℝ) ≠ 0 := by
      intro h1
      rw [h1, abs_zero] at h
      have h0 : (v 0 : ℝ) = 0 := abs_nonpos_iff.mp h
      have h0' : v 0 = 0 := by exact_mod_cast h0
      have h1' : v 1 = 0 := by exact_mod_cast h1
      exact hv (by ext i; fin_cases i <;> simp [h0', h1'])
    have hv1 : (1 : ℝ) ≤ |(v 1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by exact_mod_cast h1)
    have hd : |(v 1 : ℝ)| ≤ 2 * |(v 1 : ℝ) - c| := by
      have := abs_sub_abs_le_abs_sub (v 1 : ℝ) c
      linarith
    have hd0 : (v 1 : ℝ) - c ≠ 0 := by
      intro h'; rw [h', abs_zero] at hd; linarith
    have hb := EisensteinSeries.auxbound2 τ ((v 0 : ℝ) / ((v 1 : ℝ) - c)) (d := 1) (by norm_num)
    have he : (v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ) =
        (((v 1 : ℝ) - c : ℝ) : ℂ) * ((((v 0 : ℝ) / ((v 1 : ℝ) - c) : ℝ) : ℂ) * τ + ((1 : ℝ) : ℂ)) := by
      have : (v 1 : ℂ) - (c : ℂ) ≠ 0 := by exact_mod_cast hd0
      push_cast; field_simp
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |(v 1 : ℝ) - c| * EisensteinSeries.r τ ≤
        |(v 1 : ℝ) - c| * ‖(((v 0 : ℝ) / ((v 1 : ℝ) - c) : ℝ) : ℂ) * τ + ((1 : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    nlinarith [abs_nonneg ((v 1 : ℝ) - c)]


/-- The summable majorant on a vertical strip. -/
theorem wTerm_bound {c : ℝ} (hc : |c| ≤ 1 / 2) {A B : ℝ} (hB : 0 < B) {v : Fin 2 → ℤ} (hv : v ≠ 0)
    {w : ℂ} (hw : |w.re| < A ∧ B < w.im) :
    ‖wTerm c v w‖ ≤ 4 * (2 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 3 + 1 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 4) *
      ‖v‖ ^ (-3 : ℝ) := by
  set r₀ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ with hr₀
  have hr₀p : 0 < r₀ := EisensteinSeries.r_pos _
  have hwH : 0 < w.im := lt_trans hB hw.2
  set τ : UpperHalfPlane := ⟨w, hwH⟩ with hτ
  have hstrip : τ ∈ verticalStrip A B := ⟨hw.1.le, hw.2.le⟩
  have hrr : r₀ ≤ EisensteinSeries.r τ := EisensteinSeries.r_lower_bound_on_verticalStrip τ hB hstrip
  have hm := one_le_norm_vec hv
  set m := ‖v‖ with hmdef
  have hωb : r₀ * m ≤ ‖(v 0 : ℂ) * w + v 1‖ := by
    have := EisensteinSeries.r_mul_max_le τ hv
    calc r₀ * m ≤ EisensteinSeries.r τ * m := by gcongr
      _ ≤ _ := this
  have hδb : r₀ * m ≤ 2 * ‖(c : ℂ) - ((v 0 : ℂ) * w + v 1)‖ := by
    have := shift_bound τ hv hc
    calc r₀ * m ≤ EisensteinSeries.r τ * m := by gcongr
      _ ≤ _ := this
  have hcn : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have key := key_bound (mul_pos hr₀p (by linarith)) hωb hδb (by ring) hcn
  unfold wTerm
  refine key.trans ?_
  have h3 : m ^ (3 : ℝ) = m ^ (3 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [Real.rpow_neg (by linarith), h3]
  have hm0 : 0 < m := by linarith
  have e1 : 4 * (2 / (r₀ * m) ^ 3 + 1 / (r₀ * m) ^ 4) =
      4 * (2 / r₀ ^ 3 + 1 / (r₀ ^ 4 * m)) * (m ^ 3)⁻¹ := by
    field_simp
  rw [e1]
  gcongr
  calc r₀ ^ 4 = r₀ ^ 4 * 1 := by ring
    _ ≤ r₀ ^ 4 * m := by gcongr

/-- `z ↦ ∑ v, wTerm c v z` is holomorphic on `ℍ`. -/
theorem diffOn_tsum_wTerm {c : ℝ} (hc : |c| ≤ 1 / 2) (hcZ : ∀ m : ℤ, c ≠ m) :
    DifferentiableOn ℂ (fun z => ∑' v : Fin 2 → ℤ, wTerm c v z) Hs := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  have hB : 0 < B := by positivity
  set U : Set ℂ := {w | |w.re| < A ∧ B < w.im} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hz₀U : z₀ ∈ U := ⟨by simp [A], by simp only [B]; linarith⟩
  have hUH : U ⊆ Hs := fun w hw => lt_trans hB hw.2
  set K := 4 * (2 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 3 + 1 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 4)
  classical
  set u : (Fin 2 → ℤ) → ℝ := Function.update (fun v => K * ‖v‖ ^ (-3 : ℝ)) 0 ‖1 / (c : ℂ) ^ 2‖
  have hu : Summable u :=
    ((EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)).mul_left K).update _ _
  have hd : DifferentiableOn ℂ (fun z => ∑' v : Fin 2 → ℤ, wTerm c v z) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu (fun v => (diffOn_wTerm hcZ v).mono hUH) hUo ?_
    intro v w hw
    by_cases hv : v = 0
    · subst hv
      simp [u, wTerm]
    · simp only [u, Function.update_of_ne hv]
      exact wTerm_bound hc hB hv hw
  exact (hd.differentiableAt (hUo.mem_nhds hz₀U)).differentiableWithinAt

/-- `℘_τ(1/N)` on `ℍ`. -/
def Pf (N : ℕ) (z : ℂ) : ℂ := (pp (ofComplex z)).weierstrassP (1 / N)

theorem diffOn_Pf {N : ℕ} (hN : 2 ≤ N) : DifferentiableOn ℂ (Pf N) Hs := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : |(1 / N : ℝ)| ≤ 1 / 2 := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by norm_num) hN'
  have hcZ : ∀ m : ℤ, (1 / N : ℝ) ≠ m := by
    intro m hm
    have h0 : (0 : ℝ) < 1 / N := by positivity
    have h1 : (1 / N : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hm] at h0 h1
    have : (0 : ℤ) < m := by exact_mod_cast h0
    have : m < (1 : ℤ) := by exact_mod_cast h1
    omega
  refine (diffOn_tsum_wTerm hc hcZ).congr fun z hz => ?_
  simp only [Pf]
  rw [weierstrassP_pp_eq, ofComplex_coe hz]
  push_cast; rfl

/-- `f₁ = g₂g₃℘(1/N)/Δ` on `ℍ` (Weber's function where `g₂g₃ ≠ 0`). -/
def Wf (N : ℕ) (z : ℂ) : ℂ := G2f z * G3f z / Dlf z * Pf N z

theorem diffOn_Wf {N : ℕ} (hN : 2 ≤ N) : DifferentiableOn ℂ (Wf N) Hs :=
  ((diffOn_G2f.mul diffOn_G3f).div diffOn_Dlf fun z _ => Dlf_ne z).mul (diffOn_Pf hN)

theorem weber_eq_Wf {N : ℕ} (τ : UpperHalfPlane) (h2 : (pp τ).g₂ ≠ 0) (h3 : (pp τ).g₃ ≠ 0) :
    weber (pp τ) (1 / (N : ℂ)) = Wf N τ := by
  simp only [weber, h3, h2, ↓reduceIte, Wf, G2f, G3f, Dlf, Pf, ofComplex_apply]


/-! ### Special values: `g₃(i) = 0`, `g₂(ρ) = 0`, `j(i) = 1728`, `j(ρ) = 0` -/

theorem isScale_I : IsScale (pp UpperHalfPlane.I) (pp UpperHalfPlane.I) Complex.I := by
  refine ⟨Complex.I_ne_zero, ?_⟩
  ext x
  have h1 : (pp UpperHalfPlane.I).ω₁ = 1 := rfl
  have h2 : (pp UpperHalfPlane.I).ω₂ = Complex.I := rfl
  simp only [SetLike.mem_coe, Set.mem_smul_set, PeriodPair.mem_lattice, smul_eq_mul, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨n, -m, rfl⟩, by push_cast; linear_combination (-(m : ℂ)) * Complex.I_sq⟩
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨-n, m, by push_cast; linear_combination (-(n : ℂ)) * Complex.I_sq⟩

theorem omega3_im_pos : 0 < omega3.im := by
  simp [omega3]

/-- `ρ = e^{2πi/3}` in `ℍ`. -/
def τρ : UpperHalfPlane := ⟨omega3, omega3_im_pos⟩

theorem omega3_ne_zero : omega3 ≠ 0 := by
  intro h; have := omega3_cube; rw [h] at this; norm_num at this

theorem omega3_ne_one : omega3 ≠ 1 := by
  intro h; have := omega3_sq_add; rw [h] at this; norm_num at this

theorem isScale_ρ : IsScale (pp τρ) (pp τρ) omega3 := by
  refine ⟨omega3_ne_zero, ?_⟩
  ext x
  have h1 : (pp τρ).ω₁ = 1 := rfl
  have h2 : (pp τρ).ω₂ = omega3 := rfl
  simp only [SetLike.mem_coe, Set.mem_smul_set, PeriodPair.mem_lattice, smul_eq_mul, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨n - m, -m, rfl⟩, by push_cast; linear_combination (-(m : ℂ)) * omega3_sq_add⟩
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨-n, m - n, by push_cast; linear_combination (-(n : ℂ)) * omega3_sq_add⟩

theorem g3_I : (pp UpperHalfPlane.I).g₃ = 0 := by
  have h := isScale_I.g₃
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]; norm_num
  rw [h6, inv_neg, inv_one, neg_one_mul] at h
  linear_combination h / 2

theorem g2_ρ : (pp τρ).g₂ = 0 := by
  have h := isScale_ρ.g₂
  have h4 : omega3 ^ 4 = omega3 := by rw [pow_succ, omega3_cube, one_mul]
  rw [h4] at h
  have h' : (omega3 - 1) * (pp τρ).g₂ = 0 := by
    have : omega3 * (pp τρ).g₂ = (pp τρ).g₂ := by
      conv_lhs => rw [h]
      rw [← mul_assoc, mul_inv_cancel₀ omega3_ne_zero, one_mul]
    linear_combination this
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) omega3_ne_one
  · exact h0

theorem g2_I_ne : (pp UpperHalfPlane.I).g₂ ≠ 0 := by
  intro h
  apply disc_ppD_ne_zero UpperHalfPlane.I
  show (pp UpperHalfPlane.I).g₂ ^ 3 - 27 * (pp UpperHalfPlane.I).g₃ ^ 2 = 0
  rw [h, g3_I]; ring

theorem g3_ρ_ne : (pp τρ).g₃ ≠ 0 := by
  intro h
  apply disc_ppD_ne_zero τρ
  show (pp τρ).g₂ ^ 3 - 27 * (pp τρ).g₃ ^ 2 = 0
  rw [h, g2_ρ]; ring

theorem Jf_I : Jf (UpperHalfPlane.I : ℂ) = 1728 := by
  simp only [Jf, ofComplex_apply, jL, discL, g3_I]
  have := g2_I_ne
  field_simp
  ring

theorem Jf_ρ : Jf (τρ : ℂ) = 0 := by
  simp only [Jf, ofComplex_apply, jL, g2_ρ]
  ring

/-- `j` is not a root of a nonzero polynomial on all of `ℍ`. -/
theorem exists_eval_Jf_ne {c : Polynomial ℚ} (hc : c ≠ 0) :
    ∃ z ∈ Hs, c.eval₂ (Rat.castHom ℂ) (Jf z) ≠ 0 := by
  by_contra h
  push Not at h
  set T : Set ℂ := {x | c.eval₂ (Rat.castHom ℂ) x = 0} with hT
  have hTf : T.Finite := by
    have : T = {x | (c.map (Rat.castHom ℂ)).IsRoot x} := by
      ext x; simp [T, Polynomial.eval_map]
    rw [this]
    exact Polynomial.finite_setOfPred_isRoot
      ((Polynomial.map_ne_zero_iff (Rat.castHom ℂ).injective).mpr hc)
  have := isPreconnected_Hs.constant_of_mapsTo hTf.isDiscrete diffOn_Jf.continuousOn
    (fun z hz => h z hz) (x := (UpperHalfPlane.I : ℂ)) (y := (τρ : ℂ))
    UpperHalfPlane.I.coe_im_pos τρ.coe_im_pos
  rw [Jf_I, Jf_ρ] at this
  norm_num at this

/-- Some `τ` has `g₂(τ)g₃(τ) ≠ 0`. -/
theorem exists_good_point : ∃ z₀ ∈ Hs, G2f z₀ ≠ 0 ∧ G3f z₀ ≠ 0 := by
  by_contra h
  push Not at h
  have h' : ∀ z ∈ Hs, G2f z * G3f z = 0 := fun z hz => by
    by_cases h2 : G2f z = 0
    · rw [h2, zero_mul]
    · rw [h z hz h2, mul_zero]
  rcases eq_zero_or_eq_zero diffOn_G2f diffOn_G3f h' with h1 | h1
  · apply g2_I_ne
    have := h1 _ UpperHalfPlane.I.coe_im_pos
    simp only [G2f, ofComplex_apply] at this; exact this
  · apply g3_ρ_ne
    have := h1 _ τρ.coe_im_pos
    simp only [G3f, ofComplex_apply] at this; exact this


/-! ## E. The comparison -/

/-- `F(J, T) ∈ ℚ[J][T]` at `(J, T) = (j(τ), f₁(τ))`, `f₁(τ) = weber(⟨1, τ⟩, 1/N)`. -/
def evAn (N : ℕ) (F : Polynomial (Polynomial ℚ)) (τ : UpperHalfPlane) : ℂ :=
  (F.map (Polynomial.eval₂RingHom (Rat.castHom ℂ) (jL (pp τ)))).eval (weber (pp τ) (1 / (N : ℂ)))

/-- **GLUE (the `K_N = ℚ(j, f₁)` comparison; Diamond–Shurman §7.5–7.7, Shimura 1971 Ch. 6).** For `N ≥ 2` some
point `P` of exact order `N` of `E_j` has: a polynomial `F ∈ ℚ[J][T]` vanishes at `(j(τ), f₁(τ))` for every `τ ∈ ℍ`
with `g₂(τ)g₃(τ) ≠ 0` iff it vanishes at `(j, w(P))`. -/
def WeberFieldComparison : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ P : EjBar.toAffine.Point, addOrderOf P = N ∧
    ∀ F : Polynomial (Polynomial ℚ),
      (∀ τ : UpperHalfPlane, (pp τ).g₂ ≠ 0 → (pp τ).g₃ ≠ 0 → evAn N F τ = 0) ↔ evAlg F P = 0

/-- Evaluation `ℚ[J][T] → ℂ` at `(j(z), f₁(z))`. -/
def ez (N : ℕ) (z : ℂ) : Polynomial (Polynomial ℚ) →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom ℂ) (Jf z)) (Wf N z)

theorem diffOn_ez {N : ℕ} (hN : 2 ≤ N) (F : Polynomial (Polynomial ℚ)) :
    DifferentiableOn ℂ (fun z => ez N z F) Hs := by
  have h : (fun z => ez N z F) = fun z => ∑ i ∈ Finset.range (F.natDegree + 1),
      ((F.coeff i).map (Rat.castHom ℂ)).eval (Jf z) * Wf N z ^ i := by
    funext z
    simp only [ez, Polynomial.coe_eval₂RingHom, Polynomial.eval_map]
    rw [Polynomial.eval₂_eq_sum_range]
    rfl
  rw [h]
  exact DifferentiableOn.fun_sum fun i _ =>
    ((Polynomial.differentiable _).comp_differentiableOn diffOn_Jf).mul ((diffOn_Wf hN).pow i)

theorem ez_C (N : ℕ) (z : ℂ) (c : Polynomial ℚ) :
    ez N z (Polynomial.C c) = c.eval₂ (Rat.castHom ℂ) (Jf z) := by
  simp [ez]

theorem Jf_sub {z : ℂ} : Jf z - 1728 = 46656 * G3f z ^ 2 / Dlf z := by
  have h := Dlf_ne z
  rw [Jf_eq]
  rw [Dlf_eq] at h ⊢
  field_simp
  ring

theorem ez_DJ (N : ℕ) (z : ℂ) : ez N z DJ = Jf z - 1728 := by
  simp [ez, DJ]

/-- On the complex side a clearing of `ΨSqₙ(WG)` is `(j − 1728)^k · ΨSqₙ(y² = x³ − (g/4)x − g/4)((g₂/g₃)℘(1/N))`. -/
theorem ez_clears {n : ℤ} {Φ : Polynomial (Polynomial ℚ)} {k : ℕ} (h : Clears (WG.ΨSq n) Φ k)
    (N : ℕ) {z : ℂ} (h2 : G2f z ≠ 0) (h3 : G3f z ≠ 0) :
    ez N z Φ = (Jf z - 1728) ^ k *
      ((curveG (G2f z ^ 3 / G3f z ^ 2)).ΨSq n).eval (G2f z / G3f z * Pf N z) := by
  have hD := Dlf_ne z
  have hne : ez N z DJ ≠ 0 := by
    rw [ez_DJ, Jf_sub]; exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h3)) hD
  have e1 : 27 * ez N z (Polynomial.C Polynomial.X) / ez N z DJ = G2f z ^ 3 / G3f z ^ 2 := by
    rw [ez_DJ, Jf_sub, show ez N z (Polynomial.C Polynomial.X) = Jf z by simp [ez], Jf_eq]
    field_simp
    ring
  have e2 : 46656 * ez N z Polynomial.X / ez N z DJ = G2f z / G3f z * Pf N z := by
    rw [ez_DJ, Jf_sub, show ez N z Polynomial.X = Wf N z by simp [ez], Wf]
    field_simp
  rw [h ℂ (ez N z) hne, ev2_ΨSq, e1, e2, ez_DJ]

theorem evAn_eq {N : ℕ} (F : Polynomial (Polynomial ℚ)) (τ : UpperHalfPlane) (h2 : (pp τ).g₂ ≠ 0)
    (h3 : (pp τ).g₃ ≠ 0) : evAn N F τ = ez N τ F := by
  rw [evAn, weber_eq_Wf τ h2 h3, Polynomial.eval_map]
  simp only [ez, Polynomial.coe_eval₂RingHom, Jf, ofComplex_apply]

/-- **The comparison `K_N = ℚ(j, f₁)`.** -/
theorem weberFieldComparison : WeberFieldComparison := by
  intro N hN
  obtain ⟨ΦN, kN, hΦN⟩ := exists_clears (WG.ΨSq N)
  let I : Ideal (Polynomial (Polynomial ℚ)) := RingHom.ker (RingHom.pi fun z : Hs => ez N z)
  have hmemI : ∀ F, F ∈ I ↔ ∀ z ∈ Hs, ez N z F = 0 := by
    intro F
    simp only [I, RingHom.mem_ker]
    constructor
    · intro h z hz; exact congrFun h ⟨z, hz⟩
    · intro h; funext z; exact h z z.2
  obtain ⟨z₀, hz₀, h2₀, h3₀⟩ := exists_good_point
  set V : Set ℂ := {z | z ∈ Hs ∧ G2f z ≠ 0 ∧ G3f z ≠ 0} with hV
  have hVo : V ∈ nhds z₀ := by
    have h2c : ContinuousAt G2f z₀ :=
      (diffOn_G2f.differentiableAt (isOpen_Hs.mem_nhds hz₀)).continuousAt
    have h3c : ContinuousAt G3f z₀ :=
      (diffOn_G3f.differentiableAt (isOpen_Hs.mem_nhds hz₀)).continuousAt
    exact Filter.Eventually.and (isOpen_Hs.mem_nhds hz₀) ((h2c.eventually_ne h2₀).and (h3c.eventually_ne h3₀))
  have hext : ∀ F, (∀ z ∈ V, ez N z F = 0) → ∀ z ∈ Hs, ez N z F = 0 := fun F h =>
    eq_zero_of_eventually (diffOn_ez hN F) hz₀ (Filter.eventually_of_mem hVo fun z hz => h z hz)
  have hprime : I.IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : Polynomial (Polynomial ℚ)) ∈ I := htop ▸ Submodule.mem_top
      have := (hmemI 1).1 h1 z₀ hz₀
      rw [map_one] at this
      exact one_ne_zero this
    · intro F G hFG
      have h := (hmemI _).1 hFG
      simp only [map_mul] at h
      rcases eq_zero_or_eq_zero (diffOn_ez hN F) (diffOn_ez hN G) h with h1 | h1
      · exact Or.inl ((hmemI F).2 h1)
      · exact Or.inr ((hmemI G).2 h1)
  have hdisj : ∀ c : Polynomial ℚ, Polynomial.C c ∈ I → c = 0 := by
    intro c hc
    by_contra hc0
    obtain ⟨z, hz, hne⟩ := exists_eval_Jf_ne hc0
    exact hne (by rw [← ez_C N]; exact (hmemI _).1 hc z hz)
  have hNmem : ((N : ℕ) : ℂ) * (1 / (N : ℂ)) = 1 := by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have hΦNI : ΦN ∈ I := by
    rw [hmemI]
    apply hext
    rintro z ⟨hz, h2, h3⟩
    rw [ez_clears hΦN N h2 h3]
    have hpt := (eval_ΨSq_weber_eq_zero_iff (ofComplex z) h2 h3 hN N).mpr
      (by rw [hNmem]; exact PeriodPair.ω₁_mem_lattice _)
    have hcast : ((N : ℕ) : ℤ) = (N : ℤ) := rfl
    simp only [G2f, G3f, Pf] at hpt ⊢
    rw [hpt, mul_zero]
  have hΔ : EDSBar.Δ ≠ 0 := EDSBar.isUnit_Δ.ne_zero
  have hΦN0 : ΦN ≠ 0 := by
    intro h0
    apply ΨSq_ne_zero_of_Δ_ne_zero EDSBar hΔ (n := (N : ℤ)) (by exact_mod_cast (show N ≠ 0 by omega))
    apply Polynomial.funext
    intro x
    have hg : algebraMap Qj Kbar (gDS - 27) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective, gDS_sub]
      exact div_ne_zero (by norm_num) X_sub_1728_ne_zero
    have := evK_clears hΦN (x / algebraMap Qj Kbar (gDS - 27))
    rw [h0, map_zero, mul_div_cancel₀ _ hg] at this
    rw [Polynomial.eval_zero]
    exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ (evK_DJ_ne _))
  obtain ⟨θ, hθ⟩ := exists_root_of_isPrime hprime hdisj hΦNI hΦN0
  have hroot : (EDSBar.ΨSq (N : ℕ)).eval (algebraMap Qj Kbar (gDS - 27) * θ) = 0 := by
    have := (hθ ΦN).1 hΦNI
    rw [evK_clears hΦN] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (evK_DJ_ne θ))
  obtain ⟨P, hP0, hPN, hwP, hPd⟩ := exists_point_of_root θ hroot
  refine ⟨P, ?_, fun F => ?_⟩
  · have hd := addOrderOf_dvd_of_nsmul_eq_zero hPN
    have hdpos : 0 < addOrderOf P := Nat.pos_of_dvd_of_pos hd (by omega)
    by_contra hne
    have hdlt : addOrderOf P < N := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hne
    have hev := hPd (addOrderOf P) (addOrderOf_nsmul_eq_zero P)
    obtain ⟨Φd, kd, hΦd⟩ := exists_clears (WG.ΨSq (addOrderOf P : ℕ))
    have hΦdI : Φd ∈ I := by rw [hθ, evK_clears hΦd, hev, mul_zero]
    have h1 := (hmemI Φd).1 hΦdI z₀ hz₀
    rw [ez_clears hΦd N h2₀ h3₀] at h1
    have hD0 : Jf z₀ - 1728 ≠ 0 := by
      rw [Jf_sub]; exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h3₀)) (Dlf_ne z₀)
    have h1' := (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hD0)
    simp only [G2f, G3f, Pf] at h1'
    rw [eval_ΨSq_weber_eq_zero_iff (ofComplex z₀) h2₀ h3₀ hN] at h1'
    apply div_nat_not_mem (ofComplex z₀) hdpos hdlt
    rw [div_eq_mul_one_div]; exact h1'
  · rw [evAlg_eq, hwP, ← hθ, hmemI]
    constructor
    · intro h
      apply hext
      rintro z ⟨hz, h2, h3⟩
      have := h (ofComplex z) h2 h3
      rw [evAn_eq F _ h2 h3, ofComplex_coe hz] at this
      exact this
    · intro h τ h2 h3
      rw [evAn_eq F τ h2 h3]
      exact h τ τ.coe_im_pos


/-! ## F. `ℚ(j)(w(P)) = ℚ(j)(x(P))` (x1-igusa, verbatim) -/

/-- `ℚ(j)(w(P)) = ℚ(j)(x(P))`: `w` is a `ℚ(j)`-affine function of `x` with nonzero slope. -/
theorem adjoin_wOf (P : EjBar.toAffine.Point) :
    IntermediateField.adjoin Qj {wOf P} = fieldX1 P := by
  have hα : algebraMap Qj Kbar alpha ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]; exact alpha_ne_zero
  have hg : algebraMap Qj Kbar (gDS - 27) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective, gDS_sub]
    exact div_ne_zero (by norm_num) X_sub_1728_ne_zero
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hx : xCoord P ∈ fieldX1 P := IntermediateField.mem_adjoin_simple_self Qj _
    unfold wOf
    refine div_mem (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hx)
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.algebraMap_mem _ _)
  · unfold fieldX1
    rw [IntermediateField.adjoin_simple_le_iff]
    have hw : wOf P ∈ IntermediateField.adjoin Qj {wOf P} := IntermediateField.mem_adjoin_simple_self Qj _
    have hx : xCoord P = (wOf P * algebraMap Qj Kbar (gDS - 27) - algebraMap Qj Kbar (-3 / 2)) /
        algebraMap Qj Kbar alpha := by
      unfold wOf
      field_simp
      ring
    rw [hx]
    exact div_mem (sub_mem (mul_mem hw (IntermediateField.algebraMap_mem _ _))
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.algebraMap_mem _ _)

end X1Igusa.Weber
