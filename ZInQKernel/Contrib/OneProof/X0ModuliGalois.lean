import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.TYZChain.ModFn

/-!
# x0-moduli: the top hypothesis `hX = T5Glue.X0ModuliGalois` split at the isolated points of `(j, j_N)`

Task x0-moduli (2026-11-15). Report: `docs/research/x0-moduli.md`; log: `scratch/x0-moduli/log.md`.

`T5Glue.X0ModuliGalois` (`RingClassLattice.lean`; the canonical model of `X₀(N)` over `ℚ` at algebraic points)
is proved from

* `X0Moduli.WeierstrassGroupLaw` (textbook: the analytic chord-and-tangent law of `ℂ/Λ`; Silverman GTM 106
  VI.3.6(b) with III.2.3, Whittaker–Watson §20.3; numbers UNVERIFIED),
* `X0Moduli.VeluCyclic` (textbook: Vélu's formulas for `ℂ/⟨1,τ⟩ → ℂ/⟨1/N,τ⟩`; Vélu 1971; UNVERIFIED),
* `ShimuraModFnTask.RatX0Rep` (the kernel's existing Prop: `ℚ(X₀(N)) = ℚ(j, j_N)` with a denominator that
  does not vanish at isolated points; a textbook combination, not one print),
* `X0Moduli.X0ModuliGaloisNonIsolated` (`X0ModuliGalois` restricted to the points where the plane model
  `(j, j_N)` is not isolated; these are CM points; the same sources as `X0ModuliGalois`),

by `X0Moduli.x0ModuliGalois_of_leaves`. The step `σ(j(Nτ)) = j(Nτ')` (`X0Moduli.JNConj`) is proved
(`jnConj_of_leaves`). No `sorry`, no `axiom`; only `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

namespace X0Moduli

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM Complex T5Glue
open ZInQ.Contrib.TYZGenus.Shimura (IsRatModFn)
open ZInQ.Contrib.TYZGenus.ShimuraModFnTask (jInv scaleH evalJ IsIsolated RatX0Rep)

/-! ## `j(τ) = j(ℂ/⟨1, τ⟩)` -/

theorem ppD_eq_pp (τ : UpperHalfPlane) : ppD τ = pp τ := rfl

/-- Klein's `j = E₄³/Δ` is the `j`-invariant `1728 g₂³/(g₂³ − 27 g₃²)` of `ℂ/⟨1, τ⟩`. -/
theorem jInv_eq_jL (τ : UpperHalfPlane) : jInv τ = jL (pp τ) := by
  have h4 := G_eq_E (k := 4) (by norm_num) τ
  have h6 := G_eq_E (k := 6) (by norm_num) τ
  have hz4 : riemannZeta ((4 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 4 / 90 := by
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num]; exact riemannZeta_four
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    rw [show ((6 : ℕ) : ℂ) = 6 by norm_num]; exact riemannZeta_six
  rw [hz4] at h4
  rw [hz6] at h6
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hne := ModularForm.discriminant_ne_zero τ
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : (ppD τ).g₂ ^ 3 - 27 * (ppD τ).g₃ ^ 2 =
      64 * (Real.pi : ℂ) ^ 12 / 27 * 1728 * ModularForm.discriminant τ := by
    rw [PeriodPair.g₂, PeriodPair.g₃, h4, h6, hΔ]
    simp only [ModularForm.E₄, ModularForm.E₆]
    ring
  have hg2 : (ppD τ).g₂ = 4 / 3 * (Real.pi : ℂ) ^ 4 * ModularForm.E₄ τ := by
    rw [PeriodPair.g₂, h4]; simp only [ModularForm.E₄]; ring
  rw [← ppD_eq_pp, jL, discL, key, hg2, jInv]
  field_simp
  ring

/-- `σ(j(τ)) = j(τ')` when `σ(E_τ) ≅ E_{τ'}`. -/
theorem jInv_conj {σ : ℂ →+* ℂ} {τ τ' : UpperHalfPlane} {μ : ℂ}
    (h : IsConjModel σ (pp τ) (pp τ') μ) : σ (jInv τ) = jInv τ' := by
  rw [jInv_eq_jL, jInv_eq_jL, h.jL]

/-! ## The split -/

/-- **GLUE JN-CONJ (`σ` carries `j(E/C)` to `j(E^σ/C^σ)`).** Under the hypotheses of
`T5Glue.X0ModuliGalois` (`σ(E_τ) ≅ E_{τ'}` through `μ`, carrying `σ(1/N)` to `k/N`),
`σ(j(Nτ)) = j(Nτ')`. Content: `ℂ/⟨1/N, τ⟩ = E_τ/⟨1/N⟩ ≅ ℂ/⟨1, Nτ⟩`; Vélu's formulas express
`g₂, g₃` of `⟨1/N, τ⟩` as polynomials over `ℚ` in `g₂(τ), g₃(τ)` and `℘_τ(m/N)`, `1 ≤ m < N`; the
addition law of `℘` gives `σ(℘_τ(m/N)) = μ²℘_{τ'}(mk/N)` and `(k, N) = 1`. Glue: proved from the
textbook leaves `WeierstrassGroupLaw` and `VeluAnalytic` (see `JNConj.lean`) or open. -/
def JNConj : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      σ (jInv (scaleH N τ)) = jInv (scaleH N τ')

/-- **X0-MODULI at the non-isolated points (consequence; the same sources as
`T5Glue.X0ModuliGalois`).** `T5Glue.X0ModuliGalois` restricted to points `τ` that are not
isolated on the plane model `(j, j_N)` of `X₀(N)` (`ShimuraModFnTask.IsIsolated`: two of the
`ψ(N)` cyclic `N`-isogenies of `E_τ` have isomorphic targets). Such `E_τ` has complex
multiplication (a non-scalar endomorphism `E_τ → E_τ/C ≅ E_τ/C' → E_τ` of degree `N²`), so there
are finitely many such points on `Y₀(N)`, all CM points. -/
def X0ModuliGaloisNonIsolated : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      (∀ i < N, ∃ a : Qbar, ιC a = modCoord N τ i) →
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      ¬ IsIsolated N τ →
      σ (g τ) = g τ'

/-- `σ` commutes with evaluation at `(j, j_N)` once it carries `j(τ), j(Nτ)` to `j(τ'), j(Nτ')`. -/
theorem evalJ_conj (σ : ℂ →+* ℂ) {N : ℕ} {τ τ' : UpperHalfPlane} (h0 : σ (jInv τ) = jInv τ')
    (h1 : σ (jInv (scaleH N τ)) = jInv (scaleH N τ')) (P : MvPolynomial (Fin 2) ℚ) :
    σ (evalJ N P τ) = evalJ N P τ' := by
  have := MvPolynomial.comp_aeval_apply (f := ![jInv τ, jInv (scaleH N τ)]) σ.toRatAlgHom P
  simp only [RingHom.toRatAlgHom_apply] at this
  rw [evalJ, this, evalJ]
  congr 2
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- **X0-MODULI at isolated points** from `RatX0Rep` and `JNConj`. -/
theorem x0ModuliGalois_isolated (hR : RatX0Rep) (hJ : JNConj) :
    ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      IsIsolated N τ →
      σ (g τ) = g τ' := by
  intro N hN g hg σ τ τ' μ hμ hk hiso
  obtain ⟨A, B, hrep, hB⟩ := hR N hN g hg
  have hB0 := hB τ hiso
  have h0 : (σ : ℂ →+* ℂ) (jInv τ) = jInv τ' := jInv_conj hμ
  have h1 : (σ : ℂ →+* ℂ) (jInv (scaleH N τ)) = jInv (scaleH N τ') := hJ N hN σ τ τ' μ hμ hk
  have eB := evalJ_conj (σ : ℂ →+* ℂ) h0 h1 B
  have eA := evalJ_conj (σ : ℂ →+* ℂ) h0 h1 A
  have hB0' : evalJ N B τ' ≠ 0 := by
    rw [← eB]; intro h; exact hB0 ((map_eq_zero_iff _ (σ : ℂ →+* ℂ).injective).1 h)
  have hg1 : g τ = evalJ N A τ / evalJ N B τ := by
    rw [← hrep τ]; field_simp
  have hg2 : g τ' = evalJ N A τ' / evalJ N B τ' := by
    rw [← hrep τ']; field_simp
  have : (σ : ℂ →+* ℂ) (g τ) = g τ' := by
    rw [hg1, map_div₀, eA, eB, hg2]
  exact this

/-- **The split:** `X0ModuliGalois ⇐ RatX0Rep ∧ JNConj ∧ X0ModuliGaloisNonIsolated`. -/
theorem x0ModuliGalois_of_split (hR : RatX0Rep) (hJ : JNConj)
    (hS : X0ModuliGaloisNonIsolated) : T5Glue.X0ModuliGalois := by
  intro N hN g hg σ τ τ' μ halg hμ hk
  by_cases hiso : IsIsolated N τ
  · exact x0ModuliGalois_isolated hR hJ N hN g hg σ τ τ' μ hμ hk hiso
  · exact hS N hN g hg σ τ τ' μ halg hμ hk hiso


/-! ## The textbook leaves under `JNConj` -/

/-- **TEXTBOOK WP-GROUP-LAW (the analytic group law of `ℂ/Λ`).** For a lattice `Λ` (Mathlib's
`PeriodPair`) and `z, w ∉ Λ`:
(a) `℘(z) = ℘(w)` only if `z ≡ ±w (mod Λ)`;
(b) `℘'(z) = 0` only if `2z ∈ Λ`;
(c) (chord) if `℘(z) ≠ ℘(w)`, with `λ = (℘'(z) − ℘'(w))/(℘(z) − ℘(w))`, `ν = ℘'(z) − λ℘(z)`:
    `℘(z + w) = λ²/4 − ℘(z) − ℘(w)` and `℘'(z + w) = −(λ℘(z + w) + ν)`;
(d) (tangent) if `2z ∉ Λ`, with `λ = (6℘(z)² − g₂/2)/℘'(z)`, `ν = ℘'(z) − λ℘(z)`:
    `℘(2z) = λ²/4 − 2℘(z)` and `℘'(2z) = −(λ℘(2z) + ν)`.
That is: `z ↦ (℘(z), ℘'(z))` is an injective group homomorphism `ℂ/Λ → E_Λ(ℂ)`,
`E_Λ : y² = 4x³ − g₂x − g₃`, and the group law of `E_Λ` is the chord-and-tangent law.
Sources (numbers UNVERIFIED, from memory): Silverman, *The arithmetic of elliptic curves*, GTM 106,
Prop. VI.3.6(b) with the group law formulas III.2.3; Whittaker–Watson, *A course of modern
analysis*, §20.3 (addition theorem) and §20.31 (duplication); Lang, *Elliptic functions*, Ch. 1.
Kind: textbook, a consequence of the print (the print states (c), (d) for `y² = 4x³ − g₂x − g₃` in this
normalization; (a), (b) are the injectivity of `ℂ/Λ → E_Λ(ℂ)` and the description of `E_Λ[2]`). -/
def WeierstrassGroupLaw : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    (L.weierstrassP z = L.weierstrassP w → z - w ∈ L.lattice ∨ z + w ∈ L.lattice) ∧
    (L.derivWeierstrassP z = 0 → 2 * z ∈ L.lattice) ∧
    (L.weierstrassP z ≠ L.weierstrassP w →
      L.weierstrassP (z + w) =
          ((L.derivWeierstrassP z - L.derivWeierstrassP w) /
            (L.weierstrassP z - L.weierstrassP w)) ^ 2 / 4 - L.weierstrassP z - L.weierstrassP w ∧
      L.derivWeierstrassP (z + w) =
          -((L.derivWeierstrassP z - L.derivWeierstrassP w) /
              (L.weierstrassP z - L.weierstrassP w) * L.weierstrassP (z + w) +
            (L.derivWeierstrassP z - (L.derivWeierstrassP z - L.derivWeierstrassP w) /
              (L.weierstrassP z - L.weierstrassP w) * L.weierstrassP z))) ∧
    (2 * z ∉ L.lattice →
      L.weierstrassP (2 * z) =
          ((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z) ^ 2 / 4 -
            2 * L.weierstrassP z ∧
      L.derivWeierstrassP (2 * z) =
          -((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z * L.weierstrassP (2 * z) +
            (L.derivWeierstrassP z - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z *
              L.weierstrassP z)))

/-- **TEXTBOOK VELU-CYCLIC (Vélu's formulas for the cyclic isogeny `ℂ/⟨1, τ⟩ → ℂ/⟨1/N, τ⟩`).**
For `N ≥ 1` and `τ ∈ ℍ`: `⟨1/N, τ⟩ = N⁻¹⟨1, Nτ⟩` is the lattice of `E_τ/⟨1/N⟩`, and
`N⁴g₂(⟨1, Nτ⟩) = g₂(τ) + Σ_{m=1}^{N−1} (60℘_τ(m/N)² − 5g₂(τ))`,
`N⁶g₃(⟨1, Nτ⟩) = g₃(τ) + Σ_{m=1}^{N−1} (140℘_τ(m/N)³ − 21g₂(τ)℘_τ(m/N) − 14g₃(τ))`.
Source (UNVERIFIED numbers): J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris
Sér. A 273 (1971), 238–241 (the formulas `A₄ = a₄ − 5t`, `A₆ = a₆ − 7w` for the quotient by a finite
subgroup), here for `y² = x³ − (g₂/4)x − g₃/4`, `x = ℘`, `y = ℘'/2`, the subgroup `⟨1/N⟩`, and the
normalized isogeny `℘_{Λ'}(z) = ℘_Λ(z) + Σ_{c}(℘_Λ(z + c) − ℘_Λ(c))`; Washington, *Elliptic curves:
number theory and cryptography*, 2nd ed., Thm. 12.16. Kind: textbook, a consequence of the print plus
the uniformization (the print is algebraic). It is also a lattice-sum identity provable from
Mathlib (`℘'' = 6Σ(z − ω)⁻⁴`, `℘'''' = 120Σ(z − ω)⁻⁶`). Numerically checked (log step 4). -/
def VeluCyclic : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ τ : UpperHalfPlane,
    (N : ℂ) ^ 4 * (pp (scaleH N τ)).g₂ = (pp τ).g₂ + ∑ m ∈ Finset.Ico 1 N,
      (60 * (pp τ).weierstrassP ((m : ℂ) / N) ^ 2 - 5 * (pp τ).g₂) ∧
    (N : ℂ) ^ 6 * (pp (scaleH N τ)).g₃ = (pp τ).g₃ + ∑ m ∈ Finset.Ico 1 N,
      (140 * (pp τ).weierstrassP ((m : ℂ) / N) ^ 3 -
        21 * (pp τ).g₂ * (pp τ).weierstrassP ((m : ℂ) / N) - 14 * (pp τ).g₃)

/-! ## Lattice membership of `m/N` -/

theorem natDiv_mem_iff (τ : UpperHalfPlane) {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ((m : ℂ) / N) ∈ (pp τ).lattice ↔ N ∣ m := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · intro h
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 h
    simp only [pp] at hpq
    have him := congrArg Complex.im hpq
    have hdiv : ((m : ℂ) / N).im = 0 := by
      rw [show ((m : ℂ) / N) = ((m / N : ℝ) : ℂ) by push_cast; rfl, ofReal_im]
    rw [hdiv] at him
    simp only [add_im, mul_im, intCast_re, intCast_im, one_im, one_re, mul_zero, zero_mul,
      add_zero, zero_add] at him
    have hq : (q : ℝ) = 0 := by
      rcases mul_eq_zero.1 him with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt τ.im_pos)
    have hq' : q = 0 := by exact_mod_cast hq
    subst hq'
    simp only [Int.cast_zero, zero_mul, add_zero, mul_one] at hpq
    have h2 : (p : ℂ) * N = m := by rw [hpq]; field_simp
    have h3 : (p : ℤ) * N = m := by exact_mod_cast h2
    exact Int.natCast_dvd_natCast.1 ⟨p, by rw [← h3]; ring⟩
  · rintro ⟨c, rfl⟩
    refine PeriodPair.mem_lattice.2 ⟨c, 0, ?_⟩
    simp only [pp, Int.cast_zero, zero_mul, add_zero, mul_one, Int.cast_natCast]
    push_cast
    field_simp

theorem natCast_mem (τ : UpperHalfPlane) (q : ℕ) : (q : ℂ) ∈ (pp τ).lattice :=
  PeriodPair.mem_lattice.2 ⟨q, 0, by simp [pp]⟩

/-! ## Transfer of the chord and tangent constructions through `σ` -/

section Transfer

variable (σ : ℂ →+* ℂ) {μ : ℂ}

theorem slope_transfer (hμ : μ ≠ 0) {x1 y1 x2 y2 x1' y1' x2' y2' : ℂ}
    (h1 : σ x1 = μ ^ 2 * x1') (h2 : σ x2 = μ ^ 2 * x2') (h3 : σ y1 = μ ^ 3 * y1')
    (h4 : σ y2 = μ ^ 3 * y2') (hx : x1 ≠ x2) :
    σ ((y1 - y2) / (x1 - x2)) = μ * ((y1' - y2') / (x1' - x2')) := by
  have hx' : x1' - x2' ≠ 0 := by
    intro h
    apply hx
    apply σ.injective
    rw [h1, h2, sub_eq_zero.1 h]
  rw [map_div₀, map_sub, map_sub, h1, h2, h3, h4]
  field_simp

theorem tslope_transfer (hμ : μ ≠ 0) {x y g x' y' g' : ℂ}
    (h1 : σ x = μ ^ 2 * x') (h3 : σ y = μ ^ 3 * y') (hg : σ g = μ ^ 4 * g') (hy : y ≠ 0) :
    σ ((6 * x ^ 2 - g / 2) / y) = μ * ((6 * x' ^ 2 - g' / 2) / y') := by
  have hy' : y' ≠ 0 := by
    intro h
    apply hy
    apply σ.injective
    rw [h3, h, mul_zero, map_zero]
  rw [map_div₀, map_sub, map_mul, map_pow, map_div₀, h1, h3, hg]
  simp only [map_ofNat]
  field_simp

theorem x3_transfer {l l' x1 x2 x1' x2' : ℂ} (hl : σ l = μ * l')
    (h1 : σ x1 = μ ^ 2 * x1') (h2 : σ x2 = μ ^ 2 * x2') :
    σ (l ^ 2 / 4 - x1 - x2) = μ ^ 2 * (l' ^ 2 / 4 - x1' - x2') := by
  rw [map_sub, map_sub, map_div₀, map_pow, hl, h1, h2]
  simp only [map_ofNat]
  ring

theorem x3t_transfer {l l' x1 x1' : ℂ} (hl : σ l = μ * l') (h1 : σ x1 = μ ^ 2 * x1') :
    σ (l ^ 2 / 4 - 2 * x1) = μ ^ 2 * (l' ^ 2 / 4 - 2 * x1') := by
  rw [map_sub, map_mul, map_div₀, map_pow, hl, h1]
  simp only [map_ofNat]
  ring

theorem y3_transfer {l l' x3 x1 y1 x3' x1' y1' : ℂ} (hl : σ l = μ * l')
    (h1 : σ x1 = μ ^ 2 * x1') (h3 : σ y1 = μ ^ 3 * y1') (h5 : σ x3 = μ ^ 2 * x3') :
    σ (-(l * x3 + (y1 - l * x1))) = μ ^ 3 * (-(l' * x3' + (y1' - l' * x1'))) := by
  rw [map_neg, map_add, map_mul, map_sub, map_mul, hl, h1, h3, h5]
  ring

end Transfer

/-! ## `σ` on the multiples `m/N` -/

theorem lattice_neg_eq {L : PeriodPair} {a b : ℂ} (h : a + b ∈ L.lattice) :
    L.weierstrassP a = L.weierstrassP b := by
  have e : a - (a + b) = -b := by ring
  rw [← PeriodPair.weierstrassP_sub_coe L a ⟨a + b, h⟩]
  simp only
  rw [e, PeriodPair.weierstrassP_neg]

theorem deriv_zero_of_two {L : PeriodPair} {a : ℂ} (h : 2 * a ∈ L.lattice) :
    L.derivWeierstrassP a = 0 := by
  have e : a - 2 * a = -a := by ring
  have h1 := PeriodPair.derivWeierstrassP_sub_coe L a ⟨2 * a, h⟩
  simp only at h1
  rw [e, PeriodPair.derivWeierstrassP_neg] at h1
  have : (2 : ℂ) * L.derivWeierstrassP a = 0 := by linear_combination -h1
  simpa using this

/-- **Multiples.** Under the hypotheses of `X0ModuliGalois` (with `k`), for `1 ≤ m < N`:
`N ∤ mk`, `σ(℘_τ(m/N)) = μ²℘_{τ'}(mk/N)`, `σ(℘'_τ(m/N)) = μ³℘'_{τ'}(mk/N)`. -/
theorem conj_multiples (hG : WeierstrassGroupLaw) (σ : ℂ →+* ℂ) {τ τ' : UpperHalfPlane} {μ : ℂ}
    {N k : ℕ} (hμ : IsConjModel σ (pp τ) (pp τ') μ) (hk1 : 1 ≤ k) (hkN : k < N)
    (hp : σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N))
    (hd : σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) :
    ∀ m : ℕ, 1 ≤ m → m < N → ¬ N ∣ m * k ∧
      σ ((pp τ).weierstrassP ((m : ℂ) / N)) =
        μ ^ 2 * (pp τ').weierstrassP (((m * k : ℕ) : ℂ) / N) ∧
      σ ((pp τ).derivWeierstrassP ((m : ℂ) / N)) =
        μ ^ 3 * (pp τ').derivWeierstrassP (((m * k : ℕ) : ℂ) / N) := by
  have hN : 0 < N := by omega
  have hμ0 := hμ.1
  have hwL : (1 : ℂ) / N ∉ (pp τ).lattice := by
    have := (natDiv_mem_iff τ hN 1).not.2
      (fun h => absurd (Nat.le_of_dvd one_pos h) (by omega))
    simpa using this
  have hwL' : (k : ℂ) / N ∉ (pp τ').lattice := (natDiv_mem_iff τ' hN k).not.2
    (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
  intro m hm1
  induction m, hm1 using Nat.le_induction with
  | base =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · rw [one_mul]; exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · simpa using hp
    · simpa using hd
  | succ m hm IH =>
    intro hmN
    obtain ⟨hdiv, hpm, hdm⟩ := IH (by omega)
    rcases Nat.lt_or_ge 1 m with h2 | h1
    · -- the chord through `m/N` and `1/N`
      have hzw : ((m + 1 : ℕ) : ℂ) / N = (m : ℂ) / N + 1 / N := by push_cast; ring
      have hzw' : (((m + 1) * k : ℕ) : ℂ) / N = ((m * k : ℕ) : ℂ) / N + k / N := by
        push_cast; ring
      have hzL : (m : ℂ) / N ∉ (pp τ).lattice := (natDiv_mem_iff τ hN m).not.2
        (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
      have hzL' : ((m * k : ℕ) : ℂ) / N ∉ (pp τ').lattice := (natDiv_mem_iff τ' hN _).not.2 hdiv
      have hsL : (m : ℂ) / N + 1 / N ∉ (pp τ).lattice := by
        rw [← hzw]
        exact (natDiv_mem_iff τ hN _).not.2
          (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
      have hne : (pp τ).weierstrassP ((m : ℂ) / N) ≠ (pp τ).weierstrassP (1 / N) := by
        intro he
        rcases (hG (pp τ) _ _ hzL hwL).1 he with h | h
        · have e : (m : ℂ) / N - 1 / N = ((m - 1 : ℕ) : ℂ) / N := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [e] at h
          exact absurd (Nat.le_of_dvd (by omega) ((natDiv_mem_iff τ hN _).1 h)) (by omega)
        · exact hsL h
      have hne' : (pp τ').weierstrassP (((m * k : ℕ) : ℂ) / N) ≠ (pp τ').weierstrassP (k / N) := by
        intro he
        apply hne
        apply σ.injective
        rw [hpm, hp, he]
      have hsL' : ((m * k : ℕ) : ℂ) / N + k / N ∉ (pp τ').lattice :=
        fun h => hne' (lattice_neg_eq h)
      obtain ⟨hx, hy⟩ := (hG (pp τ) _ _ hzL hwL).2.2.1 hne
      obtain ⟨hx', hy'⟩ := (hG (pp τ') _ _ hzL' hwL').2.2.1 hne'
      have hl := slope_transfer σ hμ0 hpm hp hdm hd hne
      have h5 : σ ((pp τ).weierstrassP ((m : ℂ) / N + 1 / N)) =
          μ ^ 2 * (pp τ').weierstrassP (((m * k : ℕ) : ℂ) / N + k / N) := by
        rw [hx, x3_transfer σ hl hpm hp, hx']
      refine ⟨?_, ?_, ?_⟩
      · exact (natDiv_mem_iff τ' hN _).not.1 (by rw [hzw']; exact hsL')
      · rw [hzw, hzw']; exact h5
      · rw [hzw, hzw', hy, y3_transfer σ hl hpm hdm h5, hy']
    · -- the tangent at `1/N`
      obtain rfl : m = 1 := by omega
      have hzw : ((1 + 1 : ℕ) : ℂ) / N = 2 * (1 / N) := by push_cast; ring
      have hzw' : (((1 + 1) * k : ℕ) : ℂ) / N = 2 * ((k : ℂ) / N) := by push_cast; ring
      have h2w : 2 * ((1 : ℂ) / N) ∉ (pp τ).lattice := by
        rw [← hzw]
        exact (natDiv_mem_iff τ hN _).not.2
          (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
      have hD : (pp τ).derivWeierstrassP (1 / N) ≠ 0 :=
        fun h => h2w ((hG (pp τ) _ _ hwL hwL).2.1 h)
      have hD' : (pp τ').derivWeierstrassP (k / N) ≠ 0 := by
        intro h
        apply hD
        apply σ.injective
        rw [hd, h, mul_zero, map_zero]
      have h2w' : 2 * ((k : ℂ) / N) ∉ (pp τ').lattice := fun h => hD' (deriv_zero_of_two h)
      obtain ⟨hx, hy⟩ := (hG (pp τ) _ _ hwL hwL).2.2.2 h2w
      obtain ⟨hx', hy'⟩ := (hG (pp τ') _ _ hwL' hwL').2.2.2 h2w'
      have hl := tslope_transfer σ hμ0 hp hd hμ.2.1 hD
      have h5 : σ ((pp τ).weierstrassP (2 * (1 / N))) =
          μ ^ 2 * (pp τ').weierstrassP (2 * ((k : ℂ) / N)) := by
        rw [hx, x3t_transfer σ hl hp, hx']
      refine ⟨?_, ?_, ?_⟩
      · exact (natDiv_mem_iff τ' hN _).not.1 (by rw [hzw']; exact h2w')
      · rw [hzw, hzw']; exact h5
      · rw [hzw, hzw', hy, y3_transfer σ hl hp hd h5, hy']

/-- `k` is prime to `N` when `N ∤ mk` for every `1 ≤ m < N`. -/
theorem coprime_of_multiples {N k : ℕ} (hN : 0 < N) (h : ∀ m : ℕ, 1 ≤ m → m < N → ¬ N ∣ m * k) :
    Nat.Coprime k N := by
  by_contra hc
  have hpos : 0 < Nat.gcd k N := Nat.gcd_pos_of_pos_right _ hN
  have hd1 : 1 < Nat.gcd k N := by
    have : Nat.gcd k N ≠ 1 := hc
    omega
  have hdN : Nat.gcd k N ∣ N := Nat.gcd_dvd_right k N
  have hdk : Nat.gcd k N ∣ k := Nat.gcd_dvd_left k N
  have h1 : 1 ≤ N / Nat.gcd k N := Nat.div_pos (Nat.le_of_dvd hN hdN) hpos
  have h2 : N / Nat.gcd k N < N := Nat.div_lt_self hN hd1
  apply h _ h1 h2
  obtain ⟨c, hc⟩ := hdk
  refine ⟨c, ?_⟩
  calc N / Nat.gcd k N * k = N / Nat.gcd k N * (Nat.gcd k N * c) := by rw [← hc]
    _ = N / Nat.gcd k N * Nat.gcd k N * c := by ring
    _ = N * c := by rw [Nat.div_mul_cancel hdN]

/-- Reindexing `m ↦ mk mod N` on `{1, …, N − 1}` for `k` prime to `N`. -/
theorem sum_perm (τ' : UpperHalfPlane) {N k : ℕ} (hN : 0 < N) (hcop : Nat.Coprime k N)
    (F : ℂ → ℂ) :
    ∑ m ∈ Finset.Ico 1 N, F ((pp τ').weierstrassP (((m * k : ℕ) : ℂ) / N)) =
      ∑ m ∈ Finset.Ico 1 N, F ((pp τ').weierstrassP ((m : ℂ) / N)) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hper : ∀ m : ℕ, (pp τ').weierstrassP (((m * k : ℕ) : ℂ) / N) =
      (pp τ').weierstrassP (((m * k % N : ℕ) : ℂ) / N) := by
    intro m
    have e : (((m * k : ℕ) : ℂ) / N) = (((m * k % N : ℕ) : ℂ) / N) + ((m * k / N : ℕ) : ℂ) := by
      conv_lhs => rw [← Nat.mod_add_div (m * k) N]
      push_cast
      field_simp
    rw [e, PeriodPair.weierstrassP_add_coe (pp τ') _ ⟨_, natCast_mem τ' _⟩]
  simp_rw [hper]
  have hmaps : ∀ m ∈ Finset.Ico 1 N, m * k % N ∈ Finset.Ico 1 N := by
    intro m hm
    rw [Finset.mem_Ico] at hm ⊢
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.mod_lt _ hN⟩
    have hdvd : N ∣ m * k := Nat.dvd_of_mod_eq_zero h0
    have : N ∣ m := Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hinj : Set.InjOn (fun m => m * k % N) (Finset.Ico 1 N : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have h : a * k ≡ b * k [MOD N] := hab
    have h' := Nat.ModEq.cancel_right_of_coprime hcop.symm h
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  refine Finset.sum_nbij (fun m => m * k % N) hmaps hinj ?_ (fun _ _ => rfl)
  exact Finset.surjOn_of_injOn_of_card_le _ (fun m hm => hmaps m hm) hinj le_rfl

/-- **`JNConj` from the textbook leaves `WeierstrassGroupLaw` and `VeluCyclic`.** -/
theorem jnConj_of_leaves (hG : WeierstrassGroupLaw) (hV : VeluCyclic) : JNConj := by
  intro N hN σ τ τ' μ hμ hk
  suffices hc : IsConjModel (σ : ℂ →+* ℂ) (pp (scaleH N τ)) (pp (scaleH N τ')) μ by
    rw [jInv_eq_jL, jInv_eq_jL]; exact hc.jL
  obtain ⟨hV2, hV3⟩ := hV N hN τ
  obtain ⟨hV2', hV3'⟩ := hV N hN τ'
  have hμ0 := hμ.1
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hS : ∀ F F' : ℂ → ℂ, (∀ x x', (σ : ℂ →+* ℂ) x = μ ^ 2 * x' → (σ : ℂ →+* ℂ) (F x) = F' x') →
      (σ : ℂ →+* ℂ) (∑ m ∈ Finset.Ico 1 N, F ((pp τ).weierstrassP ((m : ℂ) / N))) =
        ∑ m ∈ Finset.Ico 1 N, F' ((pp τ').weierstrassP ((m : ℂ) / N)) := by
    intro F F' hF
    rcases Nat.lt_or_ge N 2 with h1 | h2
    · obtain rfl : N = 1 := by omega
      simp
    obtain ⟨k, hk1, hkN, hp, hd⟩ := hk h2
    have hm := conj_multiples hG (σ : ℂ →+* ℂ) hμ hk1 hkN hp hd
    have hcop := coprime_of_multiples hN fun m h1 h2 => (hm m h1 h2).1
    rw [map_sum, ← sum_perm τ' hN hcop F']
    refine Finset.sum_congr rfl fun m hm' => ?_
    rw [Finset.mem_Ico] at hm'
    exact hF _ _ (hm m hm'.1 hm'.2).2.1
  refine ⟨hμ0, ?_, ?_⟩
  · have e := congrArg (σ : ℂ →+* ℂ) hV2
    have hs := hS (fun x => 60 * x ^ 2 - 5 * (pp τ).g₂)
      (fun x' => μ ^ 4 * (60 * x' ^ 2 - 5 * (pp τ').g₂)) (by
        intro x x' hx
        simp only [map_sub, map_mul, map_pow, hx, hμ.2.1, map_ofNat]
        ring)
    beta_reduce at hs
    rw [map_mul, map_pow, map_natCast, map_add, hμ.2.1, hs, ← Finset.mul_sum, ← mul_add,
      ← hV2'] at e
    exact mul_left_cancel₀ (pow_ne_zero 4 hNc) (by rw [e]; ring)
  · have e := congrArg (σ : ℂ →+* ℂ) hV3
    have hs := hS (fun x => 140 * x ^ 3 - 21 * (pp τ).g₂ * x - 14 * (pp τ).g₃)
      (fun x' => μ ^ 6 * (140 * x' ^ 3 - 21 * (pp τ').g₂ * x' - 14 * (pp τ').g₃)) (by
        intro x x' hx
        simp only [map_sub, map_mul, map_pow, hx, hμ.2.1, hμ.2.2, map_ofNat]
        ring)
    beta_reduce at hs
    rw [map_mul, map_pow, map_natCast, map_add, hμ.2.2, hs, ← Finset.mul_sum, ← mul_add,
      ← hV3'] at e
    exact mul_left_cancel₀ (pow_ne_zero 6 hNc) (by rw [e]; ring)

/-- **The split with `JNConj` proved:** `X0ModuliGalois ⇐ WeierstrassGroupLaw ∧ VeluCyclic ∧
RatX0Rep ∧ X0ModuliGaloisNonIsolated`. -/
theorem x0ModuliGalois_of_leaves (hG : WeierstrassGroupLaw) (hV : VeluCyclic) (hR : RatX0Rep)
    (hS : X0ModuliGaloisNonIsolated) : T5Glue.X0ModuliGalois :=
  x0ModuliGalois_of_split hR (jnConj_of_leaves hG hV) hS

end X0Moduli

