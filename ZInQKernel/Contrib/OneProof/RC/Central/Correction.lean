import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Central.EulerFactors

/-!
# Lane RC15 (central): the universal integral correction `η` and the corrected coordinate

The algebra of the second half of Lemma `ex:arith-common-coordinate` (11/5 manuscript,
`diophantine_zq.tex`, lines 4142–4317; restated in Appendix G, lines 10876–10885): from the
single-prime support identity (4.7) `l_q u_rel = e_q² ε_q u_prim` to
`ũ_x = ε_x u_{prim,x}` with `ε_x ∈ Λ^×`, for the one universal correction
`η = ∏_{q ∈ Q} (1 + v_q (1 + g_q)) ∈ 𝒪[G]` and `ũ = η u_rel`.

Every declaration in this file is `PROVED`; the cohomological input (4.7) itself enters as a
hypothesis (its statement, with tex lines, is `CommonCoordinate47` in `Statements.lean`).

* `correctionFactor`, `eta`: `1 + v_q(1 + g_q)` and their product over `Q` (tex 4219–4222,
  10878).
* `map_correctionFactor_of_inactive`, `map_correctionFactor_of_active`,
  `map_eta` (tex 4220–4221): at a character `x` the factor is `x(l_q/e_q²) = 1 + 2x(v_q)` where
  `x(g_q) = 1` (unused prime) and `1` where `x(g_q) = −1` (active prime).
* `single_prime_47` (tex 4166–4193): (4.7) at one prime from the support triangle and
  `δ_q = q⁴ l_q`.
* `prod_relax` (ELLIOT gap filled, see the docstring): iterating (4.7) one unused prime at a time
  gives `(∏ l_q) u_rel = (∏ e_q² ε_q) u_prim` over all unused primes of a character.
* `corrected_eq` (tex 4222–4226): `ũ_x = η_x u_{rel,x} = (∏_{q unused} ε_q) u_{prim,x}`.
* `correction_lift_independent`, `ratio_agree_mod` (tex 4256–4271): the correction does not depend
  on the choice of Frobenius lift `z_q ↦ g_q z_q`, in `R = 𝒪[G]` before evaluation.
* `central_transfer`, `padicValuation_central_transfer`,
  `valuation_constantCoeff_of_isUnit` (tex 4155–4158, 4227–4231): a `Λ`-unit multiplier preserves
  the central value's vanishing and its two-adic valuation; only the product is specialized.
-/

namespace ZInQ.Manuscript.RC.Central

open scoped BigOperators

section Correction

variable {R : Type*} [CommRing R]

/-- The correction factor `1 + v_q (1 + g_q)` at `q ∈ Q` (tex 4220), with `g_q ∈ G` the inertia
generator of the universal quadratic character at `q`. -/
def correctionFactor (v g : R) : R := 1 + v * (1 + g)

/-- **The universal correction** `η = ∏_{q ∈ Q} (1 + v_q (1 + g_q)) ∈ 𝒪[G]` (tex 4219–4222,
10878): a finite product of integral elements, with no division by the group order. -/
def eta {ι : Type*} (Q : Finset ι) (v g : ι → R) : R :=
  ∏ q ∈ Q, correctionFactor (v q) (g q)

variable {S : Type*} [CommRing S]

/-- At a character with `x(g_q) = 1` (the constituent is unramified at `q`: an unused prime),
the factor evaluates to `1 + 2 x(v_q)`, i.e. to `x(l_q / e_q²)` (tex 4220–4221). PROVED. -/
theorem map_correctionFactor_of_inactive (x : R →+* S) {v g : R} (hg : x g = 1) :
    x (correctionFactor v g) = 1 + 2 * x v := by
  simp only [correctionFactor, map_add, map_mul, map_one, hg]; ring

/-- At a character with `x(g_q) = −1` (an active prime) the factor evaluates to `1`
(tex 4220–4221). PROVED. -/
theorem map_correctionFactor_of_active (x : R →+* S) {v g : R} (hg : x g = -1) :
    x (correctionFactor v g) = 1 := by
  simp only [correctionFactor, map_add, map_mul, map_one, hg]; ring

/-- **`η` selects the unused primes** (tex 4220–4222): if every `x(g_q)` is `±1`, then
`x(η) = ∏_{q ∈ Q, x(g_q) = 1} (1 + 2 x(v_q))`. PROVED. -/
theorem map_eta {ι : Type*} [DecidableEq ι] (x : R →+* S) (Q : Finset ι) (v g : ι → R)
    [DecidablePred fun q => x (g q) = 1]
    (hsign : ∀ q ∈ Q, x (g q) = 1 ∨ x (g q) = -1) :
    x (eta Q v g) = ∏ q ∈ Q with x (g q) = 1, (1 + 2 * x (v q)) := by
  rw [eta, map_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun q hq => ?_
  split_ifs with h
  · exact map_correctionFactor_of_inactive x h
  · rcases hsign q hq with h1 | h1
    · exact absurd h1 h
    · exact map_correctionFactor_of_active x h1

/-- **(4.7) at one unused prime from the support triangle** (tex 4166–4192). If the support
triangle gives `δ_q u_rel = e_q² ε' u_prim` (the class and the paired functional each contribute
one `e_q`, `λ_R ∘ i = e_q λ_P`; ELLIOT, tex 4166–4180, with Nekovář 6.4.1–6.4.3) and the two
quotient determinants are `δ_q = q⁴ l_q` (`quotientDet_eq`), then `l_q u_rel = e_q² ε_q u_prim`
with `ε_q = ε' q⁻⁴`, a unit when `ε'` is (tex 4189–4193: "`q^{-4}` is one also"). PROVED. -/
theorem single_prime_47 {K : Type*} [CommRing K] {urel uprim e δ l q qi ε' : K}
    (hq : q * qi = 1) (hδ : δ = q ^ 4 * l) (htri : δ * urel = e ^ 2 * ε' * uprim) :
    l * urel = e ^ 2 * (ε' * qi ^ 4) * uprim := by
  have h1 : l * urel = qi ^ 4 * (δ * urel) := by
    rw [hδ]; linear_combination (-(l * urel) * (q * qi + 1) * (q ^ 2 * qi ^ 2 + 1)) * hq
  rw [h1, htri]; ring

/-- **Iterating (4.7) over the unused primes of one character.** ELLIOT (gap filled here):
the text states (4.7) at one unused prime (tex 4185–4188) and then multiplies the correction
factors over `Q` (tex 4222, 4289–4291); the multi-prime identity is obtained by relaxing the
unused primes one at a time. Here `u T` is the coordinate relaxed at the unused primes in `T`
and primitive at the others (`u ∅ = u_prim`, `u U = u_rel`), and `hstep` is (4.7) at `q ∉ T`:
`l_q u(T ∪ {q}) = e_q² ε_q u(T)`. Then `(∏_{q ∈ U} l_q) u_rel = (∏_{q ∈ U} e_q² ε_q) u_prim`.
PROVED. -/
theorem prod_relax {ι K : Type*} [DecidableEq ι] [CommRing K] (U : Finset ι)
    (l e ε : ι → K) (u : Finset ι → K)
    (hstep : ∀ T ⊆ U, ∀ q ∈ U, q ∉ T → l q * u (insert q T) = e q ^ 2 * ε q * u T) :
    (∏ q ∈ U, l q) * u U = (∏ q ∈ U, e q ^ 2 * ε q) * u ∅ := by
  have key : ∀ T ⊆ U, (∏ q ∈ T, l q) * u T = (∏ q ∈ T, e q ^ 2 * ε q) * u ∅ := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert a T haT ih =>
      intro hT
      have hTU : T ⊆ U := (Finset.subset_insert a T).trans hT
      have haU : a ∈ U := hT (Finset.mem_insert_self a T)
      rw [Finset.prod_insert haT, Finset.prod_insert haT]
      calc l a * (∏ q ∈ T, l q) * u (insert a T)
          = (∏ q ∈ T, l q) * (l a * u (insert a T)) := by ring
        _ = (∏ q ∈ T, l q) * (e a ^ 2 * ε a * u T) := by rw [hstep T hTU a haU haT]
        _ = e a ^ 2 * ε a * ((∏ q ∈ T, l q) * u T) := by ring
        _ = e a ^ 2 * ε a * ((∏ q ∈ T, e q ^ 2 * ε q) * u ∅) := by rw [ih hTU]
        _ = e a ^ 2 * ε a * (∏ q ∈ T, e q ^ 2 * ε q) * u ∅ := by ring
  exact key U subset_rfl

/-- **`ũ_x = ε_x u_{prim,x}`** (tex 4222–4226, 10882–10885): at a character `x : R → K` with
`x(g_q) = ±1`, let `U` be its unused primes (`x(g_q) = 1`). If `x(l_q) x(e_q)^{-2} = 1 + 2x(v_q)`
(the evaluated form of `l_q/e_q² = 1 + 2v_q`, `quotientFactor_mul_inv_sq`) and the multi-prime
(4.7) holds at `x`, then `x(η) u_{rel,x} = (∏_{q ∈ U} ε_q) u_{prim,x}`: the product `ũ_x` is the
primitive coordinate times the product of the `ε_q`. PROVED. -/
theorem corrected_eq {ι K : Type*} [DecidableEq ι] [CommRing K] (x : R →+* K) (Q : Finset ι)
    (v g l e ei : ι → R) (ε : ι → K) (urel uprim : K)
    [DecidablePred fun q => x (g q) = 1]
    (hsign : ∀ q ∈ Q, x (g q) = 1 ∨ x (g q) = -1)
    (hratio : ∀ q ∈ Q, x (l q) * x (ei q) ^ 2 = 1 + 2 * x (v q))
    (hinv : ∀ q ∈ Q, x (e q) * x (ei q) = 1)
    (h47 : (∏ q ∈ Q with x (g q) = 1, x (l q)) * urel =
      (∏ q ∈ Q with x (g q) = 1, x (e q) ^ 2 * ε q) * uprim) :
    x (eta Q v g) * urel = (∏ q ∈ Q with x (g q) = 1, ε q) * uprim := by
  rw [map_eta x Q v g hsign]
  set U := Q.filter fun q => x (g q) = 1
  have hU : ∀ q ∈ U, q ∈ Q := fun q hq => (Finset.mem_filter.mp hq).1
  have h1 : (∏ q ∈ U, (1 + 2 * x (v q))) = (∏ q ∈ U, x (ei q) ^ 2) * ∏ q ∈ U, x (l q) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q hq => by rw [← hratio q (hU q hq)]; ring
  have h2 : (∏ q ∈ U, x (ei q) ^ 2) * (∏ q ∈ U, x (e q) ^ 2 * ε q) = ∏ q ∈ U, ε q := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have := hinv q (hU q hq)
    linear_combination (ε q * (x (e q) * x (ei q) + 1)) * this
  rw [h1, mul_assoc, h47, ← mul_assoc, h2]

/-- **The correction is independent of the Frobenius lift** (tex 4262–4271): in a ring without
two-torsion, if `g² = 1`, `r = 1 + 2v`, `r' = 1 + 2v'` and `r' − r ∈ (g − 1)R` (the two ratios
agree in `R/(g − 1)`), then `(1 + g)(v' − v) = 0` and the correction factors agree. PROVED. -/
theorem correction_lift_independent (h2 : ∀ y : R, 2 * y = 0 → y = 0) {g v v' r r' : R}
    (hg : g ^ 2 = 1) (hr : r = 1 + 2 * v) (hr' : r' = 1 + 2 * v')
    (hagree : r' - r ∈ Ideal.span {g - 1}) :
    (1 + g) * (v' - v) = 0 ∧ correctionFactor v' g = correctionFactor v g := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hagree
  have h0 : (1 + g) * (r' - r) = 0 := by
    rw [← hy]; linear_combination y * hg
  have hv : (1 + g) * (v' - v) = 0 := by
    apply h2
    rw [hr, hr'] at h0
    linear_combination h0
  refine ⟨hv, ?_⟩
  unfold correctionFactor
  linear_combination hv

/-- **The two ratios agree modulo `g_q − 1`** (tex 4262–4264): changing the Frobenius lift
replaces `z_q` by `g_q z_q` (tex 4246–4251). If the two choices `(z, zi)` and `(z', zi')` agree
modulo `g − 1`, the point factors, quotient factors and the ratios `r = l ei²`, `r' = l' ei'²`
(with `e ei = 1`, `e' ei' = 1`) agree modulo `g − 1`. PROVED. -/
theorem ratio_agree_mod {F : Matrix (Fin 2) (Fin 2) R} {qi a z zi z' zi' ei ei' g : R}
    (hz : z' - z ∈ Ideal.span {g - 1}) (hzi : zi' - zi ∈ Ideal.span {g - 1})
    (he : pointFactor a z zi * ei = 1) (he' : pointFactor a z' zi' * ei' = 1) :
    quotientFactor F qi z' zi' * ei' ^ 2 - quotientFactor F qi z zi * ei ^ 2 ∈
      Ideal.span {g - 1} := by
  set I := Ideal.span {g - 1}
  rw [← Ideal.Quotient.eq]
  have hz' : Ideal.Quotient.mk I z' = Ideal.Quotient.mk I z := Ideal.Quotient.eq.mpr hz
  have hzi' : Ideal.Quotient.mk I zi' = Ideal.Quotient.mk I zi := Ideal.Quotient.eq.mpr hzi
  have hl : Ideal.Quotient.mk I (quotientFactor F qi z' zi') =
      Ideal.Quotient.mk I (quotientFactor F qi z zi) := by
    unfold quotientFactor
    rw [det_one_sub_smul, det_one_sub_smul, det_one_sub_smul, det_one_sub_smul]
    simp only [map_mul, map_sub, map_add, map_one, map_pow, hz', hzi']
  have hpe : Ideal.Quotient.mk I (pointFactor a z' zi') =
      Ideal.Quotient.mk I (pointFactor a z zi) := by
    unfold pointFactor; simp only [map_sub, hz', hzi']
  have hei : Ideal.Quotient.mk I ei' = Ideal.Quotient.mk I ei := by
    have h1 := congrArg (Ideal.Quotient.mk I) he
    have h2 := congrArg (Ideal.Quotient.mk I) he'
    rw [map_mul, map_one] at h1 h2
    rw [hpe] at h2
    calc Ideal.Quotient.mk I ei'
        = (Ideal.Quotient.mk I (pointFactor a z zi) * Ideal.Quotient.mk I ei) *
            Ideal.Quotient.mk I ei' := by rw [h1, one_mul]
      _ = (Ideal.Quotient.mk I (pointFactor a z zi) * Ideal.Quotient.mk I ei') *
            Ideal.Quotient.mk I ei := by ring
      _ = Ideal.Quotient.mk I ei := by rw [h2, one_mul]
  simp only [map_mul, map_pow, hl, hei]

end Correction

/-! ### Central transfer through a `Λ`-unit -/

section Transfer

/-- **A unit multiplier preserves the central value's vanishing** (tex 4155–4158, 4227–4231):
if `ũ = ε u` with `ε` a unit and `ev` the specialization at `t = 0` to a field, then
`ev ũ = ev ε · ev u` with `ev ε ≠ 0`, so `ev ũ = 0 ↔ ev u = 0`. Only the product is
specialized; no claim is made about `η_x` alone, which may have a pole. PROVED. -/
theorem central_transfer {A k : Type*} [CommRing A] [Field k] (ev : A →+* k) {ε u ũ : A}
    (hε : IsUnit ε) (h : ũ = ε * u) :
    ev ũ = ev ε * ev u ∧ ev ε ≠ 0 ∧ (ev ũ = 0 ↔ ev u = 0) := by
  have hne : ev ε ≠ 0 := (hε.map ev).ne_zero
  refine ⟨by rw [h, map_mul], hne, ?_⟩
  rw [h, map_mul, mul_eq_zero]
  exact ⟨fun h0 => h0.resolve_left hne, fun h0 => Or.inr h0⟩

/-- **A unit multiplier preserves the central two-adic valuation** (tex 4155–4158, 4227–4229):
with values in `ℚ₂`, if `v₂(ev ε) = 0` then `v₂(ev ũ) = v₂(ev u)` (both sides are `0` when
`ev u = 0`, by the convention `v₂ 0 = 0` of `Padic.valuation`). PROVED. -/
theorem padicValuation_central_transfer {A : Type*} [CommRing A] (ev : A →+* ℚ_[2])
    {ε u ũ : A} (hε : IsUnit ε) (hv : (ev ε).valuation = 0) (h : ũ = ε * u) :
    (ev ũ).valuation = (ev u).valuation := by
  obtain ⟨hmul, hne, -⟩ := central_transfer ev hε h
  rw [hmul]
  rcases eq_or_ne (ev u) 0 with h0 | h0
  · rw [h0, mul_zero]
  · rw [Padic.valuation_mul hne h0, hv, zero_add]

/-- **`Λ`-units specialize to two-adic units** (tex 4192–4193: "their limits and inverse limits
are `Λ`-units"): for `ε ∈ ℤ₂[[t]]^×`, the constant coefficient `ε(0) ∈ ℤ₂` is a unit and has
valuation `0` in `ℚ₂`. PROVED. -/
theorem valuation_constantCoeff_of_isUnit {ε : PowerSeries ℤ_[2]} (hε : IsUnit ε) :
    ((PowerSeries.constantCoeff ε : ℤ_[2]) : ℚ_[2]).valuation = 0 := by
  have hu : IsUnit (PowerSeries.constantCoeff ε) := hε.map _
  obtain ⟨w, hw⟩ := hu
  have hw0 : (w : ℤ_[2]) ≠ 0 := w.ne_zero
  have hwi0 : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ≠ 0 := (w⁻¹).ne_zero
  have h1 := PadicInt.valuation_mul hw0 hwi0
  rw [Units.mul_inv, PadicInt.valuation_one] at h1
  rw [PadicInt.valuation_coe, ← hw]
  have : (w : ℤ_[2]).valuation = 0 := by omega
  rw [this]; rfl

end Transfer

end ZInQ.Manuscript.RC.Central
