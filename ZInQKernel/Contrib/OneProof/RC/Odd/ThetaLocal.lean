import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Operators

/-!
# Lane RC12-odd: the local weights, the sign `α(−1) = 1`, the characters (O.5), and (O.6)

Manuscript (11/5), Appendix F, Proposition `ex:app-theta-form` and its proof (tex 8409–9099).

PROVED here:
* the nilpotent sign at `p ∣ m`: the centralizer of `X₀ = (0 1; 0 0)` has square determinant, so
  `ε_p(g X₀ g⁻¹) = (det g/p)` is well defined; scaling by `u` multiplies it by `(u/p)` via
  `diag(u,1) X₀ diag(u,1)⁻¹ = u X₀` (tex 8536–8549) — `centralizer_X0`, `quadraticChar_det_eq_of_conj`,
  `diag_conj_X0`;
* the residue line at `ℓ₀`: `β² ∈ 𝔽_{ℓ₀}` is a nonsquare for a nonzero trace-zero `β`; two nonsquares
  multiply to a square; `(m/ℓ₀) = 1` forces `(D/ℓ₀) = 1` on extracted indices (tex 8551–8561) —
  `trace_zero_sq_not_square`, `legendre_extracted`;
* the dyadic weight: `e_{ux} = u e_x + (1 − u)/2`; the only idempotents of `ℤ/2^e` are `0, 1`
  (tex 8517–8531) — `dyadic_affine`, `idempotent_zmod_two_pow`;
* `α(−1) = (∏ w_{p^e} χ_{h_*}(p)^e)(∏_{p∣m}(−1/p))(−1/ℓ₀) = 1` from `w(E) = −∏ w_{p^e}`,
  `w(E^{h_*}) = w(E) χ_{h_*}(−N) = +1`, `m ≡ 3 (mod 4)`, `ℓ₀ ≡ 3 (mod 4)` (tex 8579–8592; the map's
  fill F-b: the final factor is `(−1/ℓ₀)`) — `alpha_neg_one`;
* the characters: `(m/d)/χ_{h_*}(d) = (−1/d)` for `h_* = −m` (tex 8916–8920, (O.5)) —
  `psi_div_eta`;
* the recurrence (O.6) from the Brandt identity `H(p²n) + s(−n/p)H(n) + ps²H(n/p²) =
  sχ_{h_*}(p)a_pH(n)` (tex 9076–9093), and the moving step of the neighbour operator by
  self-adjointness `N_ij/w_i = N_ji/w_j` (tex 9067–9075; the map's fill F-a) — `O6_of_brandt`,
  `brandt_adjoint`;
* the nonintegral neighbour: `p | a, c`, `p ∤ b`, `p² | −a² − bc` force `p² | c` (tex 9052–9054) —
  `nilpotent_neighbor`; the integral + nonintegral bookkeeping (tex 9059–9064) — `neighbor_sum`.

The Weil-representation calculus (tex 8623–9037), the Schwartz–Bruhat and holomorphy arguments, and
the supersingular/Hecke compatibility of `P_M` (tex 8462–8494) are ELLIOT (with the cited Weil,
Voight, Jetchev–Kane locators UNVERIFIED); they enter as hypotheses.
-/

namespace ZInQ.Manuscript.RC.Odd

open Matrix

/-! ### The nilpotent sign at `p ∣ m` (tex 8536–8549) -/

/-- `X₀ = (0 1; 0 0)`. -/
def X0 {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- **PROVED (tex 8540–8542).** The centralizer of `X₀` is `{(a b; 0 a)}`; its determinant `a²`
is a square. -/
theorem centralizer_X0 {K : Type*} [CommRing K] (g : Matrix (Fin 2) (Fin 2) K)
    (h : g * X0 = X0 * g) : g 1 0 = 0 ∧ g 0 0 = g 1 1 ∧ g.det = g 0 0 ^ 2 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [X0, mul_apply, Fin.sum_univ_two] at h00 h01 h11
  refine ⟨h11, h01, ?_⟩
  rw [det_fin_two, h11, ← h01]; ring

/-- **PROVED (tex 8542–8545).** `ε_p(g X₀ g⁻¹) = (det g/p)` is well defined: if
`g X₀ g⁻¹ = g' X₀ g'⁻¹`, i.e. `k = g'⁻¹ g` commutes with `X₀`, then `det g` and `det g'` have the same
quadratic character (`det k` is a nonzero square). -/
theorem quadraticChar_det_eq_of_conj {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (g g' : GL (Fin 2) K)
    (hk : ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X0 =
      X0 * ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    quadraticChar K (g : Matrix (Fin 2) (Fin 2) K).det =
      quadraticChar K (g' : Matrix (Fin 2) (Fin 2) K).det := by
  set k : GL (Fin 2) K := g'⁻¹ * g with hkdef
  obtain ⟨-, -, hdet⟩ := centralizer_X0 _ hk
  have hk0 : (k : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0
    have := Matrix.isUnits_det_units k
    rw [hdet, h0, zero_pow two_ne_zero] at this
    exact not_isUnit_zero this
  have hgk : g = g' * k := by rw [hkdef, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hgk, Units.val_mul, det_mul, map_mul, hdet, quadraticChar_sq_one' hk0, mul_one]

/-- **PROVED (tex 8547–8549).** `diag(u,1) X₀ = (u X₀) diag(u,1)`: scaling by `u` is conjugation
by `diag(u,1)`, so it multiplies the nilpotent sign by `(u/p)`. -/
theorem diag_conj_X0 {K : Type*} [CommRing K] (u : K) :
    !![u, 0; 0, 1] * X0 = (u • X0) * !![u, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X0, mul_apply, Fin.sum_univ_two]

/-! ### The residue line at `ℓ₀` (tex 8551–8561) -/

/-- **PROVED (tex 8556–8558).** If `φ` is a field automorphism (Frobenius) and `β ≠ 0` has
`φ β = −β` (nonzero trace zero), with `2 ≠ 0`, then `β²` is fixed by `φ` but is not the square of a
`φ`-fixed element. -/
theorem trace_zero_sq_not_square {L : Type*} [Field L] (φ : L ≃+* L) (h2 : (2 : L) ≠ 0)
    {β : L} (hβ : β ≠ 0) (hφ : φ β = -β) :
    φ (β ^ 2) = β ^ 2 ∧ ¬ ∃ a, φ a = a ∧ a ^ 2 = β ^ 2 := by
  refine ⟨by rw [map_pow, hφ, neg_sq], ?_⟩
  rintro ⟨a, ha, hsq⟩
  have : (β - a) * (β + a) = 0 := by ring_nf; rw [hsq]; ring
  rcases mul_eq_zero.mp this with h | h
  · have hb : β = a := sub_eq_zero.mp h
    have : β = -β := by rw [← hφ, hb, ha]
    apply hβ
    have : (2 : L) * β = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2
  · have hb : β = -a := eq_neg_of_add_eq_zero_left h
    have : -β = β := by rw [← hφ, hb, map_neg, ha]
    apply hβ
    have : (2 : L) * β = 0 := by linear_combination -this
    exact (mul_eq_zero.mp this).resolve_left h2

/-- **PROVED (tex 8559–8561).** Two nonsquares multiply to a square, and on extracted indices
`Q_B(x) = mD` is a nonzero square mod `ℓ₀`; with `(m/ℓ₀) = 1` this forces `(D/ℓ₀) = 1`. -/
theorem legendre_extracted {ℓ₀ : ℕ} [Fact ℓ₀.Prime] {m D a b : ℤ}
    (ha : legendreSym ℓ₀ a = -1) (hb : legendreSym ℓ₀ b = -1) :
    legendreSym ℓ₀ (a * b) = 1 ∧ (legendreSym ℓ₀ (m * D) = 1 → legendreSym ℓ₀ m = 1 →
      legendreSym ℓ₀ D = 1) := by
  refine ⟨by rw [legendreSym.mul, ha, hb]; norm_num, fun h hm => ?_⟩
  rwa [legendreSym.mul, hm, one_mul] at h

/-! ### The dyadic weight (tex 8517–8531) -/

/-- **PROVED (tex 8527).** `e_{ux} = u e_x + (1 − u)/2` for `e_x = (1 + x)/2`. -/
theorem dyadic_affine {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (u x : K) :
    (1 + u * x) / 2 = u * ((1 + x) / 2) + (1 - u) / 2 := by
  field_simp; ring

/-- **PROVED (tex 8523–8524).** The only idempotents of `ℤ/2^e` are `0` and `1`. -/
theorem idempotent_zmod_two_pow (e : ℕ) (x : ZMod (2 ^ e)) (hx : x * x = x) : x = 0 ∨ x = 1 := by
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have hv : (2 ^ e : ℕ) ∣ x.val * x.val - x.val := by
    have : ((x.val * x.val - x.val : ℕ) : ZMod (2 ^ e)) = 0 := by
      rw [Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul, ZMod.natCast_zmod_val, hx, sub_self]
    exact (CharP.cast_eq_zero_iff (ZMod (2 ^ e)) (2 ^ e) _).mp this
  have hlt := ZMod.val_lt x
  rcases Nat.even_or_odd x.val with hev | hod
  · -- `x.val − 1` is odd, hence coprime to `2^e`
    left
    rcases Nat.eq_zero_or_pos x.val with h0 | hpos
    · exact (ZMod.val_eq_zero x).mp h0
    · have hc : Nat.Coprime (2 ^ e) (x.val - 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        obtain ⟨k, hk⟩ := hev
        exact ⟨k - 1, by omega⟩
      have hfac : x.val * x.val - x.val = (x.val - 1) * x.val := by
        rw [Nat.sub_mul, one_mul]
      rw [hfac] at hv
      have := hc.dvd_of_dvd_mul_left hv
      have : x.val = 0 := Nat.eq_zero_of_dvd_of_lt this hlt
      exact (ZMod.val_eq_zero x).mp this
  · right
    have hc : Nat.Coprime (2 ^ e) x.val :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hod)
    have hfac : x.val * x.val - x.val = x.val * (x.val - 1) := by
      rw [Nat.mul_sub, mul_one]
    rw [hfac] at hv
    have h1 := hc.dvd_of_dvd_mul_left hv
    have hpos : 1 ≤ x.val := hod.pos
    have : x.val - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    have hv1 : x.val = 1 := by omega
    rw [← ZMod.natCast_zmod_val x, hv1, Nat.cast_one]

/-! ### The sign `α(−1) = 1` (tex 8579–8592) -/

/-- **PROVED (tex 8579–8592).** Write `A = ∏_{p^e‖N} w_{p^e} χ_{h_*}(p)^e`, `χ_{h_*}(N) =
∏ χ_{h_*}(p)^e`. From `w(E) = −∏ w_{p^e}` (Atkin–Lehner, GLUE), the twist formula
`w(E^{h_*}) = w(E) χ_{h_*}(−N)` with `(h_*, N) = 1` (GLUE), `χ_{h_*}(−1) = −1` (`h_* < 0`) and
`w(E^{h_*}) = +1` (from `L(E^{h_*},1) ≠ 0`): `A = 1`. With `(−1/m) = −1` (`m ≡ 3 mod 4`) and
`(−1/ℓ₀) = −1` (`ℓ₀ ≡ 3 mod 4`): `α(−1) = A · (−1/m) · (−1/ℓ₀) = 1`. -/
theorem alpha_neg_one {ι : Type*} (P : Finset ι) (w χ : ι → ℤ) (e : ι → ℕ)
    (wE wEt χm1 : ℤ) (hwE : wE = -∏ i ∈ P, w i)
    (htw : wEt = wE * χm1 * ∏ i ∈ P, χ i ^ e i) (hχm1 : χm1 = -1) (hwEt : wEt = 1)
    {m ℓ₀ : ℕ} [Fact ℓ₀.Prime] (hm : m % 4 = 3) (hℓ₀ : ℓ₀ % 4 = 3) :
    (∏ i ∈ P, w i * χ i ^ e i) = 1 ∧
      (∏ i ∈ P, w i * χ i ^ e i) * jacobiSym (-1) m * legendreSym ℓ₀ (-1) = 1 := by
  have hA : (∏ i ∈ P, w i * χ i ^ e i) = 1 := by
    rw [Finset.prod_mul_distrib]
    rw [hwEt, hwE, hχm1] at htw
    linarith
  refine ⟨hA, ?_⟩
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  rw [hA, jacobiSym.at_neg_one hmodd, ZMod.χ₄_nat_three_mod_four hm,
    legendreSym.at_neg_one (by omega : ℓ₀ ≠ 2), ZMod.χ₄_nat_three_mod_four hℓ₀]
  norm_num

/-! ### The characters (O.5) (tex 8916–8920) -/

/-- **PROVED (tex 8916–8920).** For odd `d > 0`, `h_* = −m`: `(m/d) = (−1/d) (h_*/d)`, i.e.
`ψ/η = (η_B(d)(m/d))/(η_B(d)χ_{h_*}(d)) = (−1/d) = χ_{−4}(d)` (Jacobi symbols for odd `d`). -/
theorem psi_div_eta (m : ℤ) (d : ℕ) :
    jacobiSym m d = jacobiSym (-1) d * jacobiSym (-m) d := by
  have h1 : jacobiSym (-1) d * jacobiSym (-1) d = 1 := by
    rw [← jacobiSym.mul_left]; norm_num
  rw [show -m = (-1) * m by ring, jacobiSym.mul_left, ← mul_assoc, h1, one_mul]

/-! ### The recurrence (O.6) (tex 9039–9093) -/

/-- **PROVED (tex 9052–9054).** For `y = (a b; c −a)` with `p | a, c`, `p ∤ b` and
`p² | −a² − bc`: `p² | c`. -/
theorem nilpotent_neighbor {p : ℕ} (hp : p.Prime) {a b c : ℤ} (ha : (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) (h : (p : ℤ) ^ 2 ∣ -a ^ 2 - b * c) : (p : ℤ) ^ 2 ∣ c := by
  have ha2 : (p : ℤ) ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd ha 2
  have hbc : (p : ℤ) ^ 2 ∣ b * c := by
    have := dvd_add h ha2
    have e : -a ^ 2 - b * c + a ^ 2 = -(b * c) := by ring
    rw [e] at this
    exact dvd_neg.mp this
  have hcop : IsCoprime ((p : ℤ) ^ 2) b :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hb)
  exact hcop.dvd_of_dvd_mul_left hbc

/-- **PROVED (tex 9059–9064).** Primitive nonintegral part `s⁻¹H(p²n) − H(n)` plus integral part
`(1 + (−n/p))H(n) + psH(n/p²)` is `s⁻¹H(p²n) + (−n/p)H(n) + psH(n/p²)`. -/
theorem neighbor_sum {K : Type*} [CommRing K] (sinv s Hp2n Hn Hnp2 leg pK : K) :
    (sinv * Hp2n - Hn) + ((1 + leg) * Hn + pK * s * Hnp2) =
      sinv * Hp2n + leg * Hn + pK * s * Hnp2 := by ring

/-- **PROVED (tex 9067–9075; fill F-a of the App F check).** Moving the neighbour operator onto
`P_M` by self-adjointness: if `N_ij / w_i = N_ji / w_j`, then
`∑_i (P_i χ_i / w_i) ∑_j N_ij θ_j = ∑_j θ_j (1/w_j) ∑_i N_ji P_i χ_i`. -/
theorem brandt_adjoint {K : Type*} [Field K] {ι : Type*} [Fintype ι] (N : ι → ι → K)
    (w P χ θ : ι → K) (hN : ∀ i j, N i j / w i = N j i / w j) :
    ∑ i, (P i * χ i / w i) * ∑ j, N i j * θ j = ∑ j, θ j * (1 / w j) * ∑ i, N j i * (P i * χ i) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hN i j
  calc P i * χ i / w i * (N i j * θ j) = (N i j / w i) * (P i * χ i) * θ j := by ring
    _ = (N j i / w j) * (P i * χ i) * θ j := by rw [this]
    _ = θ j * (1 / w j) * (N j i * (P i * χ i)) := by ring

variable {R : Type*} [CommRing R]

/-- **PROVED ((O.6), tex 9076–9093).** From the Brandt identity
`H(p²n) + s(−n/p)H(n) + ps²H(n/p²) = s χ_{h_*}(p) a_p H(n)` at every index (`p ∤ m`), with
`χ_{h_*}(p)² = 1`, the extracted coefficients `a(n) = H(mn)` satisfy
`a(p²n) = {η(p)a_p − ψ(p)(−n/p)} a(n) − p η(p)² a(n/p²)` with `η(p) = sχ_{h_*}(p)`,
`ψ(p) = s(m/p)`. In the notation of `RecAt`: `RecAt p (s χ) ε a_p a` whenever `(m/p) = ε χ`. -/
theorem O6_of_brandt {p : ℕ} [hp : Fact p.Prime] (H : ℕ → R) {m : ℕ} (hpm : ¬ p ∣ m)
    (s χp : R) (ap ε : ℤ) (hχ2 : χp ^ 2 = 1) (hε : ((legendreSym p m : ℤ) : R) = (ε : R) * χp)
    (hH : ∀ n : ℕ, H (p ^ 2 * n) + s * (legendreSym p (-(n : ℤ)) : R) * H n +
      (p : R) * s ^ 2 * divCoeff H (p ^ 2) n = s * χp * (ap : R) * H n) :
    RecAt p (s * χp) ε ap (fun n => H (m * n)) := by
  intro n
  have h := hH (m * n)
  have hcop : Nat.Coprime (p ^ 2) m :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
  rw [divCoeff_mul_coprime H hcop] at h
  have hleg : legendreSym p (-((m * n : ℕ) : ℤ)) = legendreSym p m * legendreSym p (-(n : ℤ)) := by
    rw [← legendreSym.mul]; push_cast; ring_nf
  rw [hleg] at h
  simp only [show p ^ 2 * (m * n) = m * (p ^ 2 * n) by ring] at h
  have hη2 : (s * χp) ^ 2 = s ^ 2 := by rw [mul_pow, hχ2, mul_one]
  rw [hη2]
  push_cast at h hε ⊢
  rw [hε] at h
  have : H (m * (p ^ 2 * n)) = s * χp * (ap : R) * H (m * n) -
      s * ((ε : R) * χp * (legendreSym p (-(n : ℤ)) : R)) * H (m * n) -
      (p : R) * s ^ 2 * divCoeff (fun k => H (m * k)) (p ^ 2) n := by
    linear_combination h
  rw [this]
  have hχ2' : χp * χp = 1 := by rw [← pow_two]; exact hχ2
  linear_combination (-(s * (ε : R) * (legendreSym p (-(n : ℤ)) : R) * H (m * n))) * hχ2' +
    s * (ε : R) * (legendreSym p (-(n : ℤ)) : R) * H (m * n) * hχ2'

end ZInQ.Manuscript.RC.Odd
