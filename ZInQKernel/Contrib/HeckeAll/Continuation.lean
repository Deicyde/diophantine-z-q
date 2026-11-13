import ZInQKernel.Contrib.HeckeFE.Basic
import ZInQKernel.Contrib.HeckeAll.LocalCd
import ZInQKernel.Contrib.HeckeAll.Iso

/-!
# `HeckeContinuation` for every `d ≠ 0`, from Gauss's point count

`ZInQ.Literature.HeckeContinuation` asks for an entire continuation of Mathlib's `L(C_d, s)`
for every `d ≠ 0`. The route:

1. **Non-squarefree `d`** (`Iso.lean`): `C_{m² d} ≅ C_d` over `ℚ` and Mathlib's L-function is an
   isomorphism invariant (`LSeries_cd_sq_mul`).
2. **Squarefree `d`, any parity** (`LocalCd.lean`): `L(C_d, s) = Σ cdCoeff d n · n^{−s}`
   (`LSeries_cd_eq'`); at `p = 2` for even `d` the model is minimal by a `c₄` argument.
3. **Quadratic twist** (this file): `cdCoeff d n = (d/n) · cdCoeff 1 n` for every squarefree `d`
   and `n ≠ 0`, with the Jacobi symbol `(d/n)` (`cdCoeff_twist`). At `p ∤ 2d` this is
   `a_p(C_d) = (d/p) a_p(C_1)` (the substitution `x ↦ dx`); at `p ∣ d` both sides vanish; at
   `p = 2` both sides vanish because `a_{2^k}(C_1) = 0`.
4. **Deuring for `d = 1`** (`Contrib/HeckeFE/Basic.lean`, from `GaussPointCount`): `cdCoeff 1 n =
   ¼ Σ_{N α = n} u(α) α`.
5. So `L(C_d, s) = Σ_α c(α mod 4d) α N(α)^{−s}` with `c(α) = ¼ (d/N α) u(α)`, a function on
   `(ℤ/4d)²` because `N α mod 4d` depends only on `α mod 4d` and `J(d | ·)` is periodic mod `4d` on
   odd arguments (`twChar_intCast`); `twistedL_continuation` gives the entire continuation.
-/

namespace ZInQ.Contrib.HeckeAll

open ZInQ.Literature ZInQ.Contrib.HeckeFE

/-! ### The Jacobi symbol `J(d | ·)` is completely multiplicative -/

theorem jacobiSym_mul_right_all (a : ℤ) (x y : ℕ) (h : Nat.Coprime x y) :
    jacobiSym a (x * y) = jacobiSym a x * jacobiSym a y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.coprime_zero_left] at h; subst h; simp [jacobiSym.one_right]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [Nat.coprime_zero_right] at h; subst h; simp [jacobiSym.one_right]
  exact jacobiSym.mul_right' a hx.ne' hy.ne'

theorem jacobiSym_factorization (a : ℤ) {n : ℕ} (hn : n ≠ 0) :
    jacobiSym a n = n.factorization.prod fun p k => jacobiSym a p ^ k := by
  rw [Nat.multiplicative_factorization (fun m => jacobiSym a m)
    (jacobiSym_mul_right_all a) (jacobiSym.one_right a) hn]
  exact Finsupp.prod_congr fun p _ => jacobiSym.pow_right a p _

/-! ### Euler factors of the twist -/

/-- The coefficient of `T ^ k` in `1 / cdEulerPoly d p`. -/
noncomputable def eulerCoeff (d p k : ℕ) : ℤ :=
  PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1)

theorem eulerCoeff_cast (d p k : ℕ) : ((eulerCoeff d p k : ℤ) : ℂ) =
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (((cdEulerPoly d p).map (Int.castRingHom ℂ) : Polynomial ℂ) : PowerSeries ℂ) 1) := by
  have hc0 : PowerSeries.constantCoeff ((cdEulerPoly d p : Polynomial ℤ) : PowerSeries ℤ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      cdEulerPoly_coeff_zero]
  rw [Polynomial.polynomial_map_coe, ← map_invOfUnit_one _ _ hc0, PowerSeries.coeff_map]
  rfl

theorem eulerCoeff_of_dvd {d p : ℕ} (h : p ∣ 2 * d) (k : ℕ) :
    eulerCoeff d p k = if k = 0 then 1 else 0 := by
  have hpoly : cdEulerPoly d p = 1 := by unfold cdEulerPoly; simp [h]
  have hinv : PowerSeries.invOfUnit ((cdEulerPoly d p : Polynomial ℤ) : PowerSeries ℤ) 1 = 1 := by
    have h1 : ((cdEulerPoly d p : Polynomial ℤ) : PowerSeries ℤ) = 1 := by
      rw [hpoly, Polynomial.coe_one]
    have := PowerSeries.mul_invOfUnit ((cdEulerPoly d p : Polynomial ℤ) : PowerSeries ℤ) 1
      (by rw [h1]; simp)
    rw [h1, one_mul] at this
    rw [h1]; exact this
  unfold eulerCoeff
  rw [hinv, PowerSeries.coeff_one]

theorem eulerCoeff_zero (d p : ℕ) : eulerCoeff d p 0 = 1 := by
  unfold eulerCoeff
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
  simp

/-- The local twist identity `a_p(C_d) = (d/p) a_p(C_1)` for `p ∤ 2d`. -/
theorem cdEulerPoly_twist {d p : ℕ} [hpp : Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    ∃ b : ℤ, (cdEulerPoly d p).map (Int.castRingHom ℂ) =
      1 - Polynomial.C ((jacobiSym d p : ℂ) * b) * Polynomial.X +
        Polynomial.C (p : ℂ) * Polynomial.X ^ 2 ∧
      (cdEulerPoly 1 p).map (Int.castRingHom ℂ) =
      1 - Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (p : ℂ) * Polynomial.X ^ 2 := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hp (dvd_mul_right 2 d)
  have hp1 : ¬ p ∣ 2 * 1 := by
    intro h
    rcases (Nat.Prime.dvd_mul hpp.out).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_two).mp h)
    · exact hpp.out.one_lt.ne' (Nat.dvd_one.mp h)
  have hpd : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hp (h.trans (dvd_mul_left d 2))
  set S := ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) with hS
  have hleg : (quadraticChar (ZMod p) d : ℤ) = jacobiSym d p := by
    have := jacobiSym.legendreSym.to_jacobiSym p d
    rw [legendreSym] at this
    push_cast at this
    exact this
  have hcard : ∀ e : ℕ, ¬ p ∣ 2 * e →
      ((p : ℤ) + 1 - Nat.card (cdModel (ZMod p) e).toAffine.Point) =
        -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (e : ZMod p) ^ 2 * x) := by
    intro e he
    rw [cdModel_eq_shortCurve, natCard_point_shortCurve_zmod p he]
    push_cast
    rw [card_cd_affine_eq hp2 e]
    ring
  have ad : ((p : ℤ) + 1 - Nat.card (cdModel (ZMod p) d).toAffine.Point) = jacobiSym d p * -S := by
    rw [hcard d hp, sum_quadraticChar_twist d hpd, hleg]; ring
  have a1 : ((p : ℤ) + 1 - Nat.card (cdModel (ZMod p) 1).toAffine.Point) = -S := by
    rw [hcard 1 hp1]; simp [S]
  refine ⟨-S, ?_, ?_⟩
  · unfold cdEulerPoly
    simp only [hp, ↓reduceIte]
    rw [ad]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
    push_cast; ring
  · unfold cdEulerPoly
    simp only [hp1, ↓reduceIte]
    rw [a1]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
    push_cast; ring

theorem coeff_twist_quadratic (ε b q : ℂ) (hε : ε ^ 2 = 1) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit (((1 - Polynomial.C (ε * b) * Polynomial.X +
      Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1) =
    ε ^ k * PowerSeries.coeff k (PowerSeries.invOfUnit (((1 - Polynomial.C b * Polynomial.X +
      Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1) := by
  obtain ⟨a0, a1, ar⟩ := coeff_inv_quadratic (ε * b) q
  obtain ⟨b0, b1, br⟩ := coeff_inv_quadratic b q
  have key : ∀ k : ℕ, (PowerSeries.coeff k (PowerSeries.invOfUnit (((1 - Polynomial.C (ε * b) *
      Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1) =
    ε ^ k * PowerSeries.coeff k (PowerSeries.invOfUnit (((1 - Polynomial.C b * Polynomial.X +
      Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1)) ∧
      (PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit (((1 - Polynomial.C (ε * b) *
      Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1) =
    ε ^ (k + 1) * PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit (((1 - Polynomial.C b *
      Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1)) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [a0, b0]; ring, by rw [a1, b1]; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, ar, br, ih.1, ih.2]
      linear_combination (q * ε ^ k *
        PowerSeries.coeff k (PowerSeries.invOfUnit (((1 - Polynomial.C b * Polynomial.X +
          Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1)) * hε
  exact (key k).1

theorem jacobiSym_sq_of_not_dvd {d p : ℕ} [hpp : Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    (jacobiSym d p : ℂ) ^ 2 = 1 := by
  have hpd : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hp (h.trans (dvd_mul_left d 2))
  rw [← jacobiSym.legendreSym.to_jacobiSym p d]
  have h := legendreSym.sq_one p (a := (d : ℤ)) (by exact_mod_cast hpd)
  exact_mod_cast h

/-- **The twist identity at prime powers**: `[T^k] 1/cdEulerPoly d p = (d/p)^k [T^k] 1/cdEulerPoly 1 p`. -/
theorem eulerCoeff_twist (d p : ℕ) [hpp : Fact p.Prime] (k : ℕ) :
    ((eulerCoeff d p k : ℤ) : ℂ) = (jacobiSym d p : ℂ) ^ k * ((eulerCoeff 1 p k : ℤ) : ℂ) := by
  by_cases h : p ∣ 2 * d
  · rcases k with _ | k
    · simp [eulerCoeff_zero]
    rw [eulerCoeff_of_dvd h]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Int.cast_zero]
    by_cases hpd : p ∣ d
    · have hj : jacobiSym d p = 0 := by
        rw [← jacobiSym.legendreSym.to_jacobiSym p d, legendreSym.eq_zero_iff]
        exact_mod_cast (ZMod.natCast_eq_zero_iff d p).mpr hpd
      simp [hj]
    · have hp2 : p ∣ 2 := by
        rcases (Nat.Prime.dvd_mul hpp.out).mp h with h | h
        · exact h
        · exact absurd h hpd
      rw [eulerCoeff_of_dvd (show p ∣ 2 * 1 by simpa using hp2)]
      simp
  · obtain ⟨b, hd, h1⟩ := cdEulerPoly_twist (d := d) h
    rw [eulerCoeff_cast, eulerCoeff_cast, hd, h1]
    exact coeff_twist_quadratic _ _ _ (jacobiSym_sq_of_not_dvd h) k

/-- **The quadratic twist**: `cdCoeff d n = (d/n) · cdCoeff 1 n` (a formal identity of the
Euler products `cdEulerPoly`; it is Mathlib's `L(C_d, s)` for squarefree `d`). -/
theorem cdCoeff_twist (d : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ((cdCoeff d n : ℤ) : ℂ) = (jacobiSym d n : ℂ) * ((cdCoeff 1 n : ℤ) : ℂ) := by
  simp only [cdCoeff, hn, ↓reduceIte]
  rw [jacobiSym_factorization _ hn]
  simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)⟩
  exact eulerCoeff_twist d p _

/-! ### The character on `(ℤ/4d)²` -/

/-- `c(α) = ¼ (d / N α) u(α)` on `(ℤ/4d)²` (computed from the least residues). -/
noncomputable def twChar (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : ℂ :=
  (1 / 4) * (jacobiSym d (x.1.val ^ 2 + x.2.val ^ 2) : ℂ) *
    unitOf (((x.1.val : ℤ) : ZMod 4), ((x.2.val : ℤ) : ZMod 4))

theorem unitG_eq_zero_of_two_mul : ∀ a b : ZMod 4, 2 * (a ^ 2 + b ^ 2) = 0 → unitG (a, b) = 0 := by
  decide

theorem twChar_intCast {d : ℕ} [NeZero d] {n : ℕ} {q : ℤ × ℤ} (hq : q ∈ normFiber n) :
    twChar d ((q.1 : ZMod (4 * d)), (q.2 : ZMod (4 * d))) =
      (1 / 4) * (jacobiSym d n : ℂ) * unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) := by
  have hN := mem_normFiber.mp hq
  have h4d : ∀ x : ℤ, ((x : ZMod (4 * d)).val : ℤ) ≡ x [ZMOD (4 * d : ℕ)] := fun x => by
    rw [ZMod.val_intCast]; exact Int.emod_emod_of_dvd x (dvd_refl _)
  have h4 : ∀ x : ℤ, ((x : ZMod (4 * d)).val : ℤ) ≡ x [ZMOD 4] := fun x => by
    have := h4d x; push_cast at this; exact this.of_mul_right d
  unfold twChar
  dsimp only
  rw [(ZMod.intCast_eq_intCast_iff _ _ 4).mpr (h4 q.1),
    (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (h4 q.2)]
  by_cases hu : unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) = 0
  · rw [hu]; ring
  congr 2
  -- `n` is odd
  have hn2 : n % 2 = 1 := by
    by_contra hne
    apply hu
    rw [unitOf_eq_unitG, unitG_eq_zero_of_two_mul]
    · simp
    have hc : ((q.1 : ZMod 4) ^ 2 + (q.2 : ZMod 4) ^ 2) = ((n : ℤ) : ZMod 4) := by
      rw [← hN]; push_cast; ring
    rw [hc]
    have : 2 * n % 4 = 0 := by omega
    have h0 : ((2 * n : ℕ) : ZMod 4) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; omega
    push_cast at h0 ⊢
    exact h0
  -- the residues of the norms agree mod `4d`
  set N' := (q.1 : ZMod (4 * d)).val ^ 2 + (q.2 : ZMod (4 * d)).val ^ 2 with hN'
  have hcast : (N' : ZMod (4 * d)) = (n : ZMod (4 * d)) := by
    rw [hN']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((n : ℤ) : ZMod (4 * d)) = (n : ZMod (4 * d)) := Int.cast_natCast n
    rw [← this, ← hN]; push_cast; ring
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  have hN'2 : N' % 2 = 1 := by
    have h1 : N' % (4 * d) % 2 = N' % 2 := Nat.mod_mod_of_dvd _ ⟨2 * d, by ring⟩
    have h2 : n % (4 * d) % 2 = n % 2 := Nat.mod_mod_of_dvd _ ⟨2 * d, by ring⟩
    rw [← h1, hmod, h2, hn2]
  have hoddN' : Odd N' := Nat.odd_iff.mpr hN'2
  have hoddn : Odd n := Nat.odd_iff.mpr hn2
  have hnat : ((d : ℤ)).natAbs = d := Int.natAbs_natCast d
  rw [jacobiSym.mod_right _ hoddN', jacobiSym.mod_right _ hoddn, hnat, hmod]

/-! ### The continuation -/

/-- **`L(C_d, s)` has an entire continuation for every squarefree `d`**, from `GaussPointCount`. -/
theorem isLContinuation_of_squarefree (h1 : GaussPointCount) {d : ℕ} (hsq : Squarefree d) :
    ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F := by
  have : NeZero d := ⟨hsq.ne_zero⟩
  have : NeZero (4 * d) := ⟨by have := NeZero.ne d; omega⟩
  have hD1 : DeuringCd 1 := deuringCd_of_gaussPointCount (by norm_num) squarefree_one h1
  obtain ⟨G, hG, hGeq⟩ := twistedL_continuation (4 * d) (twChar d)
  refine ⟨G, hG, fun s hs => ?_⟩
  rw [hGeq s hs, LSeries_cd_eq' hsq s]
  refine (LSeries_eq_twistedL (4 * d) (twChar d) _ (fun n hn => ?_) hs).symm
  rw [cdCoeff_twist d hn, hD1 n hn, heckeCoeff, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [twChar_intCast hq, jacobiSym.one_right]
  push_cast
  ring

end ZInQ.Contrib.HeckeAll

namespace ZInQ.Contrib

/-- **Hecke's continuation for every `C_d`, `d ≠ 0`, from Gauss's point count** on
`y² = x³ − x` (`HeckeFE.GaussPointCount`, from the shared copy `Contrib/HeckeFE/Basic.lean`).
-/
theorem heckeContinuation_of_gaussPointCount (h1 : HeckeFE.GaussPointCount) :
    ZInQ.Literature.HeckeContinuation := by
  intro d hd
  obtain ⟨b, a, hab, hsq⟩ := exists_sq_mul_squarefree d
  have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hd hab.symm
  subst hab
  obtain ⟨F, hF, hFeq⟩ := HeckeAll.isLContinuation_of_squarefree h1 hsq
  exact ⟨F, hF, fun s hs => by rw [hFeq s hs, HeckeAll.LSeries_cd_sq_mul a b hsq.ne_zero hb s]⟩

/-- **Both textbook CR₃ Props from Gauss's point count**: `HeckeContinuation` (every `d ≠ 0`, this
file) and `FunctionalEquation5` (bp-hecke-fe, `literature_hecke_fe_of_gaussPointCount`). -/
theorem heckeContinuation_functionalEquation5_of_gaussPointCount (h1 : HeckeFE.GaussPointCount) :
    ZInQ.Literature.HeckeContinuation ∧ ZInQ.Literature.FunctionalEquation5 :=
  ⟨heckeContinuation_of_gaussPointCount h1, (HeckeFE.literature_hecke_fe_of_gaussPointCount h1).2⟩

end ZInQ.Contrib
