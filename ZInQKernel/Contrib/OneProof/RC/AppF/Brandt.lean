import Mathlib
import ZInQKernel.Contrib.OneProof.RC.AppF.Lines
import ZInQKernel.Contrib.OneProof.RC.Odd.Operators

/-!
# App F: the neighbour identity of one class and the Brandt transfer (tex 9059–9082)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-theta-form`, the all-index recurrence.

**The `p`-frame of one class.** Fix a good prime `p` and a class `z` of the supersingular set. The
theta coefficient of `z` at `k` is the finite sum `θ_z(k) = ∑_{x ∈ R_z⁰, Q_B(x) = k} f(z⁻¹xz)`
(positive definiteness makes each fibre finite). At `p` the local function is `1_{R_p⁰}` and
`R_{z,p} ≅ M₂(ℤ_p)`. `PFrame` records this finite data:

* `vecs k` : the vectors `x ∈ R_z⁰` with `Q_B(x) = k` (a `Finset`);
* `F x` : the weight `f(z⁻¹xz)` (its factor at `p` is `1` on `R_p⁰`, so `F` is the product of the
  factors away from `p`);
* `coord x = (a, b, c)` : integer representatives mod `p²` of the image of `x` in
  `R_{z,p}⁰ ≅ 𝔰𝔩₂(ℤ_p)`, with `det ≡ Q_B(x) (mod p²)`;
* `scale x = p x`, with `p x ∈ R_z⁰`, coordinates `p · coord x`, and every `y ∈ R_z⁰` with
  `y ∈ pR_{z,p}` of this form (`y/p` is integral at `p` and, `p` being a unit, at every other place).

These fields are the definitions of the adelic construction (tex 8462–8474, 8495–8497, 8598–8604),
not mathematical claims. From them and the local counts of `Lines.lean`:

* `PFrame.neighbor_identity` (tex 9059–9066, **PROVED**): with `F(p x) = s F(x)` ("scaling by `p`
  at all other places multiplies the weight by `s`"),
  `∑_L s⁻¹ ∑_{y ∈ vecs(p²n), y/p ∈ R_L} F y = s⁻¹θ(p²n) + (−n/p)θ(n) + p s θ(n/p²)`;
  the left side is the sum over the `p + 1` neighbours `R_L` of their theta coefficients at `n`
  (a neighbour's vectors lie in `p⁻¹R_z⁰`, `memNbr_two_pdiv`, and its weight at `y/p` is
  `s⁻¹F(y)`).
* `brandt_transfer` (tex 9067–9075, **PROVED**, gap F-a of the step map written out, over any
  commutative ring with the integer masses `c₀/w_z` in place of `1/w_z`): self-adjointness
  `N_ij w_j = N_ji w_i` moves the neighbour operator onto `P_M`.
* `brandt_identity` (tex 9076–9082, **PROVED**): the identity
  `H(p²n) + s(−n/p)H(n) + ps²H(n/p²) = sχ_{h_*}(p)a_pH(n)` for `H = ∑_z (c₀/w_z) P(z) χ(Nrd z) θ_z`.
-/

namespace ZInQ.Manuscript.RC.AppF

open Finset ZInQ.Manuscript.RC.Odd

/-- The finite data of one class at a good prime `p` (see the module docstring). -/
structure PFrame (p : ℕ) (R : Type*) [CommRing R] where
  /-- the vectors of the global ternary lattice -/
  V : Type
  [deq : DecidableEq V]
  /-- `vecs k = {x ∈ R_z⁰ : Q_B(x) = k}` -/
  vecs : ℕ → Finset V
  /-- the coordinates `(a, b, c)` of `x` in `R_{z,p}⁰ ≅ 𝔰𝔩₂(ℤ_p)`, mod `p²` -/
  coord : V → ℤ × ℤ × ℤ
  /-- the weight `f(z⁻¹xz)` -/
  F : V → R
  /-- `x ↦ p x` -/
  scale : V → V
  coord_det : ∀ k, ∀ x ∈ vecs k,
    (p : ℤ) ^ 2 ∣ (-(coord x).1 ^ 2 - (coord x).2.1 * (coord x).2.2) - k
  scale_mem : ∀ k x, x ∈ vecs k → scale x ∈ vecs (p ^ 2 * k)
  div_mem : ∀ k y, y ∈ vecs k → PDiv p (coord y).1 (coord y).2.1 (coord y).2.2 →
    p ^ 2 ∣ k ∧ ∃ x ∈ vecs (k / p ^ 2), scale x = y
  scale_inj : Function.Injective scale
  coord_scale : ∀ x, (p : ℤ) ^ 2 ∣ (coord (scale x)).1 - p * (coord x).1 ∧
    (p : ℤ) ^ 2 ∣ (coord (scale x)).2.1 - p * (coord x).2.1 ∧
    (p : ℤ) ^ 2 ∣ (coord (scale x)).2.2 - p * (coord x).2.2

namespace PFrame

variable {p : ℕ} {R : Type*} [CommRing R] (Φ : PFrame p R)

attribute [instance] PFrame.deq

/-- `θ_z(k) = ∑_{Q_B(x) = k} f(z⁻¹xz)`. -/
def theta (k : ℕ) : R := ∑ x ∈ Φ.vecs k, Φ.F x

/-- `y ∈ pR_{z,p}`. -/
def pdiv (y : Φ.V) : Prop := PDiv p (Φ.coord y).1 (Φ.coord y).2.1 (Φ.coord y).2.2

/-- `y / p` lies in the neighbour of the line `L`. -/
def mem1 (y : Φ.V) (L : Option (ZMod p)) : Prop :=
  MemNbr p 1 (Φ.coord y).1 (Φ.coord y).2.1 (Φ.coord y).2.2 L

open Classical in
/-- `∑_{y ∈ vecs(p²n), y/p ∈ R_L} F y`: the neighbour's theta coefficient at `n`, before the factor
`s⁻¹` of its weight. -/
noncomputable def nbrSum (L : Option (ZMod p)) (n : ℕ) : R :=
  ∑ y ∈ (Φ.vecs (p ^ 2 * n)).filter (fun y => Φ.mem1 y L), Φ.F y

variable [hp : Fact p.Prime]

theorem pdiv_scale (x : Φ.V) : Φ.pdiv (Φ.scale x) := by
  obtain ⟨h1, h2, h3⟩ := Φ.coord_scale x
  have hp2 : (p : ℤ) ∣ (p : ℤ) ^ 2 := dvd_pow_self _ two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · have := dvd_add (dvd_trans hp2 h1) (dvd_mul_right (p : ℤ) (Φ.coord x).1)
    simpa using this
  · have := dvd_add (dvd_trans hp2 h2) (dvd_mul_right (p : ℤ) (Φ.coord x).2.1)
    simpa using this
  · have := dvd_add (dvd_trans hp2 h3) (dvd_mul_right (p : ℤ) (Φ.coord x).2.2)
    simpa using this

open Classical in
/-- The vectors of `R_z⁰ ∩ pR_{z,p}` of norm `p² n` are exactly `p · vecs n`. -/
theorem filter_pdiv_eq (n : ℕ) :
    (Φ.vecs (p ^ 2 * n)).filter Φ.pdiv = (Φ.vecs n).image Φ.scale := by
  have hp0 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  ext y
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hy, hd⟩
    obtain ⟨-, x, hx, rfl⟩ := Φ.div_mem _ y hy hd
    rw [Nat.mul_div_cancel_left n hp0] at hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Φ.scale_mem n x hx, Φ.pdiv_scale x⟩

open Classical in
/-- The vectors of `R_z⁰ ∩ pR_{z,p}` of norm `k`: empty unless `p² ∣ k`. -/
theorem sum_filter_pdiv (G : Φ.V → R) (k : ℕ) :
    ∑ y ∈ (Φ.vecs k).filter Φ.pdiv, G y = divCoeff (fun j => ∑ x ∈ Φ.vecs j, G (Φ.scale x)) (p ^ 2) k := by
  unfold divCoeff
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [Φ.filter_pdiv_eq, Nat.mul_div_cancel_left j (pow_pos hp.out.pos 2),
      sum_image (fun x _ y _ hxy => Φ.scale_inj hxy)]
  · apply Finset.sum_eq_zero
    intro y hy
    rw [mem_filter] at hy
    exact absurd (Φ.div_mem k y hy.1 hy.2).1 h

open Classical in
/-- Interchange: the sum over neighbours is a sum over vectors weighted by their multiplicity. -/
theorem sum_nbrSum (n : ℕ) :
    ∑ L : Option (ZMod p), Φ.nbrSum L n =
      ∑ y ∈ Φ.vecs (p ^ 2 * n), Φ.F y *
        ((count p 1 (Φ.coord y).1 (Φ.coord y).2.1 (Φ.coord y).2.2 : ℤ) : R) := by
  unfold nbrSum count
  simp only [sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  unfold mem1
  split_ifs <;> simp

theorem count1_scale (x : Φ.V) :
    count p 1 (Φ.coord (Φ.scale x)).1 (Φ.coord (Φ.scale x)).2.1 (Φ.coord (Φ.scale x)).2.2 =
      count p 0 (Φ.coord x).1 (Φ.coord x).2.1 (Φ.coord x).2.2 := by
  classical
  obtain ⟨h1, h2, h3⟩ := Φ.coord_scale x
  unfold count
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [memNbr_congr h1 h2 h3 L, memNbr_one_scale]

/-- **PROVED (tex 9059–9066): the neighbour identity of one class.** For an odd good prime `p`, a
unit `s` (`s = η_B(p)`, `s s⁻¹ = 1`) with `F(p x) = s F(x)`:
`∑_L s⁻¹ ∑_{y ∈ vecs(p²n), y/p ∈ R_L} F(y) = s⁻¹θ(p²n) + (−n/p)θ(n) + p s θ(n/p²)`,
`θ(n/p²) = 0` at a nonintegral index. The primitive vectors give `s⁻¹θ(p²n) − θ(n)` (one
neighbour each, `count1_primitive`); the vectors `p x` give `(1 + (−n/p))θ(n) + p s θ(n/p²)`
(`count0_primitive`, `count0_pdiv`). -/
theorem neighbor_identity (hp2 : p ≠ 2) {s sinv : R} (hs : s * sinv = 1)
    (hF : ∀ x, Φ.F (Φ.scale x) = s * Φ.F x) (n : ℕ) :
    ∑ L : Option (ZMod p), sinv * Φ.nbrSum L n =
      sinv * Φ.theta (p ^ 2 * n) + (legendreSym p (-(n : ℤ)) : R) * Φ.theta n +
        (p : R) * s * divCoeff Φ.theta (p ^ 2) n := by
  classical
  rw [← Finset.mul_sum, Φ.sum_nbrSum]
  -- split `vecs (p² n)` into primitive vectors and `p · vecs n`
  rw [← Finset.sum_filter_add_sum_filter_not (Φ.vecs (p ^ 2 * n)) Φ.pdiv]
  have hprim : ∑ y ∈ (Φ.vecs (p ^ 2 * n)).filter (fun y => ¬ Φ.pdiv y),
      Φ.F y * ((count p 1 (Φ.coord y).1 (Φ.coord y).2.1 (Φ.coord y).2.2 : ℤ) : R) =
      ∑ y ∈ (Φ.vecs (p ^ 2 * n)).filter (fun y => ¬ Φ.pdiv y), Φ.F y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [mem_filter] at hy
    have hdet : (p : ℤ) ^ 2 ∣ -(Φ.coord y).1 ^ 2 - (Φ.coord y).2.1 * (Φ.coord y).2.2 := by
      have := dvd_add (Φ.coord_det _ y hy.1) (dvd_mul_right ((p : ℤ) ^ 2) (n : ℤ))
      convert this using 1; push_cast; ring
    rw [count1_primitive hy.2 hdet]; simp
  rw [hprim, Φ.filter_pdiv_eq, sum_image (fun x _ y _ hxy => Φ.scale_inj hxy)]
  simp only [Φ.count1_scale, hF]
  -- the theta sum at `p² n` splits the same way
  have hθ : Φ.theta (p ^ 2 * n) = s * Φ.theta n +
      ∑ y ∈ (Φ.vecs (p ^ 2 * n)).filter (fun y => ¬ Φ.pdiv y), Φ.F y := by
    unfold theta
    rw [← Finset.sum_filter_add_sum_filter_not (Φ.vecs (p ^ 2 * n)) Φ.pdiv, Φ.filter_pdiv_eq,
      sum_image (fun x _ y _ hxy => Φ.scale_inj hxy), Finset.mul_sum]
    simp only [hF]
  -- the integral vectors `x ∈ vecs n`: split by `x ∈ pR_{z,p}`
  have hint : ∑ x ∈ Φ.vecs n, s * Φ.F x *
      ((count p 0 (Φ.coord x).1 (Φ.coord x).2.1 (Φ.coord x).2.2 : ℤ) : R) =
      s * ((1 + (legendreSym p (-(n : ℤ)) : R)) * Φ.theta n +
        (p : R) * divCoeff (fun j => ∑ x ∈ Φ.vecs j, Φ.F (Φ.scale x)) (p ^ 2) n) := by
    rw [← Φ.sum_filter_pdiv, ← Finset.sum_filter_add_sum_filter_not (Φ.vecs n) Φ.pdiv]
    unfold theta
    rw [← Finset.sum_filter_add_sum_filter_not (Φ.vecs n) Φ.pdiv]
    have hA : ∑ x ∈ (Φ.vecs n).filter Φ.pdiv, s * Φ.F x *
        ((count p 0 (Φ.coord x).1 (Φ.coord x).2.1 (Φ.coord x).2.2 : ℤ) : R) =
        ∑ x ∈ (Φ.vecs n).filter Φ.pdiv, s * Φ.F x * ((p : R) + 1) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_filter] at hx
      rw [count0_pdiv hx.2]; push_cast; ring
    have hB : ∑ x ∈ (Φ.vecs n).filter (fun x => ¬ Φ.pdiv x), s * Φ.F x *
        ((count p 0 (Φ.coord x).1 (Φ.coord x).2.1 (Φ.coord x).2.2 : ℤ) : R) =
        ∑ x ∈ (Φ.vecs n).filter (fun x => ¬ Φ.pdiv x), s * Φ.F x *
          (1 + (legendreSym p (-(n : ℤ)) : R)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_filter] at hx
      rw [count0_primitive hp2 hx.2]
      have hmod : legendreSym p (-(-(Φ.coord x).1 ^ 2 - (Φ.coord x).2.1 * (Φ.coord x).2.2)) =
          legendreSym p (-(n : ℤ)) := by
        have hd := dvd_trans (dvd_pow_self (p : ℤ) two_ne_zero) (Φ.coord_det n x hx.1)
        unfold legendreSym
        congr 1
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        convert hd using 1; ring
      rw [hmod]; push_cast; ring
    rw [hA, hB]
    -- at `x ∈ pR_{z,p}` of norm `n`, `p² ∣ n`, so `(−n/p) = 0`
    by_cases hn : p ^ 2 ∣ n
    · have hleg : legendreSym p (-(n : ℤ)) = 0 := by
        rw [legendreSym.eq_zero_iff]
        have : (p : ℤ) ∣ n := by
          exact_mod_cast dvd_trans (dvd_pow_self p two_ne_zero) hn
        obtain ⟨c, hc⟩ := this
        rw [hc]; push_cast; simp
      rw [hleg]
      simp only [Int.cast_zero, add_zero, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    · have hempty : ∀ x ∈ Φ.vecs n, ¬ Φ.pdiv x := fun x hx hd => hn (Φ.div_mem n x hx hd).1
      rw [Finset.filter_false_of_mem hempty]
      simp only [Finset.sum_empty, zero_add, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
  rw [hint, hθ]
  have hdc : divCoeff (fun j => ∑ x ∈ Φ.vecs j, Φ.F (Φ.scale x)) (p ^ 2) n =
      s * divCoeff Φ.theta (p ^ 2) n := by
    unfold divCoeff theta
    split_ifs
    · rw [Finset.mul_sum]; simp only [hF]
    · simp
  rw [hdc]
  linear_combination ((legendreSym p (-(n : ℤ)) : R) * Φ.theta n +
    (p : R) * s * divCoeff Φ.theta (p ^ 2) n) * hs

end PFrame

/-! ### The Brandt transfer (tex 9067–9075) -/

open Classical in
/-- `N_ij = #{L : the neighbour of `i` at `L` is in the class `j`}`. -/
noncomputable def nbrCount {X : Type*} {p : ℕ} [NeZero p] (nb : X → Option (ZMod p) → X)
    (i j : X) : ℕ :=
  #(univ.filter (fun L => nb i L = j))

theorem sum_nb_eq {X : Type*} [Fintype X] {p : ℕ} [NeZero p] {R : Type*} [CommRing R]
    (nb : X → Option (ZMod p) → X) (f : X → R) (i : X) :
    ∑ L, f (nb i L) = ∑ j, (nbrCount nb i j : R) * f j := by
  classical
  unfold nbrCount
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.sum_ite_eq]; simp

/-- **PROVED (tex 9069–9071).** Self-adjointness `N_ij w_j = N_ji w_i` with `w_i, w_j ∣ c₀` gives
`(c₀/w_i) N_ij = (c₀/w_j) N_ji`: the masses `1/w_i` scaled to integers. -/
theorem mass_adjoint {c w₁ w₂ N₁₂ N₂₁ : ℕ} (h1 : w₁ ∣ c) (h2 : w₂ ∣ c) (hw1 : 0 < w₁)
    (hw2 : 0 < w₂) (hN : N₁₂ * w₂ = N₂₁ * w₁) : c / w₁ * N₁₂ = c / w₂ * N₂₁ := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, hb⟩ := h2
  rw [Nat.mul_div_cancel_left a hw1, hb, Nat.mul_div_cancel_left b hw2]
  have : w₁ * (a * N₁₂) * w₂ = w₁ * (b * N₂₁) * w₂ := by
    calc w₁ * (a * N₁₂) * w₂ = (w₁ * a) * (N₁₂ * w₂) := by ring
      _ = (w₂ * b) * (N₂₁ * w₁) := by rw [← hb, hN]
      _ = w₁ * (b * N₂₁) * w₂ := by ring
  exact Nat.eq_of_mul_eq_mul_left hw1 (Nat.eq_of_mul_eq_mul_right hw2 this)

/-- **PROVED (tex 9067–9075; step-map gap F-a written out).** Moving the neighbour operator onto
`P_M`: if `c_i N_ij = c_j N_ji` (integer masses) and `∑_L P(nb j L) = a_p P(j)`, then
`∑_i c_i P_i ∑_L Θ(nb i L) = a_p ∑_j c_j P_j Θ_j`. -/
theorem brandt_transfer {X : Type*} [Fintype X] {p : ℕ} [NeZero p] {R : Type*} [CommRing R]
    (nb : X → Option (ZMod p) → X) (c : X → ℕ) (P Θ : X → R) (ap : R)
    (hadj : ∀ i j, c i * nbrCount nb i j = c j * nbrCount nb j i)
    (hecke : ∀ j, ∑ L, P (nb j L) = ap * P j) :
    ∑ i, (c i : R) * P i * ∑ L, Θ (nb i L) = ap * ∑ j, (c j : R) * P j * Θ j := by
  simp only [sum_nb_eq nb Θ, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, (c i : R) * P i * ((nbrCount nb i j : R) * Θ j) =
      (c j : R) * Θ j * ∑ L, P (nb j L) := by
    intro j
    rw [sum_nb_eq nb P, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrArg (fun k : ℕ => (k : R)) (hadj i j)
    push_cast at this
    linear_combination (P i * Θ j) * this
  simp only [this, hecke]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **PROVED (tex 9076–9082): the Brandt identity for the theta sum.** Let
`H(k) = ∑_z c_z P(z) Θ_z(k)`, `Θ_z = χ_{h_*}(Nrd z) θ_z`. Suppose the masses are self-adjoint, `P` is
a `T_p`-eigenfunction with eigenvalue `a_p`, and every class satisfies the neighbour identity with the
norm-character change `χ_p = χ_{h_*}(p)`:
`∑_L Θ_{nb z L}(n) = χ_p (s⁻¹Θ_z(p²n) + (−n/p)Θ_z(n) + p s Θ_z(n/p²))`. Then
`H(p²n) + s(−n/p)H(n) + p s² H(n/p²) = s χ_p a_p H(n)` at every index. -/
theorem brandt_identity {X : Type*} [Fintype X] {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (nb : X → Option (ZMod p) → X) (c : X → ℕ) (P : X → R) (Θ : X → ℕ → R) (ap s sinv χp : R)
    (hs : s * sinv = 1) (hχ : χp * χp = 1)
    (hadj : ∀ i j, c i * nbrCount nb i j = c j * nbrCount nb j i)
    (hecke : ∀ j, ∑ L, P (nb j L) = ap * P j)
    (hnbr : ∀ z n, ∑ L, Θ (nb z L) n = χp * (sinv * Θ z (p ^ 2 * n) +
      (legendreSym p (-(n : ℤ)) : R) * Θ z n + (p : R) * s * divCoeff (Θ z) (p ^ 2) n))
    (n : ℕ) :
    (∑ z, (c z : R) * P z * Θ z (p ^ 2 * n)) +
      s * (legendreSym p (-(n : ℤ)) : R) * (∑ z, (c z : R) * P z * Θ z n) +
      (p : R) * s ^ 2 * divCoeff (fun k => ∑ z, (c z : R) * P z * Θ z k) (p ^ 2) n =
      s * χp * ap * (∑ z, (c z : R) * P z * Θ z n) := by
  have ht := brandt_transfer nb c P (fun z => Θ z n) ap hadj hecke
  simp only [hnbr] at ht
  have hdc : divCoeff (fun k => ∑ z, (c z : R) * P z * Θ z k) (p ^ 2) n =
      ∑ z, (c z : R) * P z * divCoeff (Θ z) (p ^ 2) n := by
    unfold divCoeff; split_ifs <;> simp
  rw [hdc]
  have expand : ∑ i, (c i : R) * P i * (χp * (sinv * Θ i (p ^ 2 * n) +
      (legendreSym p (-(n : ℤ)) : R) * Θ i n + (p : R) * s * divCoeff (Θ i) (p ^ 2) n)) =
      χp * (sinv * (∑ z, (c z : R) * P z * Θ z (p ^ 2 * n)) +
        (legendreSym p (-(n : ℤ)) : R) * (∑ z, (c z : R) * P z * Θ z n) +
        (p : R) * s * ∑ z, (c z : R) * P z * divCoeff (Θ z) (p ^ 2) n) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [expand] at ht
  set A := ∑ z, (c z : R) * P z * Θ z (p ^ 2 * n)
  set B := ∑ z, (c z : R) * P z * Θ z n
  set C := ∑ z, (c z : R) * P z * divCoeff (Θ z) (p ^ 2) n
  set ℓ : R := (legendreSym p (-(n : ℤ)) : R)
  linear_combination (s * χp) * ht - (s * ℓ * B + (p : R) * s ^ 2 * C + A) * hχ -
    (χp * χp * A) * hs

end ZInQ.Manuscript.RC.AppF
