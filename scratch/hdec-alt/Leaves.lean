import ZInQKernel.Hypotheses.Height

/-!
# hdec-alt: the leaves of H on the route of `docs/research/hdec-alt.md`, as Lean Props

Draft (task hdec-alt, 2026-11-11). Checked with `lake env lean scratch/hdec-alt/Leaves.lean`.

The route is Glazer's proof of Theorem 4.1 (`docs/research/h-trust.md`, steps A1-F4) with one
substitution: the modularity block (h-trust C3-C5, C7, C8: Pan's theorem with the p-adic Hodge
inputs) is replaced by Ribet's theorem on building blocks and the Khare–Wintenberger modularity
of `GL₂`-type abelian varieties over `ℚ` (note §1, §3 leaves L13-L14).

## Layout

1. **The target.** `ZInQKernel/Hypotheses/HeightMin.lean` cannot be imported here (its import
   chain needs the upstream package `lean/`, not built in this worktree; log Step 3). So
   `JHeightBoundAt S` restates `ZInQ.JHeight.JHeightBound S` verbatim (same `Jmap`, same `heightX`),
   and the top-level theorem is stated for every admissible prime set `S`, which covers
   `Mult.S_mul`. `ZInQ.JHeight.sixContactMin_of_jHeightBound` (proved, in the kernel tree) then
   gives `SixContactMin`.
2. **Genuine definitions available now** (§2): abelian varieties over a field, continuous
   Galois representations, their intertwiners, semisimplicity, irreducibility, the absolute
   logarithmic height of a projective point. Built from Mathlib objects only.
3. **Leaves statable now** (§3): the Hasse principle and Hilbert reciprocity for quaternion
   algebras over `ℚ`, and Kronecker–Weber. Both are proved in Tau Ceti (prereq-survey §1).
4. **Definitions still to be built** (§4): each is an `opaque` constant with the type the
   genuine definition will have and its cost tier in the docstring. An `opaque` constant has no
   definition, so the leaves of §5 stated over it are **not yet faithful**: they become the
   published statements only when each `opaque` is replaced by the genuine definition, with the
   leaf text unchanged. Nothing here can be used to prove anything about the real objects.
5. **Leaves stated over §4** (§5).
6. **The glue** (§6): the top-level theorem, `sorry`. It cannot be proved over the `opaque`
   placeholders: the glue uses what the definitions mean (for example that the Tate module of a
   product is the direct sum), not only the leaves. The warning of `docs/research/wk-h.md` §4.3
   applies: over arbitrary interpretations of §4 the hypotheses carry no more than a height bound.
-/

open AlgebraicGeometry CategoryTheory

namespace ZInQ.HDecAlt

/-! ## 1. The target, restated (identical to `ZInQ.JHeight.JHeightBound`) -/

/-! Copied verbatim from `ZInQKernel/Hypotheses/JHeight.lean` (lines 30-232: `Fh`, `Gh`, `Jmap`,
the certificates, `dvd_C0`, `lower_bound`, `twelve_mul_ratHeight_le`), since that file cannot be
imported here. -/

/-- The binary sextic `F_h(a,b) = a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b)`. -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`, the bound for the cancellation in `J(u)`. -/
def C0 : ℤ := (57600 * 3 ^ 7) * (57600 * 104976000000 ^ 7)

/-- **Cancellation bound.** For coprime `a, b`, a common divisor of `57600F_h²` and `G_h⁶` divides
`C₀` (from `cert_x`, `cert_y` raised to the 7th power). -/
theorem dvd_C0 {a b c : ℤ} (hab : IsCoprime a b) (hP : c ∣ 57600 * Fh a b ^ 2)
    (hQ : c ∣ Gh a b ^ 6) : c ∣ C0 := by
  have key : ∀ x y : ℤ, 57600 * (x + y) ^ 7 =
      57600 * x ^ 2 * (x ^ 5 + 7 * x ^ 4 * y + 21 * x ^ 3 * y ^ 2 + 35 * x ^ 2 * y ^ 3 +
        35 * x * y ^ 4 + 21 * y ^ 5) + y ^ 6 * (57600 * (7 * x + y)) := by intros; ring
  have hsplit : ∀ (A B : ℤ), c ∣ 57600 * (A * Fh a b + B * Gh a b) ^ 7 := by
    intro A B
    rw [key]
    refine dvd_add ?_ ?_
    · have : 57600 * (A * Fh a b) ^ 2 = (57600 * Fh a b ^ 2) * A ^ 2 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hP _
    · have : (B * Gh a b) ^ 6 = Gh a b ^ 6 * B ^ 6 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hQ _
  have hx : c ∣ 57600 * 3 ^ 7 * a ^ 49 := by
    have e : 57600 * 3 ^ 7 * a ^ 49 = 57600 * (3 * a ^ 7) ^ 7 := by ring
    rw [e, cert_x]; exact hsplit _ _
  have hy : c ∣ 57600 * 104976000000 ^ 7 * b ^ 49 := by
    have e : 57600 * 104976000000 ^ 7 * b ^ 49 = 57600 * (104976000000 * b ^ 7) ^ 7 := by ring
    rw [e, cert_y]; exact hsplit _ _
  obtain ⟨s, t, hst⟩ := hab.pow (m := 49) (n := 49)
  have e : C0 = (57600 * 104976000000 ^ 7 * s) * (57600 * 3 ^ 7 * a ^ 49) +
      (57600 * 3 ^ 7 * t) * (57600 * 104976000000 ^ 7 * b ^ 49) := by
    have : C0 = C0 * (s * a ^ 49 + t * b ^ 49) := by rw [hst, mul_one]
    rw [this, C0]; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)

theorem abs_monomial_le {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _) (pow_le_pow_left₀ (abs_nonneg _) hb _)
    (by positivity) (by positivity)

/-- **Lower bound.** With `m = max(|a|, |b|) > 0`: `m¹² ≤ 10⁴⁸ max(57600F_h², G_h⁶)`. -/
theorem lower_bound {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hm : 0 < m)
    (hmax : m = |a| ∨ m = |b|) :
    m ^ 12 ≤ 10 ^ 48 * max (57600 * Fh a b ^ 2) (Gh a b ^ 6) := by
  by_contra hlt
  push Not at hlt
  have hP := le_max_left (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hQ := le_max_right (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hF : 240 * 10 ^ 24 * |Fh a b| < m ^ 6 := by
    have h2 : (240 * 10 ^ 24 * |Fh a b|) ^ 2 < (m ^ 6) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hG : 10 ^ 8 * |Gh a b| < m ^ 2 := by
    have h6 : (10 ^ 8 * |Gh a b|) ^ 6 < (m ^ 2) ^ 6 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0:ℤ) ≤ Gh a b ^ 6)]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h6
  have hX : 240 * 10 ^ 24 * (m * |Fh a b|) < m ^ 7 := by nlinarith
  have hY : 10 ^ 8 * (m ^ 5 * |Gh a b|) < m ^ 7 := by
    have : (0 : ℤ) < m ^ 5 := by positivity
    nlinarith
  have m10 : -m ≤ a ∧ a ≤ m := abs_le.mp ha
  have m01 : -m ≤ b ∧ b ≤ m := abs_le.mp hb
  have mono : ∀ i j : ℕ, i + j = 5 → -m ^ 5 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ m ^ 5 := by
    intro i j hij
    have := abs_monomial_le ha hb i j
    rw [hij] at this
    exact abs_le.mp this
  have m50 := mono 5 0 rfl
  have m41 := mono 4 1 rfl
  have m32 := mono 3 2 rfl
  have m23 := mono 2 3 rfl
  have m14 := mono 1 4 rfl
  have m05 := mono 0 5 rfl
  simp only [pow_one, pow_zero, mul_one, one_mul] at m50 m41 m32 m23 m14 m05
  have hm7 : (0 : ℤ) < m ^ 7 := by positivity
  have tri : ∀ A B : ℤ, |A * Fh a b + B * Gh a b| ≤ |A| * |Fh a b| + |B| * |Gh a b| := by
    intro A B; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rcases hmax with h | h
  · have hA : |-200 * a - 4800 * b| ≤ 5000 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4| ≤ 20328129 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-200 * a - 4800 * b) (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 +
      2880000 * a ^ 2 * b ^ 3 + 17280000 * a * b ^ 4)
    rw [← cert_x, abs_mul, abs_pow, ← h, show |(3 : ℤ)| = 3 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith
  · have hA : |-1001 * a - 37650 * b| ≤ 38651 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 +
        20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5| ≤
        184009200 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-1001 * a - 37650 * b) (143 * a ^ 5 + 20557 * a ^ 4 * b +
      1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5)
    rw [← cert_y, abs_mul, abs_pow, ← h, show |(104976000000 : ℤ)| = 104976000000 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 450` for `u ∉ 𝒞` (N5: `h(u) < h(J(u)) + 74`). -/
theorem twelve_mul_ratHeight_le (u : ℚ) (_hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 450 := by
  set a : ℤ := u.num with ha_def
  set b : ℤ := (u.den : ℤ) with hb_def
  have hb : 0 < b := by rw [hb_def]; exact_mod_cast u.den_pos
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact u.reduced
  have hu_eq : u = (a : ℚ) / (b : ℚ) := by
    rw [ha_def, hb_def]; push_cast; exact (Rat.num_div_den u).symm
  have hFq : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) =
      (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fh; push_cast; field_simp
  have hGq : 7 * u ^ 2 + 300 * u + 3600 = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gh; push_cast; field_simp
  have hG0 : 0 < Gh a b := by unfold Gh; nlinarith [sq_nonneg (7 * a + 150 * b), mul_pos hb hb]
  set n : ℤ := -(57600 * Fh a b ^ 2) with hn_def
  set d : ℤ := Gh a b ^ 6 with hd_def
  have hdpos : 0 < d := by positivity
  have hJ : Jmap u = (n : ℚ) / (d : ℚ) := by
    have hGq0 : (Gh a b : ℚ) ≠ 0 := by exact_mod_cast hG0.ne'
    unfold Jmap; rw [hFq, hGq, hn_def, hd_def]; push_cast; field_simp
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hdpos.ne'
  rw [← hJ] at hn hd
  set J := Jmap u with hJdef
  have hden : (0 : ℤ) < (J.den : ℤ) := by exact_mod_cast J.den_pos
  have hcpos : 0 < c := by
    by_contra h; push Not at h; rw [hd] at hdpos; nlinarith
  have hcdvd : c ∣ C0 := dvd_C0 hcop (dvd_neg.mp (Dvd.intro _ hn.symm)) (Dvd.intro _ hd.symm)
  have hcle : c ≤ C0 := Int.le_of_dvd (by norm_num [C0]) hcdvd
  have hmaxeq : max (57600 * Fh a b ^ 2) d = c * max |J.num| (J.den : ℤ) := by
    have h1 : 57600 * Fh a b ^ 2 = |n| := by
      rw [hn_def, abs_neg, abs_of_nonneg (by positivity)]
    rw [h1, hn, hd, abs_mul, abs_of_pos hcpos, mul_max_of_nonneg _ _ hcpos.le]
  set m := max |a| b with hm_def
  have hm : 0 < m := lt_of_lt_of_le hb (le_max_right _ _)
  have hlow := lower_bound (a := a) (b := b) (le_max_left |a| b)
    (by rw [abs_of_pos hb]; exact le_max_right _ _) hm
    (by rcases max_choice |a| b with h | h
        · left; exact h
        · right; rw [abs_of_pos hb]; exact h)
  rw [hmaxeq] at hlow
  set H := max |J.num| (J.den : ℤ) with hH_def
  have hH : 1 ≤ H := le_max_of_le_right (by exact_mod_cast J.den_pos)
  have hlow2 : m ^ 12 ≤ 10 ^ 139 * H := by
    have hC : 10 ^ 48 * C0 ≤ 10 ^ 139 := by norm_num [C0]
    calc m ^ 12 ≤ 10 ^ 48 * (c * H) := hlow
      _ ≤ 10 ^ 48 * (C0 * H) := by gcongr
      _ = (10 ^ 48 * C0) * H := by ring
      _ ≤ 10 ^ 139 * H := by gcongr
  have hu_h : ratHeight u = Real.log (m : ℝ) := by
    unfold ratHeight; rw [hm_def]; push_cast [ha_def, hb_def]; rfl
  have hJ_h : ratHeight J = Real.log (H : ℝ) := by
    unfold ratHeight; rw [hH_def]; push_cast; rfl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlowR : (m : ℝ) ^ 12 ≤ 10 ^ 139 * (H : ℝ) := by exact_mod_cast hlow2
  have hlog10 : Real.log 10 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
      pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    rw [this]; norm_num at h2 ⊢; linarith
  have key : 12 * Real.log (m : ℝ) ≤ 139 * Real.log 10 + Real.log (H : ℝ) := by
    have := Real.log_le_log (by positivity) hlowR
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  rw [hu_h, hJ_h]
  linarith

/-- `X(R) = max(1, C_cm, Q_R¹⁷)` (as `ZInQ.JHeight.heightX`). -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- `ZInQ.JHeight.JHeightBound S`, verbatim. -/
def JHeightBoundAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

/-- `ZInQ.SixContactMin` with `Mult.S_mul` replaced by a prime set `S`. -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24

/-- The admissibility conditions on `S` used by the proof (h-trust §0): primes, containing the
primes `≤ 324`, bounded by `D`. (`10¹² ≤ D` holds by definition of `D`.) -/
def Admissible (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime) ∧ (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S) ∧ (∀ p ∈ S, p ≤ heightD)

/-! ## 2. Genuine definitions available now (Mathlib objects only) -/

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral. (Commutativity follows:
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`.) Cost: cheap. -/
structure AbelianVariety (K : Type) [Field K] where
  /-- the underlying scheme over `Spec K` -/
  G : Over (Spec (CommRingCat.of K))
  [grp : GrpObj G]
  [proper : IsProper G.hom]
  [geomInt : GeometricallyIntegral G.hom]
  [smooth : Smooth G.hom]

/-- The dimension: the relative dimension of the smooth structure morphism. Cost: cheap. -/
noncomputable def AbelianVariety.dim {K : Type} [Field K] (A : AbelianVariety K) : ℕ :=
  sInf {n : ℕ | SmoothOfRelativeDimension n A.G.hom}

/-- A continuous `n`-dimensional representation of `G_K = Gal(K̄/K)` with coefficients in a
topological field `E` (for `ℓ`-adic representations, `E = ℚ_ℓ` or a finite extension). -/
structure GalRep (K : Type) [Field K] (E : Type) [Field E] [TopologicalSpace E] where
  /-- the dimension -/
  n : ℕ
  /-- the action -/
  ρ : Field.absoluteGaloisGroup K →* GL (Fin n) E
  cont : Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) E)

noncomputable instance (K E : Type) [Field K] [Field E] [TopologicalSpace E] :
    Inhabited (GalRep K E) :=
  ⟨⟨0, 1, by simpa using continuous_const⟩⟩

variable {K E : Type} [Field K] [Field E] [TopologicalSpace E]

/-- `ρ(g)` as a linear endomorphism of `Eⁿ`. -/
noncomputable def GalRep.act (ρ : GalRep K E) (g : Field.absoluteGaloisGroup K) :
    (Fin ρ.n → E) →ₗ[E] (Fin ρ.n → E) :=
  Matrix.toLin' (ρ.ρ g : Matrix (Fin ρ.n) (Fin ρ.n) E)

/-- `Hom_{G_K}(ρ, σ)`. -/
noncomputable def GalRep.intertwiners (ρ σ : GalRep K E) :
    Submodule E ((Fin ρ.n → E) →ₗ[E] (Fin σ.n → E)) where
  carrier := {f | ∀ g, f ∘ₗ ρ.act g = σ.act g ∘ₗ f}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, ha g, hb g]
  smul_mem' := by
    intro c a ha g
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha g]

/-- `dim_E Hom_{G_K}(ρ, σ)`. -/
noncomputable def GalRep.homDim (ρ σ : GalRep K E) : ℕ :=
  Module.finrank E (ρ.intertwiners σ)

/-- A `G_K`-stable subspace. -/
def GalRep.IsStable (ρ : GalRep K E) (W : Submodule E (Fin ρ.n → E)) : Prop :=
  ∀ g, ∀ v ∈ W, ρ.act g v ∈ W

/-- Semisimplicity: every stable subspace has a stable complement. -/
def GalRep.IsSemisimple (ρ : GalRep K E) : Prop :=
  ∀ W, ρ.IsStable W → ∃ W', IsCompl W W' ∧ ρ.IsStable W'

/-- Irreducibility over `E` (apply it with `E` algebraically closed, or after every finite
extension, for absolute irreducibility). -/
def GalRep.IsIrreducible (ρ : GalRep K E) : Prop :=
  0 < ρ.n ∧ ∀ W, ρ.IsStable W → W = ⊥ ∨ W = ⊤

/-- The absolute logarithmic (sup-)height of a point `x ∈ Pⁿ(L)`, `L` a number field:
`log H(x) / [L : ℚ]` with Mathlib's `Height.logHeight`. -/
noncomputable def absLogHeightVec {L : Type} [Field L] [NumberField L] {ι : Type}
    (x : ι → L) : ℝ :=
  Height.logHeight x / (Module.finrank ℚ L : ℝ)

/-! ## 3. Leaves statable now -/

/-- The quaternion algebra `(a, b)_F` splits. -/
def QSplits (F : Type) [Field F] (a b : F) : Prop :=
  Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)

/-- **Leaf L19a (Hasse principle for quaternion algebras over `ℚ`).** Part of the
Albert–Brauer–Hasse–Noether theorem (injectivity of `Br ℚ → ⊕_v Br ℚ_v`) at the `2`-torsion
classes of quaternion algebras. Used in step B2. Proved in Tau Ceti
(`TauCeti.ClassFieldTheory.brLocalization_injective`, prereq-survey §1). -/
def Leaf_HasseQuaternion : Prop :=
  ∀ a b : ℚ, a ≠ 0 → b ≠ 0 →
    (QSplits ℚ a b ↔
      (∀ p : ℕ, ∀ _ : Fact p.Prime, QSplits ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) ∧
        QSplits ℝ (a : ℝ) (b : ℝ))

open Classical in
/-- **Leaf L19b (Hilbert reciprocity).** A quaternion algebra over `ℚ` is ramified at an even,
finite number of places. Used in step B2 (the real place). Proved in Tau Ceti
(`…sumLocalInv_brLocalization_eq_zero`, `…hilbertProductFormula`). -/
def Leaf_HilbertReciprocity : Prop :=
  ∀ a b : ℚ, a ≠ 0 → b ≠ 0 →
    ∃ P : Finset ℕ, (∀ p : ℕ, ∀ _ : Fact p.Prime, (p ∈ P ↔ ¬ QSplits ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])))
      ∧ Even (P.card + if QSplits ℝ (a : ℝ) (b : ℝ) then 0 else 1)

/-- **Leaf L20 (Kronecker–Weber).** Every finite abelian extension of `ℚ` embeds in a
cyclotomic field. Used in glue G13 (the twisting character is a Dirichlet character). Proved in
Tau Ceti (`TauCeti.ClassFieldTheory.kroneckerWeber`). -/
def Leaf_KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
      ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ)

/-! ## 4. Definitions still to be built (`opaque` placeholders; cost tier in each docstring)

`𝓟 K` below abbreviates the finite places of a number field `K`. -/

/-- The finite places of a number field. -/
abbrev Places (K : Type) [Field K] [NumberField K] : Type :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- `V_ℓ(A)` with its `G_K`-action (Tate convention). Cost: **large** (points over `K̄` as a
group, torsion, inverse limit, Galois action, continuity, rank `2 dim A`). -/
noncomputable opaque tateRep (A : AbelianVariety K) (ℓ : ℕ) [Fact ℓ.Prime] : GalRep K ℚ_[ℓ]

/-- `rank_ℤ Hom_K(A, B)`. Cost: **medium** (homomorphisms of group objects; finiteness of the
rank is itself a theorem, Mumford §19). -/
opaque homRank (A B : AbelianVariety K) : ℕ

/-- There is a `K`-isogeny `A → B` of degree `d`. Cost: **medium** (finite surjective
homomorphism; degree = rank of the pushforward of the structure sheaf). -/
opaque IsIsogenyOfDegree (A B : AbelianVariety K) (d : ℕ) : Prop

/-- `P ≅ A × Z` over `K`. Cost: **cheap-medium** (products in `Over (Spec K)`). -/
opaque IsProductOf (P A Z : AbelianVariety K) : Prop

/-- `A'` over `L` is the base change of `A` over `K` along `K → L`. Cost: **medium** (pullback of
the group object; the instances). -/
opaque IsBaseChange {L : Type} [Field L] [Algebra K L] (A : AbelianVariety K)
    (A' : AbelianVariety L) : Prop

/-- `A` has good reduction at the finite place `v` (it extends to an abelian scheme over the
local ring at `v`). Cost: **medium**. -/
opaque HasGoodReductionAt [NumberField K] (A : AbelianVariety K) (v : Places K) : Prop

/-- `A` has good reduction at every place above `v` after some finite extension. Cost:
**medium** (from `HasGoodReductionAt` and `IsBaseChange`). -/
opaque HasPotentiallyGoodReductionAt [NumberField K] (A : AbelianVariety K) (v : Places K) : Prop

/-- All `3`-torsion points of `A` are `K`-rational. Cost: **medium**. -/
opaque HasFullRationalTorsion (A : AbelianVariety K) (n : ℕ) : Prop

/-- `ρ` is unramified at `v` (inertia groups in `G_K` need decomposition groups, i.e. a choice
of `K̄ → K̄_v`). Cost: **medium**. -/
opaque GalRep.IsUnramifiedAt [NumberField K] (ρ : GalRep K E) (v : Places K) : Prop

/-- The exponent of the Artin conductor of a representation of `G_ℚ` at `p` (Grothendieck's
monodromy theorem for `p ≠ ℓ`; Serre, *Corps locaux* VI §2). Cost: **medium** (Tau Ceti has
upper numbering and `artinConductorExponent` for finite Galois extensions). -/
opaque GalRep.condExp (ρ : GalRep ℚ E) (p : ℕ) : ℕ

/-- `σ'` is the twist of `σ` by a character of `G_K` of finite order. Cost: **cheap**. -/
opaque GalRep.IsFiniteTwist (σ' σ : GalRep K E) : Prop

/-- `σ` (over `E ⊇ ℚ_ℓ`) is a constituent of `ρ ⊗_{ℚ_ℓ} E`. Cost: **cheap-medium**. -/
opaque GalRep.IsConstituentOf {ℓ : ℕ} [Fact ℓ.Prime] (σ : GalRep K E) (ρ : GalRep K ℚ_[ℓ]) : Prop

/-- The stable Faltings height (Deligne's normalization as in N5; base-change invariant). Cost:
**very large** (Néron models or semistable models, metrized invariant differentials). -/
opaque faltingsHeight [NumberField K] (A : AbelianVariety K) : ℝ

/-- `J` is (isomorphic to) the Jacobian of the modular curve `X₁(N)` over `ℚ`. Cost: **very
large** (modular curves as schemes over `ℚ`, Jacobians; Anthropic FLT has Jacobians). -/
opaque IsJ1 (N : ℕ) (J : AbelianVariety ℚ) : Prop

/-- `B` is a quotient of `J` over `K` (a surjective homomorphism). Cost: **medium**. -/
opaque IsQuotientOf (J B : AbelianVariety K) : Prop

/-- `B/ℚ` is of `GL₂`-type: `End⁰_ℚ(B)` contains a number field of degree `dim B`. Cost:
**medium** (once `End` exists). -/
opaque IsGL2Type (B : AbelianVariety ℚ) : Prop

/-- `A` (over a number field) is a building block in the sense of Ribet–Pyle: over `ℚ̄`,
`End⁰(A)` is a central simple algebra over a totally real field `F` with Schur index `t ≤ 2`,
`t [F : ℚ] = dim A`, and every Galois conjugate of `A` is isogenous to `A` compatibly with
`End⁰`. Cost: **medium-large**. -/
opaque IsBuildingBlock [NumberField K] (A : AbelianVariety K) : Prop

/-- `A` is isogenous over `ℚ̄` to a quotient of `B ⊗ ℚ̄`. Cost: **medium**. -/
opaque IsQbarFactorOf [NumberField K] (A : AbelianVariety K) (B : AbelianVariety ℚ) : Prop

/-- Weight-two newforms of level `N` (Tau Ceti has newforms; Mathlib does not). Cost:
**medium** (port). -/
opaque Newform2 (N : ℕ) : Type

/-- `σ` (over `E ⊇ ℚ_ℓ`) is the `λ`-adic representation of the newform `f` for some embedding of
its coefficient field, Tate normalization: `tr σ(Frob_p) = a_p(f)` for `p ∤ Nℓ`. Cost:
**large** (Eichler–Shimura; Shimura's `A_f`; or Deligne's construction). -/
opaque IsGalRepOf {N : ℕ} (f : Newform2 N) (ℓ : ℕ) (σ : GalRep ℚ E) : Prop

/-- The ten even theta constants `z_m = θ_m(0, τ)` of a principally polarized abelian surface,
for a level-2 theta structure defined over `L`. Cost: **large** (analytic uniformization,
period matrices, theta functions; algebraicity over `L`). -/
opaque IsEvenThetaNulls {L : Type} [Field L] [NumberField L] (A : AbelianVariety K)
    (z : Fin 10 → L) : Prop

/-- `A` is a principally polarized abelian surface over `K` with an action of the maximal order
`𝒪 ⊂ (2, −3)_ℚ` of N5 L410-420 with Rosati involution `a ↦ μ⁻¹ ā μ`, and `j ∈ ℚ` is the value of
the Hauptmodul of `X₆/W` (normalized by `0, ∞, −16/27` at discriminants `−4, −3, −24`) at its
moduli point. Cost: **very large** (Shimura curves, canonical models). -/
opaque IsQMFibre [NumberField K] (A : AbelianVariety K) (j : ℚ) : Prop

/-! ## 5. Leaves stated over §4 (faithful only once §4 is genuine) -/

section Leaves

/-- **Leaf L7 (Grothendieck–Raynaud, consequence).** If `v ∤ 3`, the `3`-torsion of `A` is
rational and `A` has potentially good reduction at `v`, then `A` has good reduction at `v`.
SGA 7 I, Exp. IX: semistable reduction over `K(A[n])`, `n ≥ 3`, `v ∤ n` (Raynaud's criterion,
Prop. 4.7, UNVERIFIED number; Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5,
ASTRA-READ), and semistable plus potentially good is good (Exp. IX §3, UNVERIFIED). -/
def Leaf_RaynaudGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K) (v : Places K),
    (3 : NumberField.RingOfIntegers K) ∉ v.asIdeal → HasFullRationalTorsion A 3 →
      HasPotentiallyGoodReductionAt A v → HasGoodReductionAt A v

/-- **Leaf L8 (Néron–Ogg–Shafarevich).** Serre–Tate, Ann. of Math. 88 (1968), Thm 1
(UNVERIFIED number). -/
def Leaf_NOS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K) (v : Places K) (ℓ : ℕ)
    [Fact ℓ.Prime], (ℓ : NumberField.RingOfIntegers K) ∉ v.asIdeal →
      (HasGoodReductionAt A v ↔ (tateRep A ℓ).IsUnramifiedAt v)

/-- **Leaf L9 (rank of `Hom`).** Mumford, *Abelian varieties* (1970), §19, Thm 3 (UNVERIFIED
number): `rank Hom(A, B) ≤ 4 dim A dim B`. -/
def Leaf_MumfordRank : Prop :=
  ∀ (K : Type) [Field K] (A B : AbelianVariety K), homRank A B ≤ 4 * A.dim * B.dim

/-- **Leaf L12 (Faltings 1983, Satz 3 and Satz 4 / Korollar 1).** Over a number field, `V_ℓ(A)`
is semisimple and `Hom_K(A, B) ⊗ ℚ_ℓ ≅ Hom_{G_K}(V_ℓA, V_ℓB)`; stated through ranks, which is
equivalent given the (classical) injectivity of the comparison map. Invent. Math. 73 (1983)
(ASTRA-READ, pp. 360-361). -/
def Leaf_FaltingsTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbelianVariety K) (ℓ : ℕ) [Fact ℓ.Prime],
    (tateRep A ℓ).IsSemisimple ∧ homRank A B = (tateRep A ℓ).homDim (tateRep B ℓ)

/-- **Leaf L13 (Ribet, building blocks).** Every building block is a `ℚ̄`-factor of an abelian
variety of `GL₂`-type over `ℚ`. Ribet, *Abelian varieties over `ℚ` and modular forms* (1992;
repr. Progr. Math. 224 (2004)), and Pyle, Progr. Math. 224 (2004) (theorem numbers UNVERIFIED). -/
def Leaf_RibetBuildingBlock : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K),
    IsBuildingBlock A → ∃ B : AbelianVariety ℚ, IsGL2Type B ∧ IsQbarFactorOf A B

/-- **Leaf L14 (Khare–Wintenberger: `GL₂`-type abelian varieties over `ℚ` are modular).** Every
`2`-dimensional constituent of `V_ℓ(B) ⊗ E` is the `λ`-adic representation of a weight-two
newform. Khare–Wintenberger, Invent. Math. 178 (2009) (Serre's conjecture; with Kisin, Invent.
Math. 178 (2009) at `p = 2`), and Ribet 1992, Thm 4.4, for the implication (numbers UNVERIFIED). -/
def Leaf_KWModularity : Prop :=
  ∀ (B : AbelianVariety ℚ), IsGL2Type B →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [TopologicalSpace E] (σ : GalRep ℚ E),
      σ.n = 2 → σ.IsConstituentOf (tateRep B ℓ) → ∃ (N : ℕ) (f : Newform2 N), IsGalRepOf f ℓ σ

/-- **Leaf L15 (twists and newforms).** A finite-order twist of the representation of a newform
is the representation of a newform. Shimura 1971 Prop. 3.64 (twist of an eigenform), Li, Math.
Ann. 212 (1975) Thm 5 / Atkin–Li 1978 (newform, strong multiplicity one); proved in Tau Ceti
(`HeckeRing.GL2.Newform.primitiveTwist`, prereq-survey §1 C9). -/
def Leaf_NewformTwist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [TopologicalSpace E] (σ σ' : GalRep ℚ E)
    (N : ℕ) (f : Newform2 N), IsGalRepOf f ℓ σ → σ'.IsFiniteTwist σ →
      ∃ (N' : ℕ) (f' : Newform2 N'), IsGalRepOf f' ℓ σ'

/-- **Leaf L16 (Shimura's `A_f` and the Eichler–Shimura relation, consequence).** The
representation of a newform of level `N` is a constituent of `V_ℓ(J₁(N))`. Shimura, J. Math.
Soc. Japan 25 (1973), Thm 1; Shimura 1971, Thm 7.9 (`K_f`-linear form: Ribet 1977,
Diamond–Im 1995 §12.5) (numbers UNVERIFIED). -/
def Leaf_ShimuraAf : Prop :=
  ∀ (N : ℕ) (f : Newform2 N) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [TopologicalSpace E]
    (σ : GalRep ℚ E) (J : AbelianVariety ℚ), IsGalRepOf f ℓ σ → IsJ1 N J →
      σ.IsConstituentOf (tateRep J ℓ)

/-- **Leaf L18 (Carayol, local–global compatibility at `p ≠ ℓ`).** Carayol, Ann. Sci. ÉNS 19
(1986), Théorème (A) (UNVERIFIED that it covers `F = ℚ` at every `p ∤ ℓ`; h-trust D5). -/
def Leaf_Carayol : Prop :=
  ∀ (N : ℕ) (f : Newform2 N) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [TopologicalSpace E]
    (σ : GalRep ℚ E), IsGalRepOf f ℓ σ → ∀ p : ℕ, p.Prime → p ≠ ℓ →
      σ.condExp p = padicValNat p N

/-- **Leaf L21 (Javanpeykar, consequence for `X₁(N)`).** `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²`. Javanpeykar,
Algebra Number Theory 8 (2014), Thm 1.1.1 (`h_F(Jac X) ≤ 13·10⁶ g deg_B(X)⁵`; ASTRA-READ) with
`g, deg_B(X₁(N)) ≤ N²` (N5 L868-876). -/
def Leaf_Javanpeykar : Prop :=
  ∀ (N : ℕ) (J : AbelianVariety ℚ), 1 ≤ N → IsJ1 N J →
    faltingsHeight J ≤ 13000000 * (N : ℝ) ^ 12

/-- **Leaf L22 (Gaudron–Rémond, isogeny estimate).** If `A, B/K` are isogenous, `g = dim A`,
there is an isogeny `A → B` of degree at most
`κ(A) = ((14g)^{64g²} [K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024 g³}`, here in logarithmic form.
Duke Math. J. 163 (2014), Thm 1.4 (ASTRA-READ). -/
def Leaf_GaudronRemond : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbelianVariety K) (d₀ : ℕ),
    IsIsogenyOfDegree A B d₀ →
      ∃ d : ℕ, IsIsogenyOfDegree A B d ∧
        Real.log d ≤ 1024 * (A.dim : ℝ) ^ 3 *
          (64 * (A.dim : ℝ) ^ 2 * Real.log (14 * A.dim) + Real.log (Module.finrank ℚ K) +
            2 * Real.log (max (faltingsHeight A) (max (Real.log (Module.finrank ℚ K)) 1)))

/-- **Leaf L23 (Faltings, height variation under isogeny).** Faltings 1983, Lemma 5
(alternative: Raynaud, Astérisque 127 (1985), Exp. VII, Cor. 2.1.3) (UNVERIFIED numbers). -/
def Leaf_FaltingsIsogenyHeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbelianVariety K) (d : ℕ),
    IsIsogenyOfDegree A B d → |faltingsHeight A - faltingsHeight B| ≤ Real.log d / 2

/-- **Leaf L24 (additivity of the Faltings height).** Raynaud 1985, Exp. VII, Cor. 2.1.3
(UNVERIFIED number). -/
def Leaf_HeightAdditive : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P A Z : AbelianVariety K),
    IsProductOf P A Z → faltingsHeight P = faltingsHeight A + faltingsHeight Z

/-- **Leaf L25 (Bost's lower bound, consequence).** `h_F(A) ≥ −(3/2) dim A`. Bost, Sém. Bourbaki
795 (1996); in the form `h_F ≥ −log(π√2) dim A`: Gaudron–Rémond, Comment. Math. Helv. 89 (2014),
Cor. 8.4, or GR14 §9 (ASTRA-READ). -/
def Leaf_BostLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K),
    -(3 / 2 : ℝ) * A.dim ≤ faltingsHeight A

/-- **Leaf L26 (Pazuki, consequence in N5's normalization).** For a principally polarized abelian
surface, the even theta nulls satisfy `h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F(A))`. Pazuki, Bull. SMF 140
(2012), Cor. 1.3(2) with `g = r = 2` (ASTRA-READ); the normalization steps are N5 L934-947. The
hypothesis `IsQMFibre` stands for "principally polarized surface" (all uses are QM fibres). -/
def Leaf_Pazuki : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K) (j : ℚ) (L : Type) [Field L]
    [NumberField L] (z : Fin 10 → L), IsQMFibre A j → IsEvenThetaNulls A z →
      absLogHeightVec z ≤ 10000 * 2 ^ 24 * max 1 (faltingsHeight A)

/-- **Leaf L27 (the Hauptmodul in theta constants, consequence).** On the QM locus,
`j·(∑ z_m⁸)⁵ = 3779136·(∏ z_m)⁴`. Lin–Yang, Math. Z. 295 (2020), eqs. (13)-(14) and Example 30
(`ψ₄ = 144 j`, `χ₁₀ = −j³/4`); Igusa, Amer. J. Math. 89 (1967), pp. 833-834, 848, with
Lauter–Naehrig–Yang (2015) §2.2 for the theta expressions of `ψ₄`, `χ₁₀`; exact check
`scratch/h-v14/igusa_check.py` (h-trust F1). -/
def Leaf_IgusaLinYang : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbelianVariety K) (j : ℚ) (L : Type) [Field L]
    [NumberField L] (z : Fin 10 → L), IsQMFibre A j → IsEvenThetaNulls A z →
      (j : L) * (∑ m, z m ^ 8) ^ 5 = 3779136 * (∏ m, z m) ^ 4

end Leaves

/-- The leaves of §§3 and 5 (seventeen Props). The Shimura-curve leaves L1-L6 and L10-L11, L17
of the note are not stated: they need the definitions behind `IsQMFibre` (canonical models,
Shimura reciprocity) or schemes over `ℤ` (purity, Abhyankar), see note §3. -/
structure StatedLeaves : Prop where
  hasse : Leaf_HasseQuaternion
  hilbert : Leaf_HilbertReciprocity
  kroneckerWeber : Leaf_KroneckerWeber
  raynaud : Leaf_RaynaudGood
  nos : Leaf_NOS
  mumfordRank : Leaf_MumfordRank
  faltingsTate : Leaf_FaltingsTate
  ribet : Leaf_RibetBuildingBlock
  kw : Leaf_KWModularity
  newformTwist : Leaf_NewformTwist
  shimuraAf : Leaf_ShimuraAf
  carayol : Leaf_Carayol
  javanpeykar : Leaf_Javanpeykar
  gaudronRemond : Leaf_GaudronRemond
  faltingsIsogenyHeight : Leaf_FaltingsIsogenyHeight
  heightAdditive : Leaf_HeightAdditive
  bostLower : Leaf_BostLower
  pazuki : Leaf_Pazuki
  igusaLinYang : Leaf_IgusaLinYang

/-! ## 6. The glue

**G-top.** For admissible `S`, the leaves imply `JHeightBoundAt S`, hence (by
`ZInQ.JHeight.sixContactMin_of_jHeightBound`, proved) `SixContactMin` at `S = Mult.S_mul`.

The unstated Shimura-curve leaves enter through the glue steps G1-G5 (the fibre `A/K` of
`IsQMFibre A (J u)` exists with `[K:ℚ] ∣ 144`, `K` unramified outside `T`, good reduction outside
`T ∪ {3}`, `End⁰(A_ℚ̄) = B`): they are hypotheses of the glue in this sense, recorded in the
docstring rather than as Props. `sorry`: see the module docstring, item 6. -/

/-- The output of glue steps G1-G5 (note §4), which uses the unstated leaves L1-L6, L10-L11:
for `u ∉ 𝒞` there is a QM fibre over `J(u)` defined over a number field. Stated so that the top
theorem visibly depends on it; its proof needs the genuine `IsQMFibre`. -/
def GeometricInput : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbelianVariety K), IsQMFibre A (Jmap u)

/-- **G-top (the glue's top-level theorem).** `sorry`: the glue (note §4, G1-G20) is to be proved
over the genuine definitions of §4. -/
theorem jHeightBoundAt_of_leaves (S : Finset ℕ) (_hS : Admissible S) (_hL : StatedLeaves)
    (_hG : GeometricInput) : JHeightBoundAt S := by
  sorry

theorem contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- The final step (F4 and the numerics), as `ZInQ.JHeight.sixContactMin_of_jHeightBound`, for
an arbitrary prime set `S`. Proved. -/
theorem sixContactMinAt_of_jHeightBoundAt (S : Finset ℕ) (hJ : JHeightBoundAt S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos' _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  have hH : heightH6 (heightD : ℝ) = 2 * 10 ^ 13 * heightX heightD := rfl
  rw [hH]
  nlinarith

/-- **H from the leaves** (glue G-top followed by the proved final step). -/
theorem sixContactMinAt_of_leaves (S : Finset ℕ) (hS : Admissible S) (hL : StatedLeaves)
    (hG : GeometricInput) : SixContactMinAt S :=
  sixContactMinAt_of_jHeightBoundAt S (jHeightBoundAt_of_leaves S hS hL hG)

end ZInQ.HDecAlt
