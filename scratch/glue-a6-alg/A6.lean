-- glue-a6-alg: copy of scratch/rv-a6-route/A6.lean (namespace GlueA6Alg renamed GlueA6Alg), plus
-- (i) the algebra of scratch/glue-a6-alg/Quat.lean (namespace GlueA6Alg.Alg), (ii) a proof of
-- `QuatUnipotentTrivial`, (iii) `goodReduction_of_QM_rational3` from the three I2 leaves alone.
-- Copied from scratch/pkg-I2/I2.lean (lines 1-443, leaves and proved glue unchanged); rv-a6-route adds §10.
/-
pkg-I2: leaf statements for the reduction-theory package I2 of Theorem 4.1
(steps A5, A6, A8, C6, C10, D2 of docs/research/h-trust.md).

Every leaf is a `def … : Prop` over genuine Mathlib objects:
* abelian varieties are group objects in `Over (Spec K)` (Mathlib's `Grp`), proper, smooth and
  geometrically integral over `K`;
* points over a field extension `L/K` are morphisms `Spec L ⟶ A` over `Spec K`, with the group law
  of `CategoryTheory.MonObj.Hom.group`;
* inertia groups are Mathlib's `ValuationSubring.inertiaSubgroup`;
* good reduction is an abelian scheme (a group object in `Over (Spec O)`, proper, smooth, with
  geometrically connected fibres) whose base change along `Spec K ⟶ Spec O` is isomorphic to `A`
  in `Grp (Over (Spec K))`;
* purity and Abhyankar are stated with Mathlib's `IsRegularLocalRing`, `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`, `Algebra.QuasiFiniteAt`, `Ideal.ramificationIdx`.
No structure is invented for the purpose. No `sorry` and no `axiom` in this file.
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib

universe u

namespace GlueA6Alg.Alg

lemma three_prime : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three

lemma dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (3 : ℤ) ∣ 2 * a * y) : (3 : ℤ) ∣ y := by
  rcases three_prime.dvd_or_dvd h with h' | h'
  · rcases three_prime.dvd_or_dvd h' with h'' | h''
    · norm_num at h''
    · exact absurd h'' ha
  · exact h'

lemma nine_dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (9 : ℤ) ∣ 2 * a * y) :
    (9 : ℤ) ∣ y := by
  have h3 : (3 : ℤ) ∣ y := dvd_of_dvd_two_mul ha (dvd_trans ⟨3, by norm_num⟩ h)
  obtain ⟨y', rfl⟩ := h3
  have h' : (3 : ℤ) ∣ 2 * a * y' := by
    have : (3 : ℤ) * 3 ∣ 3 * (2 * a * y') := by
      have e : (3 : ℤ) * (2 * a * y') = 2 * a * (3 * y') := by ring
      rw [e]; simpa using h
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have := dvd_of_dvd_two_mul ha h'
  obtain ⟨z, rfl⟩ := this
  exact ⟨z, by ring⟩

lemma zmod3_aniso : ∀ x y : ZMod 3, 2 * y ^ 2 - x ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

/-- Base case: `9 ∣` every coordinate of `x²` implies `3 ∣` every coordinate of `x`. -/
lemma quat_base (a b c d : ℤ) (h1 : (9 : ℤ) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2)
    (h2 : (9 : ℤ) ∣ 2 * a * b) (h3 : (9 : ℤ) ∣ 2 * a * c) (h4 : (9 : ℤ) ∣ 2 * a * d) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d := by
  have ha : (3 : ℤ) ∣ a := by
    by_contra ha
    have hb := nine_dvd_of_dvd_two_mul ha h2
    have hc := nine_dvd_of_dvd_two_mul ha h3
    have hd := nine_dvd_of_dvd_two_mul ha h4
    have e : a ^ 2 = (a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - (2 * b) * b + (3 * c) * c
        - (6 * d) * d := by ring
    have h9 : (9 : ℤ) ∣ a ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub h1 (Dvd.dvd.mul_left hb _)) (Dvd.dvd.mul_left hc _))
        (Dvd.dvd.mul_left hd _)
    exact ha (three_prime.dvd_of_dvd_pow (dvd_trans ⟨3, by norm_num⟩ h9))
  obtain ⟨a', rfl⟩ := ha
  have hb : (3 : ℤ) ∣ b := by
    have e : 2 * b ^ 2 = ((3 * a') ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - 3 * (3 * a' ^ 2)
        + 3 * (c ^ 2) - 3 * (2 * d ^ 2) := by ring
    have h3b : (3 : ℤ) ∣ 2 * b ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub (dvd_trans ⟨3, by norm_num⟩ h1) (dvd_mul_right _ _))
        (dvd_mul_right _ _)) (dvd_mul_right _ _)
    rcases three_prime.dvd_or_dvd h3b with h | h
    · norm_num at h
    · exact three_prime.dvd_of_dvd_pow h
  obtain ⟨b', rfl⟩ := hb
  have hcd : (3 : ℤ) ∣ 2 * d ^ 2 - c ^ 2 := by
    have e : (3 : ℤ) * (2 * d ^ 2 - c ^ 2) = ((3 * a') ^ 2 + 2 * (3 * b') ^ 2 - 3 * c ^ 2
        + 6 * d ^ 2) - 9 * (a' ^ 2 + 2 * b' ^ 2) := by ring
    have : (3 : ℤ) * 3 ∣ 3 * (2 * d ^ 2 - c ^ 2) := by
      rw [e]; exact dvd_sub (by simpa using h1) (dvd_mul_right _ _)
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have hz : (((2 * d ^ 2 - c ^ 2 : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hcd)
  push_cast at hz
  obtain ⟨hc0, hd0⟩ := zmod3_aniso _ _ hz
  refine ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ?_, ?_⟩
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).mp hc0
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hd0

/-- **Valuation step (proved).** If `3^{2k}` divides every coordinate of
`(a + bi + cj + d·ij)²` in `Λ = ℤ⟨i,j⟩`, then `3^k` divides `a, b, c, d`. -/
theorem quat_sq_dvd (k : ℕ) : ∀ a b c d : ℤ,
    (3 : ℤ) ^ (2 * k) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * b → (3 : ℤ) ^ (2 * k) ∣ 2 * a * c →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * d →
    (3 : ℤ) ^ k ∣ a ∧ (3 : ℤ) ^ k ∣ b ∧ (3 : ℤ) ^ k ∣ c ∧ (3 : ℤ) ^ k ∣ d := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro a b c d h1 h2 h3 h4
    have e9 : (3 : ℤ) ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; norm_num; ring
    rw [e9] at h1 h2 h3 h4
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩ :=
      quat_base a b c d (dvd_of_mul_right_dvd h1) (dvd_of_mul_right_dvd h2)
        (dvd_of_mul_right_dvd h3) (dvd_of_mul_right_dvd h4)
    have cancel : ∀ z : ℤ, 9 * 3 ^ (2 * k) ∣ 9 * z → 3 ^ (2 * k) ∣ z := fun z hz =>
      (mul_dvd_mul_iff_left (by norm_num : (9 : ℤ) ≠ 0)).mp hz
    have := ih a' b' c' d'
      (cancel _ (by convert h1 using 1; ring)) (cancel _ (by convert h2 using 1; ring))
      (cancel _ (by convert h3 using 1; ring)) (cancel _ (by convert h4 using 1; ring))
    obtain ⟨⟨a'', rfl⟩, ⟨b'', rfl⟩, ⟨c'', rfl⟩, ⟨d'', rfl⟩⟩ := this
    exact ⟨⟨a'', by ring⟩, ⟨b'', by ring⟩, ⟨c'', by ring⟩, ⟨d'', by ring⟩⟩


/-! ## 2. Independence over `𝔽₃` -/

lemma f3_aniso : ∀ a b : ZMod 3, a ^ 2 - 2 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide

/-- Over `𝔽₃`: if `I² = 2`, `J² = 0`, `JI = -IJ` and `Jx ≠ 0`, then `x, Ix, Jx, IJx` are
linearly independent (because `a² - 2b²` is anisotropic mod 3). -/
lemma f3_indep {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] (I J : M →ₗ[ZMod 3] M)
    (hI : ∀ y, I (I y) = (2 : ZMod 3) • y) (hJ : ∀ y, J (J y) = 0)
    (hIJ : ∀ y, J (I y) = -I (J y)) (x : M) (hx : J x ≠ 0) :
    LinearIndependent (ZMod 3) ![x, I x, J x, I (J x)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have h1 : g 0 • J x - g 1 • I (J x) = 0 := by
    have := congrArg J hg
    simp only [map_add, map_smul, hJ, hIJ, map_zero, smul_neg, smul_zero,
      add_zero] at this
    linear_combination (norm := module) this
  have h2 : g 0 • I (J x) - g 1 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I h1
    simp only [map_sub, map_smul, hI, map_zero] at this
    exact this
  have k1 : (g 0 ^ 2 - 2 * g 1 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 0 • h1 + g 1 • h2
  obtain ⟨g0, g1⟩ := f3_aniso _ _ ((smul_eq_zero.mp k1).resolve_right hx)
  rw [g0, g1, zero_smul, zero_smul, zero_add, zero_add] at hg
  have h3 : g 2 • I (J x) + g 3 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I hg
    simp only [map_add, map_smul, hI, map_zero] at this
    exact this
  have k2 : (g 2 ^ 2 - 2 * g 3 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 2 • hg - g 3 • h3
  obtain ⟨g2, g3⟩ := f3_aniso _ _ ((smul_eq_zero.mp k2).resolve_right hx)
  intro i
  fin_cases i <;> assumption

/-! ## 3. The core: `T ≅ (ℤ/3^{2k})⁴` is cyclic over `Λ`, and `S - 1` is divisible by `3^k` -/

section Core

variable (k : ℕ)

abbrev Q : ℕ := 3 ^ (2 * k)

instance : NeZero (Q k) := ⟨by positivity⟩

abbrev R := ZMod (Q k)

abbrev V := Fin 4 → R k

variable {k}

/-- `φ y a = a₀ y + a₁ I y + a₂ J y + a₃ I J y`: the orbit map `Λ/q → T` at `y`. -/
def φ (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) : V k :=
  a 0 • y + a 1 • I y + a 2 • J y + a 3 • I (J y)

lemma φ_add_smul (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) (c : R k) :
    φ I J y (a + c • b) = φ I J y a + c • φ I J y b := by
  simp only [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; module

lemma φ_smul (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J y (c • a) = c • φ I J y a := by
  simp only [φ, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) :
    φ I J y (a - b) = φ I J y a - φ I J y b := by
  simp only [φ, Pi.sub_apply]; module

lemma φ_zero (I J : V k →ₗ[R k] V k) (y : V k) : φ I J y 0 = 0 := by
  simp [φ]

lemma φ_smul_left (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J (c • y) a = φ I J y (c • a) := by
  simp only [φ, map_smul, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub_left (I J : V k →ₗ[R k] V k) (y z : V k) (a : Fin 4 → R k) :
    φ I J (y - z) a = φ I J y a - φ I J z a := by
  simp only [φ, map_sub]; module

lemma Q_natCast : ((Q k : ℕ) : R k) = 0 := ZMod.natCast_self _

lemma three_pow_eq_zero : (3 : R k) ^ (2 * k) = 0 := by
  have := Q_natCast (k := k); push_cast [Q] at this; exact this

lemma three_dvd_Q (hk : 1 ≤ k) : 3 ∣ Q k := dvd_pow_self 3 (by omega)

lemma nine_dvd_Q (hk : 1 ≤ k) : 9 ∣ Q k := by
  have : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [this]; exact pow_dvd_pow 3 (by omega)

/-- If `z ≡ 0 (mod 3)` then `z = 3y`. -/
lemma eq_three_mul_of_cast_eq_zero (hk : 1 ≤ k) (z : R k)
    (hz : ZMod.castHom (three_dvd_Q hk) (ZMod 3) z = 0) : ∃ y : R k, z = 3 * y := by
  have h0 : ((z.val : ℕ) : ZMod 3) = 0 := by
    rw [← map_natCast (ZMod.castHom (three_dvd_Q hk) (ZMod 3)), ZMod.natCast_zmod_val]; exact hz
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h0
  refine ⟨(m : R k), ?_⟩
  rw [← ZMod.natCast_zmod_val z, hm]; push_cast; ring

/-- Coordinatewise reduction mod 3. -/
def red (hk : 1 ≤ k) (v : V k) : Fin 4 → ZMod 3 := fun i => ZMod.castHom (three_dvd_Q hk) (ZMod 3) (v i)

lemma red_add (hk : 1 ≤ k) (v w : V k) : red hk (v + w) = red hk v + red hk w := by
  funext i; simp only [red, Pi.add_apply, map_add]

lemma red_sub (hk : 1 ≤ k) (v w : V k) : red hk (v - w) = red hk v - red hk w := by
  funext i; simp only [red, Pi.sub_apply, map_sub]

lemma red_neg (hk : 1 ≤ k) (v : V k) : red hk (-v) = -red hk v := by
  funext i; simp only [red, Pi.neg_apply, map_neg]

lemma red_smul (hk : 1 ≤ k) (c : R k) (v : V k) :
    red hk (c • v) = ZMod.castHom (three_dvd_Q hk) (ZMod 3) c • red hk v := by
  funext i; simp only [red, Pi.smul_apply, smul_eq_mul, map_mul]

lemma eq_three_smul_of_red_eq_zero (hk : 1 ≤ k) (v : V k) (hv : red hk v = 0) :
    ∃ u : V k, v = (3 : R k) • u := by
  have h := fun i => eq_three_mul_of_cast_eq_zero hk (v i) (congrFun hv i)
  choose u hu using h
  exact ⟨u, funext fun i => by simpa using hu i⟩

/-- Lift of a vector mod 3. -/
def lift3 (y : Fin 4 → ZMod 3) : V k := fun i => ((y i).val : R k)

lemma red_lift3 (hk : 1 ≤ k) (y : Fin 4 → ZMod 3) : red hk (lift3 y) = y := by
  funext i; simp [red, lift3]

/-- The reduction of a linear map, as a matrix over `𝔽₃`. -/
noncomputable def redMap (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) :
    (Fin 4 → ZMod 3) →ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.mulVecLin ((LinearMap.toMatrix' f).map (ZMod.castHom (three_dvd_Q hk) (ZMod 3)))

lemma red_map (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) (v : V k) :
    red hk (f v) = redMap hk f (red hk v) := by
  funext i
  simp only [red, redMap, Matrix.mulVecLin_apply]
  rw [← LinearMap.toMatrix'_mulVec f v, RingHom.map_mulVec]
  rfl

/-- **Core (proved).** On `V = (ℤ/3^{2k})⁴` (`k ≥ 1`), let `I, J, S` be endomorphisms with
`I² = 2`, `J² = -3`, `JI = -IJ`, `S` commuting with `I, J` and `(S - 1)² = 0`. Then `S` is the
identity on the `3^k`-torsion. (rv-a6-route §3 steps 1-5: `V` is cyclic over `Λ` with generator
`x` (any `x` with `Jx ≢ 0 mod 3`), `S x - x = c·x` with `c² = 0` in `Λ/3^{2k}`, so `c ∈ 3^kΛ`.) -/
theorem core (hk : 1 ≤ k) (I J S : V k →ₗ[R k] V k)
    (hI : ∀ v, I (I v) = (2 : R k) • v) (hJ : ∀ v, J (J v) = (-3 : R k) • v)
    (hIJ : ∀ v, J (I v) = -I (J v))
    (hSI : ∀ v, S (I v) = I (S v)) (hSJ : ∀ v, S (J v) = J (S v))
    (hS : ∀ v, S (S v) - (2 : R k) • S v + v = 0) :
    ∀ v, (3 : R k) ^ k • v = 0 → S v = v := by
  -- the reduced relations over `𝔽₃`
  have hIb : ∀ y, redMap hk I (redMap hk I y) = (2 : ZMod 3) • y := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hI, red_smul, map_ofNat]
  have hJb : ∀ y, redMap hk J (redMap hk J y) = 0 := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hJ, red_smul]
    have : ZMod.castHom (three_dvd_Q hk) (ZMod 3) (-3 : R k) = 0 := by
      rw [map_neg, map_ofNat]; decide
    rw [this, zero_smul]
  have hIJb : ∀ y, redMap hk J (redMap hk I y) = -redMap hk I (redMap hk J y) := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, ← red_map, ← red_map, hIJ, red_neg]
  -- step 1: some `x` has `J x ≢ 0 (mod 3)`
  have hex : ∃ x : V k, red hk (J x) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := eq_three_smul_of_red_eq_zero hk _ (h (Pi.single (0 : Fin 4) (1 : R k)))
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ (h u)
    have e := hJ (Pi.single (0 : Fin 4) (1 : R k))
    rw [hu, map_smul, hu', smul_smul] at e
    have e0 := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at e0
    have e9 := congrArg (ZMod.castHom (nine_dvd_Q hk) (ZMod 9)) e0
    simp only [map_mul, map_neg, map_ofNat] at e9
    have h9 : ∀ z : ZMod 9, 3 * 3 * z ≠ -3 := by decide
    exact h9 _ e9
  obtain ⟨x, hx⟩ := hex
  have hx' : redMap hk J (red hk x) ≠ 0 := by rwa [← red_map]
  -- step 2: `x, Ix, Jx, IJx` span `V/3V`
  have hli := f3_indep (redMap hk I) (redMap hk J) hIb hJb hIJb (red hk x) hx'
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
  have mod3 : ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k, u = φ I J x a + (3 : R k) • u' := by
    intro u
    have hu : red hk u ∈ Submodule.span (ZMod 3) (Set.range ![red hk x, redMap hk I (red hk x),
        redMap hk J (red hk x), redMap hk I (redMap hk J (red hk x))]) := by
      rw [hspan]; trivial
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hu
    refine ⟨fun i => ((g i).val : R k), ?_⟩
    have hred : red hk (u - φ I J x (fun i => ((g i).val : R k))) = 0 := by
      rw [red_sub, ← hg, sub_eq_zero]
      simp only [φ, red_add, red_smul, red_map, Fin.sum_univ_four, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, map_natCast, ZMod.natCast_zmod_val]
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ hred
    exact ⟨u', by rw [← hu']; abel⟩
  -- step 2': Nakayama, `V = Λ x`
  have nak : ∀ n : ℕ, ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k,
      u = φ I J x a + (3 : R k) ^ n • u' := by
    intro n
    induction n with
    | zero => intro u; exact ⟨0, u, by rw [φ_zero, pow_zero, one_smul, zero_add]⟩
    | succ n ih =>
      intro u
      obtain ⟨a, u', h⟩ := ih u
      obtain ⟨b, u'', h'⟩ := mod3 u'
      refine ⟨a + (3 : R k) ^ n • b, u'', ?_⟩
      rw [φ_add_smul, h, h', pow_succ]; module
  have hsurj : Function.Surjective (φ I J x) := by
    intro u
    obtain ⟨a, u', h⟩ := nak (2 * k) u
    exact ⟨a, by rw [h, three_pow_eq_zero, zero_smul, add_zero]⟩
  have hinj : Function.Injective (φ I J x) := Finite.injective_iff_surjective.mpr hsurj
  have hinj0 : ∀ a, φ I J x a = 0 → a = 0 := fun a ha => hinj (by rw [ha, φ_zero])
  -- step 3: `S x - x = c x` with `c² = 0`
  have hSφ : ∀ y a, S (φ I J y a) = φ I J (S y) a := by
    intro y a; simp only [φ, map_add, map_smul, hSI, hSJ]
  obtain ⟨a, ha⟩ := hsurj (S x - x)
  have hsq : φ I J (φ I J x a) a = φ I J x ![a 0 ^ 2 + 2 * a 1 ^ 2 - 3 * a 2 ^ 2 + 6 * a 3 ^ 2,
      2 * a 0 * a 1, 2 * a 0 * a 2, 2 * a 0 * a 3] := by
    simp only [φ, map_add, map_smul, map_neg, hI, hJ, hIJ, smul_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    module
  have hNN : φ I J (φ I J x a) a = 0 := by
    rw [ha, φ_sub_left, ← hSφ, ha, map_sub]
    linear_combination (norm := module) hS x
  have hc := hinj0 _ (hsq ▸ hNN)
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have c2 := congrFun hc 2
  have c3 := congrFun hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at c0 c1 c2 c3
  -- step 4: `c ∈ 3^k Λ` (`quat_sq_dvd`)
  have hdvd : ∀ z : ℤ, (z : R k) = 0 → (3 : ℤ) ^ (2 * k) ∣ z := by
    intro z hz
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa [Q] using this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, ⟨D, hD⟩⟩ := quat_sq_dvd k ((a 0).val : ℤ) ((a 1).val : ℤ)
    ((a 2).val : ℤ) ((a 3).val : ℤ)
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c0))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c1))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c2))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c3))
  have lift : ∀ (i : Fin 4) (E : ℤ), ((a i).val : ℤ) = 3 ^ k * E → a i = (3 : R k) ^ k * (E : R k) := by
    intro i E h
    have := congrArg (fun z : ℤ => (z : R k)) h
    push_cast [ZMod.natCast_zmod_val] at this
    exact this
  have ha' : a = (3 : R k) ^ k • ![(A : R k), (B : R k), (C : R k), (D : R k)] := by
    funext i
    fin_cases i
    · simpa using lift 0 A hA
    · simpa using lift 1 B hB
    · simpa using lift 2 C hC
    · simpa using lift 3 D hD
  -- step 5: `S - 1` kills the `3^k`-torsion
  intro v hv
  obtain ⟨α, rfl⟩ := hsurj v
  have hα : (3 : R k) ^ k • α = 0 := hinj0 _ (by rw [φ_smul]; exact hv)
  have hNv : S (φ I J x α) - φ I J x α = 0 := by
    rw [hSφ, ← φ_sub_left, ← ha, ha', φ_smul, φ_smul_left, hα, φ_zero]
  exact sub_eq_zero.mp hNv

end Core


/-! ## 4. Transport from a commutative group with `G[3^{2k}] ≅ (ℤ/3^{2k})⁴` -/

section Transport

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*} [AddCommGroup M]
  (e : {x : G | x ^ q = 1} ≃ M)

open Classical in
/-- `e` extended by `0` off the `q`-torsion. -/
noncomputable def E (g : G) : M := if h : g ^ q = 1 then e ⟨g, h⟩ else 0

lemma E_mem (g : G) (h : g ^ q = 1) : E e g = e ⟨g, h⟩ := by
  simp only [E, h, dite_true]

lemma E_symm (v : M) : E e (e.symm v).1 = v := by
  rw [E_mem e _ (e.symm v).2]; simp

lemma symm_E (g : G) (h : g ^ q = 1) : (e.symm (E e g)).1 = g := by
  rw [E_mem e g h, Equiv.symm_apply_apply]

lemma E_inj (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) (h : E e a = E e b) : a = b := by
  rw [E_mem e a ha, E_mem e b hb] at h
  exact congrArg Subtype.val (e.injective h)

lemma mem_map (f : G →* G) (a : G) (ha : a ^ q = 1) : (f a) ^ q = 1 := by
  rw [← map_pow, ha, map_one]

lemma mem_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : (a * b) ^ q = 1 := by
  rw [mul_pow, ha, hb, one_mul]

lemma mem_inv (a : G) (ha : a ^ q = 1) : a⁻¹ ^ q = 1 := by
  rw [inv_pow, ha, inv_one]

lemma mem_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : (a ^ n) ^ q = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]

variable {e}
variable (he : ∀ x y : {x : G | x ^ q = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ q = 1},
  e ⟨x.1 * y.1, h⟩ = e x + e y)
include he

lemma E_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : E e (a * b) = E e a + E e b := by
  rw [E_mem e _ (mem_mul a b ha hb), E_mem e _ ha, E_mem e _ hb]
  exact he ⟨a, ha⟩ ⟨b, hb⟩ (mem_mul a b ha hb)

lemma E_one : E e (1 : G) = 0 := by
  have h := E_mul he 1 1 (one_pow _) (one_pow _)
  rw [mul_one] at h
  simpa using h

lemma E_inv (a : G) (ha : a ^ q = 1) : E e a⁻¹ = -E e a := by
  have h := E_mul he a⁻¹ a (mem_inv a ha) ha
  rw [inv_mul_cancel, E_one he] at h
  exact eq_neg_of_add_eq_zero_left h.symm

lemma E_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : E e (a ^ n) = n • E e a := by
  induction n with
  | zero => rw [pow_zero, E_one he, zero_smul]
  | succ n ih => rw [pow_succ, E_mul he _ _ (mem_pow a ha n) ha, ih, succ_nsmul]

/-- A group endomorphism, transported to an additive endomorphism of `M`. -/
noncomputable def endV (f : G →* G) : M →+ M where
  toFun v := E e (f (e.symm v).1)
  map_zero' := by
    rw [← E_one he, symm_E e 1 (one_pow _), map_one]
  map_add' v w := by
    have ha := (e.symm v).2
    have hb := (e.symm w).2
    have h1 : v + w = E e ((e.symm v).1 * (e.symm w).1) := by
      rw [E_mul he _ _ ha hb, E_symm, E_symm]
    show E e (f (e.symm (v + w)).1) = E e (f (e.symm v).1) + E e (f (e.symm w).1)
    rw [h1, symm_E e _ (mem_mul _ _ ha hb), map_mul,
      E_mul he _ _ (mem_map f _ ha) (mem_map f _ hb)]

lemma endV_E (f : G →* G) (g : G) (hg : g ^ q = 1) : endV he f (E e g) = E e (f g) := by
  show E e (f (e.symm (E e g)).1) = _
  rw [symm_E e g hg]

end Transport

/-- Extension of valuation rings (Chevalley; Mathlib `IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_valuationSubring_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) :
    ∃ w : ValuationSubring L, w.comap (algebraMap K L) = O := by
  let f : O →+* L := (algebraMap K L).comp O.subtype
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨B, ?_⟩
  ext x
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    apply hxO
    have hu : IsUnit ((f.codRestrict B.toSubring hB) ⟨x⁻¹, hinv⟩) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, ?_⟩
      apply Subtype.ext
      simp only [f, RingHom.codRestrict_apply, RingHom.comp_apply, ValuationSubring.coe_subtype,
        Subring.coe_mul, Subring.coe_one, map_inv₀]
      exact inv_mul_cancel₀ ((map_ne_zero (algebraMap K L)).mpr hx0)
    obtain ⟨⟨u, v, huv, hvu⟩, hu'⟩ := hloc.map_nonunit _ hu
    have hv : (v : K) = x := by
      have h1 : ((u : K)) * (v : K) = 1 := congrArg Subtype.val huv
      have h2 : (u : K) = x⁻¹ := congrArg Subtype.val hu'
      rw [h2] at h1
      field_simp at h1
      exact h1
    exact hv ▸ v.2
  · intro hx
    exact hB ⟨x, hx⟩

end GlueA6Alg.Alg


open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace GlueA6Alg

/-! ## 1. Purity of the branch locus (SGA 1 X 3.4; Stacks 0BMB), ring form -/

/-- **Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-! ## 2. Abelian varieties, points, Galois action, inertia, good reduction -/

section AV

variable {K : Type u} [Field K]

/-- `Spec L` as a scheme over `Spec K`. -/
noncomputable def specOver (K L : Type u) [Field K] [CommRing L] [Algebra K L] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- An abelian variety over `K`: a group object of `Over (Spec K)` whose structure morphism is
proper, smooth and geometrically integral (Mathlib's notions). Mathlib proves that such a group
object is commutative (`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
class IsAbelianVariety (A : Grp (Over (Spec (.of K)))) : Prop where
  proper : IsProper A.X.hom
  smooth : Smooth A.X.hom
  geomIntegral : GeometricallyIntegral A.X.hom

/-- An abelian scheme over a ring `O`: a group object of `Over (Spec O)`, proper, smooth, with
geometrically connected fibres (Mumford, GIT, Def. 6.1). -/
class IsAbelianScheme {O : Type u} [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) : Prop where
  proper : IsProper 𝒜.X.hom
  smooth : Smooth 𝒜.X.hom
  geomConnected : GeometricallyConnected 𝒜.X.hom

/-- The `L`-points `A(L)` of a scheme over `K`, for a `K`-algebra `L`; for a group object this
is a group (`MonObj.Hom.group`). -/
abbrev Pts (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] :=
  specOver K L ⟶ A.X

/-- The `m`-torsion `A(L)[m]`. -/
def torsion (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] (m : ℕ) :
    Set (Pts A L) :=
  {x | x ^ m = 1}

/-- The automorphism of `Spec L` over `Spec K` induced by `σ ∈ Aut(L/K)`. -/
noncomputable def galHom (L : Type u) [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) :
    specOver K L ⟶ specOver K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [specOver, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- The Galois action on points: `(σ • x)` has coordinates `σ ∘ x^*`. -/
noncomputable def galAct (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Pts A L :=
  galHom L σ ≫ x

/-- `σ` lies in the inertia group of the valuation subring `w` of `L` (Mathlib's
`ValuationSubring.inertiaSubgroup`). -/
def IsInertia {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    Prop :=
  ∃ h : σ ∈ w.decompositionSubgroup K,
    (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K

/-- `A` has good reduction at the valuation subring `O` of `K`: there is an abelian scheme over
`O` whose generic fibre is isomorphic to `A` as a group object over `K` (Serre–Tate 1968, §1). -/
def HasGoodReduction (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (.of O))), IsAbelianScheme 𝒜 ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)

/-- The inertia group of `w` acts trivially on `A(L)[m]`. -/
def InertiaTrivialOn (A : Grp (Over (Spec (.of K)))) {L : Type u} [Field L] [Algebra K L]
    (w : ValuationSubring L) (m : ℕ) : Prop :=
  ∀ σ : L ≃ₐ[K] L, IsInertia w σ → ∀ x ∈ torsion A L m, galAct A σ x = x

/-- `(σ - 1)² x = 0`, written multiplicatively (the group of points is commutative). -/
def UnipSq (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Prop :=
  galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ * (galAct A σ x)⁻¹ * x = 1

end AV

/-! ## 3. Néron–Ogg–Shafarevich and potential good reduction (Serre–Tate 1968) -/

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)


/-- Base change `A_{K'}` of a group object along a field extension `K → K'`. -/
noncomputable def baseChange {K : Type u} [Field K] (A : Grp (Over (Spec (.of K))))
    (K' : Type u) [Field K'] [Algebra K K'] : Grp (Over (Spec (.of K'))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K')))).mapGrp.obj A

/-- **Leaf I2-ST2 (Serre–Tate 1968, Thm 2; potential good reduction).** For a prime `ℓ`
invertible in `O`: `A` acquires good reduction over a finite extension `K' ⊆ K̄` (at `w ∩ K'`) iff
an open subgroup `I ∩ G_{K'}` of inertia acts trivially on every `A(K̄)[ℓⁿ]`, i.e. the image of
inertia in `Aut(T_ℓ A)` is finite. Used only on the h-b1 route for A6 (not on the route of §5 of
docs/research/pkg-I2.md). -/
def SerreTatePotentialGood : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
            (∀ x ∈ K', σ x = x) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x))

/-! ## 4. Semistable reduction: Grothendieck (SGA 7 IX 3.5, 3.6) and Raynaud (SGA 7 IX 4.7) -/

/-- **Leaf I2-SS (Grothendieck's semistable reduction theorem, monodromy form).** Consequence of
SGA 7 I, Exp. IX, Thm 3.6 (`A` acquires semistable reduction over a finite extension `K'`) and
the direction "semistable ⇒ inertia acts unipotently of echelon ≤ 2" of Prop. 3.5 (numbers
UNVERIFIED): there is a finite `K' ⊆ K̄` such that every `σ` in the inertia group of `w` fixing
`K'` satisfies `(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`.
The finite-level form is equivalent to `(σ-1)² = 0` on `T_ℓ A`, since `T_ℓ A → A[ℓⁿ]` is onto. -/
def GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-- **Leaf I2-Ray (Raynaud's criterion, Galois form).** Consequence of SGA 7 I, Exp. IX,
Prop. 4.7 (Raynaud: if `m ≥ 3` is invertible in `O` and the points of `A[m]` are rational over
`K`, then `A` has semistable reduction; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
Thm 3.5 per h-trust, ASTRA-READ there) and the direction "semistable ⇒ unipotent of echelon ≤ 2"
of SGA 7 IX Prop. 3.5 (numbers UNVERIFIED): every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`. -/
def RaynaudCriterion : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 5. Néron mapping property for abelian schemes, and reduction of torsion -/

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

section Reduction

variable {K : Type u} [Field K]

/-- The ring map `O → w` for a valuation ring `w` of `L` lying over `O`. -/
def toW {L : Type u} [Field L] [Algebra K L] (O : ValuationSubring K) (w : ValuationSubring L)
    (hw : w.comap (algebraMap K L) = O) : O →+* w :=
  ((algebraMap K L).comp O.subtype).codRestrict w.toSubring (fun x => by
    have : (x : K) ∈ w.comap (algebraMap K L) := by rw [hw]; exact x.2
    exact this)

/-- `y ∈ 𝒜(κ(w))` is the reduction of `x ∈ A(L)`: some `x̃ ∈ 𝒜(w)` restricts to `x` on the
generic point (through `e : 𝒜_K ≅ A`) and to `y` on the closed point. -/
def IsReductionOf {L : Type u} [Field L] [Algebra K L] {O : ValuationSubring K}
    {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (w : ValuationSubring L) (hw : w.comap (algebraMap K L) = O) (x : Pts A L)
    (y : Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue w).comp (toW O w hw)))) ⟶ 𝒜.X) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X,
    (x ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left ∧
    y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left

end Reduction

/-- **Leaf I2-Red (reduction of prime-to-`p` torsion at good reduction).** Serre–Tate 1968, §1
(proof of Thm 1, (a) ⇒ (b); locator UNVERIFIED): if `A` has good reduction with abelian scheme
`𝒜` and `m ≥ 1` is invertible in `O`, reduction is a bijection
`A(K̄)[m] → 𝒜(κ(w))[m]`. -/
def ReductionTorsionBijective : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (m : ℕ), 0 < m → IsUnit (m : O) →
      (∀ x ∈ torsion A (AlgebraicClosure K) m,
        ∃! y, y ^ m = 1 ∧ IsReductionOf 𝒜 e w hw x y) ∧
      (∀ y, y ^ m = 1 → ∃! x, x ∈ torsion A (AlgebraicClosure K) m ∧ IsReductionOf 𝒜 e w hw x y)

/-! ## 6. Structure of torsion (Mumford, *Abelian varieties*, §4) -/

/-- **Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space. -/
def TorsionStructure : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-! ## 7. Abhyankar's lemma for discrete valuation rings -/

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)


/-! ## 8. Characteristic polynomial independent of `ℓ` (Mumford §19, Thm 4; boundary with I3) -/

/-- **Leaf I2-Char (Mumford, *Abelian varieties*, §19, Thm 4; locator UNVERIFIED).** For an
endomorphism `φ` of an abelian variety `B` of dimension `g` over a field `k` there is a monic
`P ∈ ℤ[X]` of degree `2g` which, for every prime `ℓ ≠ char k`, is the characteristic polynomial of
`φ` on `T_ℓ B`; finite-level form: reduced mod `ℓⁿ` it is the characteristic polynomial of the
matrix of `φ` on `B(k̄)[ℓⁿ]` in any `ℤ/ℓⁿ`-basis. Used in C10 (the trace of `Frob ∘ μ̄_σ` is one
integer for all `ℓ`). -/
def CharpolyIndependentOfEll : Prop :=
  ∀ (k : Type u) [Field k] (B : Grp (Over (Spec (.of k)))) [IsAbelianVariety B] (g : ℕ),
    topologicalKrullDim B.X.left = (g : WithBot ℕ∞) → ∀ φ : B ⟶ B,
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * g ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ n : ℕ, 0 < n →
        ∀ e : torsion B (AlgebraicClosure k) (ℓ ^ n) ≃ (Fin (2 * g) → ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n),
          ∀ h : x.1 * y.1 ∈ torsion B (AlgebraicClosure k) (ℓ ^ n),
            e ⟨x.1 * y.1, h⟩ = e x + e y) →
        ∀ M : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n), y.1 = x.1 ≫ φ.hom.hom →
          e y = M.mulVec (e x)) →
        M.charpoly = P.map (Int.castRingHom (ZMod (ℓ ^ n)))

/-- **Leaf I2-Rank (Mumford, *Abelian varieties*, §19, Thm 3, rank part; boundary with I3;
locator UNVERIFIED).** For abelian varieties `A, B` over `k` of dimensions `g, g'`, the group of
homomorphisms `A → B` has rank at most `4gg'`: any `4gg' + 1` homomorphisms are `ℤ`-linearly
dependent in the (commutative) group `A.X ⟶ B.X`. Used in A8 (`r ≤ 16F₀²`). The instance argument
`IsCommMonObj B.X` holds for every abelian variety (Mathlib,
`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
def HomRankBound : Prop :=
  ∀ (k : Type u) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B] [IsCommMonObj B.X] (g g' : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) →
    topologicalKrullDim B.X.left = (g' : WithBot ℕ∞) →
    ∀ f : Fin (4 * g * g' + 1) → (A ⟶ B),
      ∃ c : Fin (4 * g * g' + 1) → ℤ, c ≠ 0 ∧ ∏ i, (f i).hom.hom ^ c i = 1

/-! ## 9. Glue proved from the leaves -/

section Glue

variable {K : Type u} [Field K]

lemma galAct_mul (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x y : Pts A L) : galAct A σ (x * y) = galAct A σ x * galAct A σ y :=
  MonObj.comp_mul _ _ _

lemma galAct_inv (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : galAct A σ x⁻¹ = (galAct A σ x)⁻¹ :=
  GrpObj.comp_inv _ _

lemma galAct_pow (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) (n : ℕ) : galAct A σ (x ^ n) = (galAct A σ x) ^ n :=
  MonObj.comp_pow _ _ _

lemma galAct_one (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : galAct A σ 1 = 1 :=
  MonObj.comp_one _

/-- **Glue C6/A8 (proved).** Good reduction at `O` makes inertia act trivially on `A[ℓⁿ]` for
every prime `ℓ` invertible in `O` (NOS, (a) ⇒ (b)): `r_ℓ` is unramified at such places. -/
theorem inertiaTrivial_of_goodReduction (hNOS : NeronOggShafarevich.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n : ℕ) :
    InertiaTrivialOn A w (ℓ ^ n) :=
  ((hNOS K O w hw A).1.mp hA) (ℓ ^ n) (pow_pos hℓ.pos n) (by
    rw [Nat.cast_pow]; exact hℓO.pow n)

/-- Algebraic core of D2 (proved): in a commutative group of points, if `σ` satisfies
`(σ - 1)² x = 0`, `x` has order dividing `ℓⁿ`, and `σ^{pᵃ} x = x` with `p` prime to `ℓ`,
then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate (A : Grp (Over (Spec (.of K)))) [IsCommMonObj A.X]
    {L : Type u} [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) (x : Pts A L) (ℓ n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n)) (hx : x ∈ torsion A L (ℓ ^ n))
    (hu : UnipSq A σ x) (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  set N := galAct A σ x * x⁻¹ with hN
  have hσN : galAct A σ N = N := by
    rw [hN, galAct_mul, galAct_inv]
    unfold UnipSq at hu
    have h2 : galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ =
        ((galAct A σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (galAct A σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, galAct_mul, galAct_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (p ^ a) = 1 := by
    have := hiter (p ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    have hx' : x ^ (ℓ ^ n) = 1 := hx
    rw [hN, mul_pow, ← galAct_pow, hx', galAct_one, inv_pow, hx']; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue D2 (proved from Raynaud).** At a place of residue characteristic `p` where `A[m]` is
rational (`m ≥ 3` prime to `p`), every inertia element `σ` that acts on a point `x ∈ A[ℓⁿ]`
(`ℓ ≠ p`) with `p`-power order fixes it. Applied to wild inertia (pro-`p`, and the action on the
finite set `A[ℓⁿ]` factors through a finite quotient), this is D2's "wild inertia acts
trivially on `V_ℓ(A)`". The two facts in parentheses are I6/glue. -/
theorem D2_fixed_of_raynaud (hRay : RaynaudCriterion.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ) (hm : 3 ≤ m)
    (hmO : IsUnit (m : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : IsInertia w σ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n))
    (x : Pts A (AlgebraicClosure K)) (hx : x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n))
    (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  exact fixed_of_unipSq_of_iterate A σ x ℓ n p a hcop hx
    (hRay K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx) hit

/-! ## 10. rv-a6-route: A6 (Lemma PR(ii)) by the Raynaud route, from the leaves plus one
pure-algebra glue statement -/

/-- **Glue (pure algebra, not a leaf; to be proved by the project).** Let `G` be a commutative
group whose `3^{2k}`-torsion `T` is isomorphic to `(ℤ/3^{2k})⁴` (`k ≥ 1`), with endomorphisms
`I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` (so `T` is a module over `Λ = ℤ⟨i,j⟩`, whose
`3`-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`), and an
endomorphism `S` commuting with `I, J` with `(S - 1)² = 0` on `T`. Then `S` is the identity on
the `3^k`-torsion. Proof (docs/research/rv-a6-route.md §3): `T/JT` is an `𝔽₉`-space of dimension
1 (dimension 2 would force `J = 3J'` on the free `ℤ/3^{2k}`-module `T`, whence `3·unit = 0`), so
`T` is cyclic, hence free of rank one over `Λ/3^{2k}` by counting; `S - 1` is right
multiplication by some `c` with `c² = 0`, so `v_Π(c) ≥ 2k`, `c ∈ 3^kΛ`, and `S - 1` kills
`3^k T = G[3^k]`. -/
def QuatUnipotentTrivial : Prop :=
  ∀ (G : Type u) [CommGroup G] (k : ℕ), 1 ≤ k → ∀ (I J S : G →* G),
    (∀ x, I (I x) = x ^ 2) → (∀ x, J (J x) * x ^ 3 = 1) → (∀ x, J (I x) * I (J x) = 1) →
    (∀ x, S (I x) = I (S x)) → (∀ x, S (J x) = J (S x)) →
    (∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y) →
    (∀ x, x ^ (3 ^ (2 * k)) = 1 → S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1) →
    ∀ x, x ^ (3 ^ k) = 1 → S x = x

open GlueA6Alg.Alg in
/-- **`QuatUnipotentTrivial` (proved).** -/
theorem quatUnipotentTrivial : QuatUnipotentTrivial.{u} := by
  intro G _ k hk I J S hI hJ hIJ hSI hSJ ⟨e₀, he₀⟩ hS x hx
  let e : {x : G | x ^ (Q k) = 1} ≃ V k := e₀
  have he : ∀ x y : {x : G | x ^ (Q k) = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ (Q k) = 1},
      e ⟨x.1 * y.1, h⟩ = e x + e y := he₀
  -- every `v` is `E a` with `a ∈ G[q]`
  have hv : ∀ v : V k, ∃ a : G, a ^ (Q k) = 1 ∧ E e a = v :=
    fun v => ⟨_, (e.symm v).2, E_symm e v⟩
  let IV := (endV he I).toZModLinearMap (Q k)
  let JV := (endV he J).toZModLinearMap (Q k)
  let SV := (endV he S).toZModLinearMap (Q k)
  have hIV : ∀ g, g ^ (Q k) = 1 → IV (E e g) = E e (I g) := fun g hg => endV_E he I g hg
  have hJV : ∀ g, g ^ (Q k) = 1 → JV (E e g) = E e (J g) := fun g hg => endV_E he J g hg
  have hSV : ∀ g, g ^ (Q k) = 1 → SV (E e g) = E e (S g) := fun g hg => endV_E he S g hg
  have mI := mem_map (q := Q k) I
  have mJ := mem_map (q := Q k) J
  have mS := mem_map (q := Q k) S
  have key := core hk IV JV SV
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hIV _ (mI a ha), hI, E_pow he a ha, two_smul, two_smul])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hJV _ (mJ a ha)]
      have h := congrArg (E e) (hJ a)
      rw [E_mul he _ _ (mJ _ (mJ a ha)) (mem_pow a ha 3), E_pow he a ha, E_one he] at h
      rw [neg_smul, ofNat_smul_eq_nsmul]
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hJV _ (mI a ha), hJV a ha, hIV _ (mJ a ha)]
      have h := congrArg (E e) (hIJ a)
      rw [E_mul he _ _ (mJ _ (mI a ha)) (mI _ (mJ a ha)), E_one he] at h
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hSV _ (mI a ha), hSV a ha, hIV _ (mS a ha), hSI])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hSV _ (mJ a ha), hSV a ha, hJV _ (mS a ha), hSJ])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hSV a ha, hSV _ (mS a ha)]
      have h := congrArg (E e) (hS a ha)
      have m1 := mS _ (mS a ha)
      have m2 := mem_inv _ (mS a ha)
      rw [E_mul he _ _ (mem_mul _ _ (mem_mul _ _ m1 m2) m2) ha,
        E_mul he _ _ (mem_mul _ _ m1 m2) m2, E_mul he _ _ m1 m2, E_inv he _ (mS a ha),
        E_one he] at h
      rw [← h]; module)
  have hxq : x ^ (Q k) = 1 := by
    show x ^ (3 ^ (2 * k)) = 1
    rw [two_mul, pow_add, pow_mul, hx, one_pow]
  have h3 : (3 : R k) ^ k • E e x = 0 := by
    have : (3 : R k) ^ k = ((3 ^ k : ℕ) : R k) := by push_cast; rfl
    rw [this, Nat.cast_smul_eq_nsmul, ← E_pow he x hxq, hx, E_one he]
  have := key (E e x) h3
  rw [hSV x hxq] at this
  exact E_inj e _ _ (mS x hxq) hxq this


section A6

/-- The Galois action of `σ` as a group endomorphism of `A(L)`. -/
noncomputable def galHomPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (σ : L ≃ₐ[K] L) : Pts A L →* Pts A L where
  toFun := galAct A σ
  map_one' := galAct_one A σ
  map_mul' := galAct_mul A σ

/-- A homomorphism of group objects `f : A ⟶ A` as a group endomorphism of `A(L)`. -/
noncomputable def endPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (f : A ⟶ A) : Pts A L →* Pts A L where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' x y := MonObj.mul_comp x y _

/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` and the pure-algebra glue `QuatUnipotentTrivial`.**
Same statement as `PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3_of_alg (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (hAlg : QuatUnipotentTrivial.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have h3' : IsUnit ((3 : ℕ) : O) := by exact_mod_cast h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    apply h3.ne_zero
    apply Subtype.val_injective
    have h' : (3 : K) = 0 := by exact_mod_cast h
    have e3 : ((3 : O) : K) = 3 := rfl
    rw [e3, h']
    rfl
  -- inertia acts trivially on `A[3^k]` for every `k ≥ 1`
  have key : ∀ k : ℕ, 1 ≤ k → InertiaTrivialOn A w (3 ^ k) := by
    intro k hk σ hσ x hx
    obtain ⟨e, he⟩ := hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K)
    exact hAlg (Pts A (AlgebraicClosure K)) k hk (endPts A I) (endPts A J) (galHomPts A σ)
      hI hJ hIJ (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      ⟨e, he⟩ (fun y hy => hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
        (2 * k) y hy) x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a)
  refine (hNOS K O w hw A).2.mpr ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the three I2 leaves
`NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure` alone** (the pure-algebra glue
`QuatUnipotentTrivial` is now a theorem). Same statement as
`PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3 (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O :=
  goodReduction_of_QM_rational3_of_alg hNOS hRay hTors quatUnipotentTrivial O w hw A hdim I J
    hI hJ hIJ h3 hrat

/-- **A6 without the auxiliary `w`**: the valuation subring of `K̄` over `O` exists
(`Alg.exists_valuationSubring_comap_eq`), so it is not a hypothesis. -/
theorem goodReduction_of_QM_rational3' (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  obtain ⟨w, hw⟩ := Alg.exists_valuationSubring_comap_eq (L := AlgebraicClosure K) O
  exact goodReduction_of_QM_rational3 hNOS hRay hTors O w hw A hdim I J hI hJ hIJ h3 hrat

end A6

end Glue

end GlueA6Alg

#print axioms GlueA6Alg.quatUnipotentTrivial
#print axioms GlueA6Alg.goodReduction_of_QM_rational3
#print axioms GlueA6Alg.goodReduction_of_QM_rational3'
