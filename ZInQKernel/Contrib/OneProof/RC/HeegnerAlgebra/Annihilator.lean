import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 1: one uniform torsion annihilator and the matrix span

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 1 "One uniform torsion annihilator", tex lines 2881–2912.

Elliot's text.  By the non-CM open-image theorem choose `n ≥ 2` with
`1 + 2^n M₂(ℤ₂) ⊂ ρ_T(G_ℚ)` and `g ∈ G_ℚ` with `ρ_T(g) = u I`, `u = 1 + 2^n`.  For a complex
conjugation `τ` put `z = g² τ g² τ⁻¹` and `e = v₂(u⁴ - 1) = n + 2` (H1).  The element `g²` fixes
every quadratic field, its image in the abelian group `Gal(H_d/K)` is inverted by `τ`, so `z` fixes
every ring-class field `H_d`, while `ρ_T(z) = u⁴ I`; hence `2^e E(H_d)[2^∞] = 0` (H2).  For the matrix
span, the squares of preimages of `I + 2^n E₁₁`, `I + 2^n E₁₂`, `I + 2^n E₂₁` together with `I`
have `ℤ₂`-span containing `2^{n+1} M₂(ℤ₂)`, because `1 + 2^{n-1}` is odd.

Everything in this file is `PROVED` (Lean proofs).  The arithmetic inputs (Serre's open image
theorem, the identification of `E(H_d)[2^∞]` with the fixed points of `G_{H_d}` on `E[2^∞]`, and the
fact that `Gal(H_d/ℚ)` is generalized dihedral) enter as explicit hypotheses of the abstract
statements: they are the `PRINT`/`GLUE` inputs, stated in the interface file.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Matrix

/-! ## (H1): `e = v₂(u⁴ - 1) = n + 2` for `u = 1 + 2^n`, `n ≥ 2` -/

/-- (H1), tex 2884–2887, `PROVED`.  For `n = k + 2 ≥ 2` and `u = 1 + 2^n`,
`u⁴ - 1 = 2^{n+2} · o` with the explicit odd cofactor `o = 1 + 6·2^k + 16·4^k + 16·8^k`. -/
theorem H1_factor (k : ℕ) :
    ((1 : ℤ) + 2 ^ (k + 2)) ^ 4 - 1 =
      2 ^ ((k + 2) + 2) * (1 + 6 * 2 ^ k + 16 * (2 ^ k) ^ 2 + 16 * (2 ^ k) ^ 3) := by
  ring

/-- The cofactor in `H1_factor` is odd. -/
theorem H1_cofactor_odd (k : ℕ) :
    Odd ((1 : ℤ) + 6 * 2 ^ k + 16 * (2 ^ k) ^ 2 + 16 * (2 ^ k) ^ 3) :=
  ⟨3 * 2 ^ k + 8 * (2 ^ k) ^ 2 + 8 * (2 ^ k) ^ 3, by ring⟩

/-- (H1), tex 2887, `PROVED`: for `n ≥ 2`, `u⁴ - 1 = 2^{n+2} · o` with `o` odd. -/
theorem H1_exists_odd (n : ℕ) (hn : 2 ≤ n) :
    ∃ o : ℤ, Odd o ∧ ((1 : ℤ) + 2 ^ n) ^ 4 - 1 = 2 ^ (n + 2) * o := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact ⟨_, H1_cofactor_odd k, H1_factor k⟩

/-- (H1), tex 2887, `PROVED`: `e = v₂(u⁴ - 1) = n + 2` for `u = 1 + 2^n`, `n ≥ 2`. -/
theorem H1_padicVal (n : ℕ) (hn : 2 ≤ n) :
    padicValInt 2 (((1 : ℤ) + 2 ^ n) ^ 4 - 1) = n + 2 := by
  obtain ⟨o, ho, h⟩ := H1_exists_odd n hn
  rw [h]
  have ho0 : o ≠ 0 := by rintro rfl; simp at ho
  have h2 : ((2 : ℤ) ^ (n + 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValInt.mul h2 ho0]
  have hodd : ¬ (2 : ℤ) ∣ o := by
    rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ho
  rw [padicValInt.eq_zero_of_not_dvd hodd, add_zero]
  have : ((2 : ℤ) ^ (n + 2)) = ((2 ^ (n + 2) : ℕ) : ℤ) := by norm_cast
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- Negative control for (H1): the hypothesis `n ≥ 2` is needed.  For `n = 1`, `u = 3` and
`2^{n+3} = 16` divides `u⁴ - 1 = 80`, so `v₂(u⁴ - 1) = 4 ≠ n + 2`. `PROVED`. -/
theorem H1_fails_at_one : padicValInt 2 (((1 : ℤ) + 2 ^ 1) ^ 4 - 1) ≠ 1 + 2 := by
  have : ((1 : ℤ) + 2 ^ 1) ^ 4 - 1 = 2 ^ 4 * 5 := by norm_num
  rw [this, padicValInt.mul (by norm_num) (by norm_num),
    padicValInt.eq_zero_of_not_dvd (by decide : ¬ ((2 : ℕ) : ℤ) ∣ 5)]
  have h16 : ((2 : ℤ) ^ 4) = ((2 ^ 4 : ℕ) : ℤ) := by norm_cast
  rw [h16, padicValInt.of_nat, padicValNat.prime_pow]
  norm_num

/-! ## (H2): the element `z` and the annihilator `2^e` -/

/-- tex 2889, `PROVED`: squares lie in every index-two subgroup ("`g²` fixes every quadratic
field": `G_K` has index two in `G_ℚ`). -/
theorem sq_mem_of_index_two {G : Type*} [Group G] (GK : Subgroup G) (h : GK.index = 2) (g : G) :
    g ^ 2 ∈ GK :=
  Subgroup.sq_mem_of_index_two h g

/-- tex 2889–2892, `PROVED`.  Let `N = G_{H_d}` be normal in `G = G_ℚ` and contained in `G_K`, and
let complex conjugation `τ` invert the image of `G_K` in `G/N` ("its image in the abelian group
`Gal(H_d/K)` is inverted by `τ`": `τ x τ⁻¹ ≡ x⁻¹ (mod N)` for `x ∈ G_K`).  If `g² ∈ G_K`, then
`z = g² τ g² τ⁻¹ ∈ N`, i.e. `z` fixes `H_d`. -/
theorem z_mem_of_inverted {G : Type*} [Group G] (N GK : Subgroup G) [N.Normal]
    (τ : G) (hτ : ∀ x ∈ GK, τ * x * τ⁻¹ * x ∈ N) (g : G) (hg : g ^ 2 ∈ GK) :
    g ^ 2 * τ * g ^ 2 * τ⁻¹ ∈ N := by
  have h1 := hτ _ hg
  have h2 := Subgroup.Normal.conj_mem ‹N.Normal› _ h1 (g ^ 2)
  have : g ^ 2 * (τ * g ^ 2 * τ⁻¹ * g ^ 2) * (g ^ 2)⁻¹ = g ^ 2 * τ * g ^ 2 * τ⁻¹ := by group
  rwa [this] at h2

/-- tex 2892, `PROVED`: if `ρ(g)` is central (here `ρ_T(g) = uI`), then `ρ(z) = ρ(g)⁴`
(here `u⁴ I`). -/
theorem rho_z {G M : Type*} [Group G] [Group M] (ρ : G →* M) (g τ : G)
    (hc : ∀ x : M, Commute (ρ g) x) :
    ρ (g ^ 2 * τ * g ^ 2 * τ⁻¹) = ρ g ^ 4 := by
  simp only [map_mul, map_pow, map_inv]
  have h : ρ g ^ 2 * ρ τ = ρ τ * ρ g ^ 2 := ((hc (ρ τ)).pow_left 2)
  calc ρ g ^ 2 * ρ τ * ρ g ^ 2 * (ρ τ)⁻¹ = ρ g ^ 2 * (ρ τ * ρ g ^ 2) * (ρ τ)⁻¹ := by group
    _ = ρ g ^ 2 * (ρ g ^ 2 * ρ τ) * (ρ τ)⁻¹ := by rw [h]
    _ = ρ g ^ 4 := by group

/-- (H2) arithmetic core, tex 2892–2895, `PROVED`: a `2`-primary element killed by `u⁴ - 1`
(`u = 1 + 2^n`, `n ≥ 2`) is killed by `2^e`, `e = n + 2`. -/
theorem H2_of_scalar {V : Type*} [AddCommGroup V] (n : ℕ) (hn : 2 ≤ n) (P : V)
    (hu : (((1 : ℤ) + 2 ^ n) ^ 4 - 1) • P = 0) (htors : ∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) :
    ((2 : ℤ) ^ (n + 2)) • P = 0 := by
  obtain ⟨o, ho, h⟩ := H1_exists_odd n hn
  obtain ⟨k, hk⟩ := htors
  rw [h, mul_comm, mul_smul] at hu
  have hcop : IsCoprime o ((2 : ℤ) ^ k) := by
    obtain ⟨m, rfl⟩ := ho
    exact IsCoprime.pow_right ⟨1, -m, by ring⟩
  obtain ⟨a, b, hab⟩ := hcop
  have hk' : ((2 : ℤ) ^ k) • (((2 : ℤ) ^ (n + 2)) • P) = 0 := by
    rw [smul_comm, hk, smul_zero]
  calc ((2 : ℤ) ^ (n + 2)) • P = (a * o + b * 2 ^ k) • (((2 : ℤ) ^ (n + 2)) • P) := by
        rw [hab, one_smul]
    _ = a • (o • (((2 : ℤ) ^ (n + 2)) • P)) + b • (((2 : ℤ) ^ k) • (((2 : ℤ) ^ (n + 2)) • P)) := by
        rw [add_smul, mul_smul, mul_smul]
    _ = 0 := by rw [hu, hk', smul_zero, smul_zero, add_zero]

/-- (H2), tex 2889–2900, `PROVED`, abstract form.  `G = G_ℚ` acts on `V = E[2^∞](ℚ̄)`;
`N = G_{H_d}` (or the Galois group of any compositum of ring-class fields, i.e. an intersection
of such groups); `z ∈ N` acts on `V` as the scalar `u⁴` (`ρ_T(z) = u⁴ I`).  Then every
`N`-fixed `2`-primary element (a point of `E(H_d)[2^∞]`) is killed by `2^e`, `e = n + 2`. -/
theorem H2_abstract {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (N : Subgroup G) (z : G) (hz : z ∈ N) (n : ℕ) (hn : 2 ≤ n)
    (hscalar : ∀ v : V, z • v = (((1 : ℤ) + 2 ^ n) ^ 4) • v)
    (P : V) (hP : ∀ x ∈ N, x • P = P) (htors : ∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) :
    ((2 : ℤ) ^ (n + 2)) • P = 0 := by
  apply H2_of_scalar n hn P _ htors
  have h1 := hP z hz
  rw [hscalar] at h1
  rw [sub_smul, h1, one_smul, sub_self]

/-- (H2) assembled, tex 2881–2900, `PROVED`: from the generalized-dihedral structure of
`Gal(H_d/ℚ)` (hypothesis `hτ`), `G_K` of index two, `ρ_T(g)` central and acting as the scalar `u`,
every point of `E(H_d)[2^∞]` (the `N`-fixed `2`-primary elements) is killed by `2^{n+2}`.  The
bound does not depend on `d`, on `K`, or on the number of conductor primes. -/
theorem H2_ringClass {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (N GK : Subgroup G) [N.Normal] (hK : GK.index = 2) (τ : G)
    (hτ : ∀ x ∈ GK, τ * x * τ⁻¹ * x ∈ N) (n : ℕ) (hn : 2 ≤ n) (g : G)
    (hg : ∀ v : V, g • v = ((1 : ℤ) + 2 ^ n) • v)
    (P : V) (hP : ∀ x ∈ N, x • P = P) (htors : ∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) :
    ((2 : ℤ) ^ (n + 2)) • P = 0 := by
  have hz := z_mem_of_inverted N GK τ hτ g (sq_mem_of_index_two GK hK g)
  refine H2_abstract N _ hz n hn ?_ P hP htors
  intro v
  -- `g` acts as the integer scalar `u`, which commutes with the action of `τ`
  have hg2 : ∀ w : V, (g ^ 2) • w = (((1 : ℤ) + 2 ^ n) ^ 2) • w := by
    intro w; rw [pow_two, mul_smul, hg, hg, smul_comm, ← mul_smul, ← pow_two]
  have hcomm : ∀ (m : ℤ) (x : G) (w : V), x • (m • w) = m • (x • w) := fun m x w =>
    (smul_comm x m w)
  calc (g ^ 2 * τ * g ^ 2 * τ⁻¹) • v = (g ^ 2) • (τ • ((g ^ 2) • (τ⁻¹ • v))) := by
        simp only [mul_smul]
    _ = (((1 : ℤ) + 2 ^ n) ^ 2) • (τ • ((((1 : ℤ) + 2 ^ n) ^ 2) • (τ⁻¹ • v))) := by
        rw [hg2, hg2]
    _ = (((1 : ℤ) + 2 ^ n) ^ 4) • v := by
        rw [hcomm, smul_inv_smul, ← mul_smul]; ring_nf

/-! ## The matrix span (tex 2902–2912) -/

/-- The matrix units `E₁₁, E₁₂, E₂₁` of `M₂` (manuscript indexing). -/
def E11 (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]
/-- The matrix unit `E₁₂`. -/
def E12 (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
/-- The matrix unit `E₂₁`. -/
def E21 (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]
/-- The matrix unit `E₂₂`. -/
def E22 (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

/-- tex 2906–2908, `PROVED`: `(I + 2^n E₁₁)² = I + (2^{n+1} + 2^{2n}) E₁₁`. -/
theorem sq_E11 {R : Type*} [CommRing R] (n : ℕ) :
    (1 + (2 : R) ^ n • E11 R) ^ 2 = 1 + ((2 : R) ^ (n + 1) + (2 : R) ^ (2 * n)) • E11 R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E11, pow_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- tex 2906–2908, `PROVED`: `(I + 2^n E₁₂)² = I + 2^{n+1} E₁₂`. -/
theorem sq_E12 {R : Type*} [CommRing R] (n : ℕ) :
    (1 + (2 : R) ^ n • E12 R) ^ 2 = 1 + (2 : R) ^ (n + 1) • E12 R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E12, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- tex 2906–2908, `PROVED`: `(I + 2^n E₂₁)² = I + 2^{n+1} E₂₁`. -/
theorem sq_E21 {R : Type*} [CommRing R] (n : ℕ) :
    (1 + (2 : R) ^ n • E21 R) ^ 2 = 1 + (2 : R) ^ (n + 1) • E21 R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E21, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The four matrices of tex 2906–2908: `I` and the squares of `I + 2^n E₁₁`, `I + 2^n E₁₂`,
`I + 2^n E₂₁`. -/
def spanSet (R : Type*) [CommRing R] (n : ℕ) : Set (Matrix (Fin 2) (Fin 2) R) :=
  {1, (1 + (2 : R) ^ n • E11 R) ^ 2, (1 + (2 : R) ^ n • E12 R) ^ 2, (1 + (2 : R) ^ n • E21 R) ^ 2}

/-- The matrix span, tex 2910–2912, `PROVED`, over any commutative ring in which `1 + 2^{n-1}` is
a unit ("use that `1 + 2^{n-1}` is odd"): the span of the four matrices contains
`2^{n+1} M₂(R)`. -/
theorem matrix_span {R : Type*} [CommRing R] (n : ℕ) (hn : 1 ≤ n)
    (hu : IsUnit ((1 : R) + 2 ^ (n - 1))) (M : Matrix (Fin 2) (Fin 2) R) :
    (2 : R) ^ (n + 1) • M ∈ Submodule.span R (spanSet R n) := by
  set S := Submodule.span R (spanSet R n)
  have h1 : (1 : Matrix (Fin 2) (Fin 2) R) ∈ S := Submodule.subset_span (by simp [spanSet])
  have hA : (1 + (2 : R) ^ n • E11 R) ^ 2 ∈ S := Submodule.subset_span (by simp [spanSet])
  have hB : (1 + (2 : R) ^ n • E12 R) ^ 2 ∈ S := Submodule.subset_span (by simp [spanSet])
  have hC : (1 + (2 : R) ^ n • E21 R) ^ 2 ∈ S := Submodule.subset_span (by simp [spanSet])
  obtain ⟨u, hu'⟩ := hu
  have e11 : (2 : R) ^ (n + 1) • E11 R ∈ S := by
    have hsub := S.sub_mem hA h1
    rw [sq_E11, add_sub_cancel_left] at hsub
    have h2n : (2 : R) ^ (n + 1) + (2 : R) ^ (2 * n) = (2 : R) ^ (n + 1) * (1 + 2 ^ (n - 1)) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    rw [h2n, ← hu'] at hsub
    have := S.smul_mem (↑u⁻¹ : R) hsub
    rwa [smul_smul, mul_comm, mul_assoc, Units.mul_inv, mul_one] at this
  have e12 : (2 : R) ^ (n + 1) • E12 R ∈ S := by
    have hsub := S.sub_mem hB h1; rwa [sq_E12, add_sub_cancel_left] at hsub
  have e21 : (2 : R) ^ (n + 1) • E21 R ∈ S := by
    have hsub := S.sub_mem hC h1; rwa [sq_E21, add_sub_cancel_left] at hsub
  have e22 : (2 : R) ^ (n + 1) • E22 R ∈ S := by
    have hsub := S.sub_mem (S.smul_mem ((2 : R) ^ (n + 1)) h1) e11
    have : (2 : R) ^ (n + 1) • (1 : Matrix (Fin 2) (Fin 2) R) - (2 : R) ^ (n + 1) • E11 R =
        (2 : R) ^ (n + 1) • E22 R := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E22]
    rwa [this] at hsub
  have hM : (2 : R) ^ (n + 1) • M = M 0 0 • ((2 : R) ^ (n + 1) • E11 R) +
      M 0 1 • ((2 : R) ^ (n + 1) • E12 R) + M 1 0 • ((2 : R) ^ (n + 1) • E21 R) +
      M 1 1 • ((2 : R) ^ (n + 1) • E22 R) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E12, E21, E22] <;> ring
  rw [hM]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ e11) (S.smul_mem _ e12))
    (S.smul_mem _ e21)) (S.smul_mem _ e22)

/-- tex 2911, `PROVED`: in `ℤ₂`, `1 + 2^{n-1}` is a unit for `n ≥ 2` (it is odd). -/
theorem isUnit_one_add_two_pow (n : ℕ) (hn : 2 ≤ n) :
    IsUnit ((1 : ℤ_[2]) + 2 ^ (n - 1)) := by
  have hcast : ((1 : ℤ_[2]) + 2 ^ (n - 1)) = (((1 + 2 ^ (n - 1) : ℕ)) : ℤ_[2]) := by push_cast; rfl
  rw [hcast, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
  rw [hk, Nat.coprime_comm, Nat.Coprime, pow_succ]
  have : (1 + 2 ^ k * 2) = 2 * 2 ^ k + 1 := by ring
  rw [this]; simp [Nat.gcd_comm]

/-- The matrix span over `ℤ₂`, tex 2910–2912, `PROVED`: for `n ≥ 2` the `ℤ₂`-span of `I` and the
three squares contains `2^{n+1} M₂(ℤ₂)`. -/
theorem matrix_span_Z2 (n : ℕ) (hn : 2 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    (2 : ℤ_[2]) ^ (n + 1) • M ∈ Submodule.span ℤ_[2] (spanSet ℤ_[2] n) :=
  matrix_span n (by omega) (isUnit_one_add_two_pow n hn) M

/-- Negative control for the matrix span (tex 2911, "use that `1 + 2^{n-1}` is odd"), `PROVED`:
over `ℤ` (no `2`-adic units) the span does *not* contain `2^{n+1} E₁₁` for `n ≥ 2`; the statement
is a `ℤ_(2)`-span statement. -/
theorem matrix_span_fails_over_Z (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℤ) ^ (n + 1) • E11 ℤ ∉ Submodule.span ℤ (spanSet ℤ n) := by
  intro hmem
  simp only [spanSet] at hmem
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨a, x, hx, hax⟩ := hmem
  rw [Submodule.mem_span_insert] at hx
  obtain ⟨b, y, hy, hby⟩ := hx
  rw [Submodule.mem_span_insert] at hy
  obtain ⟨c, w, hw, hcw⟩ := hy
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨d, rfl⟩ := hw
  subst hcw; subst hby
  rw [sq_E11, sq_E12, sq_E21] at hax
  have h00 := congrFun (congrFun hax 0) 0
  have h11 := congrFun (congrFun hax 1) 1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, E11, E12, E21,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, mul_one, mul_zero,
    add_zero] at h00 h11
  -- from the two diagonal entries: `b (2^{n+1} + 2^{2n}) = 2^{n+1}`
  have key : b * ((2 : ℤ) ^ (n + 1) + 2 ^ (2 * n)) = 2 ^ (n + 1) := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have key' : (2 : ℤ) ^ (k + 3) * (b * (1 + 2 * 2 ^ k) - 1) = 0 := by
    linear_combination key
  have hb : b * (1 + 2 * 2 ^ k) = 1 := by
    have := (mul_eq_zero.mp key').resolve_left (pow_ne_zero _ (by norm_num)); linarith
  have hge : (3 : ℤ) ≤ 1 + 2 * 2 ^ k := by
    have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hb with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith

end ZInQ.Manuscript.RC.HeegnerAlgebra
