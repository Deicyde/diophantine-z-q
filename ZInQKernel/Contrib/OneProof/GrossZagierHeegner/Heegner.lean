import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-!
# gz-heegner: `GZHL3.HeegnerPointRational` from the main theorem of complex multiplication and the
canonical model of `X₀(N)`

Task gz-heegner (2026-11-15). Report: `docs/research/gz-heegner.md`; scratch and log: `scratch/gz-heegner/`.

gz-hl3 (`GrossZagierHeegner.lean`) proved `hL3` from six leaves, one of them the composite
`GZHL3.HeegnerPointRational` (the Heegner point `Σ_{Q ∈ S} φ(τ_Q)` is the image of a point of `E(K)`).
This file proves it from two printed leaves and nothing else:

* `T5Glue.ShimuraMainCM` (Shimura 1971 Thm 5.4; already the hypothesis `hCM` of `frozenTarget`),
* `X0ModuliGaloisMero` (§2): the canonical model of `X₀(N)` in its printed form, for every
  `g ∈ ℚ(X₀(N))` regular at the two points. The kernel's `T5Glue.X0ModuliGalois` (hypothesis `hX`)
  is its special case for `g` regular on all of `ℍ` (`x0ModuliGalois_of_mero`, §7), so a fold can
  replace `hX` by it. The weakening of the regularity hypothesis is needed: the coordinates `x∘φ`,
  `y∘φ` of a modular parametrization have poles in `ℍ` (at the non-cuspidal points of `φ⁻¹(O)`).

Everything else is proved here:

* lattice algebra: the Dirichlet composition `J·⟨1, τ_{Q'}⟩ = ⟨1, τ_Q⟩` (`exists_compose`) and
  homothety of lattice pairs ⇔ `Γ₀(N)`-equivalence (`pairHom_of_equiv`, `equiv_of_pairHom`);
* class field theory: every ideal class of `ℚ(√−m)` contains `⟨a, (−b + √D)/2⟩` with `a` prime to
  `M` (`heegnerClassJ`, from Tau Ceti's Chebotarev theorem);
* Galois theory of `ℂ`: the restriction `Aut(ℂ) → Gal(ℚ̄/ℚ)`, the fixed fields of `Aut(ℂ/κ(K))` and of
  `Aut(ℂ)` (`mem_kappa_of_fixed`, `rat_of_fixed`);
* the Galois transport of the points `φ(τ_Q)` (poles handled through `1/(x∘φ − t)`) and the
  permutation of the Heegner points (`heegnerC_fixed`);
* the analysis of `φ = weierPt E L (c φ_f)` (§8, §9): the coordinates lie in `ℚ(X₀(N))`:
  meromorphy (`paramRegular`), moderate growth at every cusp (`paramCuspGrowth`: `D φ_f = f` and
  `φ_f(γτ) = K₀ + G(q_N)` from the `q_N`-expansion of `f|₂γ`), and rational `q`-expansions at `∞`
  (`paramQExpansion`: `w²x(φ)` satisfies the Weierstrass equation in `w = q`, whose formal solution
  with constant term `1/c²` is unique, hence fixed by `Aut(ℂ)`, hence rational).

Main theorem: `heegnerPointRational_of_printed (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero) :
GZHL3.HeegnerPointRational`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open scoped MatrixGroups

namespace ZInQ.GZHeegner

/-! ## §1. Lattice algebra: Dirichlet composition, homothety of lattice pairs -/

/-- `s_D = i√|D|`, the normalized square root of `D < 0`. -/
def sD (D : ℤ) : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)

theorem sD_sq {D : ℤ} (hD : D < 0) : sD D ^ 2 = D := ZInQ.GZHL3.Reps.sqrt_sq_D hD

theorem tau_eq {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    Q.tau = (-(Q.B : ℂ) + sD D) / (2 * Q.A) := rfl

theorem A_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (Q.A : ℂ) ≠ 0 := by
  exact_mod_cast Q.A_pos.ne'

/-- The lattice `⟨a, (−b + √D)/2⟩ ⊂ ℂ` (the ideal of norm `a` attached to the form `[a, b, c]`). -/
def jLat (D a b : ℤ) : Submodule ℤ ℂ := Submodule.span ℤ {(a : ℂ), (-(b : ℂ) + sD D) / 2}

/-- Product of two lattices given by pairs of generators. -/
theorem span_pair_mul_span_pair (x₁ x₂ y₁ y₂ : ℂ) (L : Submodule ℤ ℂ)
    (h11 : x₁ * y₁ ∈ L) (h12 : x₁ * y₂ ∈ L) (h21 : x₂ * y₁ ∈ L) (h22 : x₂ * y₂ ∈ L) :
    Submodule.span ℤ {x₁, x₂} * Submodule.span ℤ {y₁, y₂} ≤ L := by
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact h11
  · rw [Set.mem_singleton_iff] at hy; subst hy; exact h12
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact h21
  · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact h22

theorem mul_mem_span_pair_mul (x₁ x₂ y₁ y₂ : ℂ) {x y : ℂ} (hx : x = x₁ ∨ x = x₂)
    (hy : y = y₁ ∨ y = y₂) :
    x * y ∈ Submodule.span ℤ {x₁, x₂} * Submodule.span ℤ {y₁, y₂} := by
  apply Submodule.mul_mem_mul
  · rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rcases hy with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

theorem mem_span_pair_of {u v z : ℂ} (c d : ℤ) (h : z = c * u + d * v) :
    z ∈ Submodule.span ℤ {u, v} :=
  Submodule.mem_span_pair.2 ⟨c, d, by rw [h]; simp [zsmul_eq_mul]⟩

/-! ### Parity and Bezout -/

theorem add_even_of_disc {A B C a b t D : ℤ} (hd : B ^ 2 - 4 * A * C = D)
    (ht : b ^ 2 - D = 4 * a * t) : ∃ e : ℤ, b + B = 2 * e := by
  rcases Int.even_or_odd (b + B) with ⟨e, he⟩ | ⟨e, he⟩
  · exact ⟨e, by omega⟩
  · exfalso
    have h1 : (2 * e + 1) * (2 * e + 1 - 2 * B) = 2 * (2 * (a * t - A * C)) := by
      have hb : b = 2 * e + 1 - B := by omega
      subst hb; linear_combination ht - hd
    have hodd : Odd ((2 * e + 1) * (2 * e + 1 - 2 * B)) :=
      Int.odd_mul.2 ⟨⟨e, rfl⟩, ⟨e - B, by ring⟩⟩
    rw [h1] at hodd
    exact (Int.not_even_iff_odd.2 hodd) ⟨2 * (a * t - A * C), by ring⟩

/-- A form of squarefree discriminant is primitive. -/
theorem gcd_eq_one_of_squarefree {A B C D : ℤ} (hsq : Squarefree D) (hd : B ^ 2 - 4 * A * C = D) :
    Int.gcd (Int.gcd A B) C = 1 := by
  set g : ℕ := Int.gcd (Int.gcd A B) C
  have hgA : (g : ℤ) ∣ A := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  have h2 : (g : ℤ) * g ∣ D := by
    rw [← hd]
    exact dvd_sub (by rw [sq]; exact mul_dvd_mul hgB hgB)
      (by
        obtain ⟨x, hx⟩ := hgA; obtain ⟨y, hy⟩ := hgC
        exact ⟨4 * x * y, by rw [hx, hy]; ring⟩)
  have hu := hsq _ h2
  rw [Int.isUnit_iff] at hu
  rcases hu with h | h
  · exact_mod_cast h
  · have : (0 : ℤ) ≤ g := Int.natCast_nonneg _
    omega

/-- Bezout for a triple with `gcd = 1`. -/
theorem exists_bezout3 {x y z : ℤ} (h : Int.gcd (Int.gcd x y) z = 1) :
    ∃ p q r : ℤ, p * x + q * y + r * z = 1 := by
  have h1 : IsCoprime ((Int.gcd x y : ℕ) : ℤ) z := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using h)
  obtain ⟨u, v, huv⟩ := h1
  refine ⟨u * Int.gcdA x y, u * Int.gcdB x y, v, ?_⟩
  rw [Int.gcd_eq_gcd_ab x y] at huv
  linear_combination huv

/-! ### Dirichlet composition with an ideal of norm prime to `A` -/

section Compose

variable {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) {a b : ℤ}

/-- The composite form `[aA, B + 2Ak, C']` (data of the composition, see `exists_compose`). -/
theorem exists_compose (hsq : Squarefree D) (ha : 0 < a) (hab : 4 * a ∣ b ^ 2 - D)
    (hcop : IsCoprime a Q.A) :
    ∃ Q' : HeegnerForm N D, 2 * Q.A ∣ Q'.B - Q.B ∧ jLat D a b * Q'.lat = Q.lat ∧
      jLat D a b * Q'.latN = Q.latN := by
  obtain ⟨t, ht⟩ := hab
  have hd := Q.disc
  obtain ⟨e, he⟩ := add_even_of_disc hd ht
  obtain ⟨u, v, huv⟩ := hcop
  set A := Q.A with hAdef
  set B := Q.B with hBdef
  set C := Q.C with hCdef
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = -(e * v) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, l = e * u := ⟨_, rfl⟩
  have hkl : B + 2 * A * k = -b + 2 * a * l := by
    rw [hk, hl]; linear_combination he - 2 * e * huv
  obtain ⟨W, hW⟩ : ∃ W : ℤ, W = C + B * k + A * k ^ 2 := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ℤ, C' = u * W + v * (t + l * (B + 2 * A * k) - a * l ^ 2) :=
    ⟨_, rfl⟩
  have hW' : A * W = a * (t + l * (B + 2 * A * k) - a * l ^ 2) := by
    have hb : b = 2 * a * l - B - 2 * A * k := by linarith
    rw [hb] at ht
    have h4 : 4 * (A * W) = 4 * (a * (t + l * (B + 2 * A * k) - a * l ^ 2)) := by
      rw [hW]; linear_combination ht - hd
    omega
  have haC : a * C' = W := by
    rw [hC']
    linear_combination W * huv - v * hW'
  obtain ⟨B', hB'⟩ : ∃ B' : ℤ, B' = B + 2 * A * k := ⟨_, rfl⟩
  have hdisc : B' ^ 2 - 4 * (a * A) * C' = D := by
    have : 4 * (a * A) * C' = 4 * A * (a * C') := by ring
    rw [this, haC, hW, hB']; linear_combination hd
  let Q' : HeegnerForm N D :=
    { A := a * A
      B := B'
      C := C'
      A_pos := mul_pos ha Q.A_pos
      N_dvd := dvd_mul_of_dvd_right Q.N_dvd a
      disc := hdisc
      D_neg := Q.D_neg
      primitive := gcd_eq_one_of_squarefree hsq hdisc }
  obtain ⟨A₁, hA₁⟩ := Q.N_dvd
  -- Bezout for `(a, B', N C')`
  obtain ⟨p, q, r, hpqr⟩ := exists_bezout3 (gcd_eq_one_of_squarefree hsq hdisc)
  have hbez : (p * A + r * u * C') * a + q * B' + (r * v * A₁) * (N * C') = 1 := by
    have hA : A = N * A₁ := hA₁
    rw [hA] at huv hpqr ⊢
    linear_combination hpqr + r * C' * huv
  -- complex numbers
  have hA0 : (A : ℂ) ≠ 0 := A_ne_zero Q
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN0 : (N : ℂ) ≠ 0 := by
    have : (N : ℤ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hA₁; exact Q.A_pos.ne' hA₁
    exact_mod_cast this
  have hs := sD_sq Q.D_neg
  set s := sD D
  have hτ : Q.tau = (-(B : ℂ) + s) / (2 * A) := rfl
  have hτ' : Q'.tau = (-(B' : ℂ) + s) / (2 * (a * A)) := by
    show cmPoint (a * A) B' D = _
    simp only [cmPoint]; push_cast; rfl
  have hkl' : (B : ℂ) + 2 * A * k = -b + 2 * a * l := by exact_mod_cast hkl
  have hB'c : (B' : ℂ) = B + 2 * A * k := by simp only [hB']; push_cast; ring
  have haC' : (a : ℂ) * C' = C + B * k + A * k ^ 2 := by
    have := haC; rw [hW] at this; exact_mod_cast this
  have hdc : (B : ℂ) ^ 2 - 4 * A * C = D := by exact_mod_cast hd
  have hAN : (A : ℂ) = N * A₁ := by exact_mod_cast hA₁
  -- the four products, in the basis `(1, τ)`
  have e1 : (a : ℂ) * Q'.tau = -k + Q.tau := by
    rw [hτ', hτ, hB'c]; field_simp; ring
  have e2 : (-(b : ℂ) + s) / 2 = (A * k + B - a * l) + A * Q.tau := by
    rw [hτ]; field_simp; linear_combination (-1 : ℂ) * hkl'
  have hroot : (A : ℂ) * Q.tau ^ 2 + B * Q.tau + C = 0 :=
    ZInQ.GZHL3.Reps.cmPoint_root Q.A_pos Q.disc Q.D_neg
  have hτ'' : Q'.tau = (Q.tau - k) / a := by
    rw [eq_div_iff ha0]; linear_combination e1
  have e3 : (-(b : ℂ) + s) / 2 * Q'.tau = (k * l - C') - l * Q.tau := by
    rw [hτ'', e2]
    field_simp
    linear_combination hroot + haC'
  -- generators of the product lattices
  have gen : ∀ (y₁ : ℂ) {L : Submodule ℤ ℂ}, L = Submodule.span ℤ {y₁, Q'.tau} →
      (a : ℂ) * y₁ ∈ jLat D a b * L ∧ (a : ℂ) * Q'.tau ∈ jLat D a b * L ∧
      (-(b : ℂ) + s) / 2 * y₁ ∈ jLat D a b * L ∧
      (-(b : ℂ) + s) / 2 * Q'.tau ∈ jLat D a b * L := by
    intro y₁ L hL
    subst hL
    exact ⟨mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inl rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inr rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inl rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inr rfl)⟩
  have zmem : ∀ {M : Submodule ℤ ℂ} (c : ℤ) {x : ℂ}, x ∈ M → (c : ℂ) * x ∈ M := by
    intro M c x hx
    have := M.smul_mem c hx
    rwa [zsmul_eq_mul] at this
  have hbezC : (((p * A + r * u * C') * a + q * B' + r * v * A₁ * (N * C') : ℤ) : ℂ) = 1 := by
    exact_mod_cast hbez
  push_cast at hbezC
  rw [hB'c] at hbezC
  refine ⟨Q', ⟨k, by simp [Q', hB']⟩, ?_, ?_⟩
  · obtain ⟨m1, m2, m3, m4⟩ := gen 1 (L := Q'.lat) rfl
    rw [mul_one] at m1 m3
    apply le_antisymm
    · apply span_pair_mul_span_pair
      · exact mem_span_pair_of a 0 (by simp)
      · exact mem_span_pair_of (-k) 1 (by rw [e1]; simp)
      · exact mem_span_pair_of (A * k + B - a * l) A (by rw [mul_one, e2]; push_cast; ring)
      · exact mem_span_pair_of (k * l - C') (-l) (by rw [e3]; push_cast; ring)
    · set M := jLat D a b * Q'.lat
      have hone : (1 : ℂ) ∈ M := by
        have h : (1 : ℂ) = ((p * A + r * u * C' + q * l : ℤ) : ℂ) * a +
            (q : ℂ) * ((-(b : ℂ) + s) / 2 - (A : ℤ) * ((a : ℂ) * Q'.tau)) +
            (-(r * v * A₁ * N) : ℤ) * ((-(b : ℂ) + s) / 2 * Q'.tau + (l : ℤ) * ((a : ℂ) * Q'.tau)) := by
          rw [e3, e1, e2]
          push_cast
          linear_combination -hbezC
        rw [h]
        exact M.add_mem (M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2))))
          (zmem _ (M.add_mem m4 (zmem _ m2)))
      rw [HeegnerForm.lat, Submodule.span_le]
      rintro _ (rfl | h)
      · exact hone
      · rw [Set.mem_singleton_iff] at h; subst h
        have : Q.tau = (a : ℂ) * Q'.tau + (k : ℤ) * 1 := by rw [e1]; ring
        rw [this]
        exact M.add_mem m2 (zmem _ hone)
  · obtain ⟨m1, m2, m3, m4⟩ := gen (1 / (N : ℂ)) (L := Q'.latN) rfl
    apply le_antisymm
    · apply span_pair_mul_span_pair
      · exact mem_span_pair_of a 0 (by simp)
      · exact mem_span_pair_of (-(k * N)) 1 (by rw [e1]; field_simp; push_cast; ring)
      · exact mem_span_pair_of (A * k + B - a * l) A₁ (by
          rw [e2]; push_cast; rw [hAN]; field_simp)
      · exact mem_span_pair_of (N * (k * l - C')) (-l) (by rw [e3]; field_simp; push_cast; ring)
    · set M := jLat D a b * Q'.latN
      have hone : (1 / (N : ℂ)) ∈ M := by
        have h : (1 / (N : ℂ)) = ((p * A + r * u * C' + q * l : ℤ) : ℂ) * (a * (1 / (N : ℂ))) +
            (q : ℂ) * ((-(b : ℂ) + s) / 2 * (1 / (N : ℂ)) - (A₁ : ℤ) * ((a : ℂ) * Q'.tau)) +
            (-(r * v * A₁) : ℤ) * ((-(b : ℂ) + s) / 2 * Q'.tau + (l : ℤ) * ((a : ℂ) * Q'.tau)) := by
          rw [e3, e1, e2, hAN]
          rw [hAN] at hbezC
          field_simp
          push_cast
          linear_combination -hbezC - ((p : ℂ) * a) * hAN
        rw [h]
        exact M.add_mem (M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2))))
          (zmem _ (M.add_mem m4 (zmem _ m2)))
      rw [HeegnerForm.latN, Submodule.span_le]
      rintro _ (rfl | h)
      · exact hone
      · rw [Set.mem_singleton_iff] at h; subst h
        have : Q.tau = (a : ℂ) * Q'.tau + (k * N : ℤ) * (1 / (N : ℂ)) := by
          rw [e1]; field_simp; push_cast; ring
        rw [this]
        exact M.add_mem m2 (zmem _ hone)

end Compose

/-! ### Homothety of lattice pairs versus `Γ₀(N)`-equivalence -/

/-- `(⟨1, τ_Q⟩, ⟨1/N, τ_Q⟩) = j·(⟨1, τ_{Q'}⟩, ⟨1/N, τ_{Q'}⟩)`. -/
def PairHom {N : ℕ} {D : ℤ} (Q Q' : HeegnerForm N D) (j : ℂ) : Prop :=
  Q.lat = Q'.lat.map (LinearMap.mulLeft ℤ j) ∧ Q.latN = Q'.latN.map (LinearMap.mulLeft ℤ j)

theorem map_mulLeft_span_pair (j u v : ℂ) :
    (Submodule.span ℤ {u, v}).map (LinearMap.mulLeft ℤ j) = Submodule.span ℤ {j * u, j * v} := by
  rw [Submodule.map_span, Set.image_pair]; rfl

theorem span_pair_eq {u₁ u₂ v₁ v₂ : ℂ} (h1 : u₁ ∈ Submodule.span ℤ {v₁, v₂})
    (h2 : u₂ ∈ Submodule.span ℤ {v₁, v₂}) (h3 : v₁ ∈ Submodule.span ℤ {u₁, u₂})
    (h4 : v₂ ∈ Submodule.span ℤ {u₁, u₂}) :
    Submodule.span ℤ {u₁, u₂} = Submodule.span ℤ {v₁, v₂} := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ (rfl | h)
    · exact h1
    · rw [Set.mem_singleton_iff] at h; subst h; exact h2
  · rw [Submodule.span_le]; rintro _ (rfl | h)
    · exact h3
    · rw [Set.mem_singleton_iff] at h; subst h; exact h4

theorem gamma0_dvd {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ

theorem N_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (N : ℂ) ≠ 0 := by
  have : (N : ℤ) ≠ 0 := by
    intro h0; obtain ⟨x, hx⟩ := Q.N_dvd; rw [h0, zero_mul] at hx; exact Q.A_pos.ne' hx
  exact_mod_cast this

/-- **`Γ₀(N)`-equivalent Heegner forms have homothetic lattice pairs.** -/
theorem pairHom_of_equiv {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D}
    (h : ZInQ.GZHL3.Gamma0Equiv Q Q') : ∃ j : ℂ, j ≠ 0 ∧ PairHom Q Q' j := by
  obtain ⟨γ, hγ, e⟩ := h
  obtain ⟨c₁, hc₁⟩ := gamma0_dvd hγ
  have hdet : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast ZInQ.GZHL3.Reps.det_SL γ
  set τ : ℂ := (Q.tauH : ℂ)
  set w : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) with hwdef
  have hw : w ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ Q.tauH
    simpa [UpperHalfPlane.denom, w, τ] using this
  have hzw : (Q'.tau : ℂ) * w = ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) := by
    have : (Q'.tau : ℂ) = ((γ • Q.tauH : ℍ) : ℂ) := by rw [e]; rfl
    rw [this, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    exact div_mul_cancel₀ _ hw
  have hc : ((γ 1 0 : ℤ) : ℂ) = N * c₁ := by exact_mod_cast hc₁
  have hN := N_ne_zero Q
  have hτ : Q.tau = τ := rfl
  have hdet' : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) - 1 = 0 := by
    rw [hdet]; ring
  set iN : ℂ := 1 / (N : ℂ) with hiNdef
  have hiN : (N : ℂ) * iN - 1 = 0 := by rw [hiNdef]; field_simp; ring
  have hc' : ((γ 1 0 : ℤ) : ℂ) - N * c₁ = 0 := by rw [hc]; ring
  refine ⟨w, hw, ?_, ?_⟩
  · rw [HeegnerForm.lat, HeegnerForm.lat, map_mulLeft_span_pair, mul_one, hτ]
    apply span_pair_eq
    · exact mem_span_pair_of (γ 0 0) (-(γ 1 0)) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast; linear_combination -hdet)
    · exact mem_span_pair_of (-(γ 0 1)) (γ 1 1) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast; linear_combination -τ * hdet)
    · exact mem_span_pair_of (γ 1 1) (γ 1 0) (by rw [hwdef]; ring)
    · exact mem_span_pair_of (γ 0 1) (γ 0 0) (by rw [mul_comm w Q'.tau, hzw]; ring)
  · rw [HeegnerForm.latN, HeegnerForm.latN, map_mulLeft_span_pair, ← hiNdef, hτ]
    apply span_pair_eq
    · exact mem_span_pair_of (γ 0 0) (-c₁) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast
        linear_combination (-iN) * hdet' - ((γ 0 1 : ℤ) + (γ 0 0 : ℤ) * τ) * iN * hc' -
          ((γ 0 1 : ℤ) + (γ 0 0 : ℤ) * τ) * c₁ * hiN)
    · exact mem_span_pair_of (-(γ 0 1 * N)) (γ 1 1) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast
        linear_combination (-τ) * hdet' +
          ((γ 0 1 : ℤ) * (((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ))) * hiN)
    · exact mem_span_pair_of (γ 1 1) c₁ (by
        rw [hwdef]; linear_combination (τ * iN) * hc' + (c₁ * τ) * hiN)
    · exact mem_span_pair_of (γ 0 1 * N) (γ 0 0) (by
        rw [mul_comm w Q'.tau, hzw]; push_cast; linear_combination (-((γ 0 1 : ℤ) : ℂ)) * hiN)

theorem int_indep {τ : ℂ} (hτ : 0 < τ.im) {x y : ℤ} (h : (x : ℂ) + y * τ = 0) : x = 0 ∧ y = 0 := by
  have him := congrArg Complex.im h
  simp at him
  rcases him with h1 | h1
  · subst h1; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exact absurd h1 hτ.ne'

theorem exists_coords {u v z : ℂ} (h : z ∈ Submodule.span ℤ {u, v}) :
    ∃ c d : ℤ, z = c * u + d * v := by
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 h
  exact ⟨c, d, by rw [← hcd]; simp [zsmul_eq_mul]⟩

/-- **Homothetic lattice pairs come from `Γ₀(N)`-equivalent Heegner forms.** -/
theorem equiv_of_pairHom {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} {j : ℂ} (h : PairHom Q Q' j) :
    ZInQ.GZHL3.Gamma0Equiv Q Q' := by
  obtain ⟨hL, hLN⟩ := h
  rw [HeegnerForm.lat, HeegnerForm.lat, map_mulLeft_span_pair, mul_one] at hL
  rw [HeegnerForm.latN, HeegnerForm.latN, map_mulLeft_span_pair] at hLN
  have hτ1 : 0 < Q.tau.im := Q.tauH.im_pos
  have hτ2 : 0 < Q'.tau.im := Q'.tauH.im_pos
  have hN := N_ne_zero Q
  -- `j = t + r τ`, `j τ' = q + p τ`
  obtain ⟨t, r, htr⟩ := exists_coords (z := j) (by rw [hL]; exact Submodule.subset_span (by simp))
  obtain ⟨q, p, hqp⟩ := exists_coords (z := j * Q'.tau)
    (by rw [hL]; exact Submodule.subset_span (by simp))
  obtain ⟨x, y, hxy⟩ := exists_coords (z := 1) (by rw [← hL]; exact Submodule.subset_span (by simp))
  obtain ⟨u, v, huv⟩ := exists_coords (z := Q.tau) (by
    rw [← hL]; exact Submodule.subset_span (by simp))
  obtain ⟨α, β, hαβ⟩ := exists_coords (z := j * (1 / N)) (by
    rw [hLN]; exact Submodule.subset_span (by simp))
  have e1 : ((x * t + y * q - 1 : ℤ) : ℂ) + ((x * r + y * p : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast; linear_combination -hxy - x * htr - y * hqp
  have e2 : ((u * t + v * q : ℤ) : ℂ) + ((u * r + v * p - 1 : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast; linear_combination -huv - u * htr - v * hqp
  have e3 : ((t - α : ℤ) : ℂ) + ((r - N * β : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast
    have : j = α + N * β * Q.tau := by
      have h' := hαβ; field_simp at h'; linear_combination h'
    linear_combination this - htr
  obtain ⟨i1, i2⟩ := int_indep hτ1 e1
  obtain ⟨i3, i4⟩ := int_indep hτ1 e2
  obtain ⟨-, i6⟩ := int_indep hτ1 e3
  have hdet1 : (x * v - y * u) * (t * p - q * r) = 1 := by
    linear_combination (u * r + v * p) * i1 + i4 - (u * t + v * q) * i2
  have hj : j ≠ 0 := by
    rintro rfl; simp at hxy
  -- the determinant is positive
  have him : (((t * p - q * r : ℤ) : ℝ)) * Q.tau.im = Complex.normSq j * Q'.tau.im := by
    have h1 : (starRingEnd ℂ) j * (j * Q'.tau) = (Complex.normSq j : ℂ) * Q'.tau := by
      rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    have h2 := congrArg Complex.im h1
    rw [hqp] at h2
    conv_lhs at h2 => rw [htr]
    simp only [map_add, map_mul, map_intCast, map_one, Complex.mul_im, Complex.add_im,
      Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im] at h2
    push_cast
    linear_combination h2
  have hpos : 0 < t * p - q * r := by
    have h3 : 0 < Complex.normSq j * Q'.tau.im := mul_pos (Complex.normSq_pos.2 hj) hτ2
    rw [← him] at h3
    have h4 : (0 : ℝ) < ((t * p - q * r : ℤ) : ℝ) := pos_of_mul_pos_left h3 hτ1.le
    exact_mod_cast h4
  have hdet : t * p - q * r = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' (by linarith [hdet1] : (t * p - q * r) * (x * v - y * u) = 1) with h | h
    · exact h.1
    · omega
  have hr : r = N * β := by linarith
  let γ : SL(2, ℤ) := ⟨!![p, q; r, t], by simp [Matrix.det_fin_two]; linarith⟩
  refine ⟨γ, ?_, ?_⟩
  · show ((γ 1 0 : ℤ) : ZMod N) = 0
    simp [γ, hr]
  · apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [γ, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    have hτ' : (Q'.tauH : ℂ) = Q'.tau := rfl
    have hτq : (Q.tauH : ℂ) = Q.tau := rfl
    have hden : (r : ℂ) * Q.tau + t = j := by rw [htr]; ring
    rw [hτ', hτq, div_eq_iff (by rw [hden]; exact hj), hden]
    linear_combination -hqp


/-! ## §2. The canonical model of `X₀(N)` for meromorphic functions (the leaf) -/

open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA
open scoped WeierstrassCurve.Affine

/-- **`g ∈ ℚ(X₀(N))`, as a function on `ℍ`**: `g` is `Γ₀(N)`-invariant, meromorphic on `ℍ`,
of moderate growth at every cusp (`g(γτ) = O(e^{2πk Im τ})` as `Im τ → ∞`, i.e. meromorphic at the
cusp `γ∞`), and has a Laurent expansion `g = q^{-k} Σ aₙ qⁿ` with `aₙ ∈ ℚ` for `Im τ` large.
The values of `g` at its poles are irrelevant (junk). Compared with the kernel's `IsRatModFn`, the
only change is that poles in `ℍ` are allowed: the `q`-expansion is required only near `∞`. -/
def IsRatModFnMero (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ τ : UpperHalfPlane, MeromorphicAt (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
  (∀ γ : SL(2, ℤ), ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty]
        fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

/-- `g` is **regular at `τ`** (holomorphic in a neighbourhood, with value `g τ`). -/
def RegularAt (g : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : Prop :=
  AnalyticAt ℂ (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)

/-- **X0-MODULI, printed form (every `g ∈ ℚ(X₀(N))` regular at the two points).** As the kernel's
`T5Glue.X0ModuliGalois`, with `IsRatModFn N g` (regular on all of `ℍ`) weakened to
`IsRatModFnMero N g` (`g ∈ ℚ(X₀(N))`, poles allowed) plus regularity of `g` at `τ` and `τ'`:
for `σ ∈ Aut(ℂ)` carrying the algebraic point `(E_τ, ⟨1/N⟩)` of `Y₀(N)` to `(E_{τ'}, ⟨k/N⟩)`,
`σ(g(τ)) = g(τ')`.

This is the printed statement: `X₀(N)_ℚ` is the coarse moduli space of pairs `(E, C)`, compatibly
with `Aut(ℂ)`, and `g(x)^σ = g(x^σ)` for every `g ∈ ℚ(X₀(N))` **regular at `x`** (Shimura 1971,
*Introduction to the arithmetic theory of automorphic functions*, §6.7, Prop. 6.9, Thm. 6.23;
Deligne–Rapoport, LNM 349, VI.6 and VII; Diamond–Shurman, §7.5–7.7; theorem numbers UNVERIFIED,
from memory). The kernel's regular-on-`ℍ` form is the special case (`x0ModuliGalois_of_mero`). -/
def X0ModuliGaloisMero : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFnMero N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ), RegularAt g τ → RegularAt g τ' →
      (∀ i < N, ∃ a : Qbar, ιC a = T5Glue.modCoord N τ i) →
      T5Glue.IsConjModel (σ : ℂ →+* ℂ) (T5Glue.pp τ) (T5Glue.pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((T5Glue.pp τ).weierstrassP (1 / N)) = μ ^ 2 * (T5Glue.pp τ').weierstrassP (k / N) ∧
        σ ((T5Glue.pp τ).derivWeierstrassP (1 / N)) =
          μ ^ 3 * (T5Glue.pp τ').derivWeierstrassP (k / N)) →
      σ (g τ) = g τ'

/-! ## §3. The coordinates of the modular parametrization, and the analytic glue -/

section Param

variable (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℚ)

/-- `z(τ) = c·φ_f(τ) ∈ ℂ`, the parameter of `φ(τ) ∈ ℂ/L`. -/
def zPar (τ : UpperHalfPlane) : ℂ := (c : ℂ) * ZInQ.GZHL3.eichler f τ

/-- `x(φ(τ)) = ℘_L(c φ_f(τ)) − b₂/12` (junk at the poles `c φ_f(τ) ∈ L`). -/
def xPar (τ : UpperHalfPlane) : ℂ := L.weierstrassP (zPar f c τ) - (E⁄ℂ).b₂ / 12

/-- `y(φ(τ)) = (℘'_L(c φ_f(τ)) − a₁x − a₃)/2`. -/
def yPar (τ : UpperHalfPlane) : ℂ :=
  (L.derivWeierstrassP (zPar f c τ) - (E⁄ℂ).a₁ * xPar E L f c τ - (E⁄ℂ).a₃) / 2

open Classical in
/-- `1/(x(φ(τ)) − t)`, `0` at the poles of `x∘φ`. -/
def gPar (t : ℚ) (τ : UpperHalfPlane) : ℂ :=
  if zPar f c τ ∈ L.lattice then 0 else (xPar E L f c τ - t)⁻¹

end Param

/-- The hypotheses shared by the analytic glue: `E/ℚ` with the L-series of the newform `f` of
level `N`, trivial character, `L` the period lattice of `E`, `c ∈ ℚ^×` with `c Λ_f ⊆ L`. -/
def ParamSetting (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) : Prop :=
  f.χ = 1 ∧ (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) ∧
    ZInQ.GZHL3.IsPeriodLattice E L ∧ c ≠ 0 ∧ ZInQ.GZHL3.PeriodsIn f c L

/-- **(GLUE, analysis; proved: `paramRegular`) Meromorphy and regularity of the coordinates of `φ`.** `x∘φ`, `y∘φ` and
`1/(x∘φ − t)` are meromorphic on `ℍ`; `x∘φ`, `y∘φ` are regular where `c φ_f(τ) ∉ L`, and
`1/(x∘φ − t)` (value `0` at the poles of `x∘φ`) is regular where `c φ_f(τ) ∈ L` or `x(φ(τ)) ≠ t`.
Content: `φ_f` is holomorphic on `ℍ` (Hecke's bound `aₙ(f) = O(n)`; Mathlib
`ModularForms/Bounds.lean`), `℘_L` is holomorphic off `L` with a double pole at each point of `L`
(Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). -/
def ParamRegular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    (∀ τ : UpperHalfPlane, MeromorphicAt (xPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      MeromorphicAt (yPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      ∀ t : ℚ, MeromorphicAt (gPar E L f c t ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
    (∀ τ : UpperHalfPlane, zPar f c τ ∉ L.lattice →
      RegularAt (xPar E L f c) τ ∧ RegularAt (yPar E L f c) τ) ∧
    (∀ (t : ℚ) (τ : UpperHalfPlane), (zPar f c τ ∈ L.lattice ∨ xPar E L f c τ ≠ t) →
      RegularAt (gPar E L f c t) τ)

/-- **(GLUE, analysis; proved: `paramCuspGrowth`) Moderate growth of the coordinates of `φ` at every
cusp.** For `γ ∈ SL₂(ℤ)`, each of `x(φ(γτ))`, `y(φ(γτ))`, `1/(x(φ(γτ)) − t)` is `O(e^{2πk Im τ})` as
`Im τ → ∞`, for some `k`. -/
def ParamCuspGrowth : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c → ∀ γ : SL(2, ℤ),
    (∃ k : ℕ, (fun τ : UpperHalfPlane => xPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))) ∧
    (∃ k : ℕ, (fun τ : UpperHalfPlane => yPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))) ∧
    ∀ t : ℚ, ∃ k : ℕ, (fun τ : UpperHalfPlane => gPar E L f c t (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))

/-- A rational Laurent expansion in `q = e^{2πiτ}` valid for `Im τ > T`. -/
def HasRatQExp (g : UpperHalfPlane → ℂ) : Prop :=
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

/-- **(GLUE, analysis; proved: `paramQExpansion`) Rational `q`-expansions of the coordinates of `φ`.** Near `∞`,
`c φ_f(τ) = c q + …` has rational coefficients (`aₙ(f) = aₙ(E) ∈ ℤ`, `c ∈ ℚ`), and the Laurent
expansion of `℘_L` at `0` has coefficients in `ℚ[g₂, g₃] = ℚ` (`g₂ = c₄/12`, `g₃ = c₆/216`), so
`x∘φ = c⁻²q⁻² + …`, `y∘φ`, `1/(x∘φ − t)` are Laurent series in `q` with rational coefficients. -/
def ParamQExpansion : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    HasRatQExp (xPar E L f c) ∧ HasRatQExp (yPar E L f c) ∧ ∀ t : ℚ, HasRatQExp (gPar E L f c t)

/-! ## §4. The class-group glue -/

open TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField

/-- **(GLUE, algebraic number theory) Every ideal class of `ℚ(√−m)`, `m ≡ 3 (mod 4)`
squarefree, contains an ideal `J = ⟨a, (−b + √−m)/2⟩` with `a` prime to a given `M`.** (E.g. a
prime of degree one not dividing `M`, by Tau Ceti's Chebotarev theorem, as in the kernel's
`RingClassTwo.exists_prime_picClass_eq`; or: every class contains an integral ideal prime to `M`,
whose primitive part has the Hermite basis `⟨a, (−b + √D)/2⟩`.) -/
def HeegnerClassJ : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → ∀ M : ℤ, M ≠ 0 →
    ∀ cl : Pic (conductorOrder (QNeg m) 1),
    ∃ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b

/-! ### `HeegnerClassJ`, proved -/

section ClassJProof

open TauCeti.GlobalNumberFields.NumberFieldOrder IsDedekindDomain ZInQ.RouteK.Redei

section ClassJ

variable {m : ℕ} [NeZero m]

set_option maxRecDepth 20000 in
/-- **Chebotarev for the Hilbert class field of `ℚ(√−m)`**: every class of `Pic(𝓞_K)` contains a
prime outside a given finite set (copy of the kernel's `RingClassTwo.exists_prime_picClass_eq`,
for the maximal order). -/
theorem exists_prime_picClass_eq1 (c : Pic (conductorOrder (QNeg m) 1))
    (T : Set (HeightOneSpectrum (𝓞 (QNeg m)))) (hT : T.Finite) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 (QNeg m)), 𝔭 ∉ T ∧
      ¬ (conductorOrder (QNeg m) 1).conductor ≤ 𝔭.asIdeal ∧
      ∀ hJ : 𝔭.asIdeal ∈ integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus,
        (conductorOrder (QNeg m) 1).picClass ⟨_, hJ⟩ = c := by
  have hD := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (QNeg m) (ringClassField (conductorOrder (QNeg m) 1))
    (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c))
  have hδ : (Nat.card (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier : ℝ) /
      Nat.card (ringClassField (conductorOrder (QNeg m) 1) ≃ₐ[QNeg m] ringClassField (conductorOrder (QNeg m) 1)) ≠ 0 := by
    apply div_ne_zero
    · have : Nonempty (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier :=
        ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier)).ne'
    · exact_mod_cast (Nat.card_pos (α := ringClassField (conductorOrder (QNeg m) 1) ≃ₐ[QNeg m] ringClassField (conductorOrder (QNeg m) 1))).ne'
  have hinf := ((hD.infinite hδ).sdiff (hT.union (finite_conductor_primes (d := m) 1)))
  obtain ⟨𝔭, h𝔭, h𝔭T⟩ := hinf.nonempty
  rw [Set.mem_union, not_or] at h𝔭T
  refine ⟨𝔭, h𝔭T.1, h𝔭T.2, fun hJ => ?_⟩
  obtain ⟨⟨Q, hQp, hQo⟩, hF⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have hur := NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) :
    Ideal (𝓞 (QNeg m))).IsMaximal := 𝔭.isMaximal
  have : Q.LiesOver ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) :
    Ideal (𝓞 (QNeg m))) := hQo
  have hF' := isArithFrobAt_ringClassArtinEquiv_picClass (conductorOrder (QNeg m) 1) ⟨_, hJ⟩ Q
  exact (ringClassArtinEquiv (conductorOrder (QNeg m) 1)).injective (isArithFrobAt_eq_of_isUnramifiedAt hF' hF)

/-- Elements of `𝓞_K`, `m ≡ 3 (mod 4)`, are `x₀ + x₁θ`, `θ = (1 + √−m)/2`. -/
theorem exists_coords_theta (hsq : Squarefree m) (h3 : m % 4 = 3) (y : 𝓞 (QNeg m)) :
    ∃ x₀ x₁ : ℤ, y = (x₀ : 𝓞 (QNeg m)) + x₁ * thetaO m h3 := by
  obtain ⟨a, t, N, ha, ht, hN⟩ := two_coords hsq y
  have hm : (m : ℤ) % 4 = 3 := by exact_mod_cast h3
  have hpar := parity_three hm hN
  have hat : 2 ∣ a - t := by
    rcases Int.emod_two_eq_zero_or_one t with h | h
    · have h2t : 2 ∣ t := Int.dvd_of_emod_eq_zero h
      exact dvd_sub (hpar.2 h2t) h2t
    · have hnt : ¬ 2 ∣ t := by omega
      have hna : ¬ 2 ∣ a := fun h' => hnt (hpar.1 h')
      omega
  obtain ⟨x₀, hx₀⟩ := hat
  refine ⟨x₀, t, ?_⟩
  rw [RingOfIntegers.ext_iff]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, algebraMap_thetaO,
    theta_eq]
  have hre : (algebraMap (𝓞 (QNeg m)) (QNeg m) y).re = a / 2 := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← ha]; ring
  have him : (algebraMap (𝓞 (QNeg m)) (QNeg m) y).im = t / 2 := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← ht]; ring
  have hax : (a : ℚ) = 2 * x₀ + t := by exact_mod_cast (by linarith : a = 2 * x₀ + t)
  ext
  · rw [hre]; simp [hax]; ring
  · rw [him]; simp [div_eq_mul_inv]

theorem coe_thetaO (h3 : m % 4 = 3) : ((thetaO m h3 : 𝓞 (QNeg m)) : QNeg m) = ⟨1 / 2, 1 / 2⟩ := by
  rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq]

theorem kappa_theta_sub (h3 : m % 4 = 3) (r : ℤ) :
    kappa m (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) =
      (-(((2 * r - 1 : ℤ)) : ℂ) + sD (-(m : ℤ))) / 2 := by
  have h1 : (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) = ⟨1 / 2 - r, 1 / 2⟩ := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_sub, ← RingOfIntegers.coe_eq_algebraMap,
      coe_thetaO, map_intCast]
    ext <;> simp
  rw [h1]
  simp only [kappa, sD]
  push_cast
  simp only [neg_neg]
  ring

theorem kappa_intCast (r : ℤ) : kappa m (((r : 𝓞 (QNeg m)) : QNeg m)) = r := by
  rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
  simp [kappa]

theorem kappa_lin (u v : ℤ) (x y : QNeg m) :
    kappa m (u * x + v * y) = u * kappa m x + v * kappa m y := by
  simp only [← kappaAlg_apply, map_add, map_mul, map_intCast]

theorem mem_order_one (y : 𝓞 (QNeg m)) :
    (y : QNeg m) ∈ (conductorOrder (QNeg m) 1).toSubalgebra :=
  ⟨0, y, by simp⟩

/-- **The lattice of an ideal with basis `⟨a, θ − r⟩`.** -/
theorem idealLat_eq_jLat (h3 : m % 4 = 3) (I : Ideal (𝓞 (QNeg m))) (a r : ℤ)
    (ha : ((a : ℤ) : 𝓞 (QNeg m)) ∈ I) (hr : thetaO m h3 - (r : 𝓞 (QNeg m)) ∈ I)
    (hI : ∀ y ∈ I, ∃ u v : ℤ, y = (u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r)) :
    idealLat m 1 I = jLat (-(m : ℤ)) a (2 * r - 1) := by
  unfold idealLat jLat
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyI, rfl⟩, rfl⟩
    obtain ⟨u, v, rfl⟩ := hI y hyI
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨u, v, ?_⟩
    have : ((((u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r) : 𝓞 (QNeg m))) : QNeg m) =
        (u : QNeg m) * (((a : 𝓞 (QNeg m)) : QNeg m)) +
          (v : QNeg m) * (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
    rw [this, kappa_lin, kappa_intCast, kappa_theta_sub]
    simp [zsmul_eq_mul]
  · rw [Submodule.span_le]
    rintro _ (rfl | h)
    · exact Submodule.subset_span ⟨_, ⟨mem_order_one _, _, ha, rfl⟩, kappa_intCast a⟩
    · rw [Set.mem_singleton_iff] at h; subst h
      exact Submodule.subset_span ⟨_, ⟨mem_order_one _, _, hr, rfl⟩, kappa_theta_sub h3 r⟩

/-- `(θ − r)(1 − θ − r) = r² − r + (m + 1)/4`. -/
theorem theta_norm (h3 : m % 4 = 3) (r : ℤ) :
    (thetaO m h3 - r) * (1 - thetaO m h3 - r) =
      (((r ^ 2 - r + ((m : ℤ) + 1) / 4) : ℤ) : 𝓞 (QNeg m)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
  have hk' : ((m : ℤ) + 1) / 4 = k + 1 := by omega
  rw [hk', RingOfIntegers.ext_iff]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_one, map_intCast]
  rw [← RingOfIntegers.coe_eq_algebraMap, coe_thetaO]
  have hm : (m : ℚ) = 4 * k + 3 := by exact_mod_cast hk
  push_cast
  simp only [sq]
  ext <;> simp [hm] <;> ring

end ClassJ

open ZInQ.Contrib.TYZGenus.RingClass in
/-- **`HeegnerClassJ`, proved** (Chebotarev in the Hilbert class field, Tau Ceti; the prime is split
or ramified, so `𝔭 = ⟨p, θ − r⟩`; an inert prime is principal, so its class is trivial and `J = 𝓞_K`). -/
theorem heegnerClassJ' (m : ℕ) [NeZero m] (hsq : Squarefree m) (h3 : m % 4 = 3) (M : ℤ)
    (hM : M ≠ 0) (cl : Pic (conductorOrder (QNeg m) 1)) :
    ∃ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b := by
  have hT : {𝔭 : HeightOneSpectrum (𝓞 (QNeg m)) |
      Ideal.span {((M : ℤ) : 𝓞 (QNeg m))} ≤ 𝔭.asIdeal}.Finite := by
    have hne : Ideal.span {((M : ℤ) : 𝓞 (QNeg m))} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
    exact (Ideal.finite_factors hne).subset fun 𝔭 h𝔭 => Ideal.dvd_iff_le.2 h𝔭
  obtain ⟨𝔭, h𝔭T, hcond, h𝔭c⟩ := exists_prime_picClass_eq1 cl _ hT
  have hJ := mem_primeTo_of_not_le (d := m) (f := 1) 𝔭 hcond
  have hM𝔭 : ((M : ℤ) : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h =>
    h𝔭T ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨p, hp, hlies⟩ := exists_prime_liesOver 𝔭.asIdeal 𝔭.ne_bot
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := m)
  -- the split/ramified case
  have split : Ideal.absNorm 𝔭.asIdeal = p → ∃ (J : integralIdealsPrimeTo
      (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b := by
    intro hN
    obtain ⟨r, hr⟩ := exists_int_sub_mem_of_absNorm 𝔭.asIdeal hp hN (thetaO m h3)
    refine ⟨⟨𝔭.asIdeal, hJ⟩, p, 2 * r - 1, h𝔭c hJ, by exact_mod_cast hp.pos, ?_, ?_, ?_⟩
    · -- `p ∣ r² − r + (m+1)/4`
      have hmem : (((r ^ 2 - r + ((m : ℤ) + 1) / 4) : ℤ) : 𝓞 (QNeg m)) ∈ 𝔭.asIdeal := by
        rw [← theta_norm h3 r]; exact Ideal.mul_mem_right _ _ hr
      obtain ⟨t, ht⟩ := (intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal _).1 hmem
      obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
      have hk' : ((m : ℤ) + 1) / 4 = k + 1 := by omega
      rw [hk'] at ht
      refine ⟨t, ?_⟩
      have hm : (m : ℤ) = 4 * k + 3 := by exact_mod_cast hk
      rw [hm]; linear_combination 4 * ht
    · have hpM : ¬ (p : ℤ) ∣ M := fun h => hM𝔭 ((intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal M).2 h)
      exact (Prime.irreducible (Nat.prime_iff_prime_int.1 hp)).coprime_iff_not_dvd.2 hpM
    · apply idealLat_eq_jLat h3 𝔭.asIdeal p r (by exact_mod_cast natCast_mem_of_liesOver (p := p) 𝔭.asIdeal) hr
      intro y hy
      obtain ⟨x₀, x₁, rfl⟩ := exists_coords_theta hsq h3 y
      have h1 : (((x₀ + x₁ * r : ℤ)) : 𝓞 (QNeg m)) ∈ 𝔭.asIdeal := by
        have : (((x₀ + x₁ * r : ℤ)) : 𝓞 (QNeg m)) =
            ((x₀ : 𝓞 (QNeg m)) + x₁ * thetaO m h3) - x₁ * (thetaO m h3 - r) := by push_cast; ring
        rw [this]; exact Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hr)
      obtain ⟨t, ht⟩ := (intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal _).1 h1
      refine ⟨t, x₁, ?_⟩
      have ht' : (x₀ : 𝓞 (QNeg m)) = p * t - x₁ * r := by
        have : ((x₀ : ℤ) : 𝓞 (QNeg m)) = ((p * t - x₁ * r : ℤ) : 𝓞 (QNeg m)) := by
          congr 1; linarith
        rw [this]; push_cast; ring
      rw [ht']; push_cast; ring
  rcases prime_trichotomy m σ hσ hp 𝔭.asIdeal with ⟨-, -, hN⟩ | ⟨-, hP, -⟩ | ⟨-, -, hN⟩
  · exact split hN
  · -- inert: `𝔭 = (p)` is principal, so `cl = 1`
    have h1 : (conductorOrder (QNeg m) 1).picClass ⟨𝔭.asIdeal, hJ⟩ = 1 :=
      ((conductorOrder (QNeg m) 1).picClass_eq_one_iff _).2
        ⟨p, Subalgebra.natCast_mem _ p, hP⟩
    rw [h𝔭c hJ] at h1
    subst h1
    refine ⟨1, 1, 1, map_one _, one_pos, ⟨((m : ℤ) + 1) / 4, by omega⟩, isCoprime_one_left, ?_⟩
    have h := idealLat_eq_jLat h3 (⊤ : Ideal (𝓞 (QNeg m))) 1 1 Submodule.mem_top
      Submodule.mem_top (fun y _ => by
        obtain ⟨x₀, x₁, rfl⟩ := exists_coords_theta hsq h3 y
        exact ⟨x₀ + x₁, x₁, by push_cast; ring⟩)
    norm_num at h
    convert h using 2
    simp [Ideal.one_eq_top]
  · exact split hN


/-- **`HeegnerClassJ`, proved.** -/
theorem heegnerClassJ : HeegnerClassJ := fun m _ hsq h3 M hM cl => heegnerClassJ' m hsq h3 M hM cl

end ClassJProof

/-! ## §5. Glue: Galois theory of `ℂ`, periodicity, the coordinates in `ℚ(X₀(N))` -/

/-- **`σ ∈ Aut(ℂ)` restricts to `ℚ̄`** (through `ιC`). -/
theorem exists_galQ_of_sigma (σ : ℂ ≃+* ℂ) : ∃ ρ : GalQ, ∀ a : Qbar, σ (ιC a) = ιC (ρ a) := by
  letI : Algebra Qbar ℂ := ιC.toAlgebra
  have hst : IsScalarTower ℚ Qbar ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp [RingHom.algebraMap_toAlgebra]
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Qbar, ιC y = z := by
    intro z hz
    have hz' : IsAlgebraic Qbar z := hz.extendScalars (algebraMap ℚ Qbar).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ (φ : ℂ ≃+* ℂ) (x : Qbar), IsAlgebraic ℚ (φ (ιC x)) := by
    intro φ x
    have h1 : IsAlgebraic ℚ (ιCA x) := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom ιCA
    exact h1.algHom ((φ : ℂ →+* ℂ).toRatAlgHom)
  choose ρf hρf using fun x => hrange (σ (ιC x)) (halg σ x)
  choose ρi hρi using fun x => hrange (σ.symm (ιC x)) (halg σ.symm x)
  have hinj : Function.Injective ιC := ιC.injective
  let ρh : Qbar →+* Qbar :=
    { toFun := ρf
      map_one' := hinj (by rw [hρf]; simp)
      map_mul' := fun x y => hinj (by rw [hρf, map_mul, map_mul, map_mul, hρf, hρf])
      map_zero' := hinj (by rw [hρf]; simp)
      map_add' := fun x y => hinj (by rw [hρf, map_add, map_add, map_add, hρf, hρf]) }
  have hbij : Function.Bijective ρh := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨ρi y, ?_⟩⟩
    · have h := congrArg ιC hxy
      change ιC (ρf x) = ιC (ρf y) at h
      rw [hρf, hρf] at h
      exact hinj (σ.injective h)
    · apply hinj
      change ιC (ρf (ρi y)) = ιC y
      rw [hρf, hρi, RingEquiv.apply_symm_apply]
  exact ⟨AlgEquiv.ofBijective ρh.toRatAlgHom hbij, fun x => (hρf x).symm⟩

/-- **The fixed field of `Aut(ℂ/κ(K))` is `κ(K)`**, `K = ℚ(√−m)`. -/
theorem mem_kappa_of_fixed {m : ℕ} [NeZero m] (z : ℂ)
    (hz : ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) → σ z = z) :
    ∃ k : QNeg m, kappa m k = z := by
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  let ε : SeparableClosure (QNeg m) →+* ℂ := ιC.comp e.toRingHom
  have hK : ∀ k : QNeg m, ε (algebraMap (QNeg m) (SeparableClosure (QNeg m)) k) = kappa m k :=
    fun k => T5Glue.kappa_eq_of_normalized e he k
  obtain ⟨a, ha⟩ := T5Glue.fixedAlgebraic z (fun σ hσ => hz σ (fun k => by
    rw [← hK k]; exact hσ _))
  letI : Algebra (SeparableClosure (QNeg m)) ℂ := ε.toAlgebra
  have hst : IsScalarTower ℚ (SeparableClosure (QNeg m)) ℂ :=
    IsScalarTower.of_algebraMap_eq fun q => by simp [RingHom.algebraMap_toAlgebra]
  have hzalg : IsAlgebraic ℚ z := by
    rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom ιCA
  obtain ⟨b, hb⟩ := T5Glue.mem_range_of_isAlgebraic
    (hzalg.extendScalars (algebraMap ℚ (SeparableClosure (QNeg m))).injective)
  have hb' : ε b = z := hb
  have hfix : ∀ τ : SeparableClosure (QNeg m) ≃ₐ[QNeg m] SeparableClosure (QNeg m), τ b = b := by
    intro τ
    obtain ⟨σ, hσ⟩ := T5Glue.exists_ringEquiv_extend ε τ.toRingEquiv
    have hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k := fun k => by
      rw [← hK k, hσ]; simp
    have h1 := hz σ hσK
    rw [← hb', hσ] at h1
    exact ε.injective h1
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed b).2 hfix
  exact ⟨k, by rw [← hK, hk, hb']⟩

theorem weierPt_eq_zero (E : WeierstrassCurve ℚ) (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    ZInQ.GZHL3.weierPt E L z = 0 := by
  unfold ZInQ.GZHL3.weierPt
  rw [dif_neg (fun h => h.1 hz)]

theorem weierPt_eq_some (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) {z : ℂ} (hz : z ∉ L.lattice) :
    ZInQ.GZHL3.weierPt E L z = .some _ _ (ZInQ.GZHL3.weierPt_some E hL hz) := by
  unfold ZInQ.GZHL3.weierPt
  rw [dif_pos ⟨hz, ZInQ.GZHL3.weierPt_some E hL hz⟩]

/-- `weierPt E L` is `L`-periodic. -/
theorem weierPt_add (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : ZInQ.GZHL3.weierPt E L (z + l) = ZInQ.GZHL3.weierPt E L z := by
  have h1 : L.weierstrassP (z + l) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨l, hl⟩
  have h2 : L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  by_cases hz : z ∈ L.lattice
  · rw [weierPt_eq_zero E L hz, weierPt_eq_zero E L (L.lattice.add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h hl)
    rw [weierPt_eq_some E hL hz, weierPt_eq_some E hL hzl]
    simp only [Affine.Point.some.injEq, h1, h2, and_self]

section Inv

variable {E : WeierstrassCurve ℚ} {L : PeriodPair} {N : ℕ} [NeZero N] {f : Newform N 2} {c : ℚ}

theorem zPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    ∃ l ∈ L.lattice, zPar f c (γ • τ) = zPar f c τ + l :=
  ⟨_, hP γ hγ τ, by simp only [zPar]; ring⟩

theorem xPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    xPar E L f c (γ • τ) = xPar E L f c τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  simp only [xPar, e, L.weierstrassP_add_coe _ ⟨l, hl⟩]

theorem yPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    yPar E L f c (γ • τ) = yPar E L f c τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  simp only [yPar, xPar_smul hP hγ τ, e, L.derivWeierstrassP_add_coe _ ⟨l, hl⟩]

theorem gPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (t : ℚ) (τ : UpperHalfPlane) :
    gPar E L f c t (γ • τ) = gPar E L f c t τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  have h3 : zPar f c τ + l ∈ L.lattice ↔ zPar f c τ ∈ L.lattice :=
    ⟨fun h => by simpa using L.lattice.sub_mem h hl, fun h => L.lattice.add_mem h hl⟩
  unfold gPar
  rw [xPar_smul hP hγ τ]
  by_cases h : zPar f c τ ∈ L.lattice
  · rw [if_pos (by rw [e]; exact h3.2 h), if_pos h]
  · rw [if_neg (by rw [e]; exact fun h' => h (h3.1 h')), if_neg h]

theorem weierPt_smul [E.IsElliptic] (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    ZInQ.GZHL3.weierPt E L (zPar f c (γ • τ)) = ZInQ.GZHL3.weierPt E L (zPar f c τ) := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  rw [e, weierPt_add E hL _ hl]

end Inv

/-- **The coordinates of `φ` lie in `ℚ(X₀(N))`** (from the three analytic glue Props; the
`Γ₀(N)`-invariance is proved here from `c Λ_f ⊆ L`). -/
theorem isRatModFnMero_coords (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) :
    IsRatModFnMero N (xPar E L f c) ∧ IsRatModFnMero N (yPar E L f c) ∧
      ∀ t : ℚ, IsRatModFnMero N (gPar E L f c t) := by
  obtain ⟨hmer, -, -⟩ := hR E N f L c hs
  obtain ⟨qx, qy, qg⟩ := hQ E N f L c hs
  have hP := hs.2.2.2.2
  refine ⟨⟨fun γ hγ τ => xPar_smul hP hγ τ, fun τ => (hmer τ).1, fun γ => ?_, qx⟩,
    ⟨fun γ hγ τ => yPar_smul hP hγ τ, fun τ => (hmer τ).2.1, fun γ => ?_, qy⟩,
    fun t => ⟨fun γ hγ τ => gPar_smul hP hγ t τ, fun τ => (hmer τ).2.2 t, fun γ => ?_, qg t⟩⟩
  · exact (hG E N f L c hs γ).1
  · exact (hG E N f L c hs γ).2.1
  · exact (hG E N f L c hs γ).2.2 t

/-- `σ` as a `ℚ`-algebra map. -/
abbrev sigA (σ : ℂ ≃+* ℂ) : ℂ →ₐ[ℚ] ℂ := (σ : ℂ →+* ℂ).toRatAlgHom

/-- **Galois transport of a point of the modular parametrization.** If `σ(g(τ)) = g(τ')` for every
`g ∈ ℚ(X₀(N))` regular at `τ` and `τ'`, then `σ(φ(τ)) = φ(τ')` in `E(ℂ)`. -/
theorem point_transport (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane)
    (hσ : ∀ g, IsRatModFnMero N g → RegularAt g τ → RegularAt g τ' → σ (g τ) = g τ') :
    Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c τ)) =
      ZInQ.GZHL3.weierPt E L (zPar f c τ') := by
  obtain ⟨-, hreg, hgreg⟩ := hR E N f L c hs
  obtain ⟨mx, my, mg⟩ := isRatModFnMero_coords hR hG hQ E f L c hs
  have hL := hs.2.2.1
  -- a value `t ∈ {0, 1}` avoiding a given complex number
  have avoid : ∀ w : ℂ, ∃ t : ℚ, w ≠ t := fun w => by
    by_cases h : w = ((0 : ℚ) : ℂ)
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨0, h⟩
  by_cases hz : zPar f c τ ∈ L.lattice <;> by_cases hz' : zPar f c τ' ∈ L.lattice
  · rw [weierPt_eq_zero E L hz, weierPt_eq_zero E L hz', map_zero]
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ')
    have h := hσ _ (mg t) (hgreg t τ (Or.inl hz)) (hgreg t τ' (Or.inr ht))
    simp only [gPar, hz, hz', ite_true, ite_false, map_zero] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h.symm
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ)
    have h := hσ _ (mg t) (hgreg t τ (Or.inr ht)) (hgreg t τ' (Or.inl hz'))
    simp only [gPar, hz, hz', ite_true, ite_false, map_eq_zero_iff _ σ.injective] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h
  · have hx := hσ _ mx (hreg τ hz).1 (hreg τ' hz').1
    have hy := hσ _ my (hreg τ hz).2 (hreg τ' hz').2
    rw [weierPt_eq_some E hL hz, weierPt_eq_some E hL hz', Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

/-! ## §6. `HeegnerPointRational` -/

theorem squarefree_neg_iff {x : ℤ} : Squarefree (-x) ↔ Squarefree x :=
  ⟨fun h y hy => h y (dvd_neg.2 hy), fun h y hy => h y (dvd_neg.1 hy)⟩

theorem mul_map_mulLeft (P M : Submodule ℤ ℂ) (j : ℂ) :
    P * M.map (LinearMap.mulLeft ℤ j) = (P * M).map (LinearMap.mulLeft ℤ j) := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    rintro p hp _ ⟨y, hy, rfl⟩
    refine ⟨p * y, Submodule.mul_mem_mul hp hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]; ring
  · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
    intro p hp y hy
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply,
      show j * (p * y) = p * (j * y) by ring]
    exact Submodule.mul_mem_mul hp ⟨y, hy, rfl⟩

theorem map_mulLeft_one (M : Submodule ℤ ℂ) : M.map (LinearMap.mulLeft ℤ (1 : ℂ)) = M := by
  rw [LinearMap.mulLeft_one, Submodule.map_id]

/-- **The Heegner sum is fixed by `Aut(ℂ/κ(K))`.** Every `σ` fixing `K = ℚ(√−m)` permutes the
points `φ(τ_Q)`, `Q ∈ S`: `σ` acts on the Hilbert class field as `Art([J])`
(`J = ⟨a, (−b + √D)/2⟩`, `HeegnerClassJ`), the main theorem of CM (`ShimuraMainCM`, through the
kernel's `CMModuli`) and the canonical model (`X0ModuliGaloisMero`) give `σ(φ(τ_Q)) = φ(τ_{Q'})`
for the Dirichlet composite `Q'` of `Q` with `J̄` (`exists_compose`), and `Q ↦ [Q']` is injective on
`Γ₀(N)`-classes (`pairHom_of_equiv`, `equiv_of_pairHom`). -/
theorem heegnerC_fixed (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero)
    (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion) (hJ : HeegnerClassJ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) {m : ℕ} [NeZero m] (hsq : Squarefree m) (hm3 : m % 4 = 3)
    {β : ℤ} (S : Finset (HeegnerForm N (-(m : ℤ))))
    (hS : ZInQ.GZHL3.IsHeegnerReps N (-(m : ℤ)) β S)
    (σ : ℂ ≃+* ℂ) (hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k) :
    Affine.Point.map (sigA σ) (ZInQ.GZHL3.heegnerC E L f c S) =
      ZInQ.GZHL3.heegnerC E L f c S := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  obtain ⟨τg, hτg⟩ := T5Glue.exists_tau_of_sigma e he σ hσK
  obtain ⟨ρ, hρ⟩ := exists_galQ_of_sigma σ
  have hρe : ∀ x, ρ (e x) = e (τg x) := fun x => ιC.injective (by rw [← hρ, hτg])
  set O := conductorOrder (QNeg m) 1 with hO
  set cl : Pic O := (ringClassArtinEquiv O).symm
    (AlgEquiv.restrictNormalHom (ringClassField O) τg) with hcl
  set M : ℤ := ∏ Q ∈ S, Q.A with hMdef
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => Q.A_pos.ne'
  obtain ⟨J, a, b, hJc, ha, hab, hcop, hJlat⟩ := hJ m hsq hm3 M hM cl
  have hArt : ∀ x : ringClassField O,
      ρ (e x) = e (ringClassArtinEquiv O (O.picClass J) x) := by
    intro x
    rw [hJc, hρe, hcl, MulEquiv.apply_symm_apply]
    congr 1
    exact (AlgEquiv.restrictNormalHom_apply _ τg x).symm
  have hsqD : Squarefree (-(m : ℤ)) := squarefree_neg_iff.2 (Int.squarefree_natCast.2 hsq)
  have hdisc : -(m : ℤ) = discOf m 1 := by simp [discOf, hm3]
  have hCMM := T5Glue.cmModuli_of_t5 hCM
    (T5Glue.ideleLatticeScale_of T5Glue.ringClassLattice T5Glue.invertibleColon)
  -- per-form data
  have step : ∀ Q ∈ S, ∃ Q' : HeegnerForm N (-(m : ℤ)), ZInQ.GZHL3.HasResidue β Q' ∧
      jLat (-(m : ℤ)) a b * Q'.lat = Q.lat ∧ jLat (-(m : ℤ)) a b * Q'.latN = Q.latN ∧
      Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c Q.tauH)) =
        ZInQ.GZHL3.weierPt E L (zPar f c Q'.tauH) := by
    intro Q hQS
    have hcopQ : IsCoprime a Q.A :=
      IsCoprime.of_isCoprime_of_dvd_right hcop (Finset.dvd_prod_of_mem _ hQS)
    obtain ⟨Q', hBB, hlat, hlatN⟩ := exists_compose Q hsqD ha hab hcopQ
    have hres : ZInQ.GZHL3.HasResidue β Q' := by
      have h1 := hS.1 Q hQS
      obtain ⟨A₁, hA₁⟩ := Q.N_dvd
      show (2 * N : ℤ) ∣ Q'.B - β
      have : Q'.B - β = (Q'.B - Q.B) + (Q.B - β) := by ring
      rw [this]
      exact dvd_add (dvd_trans ⟨A₁, by rw [hA₁]; ring⟩ hBB) h1
    refine ⟨Q', hres, hlat, hlatN, ?_⟩
    obtain ⟨x, hx, hx'⟩ := hCMM N hN m 1 hsq e he J ρ hArt (-(m : ℤ)) hdisc Q Q' 1
      (by rw [map_mulLeft_one, hJlat]; exact hlat) (by rw [map_mulLeft_one, hJlat]; exact hlatN)
    have hmod : ∀ i < N, (σ : ℂ →+* ℂ) (T5Glue.modCoord N Q.tauH i) =
        T5Glue.modCoord N Q'.tauH i := by
      intro i hi; rw [← hx i hi, ← hx' i hi]; exact hρ (x i)
    obtain ⟨μ, hμ, hk⟩ := T5Glue.moduli_transport T5Glue.discNeZero (σ : ℂ →+* ℂ) hN hmod
    exact point_transport hR hG hQ E f L c hs σ Q.tauH Q'.tauH fun g hg h1 h2 =>
      hX N hN g hg σ Q.tauH Q'.tauH μ h1 h2 (fun i hi => ⟨x i, hx i hi⟩) hμ hk
  choose! Q' hQ'res hQ'lat hQ'latN hQ'pt using step
  -- the representative in `S`
  have hrep : ∀ Q ∈ S, ∃ R ∈ S, ZInQ.GZHL3.Gamma0Equiv (Q' Q) R := fun Q hQ => by
    obtain ⟨R, ⟨hR, hE⟩, -⟩ := hS.2 (Q' Q) (hQ'res Q hQ)
    exact ⟨R, hR, hE⟩
  choose! π hπS hπE using hrep
  have hπpt : ∀ Q ∈ S, Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c Q.tauH)) =
      ZInQ.GZHL3.weierPt E L (zPar f c (π Q).tauH) := by
    intro Q hQ
    rw [hQ'pt Q hQ]
    obtain ⟨γ, hγ, hγe⟩ := hπE Q hQ
    rw [← hγe, weierPt_smul hs.2.2.1 hs.2.2.2.2 hγ]
  have hπinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, π Q₁ = π Q₂ → Q₁ = Q₂ := by
    intro Q₁ h1 Q₂ h2 hπ
    have hE : ZInQ.GZHL3.Gamma0Equiv (Q' Q₁) (Q' Q₂) :=
      ZInQ.GZHL3.Reps.equiv_trans (hπE Q₁ h1)
        (by rw [hπ]; exact ZInQ.GZHL3.Reps.equiv_symm (hπE Q₂ h2))
    obtain ⟨j, -, hjL, hjN⟩ := pairHom_of_equiv hE
    have hP : PairHom Q₁ Q₂ j := by
      constructor
      · rw [← hQ'lat Q₁ h1, ← hQ'lat Q₂ h2, hjL, mul_map_mulLeft]
      · rw [← hQ'latN Q₁ h1, ← hQ'latN Q₂ h2, hjN, mul_map_mulLeft]
    have hE' := equiv_of_pairHom hP
    obtain ⟨R, -, huniq⟩ := hS.2 Q₁ (hS.1 Q₁ h1)
    exact (huniq Q₁ ⟨h1, ZInQ.GZHL3.Reps.equiv_refl Q₁⟩).trans (huniq Q₂ ⟨h2, hE'⟩).symm
  unfold ZInQ.GZHL3.heegnerC
  rw [map_sum]
  refine Finset.sum_bij (fun Q _ => π Q) hπS (fun Q₁ h1 Q₂ h2 h => hπinj Q₁ h1 Q₂ h2 h) ?_ ?_
  · intro R hR
    obtain ⟨Q, hQ, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun Q _ => π Q) hπS
      (fun a₁ a₂ ha₁ ha₂ h => hπinj a₁ ha₁ a₂ ha₂ h) le_rfl R hR
    exact ⟨Q, hQ, h.symm⟩
  · intro Q hQ; exact hπpt Q hQ

/-- **`HeegnerPointRational` (gz-hl3's leaf) from the main theorem of complex multiplication, the
canonical model of `X₀(N)` in printed (meromorphic) form, and glue.** -/
theorem heegnerPointRational_of (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero)
    (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion) (hJ : HeegnerClassJ) :
    ZInQ.GZHL3.HeegnerPointRational := by
  intro E _ N _ f hχ hcoeff D β hDf hD4 hHH hβ S hS L c hL hc hPer K _ _ _ hK2 δ hδ ι hι
  obtain ⟨hD0, hD1, hDsq⟩ := hDf
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, D = -(m : ℤ) := ⟨D.natAbs, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm0⟩
  have hsq : Squarefree m := Int.squarefree_natCast.1 (squarefree_neg_iff.1 hDsq)
  have hm3 : m % 4 = 3 := by omega
  have hs : ParamSetting E f L c := ⟨hχ, hcoeff, hL, hc, hPer⟩
  have hfix := heegnerC_fixed hCM hX hR hG hQ hJ E f L c hs hsq hm3 S hS
  -- `θ : ℚ(√−m) → K`, `√−m ↦ δ`, with `ι ∘ θ = κ`
  have hδ' : δ * δ = (-(m : ℚ)) • (1 : K) + (0 : ℚ) • δ := by
    rw [← sq, hδ]; simp [Rat.smul_def]
  let θ : QNeg m →ₐ[ℚ] K := QuadraticAlgebra.lift ⟨δ, hδ'⟩
  have hιθ : ∀ k : QNeg m, ι (θ k) = kappa m k := by
    have h : ι.comp θ = kappaAlg m := by
      apply QuadraticAlgebra.algHom_ext
      rw [kappaAlg_apply, T5Glue.kappa_omega, AlgHom.comp_apply]
      have : θ QuadraticAlgebra.omega = δ := by simp [θ]
      rw [this, hι]
      push_cast; simp
    intro k
    rw [← kappaAlg_apply, ← h]; rfl
  rcases hZ : ZInQ.GZHL3.heegnerC E L f (c : ℂ) S with _ | ⟨x, y, hxy⟩
  · exact ⟨0, by rw [map_zero]; rfl⟩
  · have hfx : ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) → σ x = x ∧ σ y = y := by
      intro σ hσ
      have h := hfix σ hσ
      rw [hZ, Affine.Point.map_some] at h
      simp only [Affine.Point.some.injEq] at h
      exact h
    obtain ⟨k₁, hk₁⟩ := mem_kappa_of_fixed x (fun σ hσ => (hfx σ hσ).1)
    obtain ⟨k₂, hk₂⟩ := mem_kappa_of_fixed y (fun σ hσ => (hfx σ hσ).2)
    have hns : (E⁄K).Nonsingular (θ k₁) (θ k₂) := by
      rw [← WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := ι) ι.injective,
        hιθ, hιθ, hk₁, hk₂]
      exact hxy
    refine ⟨.some _ _ hns, ?_⟩
    rw [Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨(hιθ k₁).trans hk₁, (hιθ k₂).trans hk₂⟩

/-! ## §7. The kernel's `X0ModuliGalois` is the regular case of `X0ModuliGaloisMero` -/

/-- `q = e^{2πiτ}` as a function of `w ∈ ℂ`. -/
def qC (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

theorem norm_qC_lt_one {w : ℂ} (hw : 0 < w.im) : ‖qC w‖ < 1 := by
  rw [qC, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * w).re = -(2 * Real.pi * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp 0 :=
        Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

/-- Every `r ∈ [0, 1)` is `|q(τ)|` for some `τ ∈ ℍ`... (for `r > 0`). -/
theorem exists_qC_norm {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ τ : UpperHalfPlane, ‖qC τ‖ = r := by
  have hl : 0 < -Real.log r := by
    have := Real.log_neg hr0 hr1; linarith
  refine ⟨⟨Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ), ?_⟩, ?_⟩
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    exact div_pos hl (by positivity)
  · rw [qC, Complex.norm_exp]
    show Real.exp (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re = r
    have : (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re =
        Real.log r := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
      field_simp
      ring
    rw [this, Real.exp_log hr0]

/-- **A function with a `q`-expansion valid on all of `ℍ` is holomorphic on `ℍ`.** -/
theorem regularAt_of_hasSum {g : UpperHalfPlane → ℂ} {k : ℕ} {a : ℕ → ℚ}
    (h : ∀ τ : UpperHalfPlane, HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)) (τ : UpperHalfPlane) :
    RegularAt g τ := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  -- the radius is at least `1`
  have hrad : ∀ r : NNReal, (r : ℝ) < 1 → (r : ENNReal) ≤ p.radius := by
    intro r hr
    rcases eq_or_lt_of_le r.2 with h0 | h0
    · have : r = 0 := by ext; exact h0.symm
      rw [this]; simp
    obtain ⟨σ, hσ⟩ := exists_qC_norm h0 hr
    apply p.le_radius_of_tendsto (l := 0)
    have ht := (h σ).summable.tendsto_atTop_zero
    have ht' := ht.norm
    simp only [norm_zero] at ht'
    have hσ' : ‖Complex.exp (2 * Real.pi * Complex.I * σ)‖ = r := hσ
    refine ht'.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, hσ']
  have hq := norm_qC_lt_one τ.im_pos
  obtain ⟨r, hr1, hr2⟩ := exists_between hq
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩ with hr'
  have hmem : qC τ ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    calc (‖qC τ‖₊ : ENNReal) < (r' : ENNReal) := by
          rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
      _ ≤ p.radius := hrad r' hr2
  have hpos : 0 < p.radius := by
    have := hmem; rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this
  have hF := p.hasFPowerSeriesOnBall hpos
  have hFa : AnalyticAt ℂ p.sum (qC τ) := hF.analyticAt_of_mem hmem
  have hqa : AnalyticAt ℂ qC (τ : ℂ) := by
    unfold qC; fun_prop
  have hG : AnalyticAt ℂ (fun w => p.sum (qC w) / qC w ^ k) (τ : ℂ) :=
    (hFa.comp hqa).div (hqa.pow k) (pow_ne_zero _ (Complex.exp_ne_zero _))
  apply hG.congr
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds τ.im_pos] with w hw
  have hw' : (UpperHalfPlane.ofComplex w : ℂ) = w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hs := h (UpperHalfPlane.ofComplex w)
  rw [hw'] at hs
  have hsum : p.sum (qC w) = qC w ^ k * g (UpperHalfPlane.ofComplex w) := by
    rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simp only [smul_eq_mul]
    exact hs.tsum_eq
  simp only [Function.comp_apply, hsum]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.exp_ne_zero _))

theorem isRatModFnMero_of (N : ℕ) {g : UpperHalfPlane → ℂ} (hg : IsRatModFn N g) :
    IsRatModFnMero N g := by
  obtain ⟨hinv, hgr, k, a, ha⟩ := hg
  exact ⟨hinv, fun τ => (regularAt_of_hasSum ha τ).meromorphicAt, hgr, k, a, 0, fun τ _ => ha τ⟩

/-- **The kernel's `X0ModuliGalois` follows from its printed form `X0ModuliGaloisMero`.** -/
theorem x0ModuliGalois_of_mero (h : X0ModuliGaloisMero) : T5Glue.X0ModuliGalois := by
  intro N hN g hg σ τ τ' μ halg hμ hk
  obtain ⟨-, -, k, a, ha⟩ := id hg
  exact h N hN g (isRatModFnMero_of N hg) σ τ τ' μ (regularAt_of_hasSum ha τ)
    (regularAt_of_hasSum ha τ') halg hμ hk

/-! ## §8. The analytic glue `ParamRegular` and `ParamCuspGrowth`, proved -/

section AnalyticGlue

open scoped Manifold ModularForm

/-! ## The Weierstrass side: `℘`, `℘'` and `1/(℘ − c₀)` as functions on `ℂ` -/

section Wp

variable (L : PeriodPair)

theorem analyticAt_wp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.weierstrassP z :=
  L.differentiableOn_weierstrassP.analyticAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

theorem analyticAt_dwp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.derivWeierstrassP z :=
  L.analyticOnNhd_derivWeierstrassP z hz

theorem meromorphicAt_inv_pow (z₀ : ℂ) (n : ℕ) : MeromorphicAt (fun z : ℂ => 1 / (z - z₀) ^ n) z₀ :=
  (MeromorphicAt.const 1 z₀).div (((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀)).pow n)

theorem meromorphicAt_wp (z₀ : ℂ) : MeromorphicAt L.weierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.weierstrassP =
        fun z => L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) :=
      funext fun z => (L.weierstrassPExcept_add ⟨z₀, h⟩ z).symm
    rw [e]
    exact (L.analyticAt_weierstrassPExcept z₀).meromorphicAt.add
      ((meromorphicAt_inv_pow z₀ 2).sub (MeromorphicAt.const _ z₀))
  · exact (analyticAt_wp L h).meromorphicAt

theorem meromorphicAt_dwp (z₀ : ℂ) : MeromorphicAt L.derivWeierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.derivWeierstrassP =
        fun z => L.derivWeierstrassPExcept z₀ z - 2 * (1 / (z - z₀) ^ 3) :=
      funext fun z => by rw [← L.derivWeierstrassPExcept_sub ⟨z₀, h⟩ z]; ring
    rw [e]
    exact (L.analyticAt_derivWeierstrassPExcept z₀).meromorphicAt.sub
      ((MeromorphicAt.const 2 z₀).mul (meromorphicAt_inv_pow z₀ 3))
  · exact (analyticAt_dwp L h).meromorphicAt

open Classical in
/-- `z ↦ 1/(℘(z) − c₀)`, `0` on `L`. -/
def phiT (c₀ : ℂ) (z : ℂ) : ℂ := if z ∈ L.lattice then 0 else (L.weierstrassP z - c₀)⁻¹

theorem analyticAt_phiT_of_mem (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∈ L.lattice) :
    AnalyticAt ℂ (phiT L c₀) z₀ := by
  set A : ℂ → ℂ := fun z => L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀ with hAdef
  have hA : AnalyticAt ℂ A z₀ := (L.analyticAt_weierstrassPExcept z₀).sub analyticAt_const
    |>.sub analyticAt_const
  set R : ℂ → ℂ := fun z => (z - z₀) ^ 2 / (1 + (z - z₀) ^ 2 * A z) with hRdef
  have hR : AnalyticAt ℂ R z₀ := by
    apply AnalyticAt.div
    · fun_prop
    · exact analyticAt_const.add (((analyticAt_id.sub analyticAt_const).pow 2).mul hA)
    · simp
  apply hR.congr
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z₀] with z hz
  by_cases hzz : z = z₀
  · subst hzz; simp [phiT, h, R]
  · have hzL : z ∉ L.lattice := fun hz' => hz ⟨hz', hzz⟩
    have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
    simp only [phiT, hzL, if_false, R, A]
    rw [← L.weierstrassPExcept_add ⟨z₀, h⟩ z]
    have : L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) - c₀ =
        (1 + (z - z₀) ^ 2 * (L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀)) / (z - z₀) ^ 2 := by
      field_simp; ring
    rw [this, inv_div]

theorem phiT_eventuallyEq {c₀ z₀ : ℂ} (h : z₀ ∉ L.lattice) :
    phiT L c₀ =ᶠ[nhds z₀] fun z => (L.weierstrassP z - c₀)⁻¹ := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds h] with z hz
  simp only [phiT, if_neg (show z ∉ L.lattice from hz)]

theorem analyticAt_phiT_of_ne (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∉ L.lattice)
    (hne : L.weierstrassP z₀ ≠ c₀) : AnalyticAt ℂ (phiT L c₀) z₀ :=
  (((analyticAt_wp L h).sub analyticAt_const).inv (sub_ne_zero.2 hne)).congr
    (phiT_eventuallyEq L h).symm

theorem meromorphicAt_phiT (c₀ z₀ : ℂ) : MeromorphicAt (phiT L c₀) z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · exact (analyticAt_phiT_of_mem L c₀ h).meromorphicAt
  · exact (((meromorphicAt_wp L z₀).sub (MeromorphicAt.const c₀ z₀)).inv).congr
      ((phiT_eventuallyEq L h).symm.filter_mono nhdsWithin_le_nhds)

end Wp

/-! ## The Eichler integral is holomorphic on `ℍ` -/

section Eichler

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- The coefficients of `φ_f = Σ aₙ/n qⁿ`. -/
def eCoeff (n : ℕ) : ℂ := if n = 0 then 0 else ZInQ.GZDecomp.coeff f n / n

/-- `φ_f` as a power series in `q`. -/
def eSeries : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (eCoeff f)

theorem hasSum_newform (τ : UpperHalfPlane) :
    HasSum (fun n => ZInQ.GZDecomp.coeff f n * qC τ ^ n) (f.toCuspForm τ) := by
  have h := ModularForm.hasSum_qExpansion f.toCuspForm one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = qC τ := by
    simp [Function.Periodic.qParam, qC]
  rw [hq] at h
  exact h

theorem coeff_zero_newform : ZInQ.GZDecomp.coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)

theorem eSeries_radius (r : NNReal) (hr : (r : ℝ) < 1) : (r : ENNReal) ≤ (eSeries f).radius := by
  rcases eq_or_lt_of_le r.2 with h0 | h0
  · have : r = 0 := by ext; exact h0.symm
    rw [this]; simp
  obtain ⟨σ, hσ⟩ := exists_qC_norm h0 hr
  apply (eSeries f).le_radius_of_tendsto (l := 0)
  have ht := ((hasSum_newform f σ).summable.tendsto_atTop_zero).norm
  simp only [norm_zero] at ht
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) ht
  rw [eSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, hσ]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold eCoeff
  split_ifs with hn
  · simp
  · rw [norm_div]
    have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_self (norm_nonneg _) h1

theorem eSeries_mem_ball {w : ℂ} (hw : ‖w‖ < 1) : w ∈ Metric.eball (0 : ℂ) (eSeries f).radius := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖w‖₊ : ENNReal) < (r' : ENNReal) := by rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
    _ ≤ _ := eSeries_radius f r' hr2

theorem eSeries_radius_pos : 0 < (eSeries f).radius := by
  have := eSeries_mem_ball f (w := 0) (by simp)
  rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this

theorem eichler_eq (τ : UpperHalfPlane) : ZInQ.GZHL3.eichler f τ = (eSeries f).sum (qC τ) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f (norm_qC_lt_one τ.im_pos))
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  have h1 := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.range_one, Finset.sum_singleton, eCoeff] at h1
  unfold ZInQ.GZHL3.eichler
  refine (HasSum.tsum_eq ?_)
  convert h1 using 1
  · funext n
    rw [if_neg (Nat.succ_ne_zero n), qC, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  · simp [eSeries]

theorem analyticAt_eSum {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (eSeries f).sum w :=
  ((eSeries f).hasFPowerSeriesOnBall (eSeries_radius_pos f)).analyticAt_of_mem
    (eSeries_mem_ball f hw)

theorem analyticAt_qC (w : ℂ) : AnalyticAt ℂ qC w := by unfold qC; fun_prop

theorem eichler_ofComplex_eventuallyEq (τ : UpperHalfPlane) :
    (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      fun w => (eSeries f).sum (qC w) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds τ.im_pos] with w hw
  simp only [Function.comp_apply]
  rw [eichler_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

theorem analyticAt_eichler (τ : UpperHalfPlane) :
    AnalyticAt ℂ (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) τ :=
  ((analyticAt_eSum f (norm_qC_lt_one τ.im_pos)).comp (analyticAt_qC _)).congr
    (eichler_ofComplex_eventuallyEq f τ).symm

theorem analyticAt_zPar (c : ℚ) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (zPar f c ∘ UpperHalfPlane.ofComplex) τ :=
  show AnalyticAt ℂ (fun w => (c : ℂ) * (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) w) τ from
    analyticAt_const.mul (analyticAt_eichler f τ)

theorem zPar_ofComplex (c : ℚ) (τ : UpperHalfPlane) :
    (zPar f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) = zPar f c τ := by
  simp [UpperHalfPlane.ofComplex_apply]

end Eichler

/-- **`ParamRegular`, proved.** -/
theorem paramRegular : ParamRegular := by
  intro E _ N _ f L c _
  set b : ℂ := (E⁄ℂ).b₂ / 12 with hb
  have hz := analyticAt_zPar f c
  have hval := zPar_ofComplex f c
  have ex : xPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => L.weierstrassP z - b) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have ey : yPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) ∘
        (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have eg : ∀ t : ℚ, gPar E L f c t ∘ UpperHalfPlane.ofComplex =
      phiT L (b + t) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := by
    intro t; funext w; simp only [Function.comp_apply, gPar, phiT, xPar, sub_sub, hb]
  have mx : ∀ z₀, MeromorphicAt (fun z => L.weierstrassP z - b) z₀ := fun z₀ =>
    (meromorphicAt_wp L z₀).sub (MeromorphicAt.const _ _)
  have my : ∀ z₀, MeromorphicAt (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ *
      (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) z₀ := fun z₀ =>
    (((meromorphicAt_dwp L z₀).sub ((MeromorphicAt.const _ _).mul (mx z₀))).sub
      (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)
  refine ⟨fun τ => ⟨?_, ?_, fun t => ?_⟩, fun τ hτ => ⟨?_, ?_⟩, fun t τ h => ?_⟩
  · rw [ex]; exact (mx _).comp_analyticAt (hz τ)
  · rw [ey]; exact (my _).comp_analyticAt (hz τ)
  · rw [eg]; exact (meromorphicAt_phiT L _ _).comp_analyticAt (hz τ)
  · show AnalyticAt ℂ _ _
    rw [ex]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact (analyticAt_wp L hτ).sub analyticAt_const
  · show AnalyticAt ℂ _ _
    rw [ey]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact ((((analyticAt_dwp L hτ).sub (analyticAt_const.mul ((analyticAt_wp L hτ).sub
      analyticAt_const))).sub analyticAt_const).div analyticAt_const two_ne_zero)
  · show AnalyticAt ℂ _ _
    rw [eg]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    rcases h with h | h
    · exact analyticAt_phiT_of_mem L _ h
    · by_cases hm : zPar f c τ ∈ L.lattice
      · exact analyticAt_phiT_of_mem L _ hm
      · refine analyticAt_phiT_of_ne L _ hm ?_
        intro he; apply h; simp only [xPar, ← hb, he]; ring


/-! ## Power series converging on the unit disc -/

section PSeries

/-- A power series converging on the unit disc has `‖cₙ‖ rⁿ` bounded for each `r < 1`. -/
theorem pseries_bound (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : ∃ C, ∀ n, ‖c n‖ * r ^ n ≤ C := by
  have hs := (hc (r : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1))
  have ht := hs.tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have := hC ⟨n, rfl⟩
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0] using this

/-- Absolute convergence of a dominated power series inside the unit disc. -/
theorem pseries_summable_norm (c d : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    (K : ℝ) (hK : 0 ≤ K) (k : ℕ) (hd : ∀ n, ‖d n‖ ≤ K * (n : ℝ) ^ k * ‖c n‖) {q : ℂ}
    (hq : ‖q‖ < 1) : Summable (fun n => ‖d n‖ * ‖q‖ ^ n) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hq
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  obtain ⟨C, hC⟩ := pseries_bound c hc hr0.le hr2
  have hρ : ‖‖q‖ / r‖ < 1 := by
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hr0.le), div_lt_one hr0]; exact hr1
  have hgeo := (summable_pow_mul_geometric_of_norm_lt_one k hρ).mul_left (K * C)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have h1 : ‖c n‖ * ‖q‖ ^ n ≤ C * (‖q‖ / r) ^ n := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hr0 n)]
    calc ‖c n‖ * ‖q‖ ^ n * r ^ n = (‖c n‖ * r ^ n) * ‖q‖ ^ n := by ring
      _ ≤ C * ‖q‖ ^ n := by gcongr; exact hC n
  calc ‖d n‖ * ‖q‖ ^ n ≤ (K * (n : ℝ) ^ k * ‖c n‖) * ‖q‖ ^ n := by gcongr; exact hd n
    _ = K * (n : ℝ) ^ k * (‖c n‖ * ‖q‖ ^ n) := by ring
    _ ≤ K * (n : ℝ) ^ k * (C * (‖q‖ / r) ^ n) := by gcongr
    _ = K * C * ((n : ℝ) ^ k * (‖q‖ / r) ^ n) := by ring

/-- **Termwise differentiation** of a power series converging on the unit disc. -/
theorem hasDerivAt_pseries (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => ∑' n, c n * w ^ n) (∑' n, c n * ((n : ℂ) * z ^ (n - 1))) z := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hz
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  have hrr : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr2
  have hs := pseries_summable_norm c (fun n => (n : ℂ) * c n) hc 1 zero_le_one 1
    (fun n => by simp [norm_mul]) hrr
  have hu : Summable (fun n => ‖c n‖ * (n : ℝ) * r ^ (n - 1)) := by
    refine (hs.mul_left r⁻¹).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_mul, Complex.norm_natCast]
    rcases n with _ | n
    · simp
    · rw [pow_succ]; field_simp; simp
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n w => c n * w ^ n)
    (g' := fun n w => c n * ((n : ℂ) * w ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => ?_) (Metric.mem_ball_self hr0) (hc 0 (by simp)) (by simpa using hr1)
  rw [Metric.mem_ball, dist_zero_right] at hy
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, ← mul_assoc]
  gcongr

end PSeries

/-! ## The derivative of the Eichler integral -/

section EichlerDeriv

variable {N : ℕ} [NeZero N] (f : Newform N 2)

theorem eCoeff_summable (q : ℂ) (hq : ‖q‖ < 1) : Summable (fun n => eCoeff f n * q ^ n) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f hq)
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hs.summable

theorem eSum_eq_tsum (q : ℂ) : (eSeries f).sum q = ∑' n, eCoeff f n * q ^ n := by
  rw [eSeries, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp

theorem hasDerivAt_qC (w : ℂ) : HasDerivAt qC (2 * Real.pi * Complex.I * qC w) w := by
  unfold qC
  have := ((hasDerivAt_id w).const_mul (2 * Real.pi * Complex.I)).cexp
  simpa [mul_comm] using this

theorem hasDerivAt_eichler (τ : UpperHalfPlane) :
    HasDerivAt (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * Complex.I * f.toCuspForm τ) τ := by
  have hq := norm_qC_lt_one τ.im_pos
  have h1 := (hasDerivAt_pseries (eCoeff f) (eCoeff_summable f) hq).comp (τ : ℂ) (hasDerivAt_qC τ)
  have hev : (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      ((fun w => ∑' n, eCoeff f n * w ^ n) ∘ qC) := by
    filter_upwards [eichler_ofComplex_eventuallyEq f τ] with w hw
    rw [hw, Function.comp_apply, eSum_eq_tsum]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert h1 using 1
  have key : ∀ n : ℕ, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1)) * (2 * Real.pi * Complex.I * qC τ) =
      2 * Real.pi * Complex.I * (ZInQ.GZDecomp.coeff f n * qC τ ^ n) := by
    intro n
    rcases n with _ | n
    · simp [eCoeff, coeff_zero_newform]
    · simp only [eCoeff, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [pow_succ]
      field_simp
  show _ = (∑' n, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1))) * (2 * Real.pi * Complex.I * qC τ)
  rw [← tsum_mul_right, funext key, tsum_mul_left, (hasSum_newform f τ).tsum_eq]

theorem mdiff_eichler : MDiff (ZInQ.GZHL3.eichler f) := fun τ =>
  UpperHalfPlane.mdifferentiableAt_iff.2 (hasDerivAt_eichler f τ).differentiableAt

theorem D_eichler : Derivative.normalizedDerivOfComplex (ZInQ.GZHL3.eichler f) = ⇑f.toCuspForm := by
  funext τ
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_eichler f τ).deriv]
  field_simp

end EichlerDeriv

/-! ## The Eichler integral at the other cusps -/

section Cusp

variable {N : ℕ} [NeZero N] (f : Newform N 2)

theorem conj_T_mem_Gamma1 (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simp only [CongruenceSubgroup.Gamma_mem, ModularGroup.coe_T_zpow]
    simp
  have h := (CongruenceSubgroup.Gamma_normal (N := N)).conj_mem _ hT γ
  rw [CongruenceSubgroup.Gamma_mem] at h
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨h.1, h.2.2.2, h.2.2.1⟩

/-- `f|₂γ`. -/
def fSlash (γ : SL(2, ℤ)) : UpperHalfPlane → ℂ := (⇑f.toCuspForm) ∣[(2 : ℤ)] γ

theorem fSlash_T (γ : SL(2, ℤ)) :
    fSlash f γ ∣[(2 : ℤ)] (ModularGroup.T ^ (N : ℤ)) = fSlash f γ := by
  unfold fSlash
  rw [← SlashAction.slash_mul]
  have e : γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ := by group
  rw [e, SlashAction.slash_mul]
  congr 1
  rw [ModularForm.SL_slash]
  exact f.toCuspForm.slash_action_eq' _ (Subgroup.mem_map_of_mem _ (conj_T_mem_Gamma1 γ))

theorem fSlash_periodic (γ : SL(2, ℤ)) :
    Function.Periodic (fSlash f γ ∘ UpperHalfPlane.ofComplex) (N : ℝ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + ((N : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have h := congrFun (fSlash_T f γ) ⟨w, hw⟩
    rw [ModularForm.SL_slash_apply] at h
    have h10 : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0) = 0 := by
      rw [show ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0) = (ModularGroup.T ^ (N : ℤ)).1 1 0 from rfl,
        ModularGroup.coe_T_zpow]; simp
    have h11 : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 1) = 1 := by
      rw [show ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 1) = (ModularGroup.T ^ (N : ℤ)).1 1 1 from rfl,
        ModularGroup.coe_T_zpow]; simp
    have hd : UpperHalfPlane.denom (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ))
        (⟨w, hw⟩ : UpperHalfPlane) = 1 := by
      rw [ModularGroup.denom_apply, h10, h11]; simp
    rw [hd, one_zpow, mul_one] at h
    rw [← h]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_zpow_smul]
    simp [add_comm]
  · have hw' : ¬ 0 < (w + ((N : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hw),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hw')]

theorem fSlash_mdiff (γ : SL(2, ℤ)) : MDiff (fSlash f γ) := by
  unfold fSlash
  rw [ModularForm.SL_slash]
  exact (ModularFormClass.holo f.toCuspForm).slash _ _

theorem fSlash_zero (γ : SL(2, ℤ)) : UpperHalfPlane.IsZeroAtImInfty (fSlash f γ) :=
  CuspFormClass.zero_at_infty_slash f.toCuspForm γ

theorem hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- The `q_N`-expansion coefficients of `f|₂γ`. -/
def bCoeff (γ : SL(2, ℤ)) (m : ℕ) : ℂ := (UpperHalfPlane.qExpansion (N : ℝ) (fSlash f γ)).coeff m

theorem hasSum_fSlash (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasSum (fun m => bCoeff f γ m * Function.Periodic.qParam (N : ℝ) τ ^ m) (fSlash f γ τ) := by
  simpa [smul_eq_mul, bCoeff] using UpperHalfPlane.hasSum_qExpansion (hNpos (N := N))
    (fSlash_periodic f γ) (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty τ

theorem bCoeff_summable (γ : SL(2, ℤ)) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m => bCoeff f γ m * q ^ m) := by
  simpa [smul_eq_mul, bCoeff] using (UpperHalfPlane.hasSum_qExpansion_of_norm_lt (hNpos (N := N))
    (fSlash_periodic f γ) (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty hq).summable

theorem bCoeff_zero (γ : SL(2, ℤ)) : bCoeff f γ 0 = 0 := by
  rw [bCoeff, UpperHalfPlane.qExpansion_coeff_zero (hNpos (N := N))
    (UpperHalfPlane.analyticAt_cuspFunction_zero (hNpos (N := N)) (fSlash_periodic f γ)
      (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty) (fSlash_periodic f γ)]
  exact (fSlash_zero f γ).valueAtInfty_eq_zero

/-- The coefficients of the antiderivative `Σ_{m ≥ 1} b_m (N/m) q_N^m`. -/
def betaC (γ : SL(2, ℤ)) (m : ℕ) : ℂ := if m = 0 then 0 else bCoeff f γ m * N / m

theorem betaC_norm (γ : SL(2, ℤ)) (m : ℕ) : ‖betaC f γ m‖ ≤ N * (m : ℝ) ^ 0 * ‖bCoeff f γ m‖ := by
  unfold betaC
  split_ifs with hm
  · simp only [norm_zero, pow_zero, mul_one]; positivity
  · rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ N * ‖bCoeff f γ m‖)
    linarith

theorem betaC_summable_norm (γ : SL(2, ℤ)) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m => ‖betaC f γ m‖ * ‖q‖ ^ m) :=
  pseries_summable_norm (bCoeff f γ) (betaC f γ) (bCoeff_summable f γ) N (by positivity) 0
    (betaC_norm f γ) hq

theorem betaC_summable (γ : SL(2, ℤ)) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m => betaC f γ m * q ^ m) :=
  Summable.of_norm ((betaC_summable_norm f γ hq).congr fun m => by rw [norm_mul, norm_pow])

/-- `G(τ) = Σ_{m ≥ 1} b_m (N/m) q_N(τ)^m`. -/
def Gq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : ℂ :=
  ∑' m, betaC f γ m * Function.Periodic.qParam (N : ℝ) τ ^ m

theorem hasDerivAt_qParamN (w : ℂ) :
    HasDerivAt (fun w => Function.Periodic.qParam (N : ℝ) w)
      (2 * Real.pi * Complex.I / N * Function.Periodic.qParam (N : ℝ) w) w := by
  have := ((hasDerivAt_id w).const_mul (2 * Real.pi * Complex.I / (N : ℂ))).cexp
  convert this using 1
  · funext z; simp [Function.Periodic.qParam]; ring_nf
  · simp [Function.Periodic.qParam]; ring_nf

theorem hasDerivAt_Gq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasDerivAt (Gq f γ ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * Complex.I * fSlash f γ τ) τ := by
  have hq : ‖Function.Periodic.qParam (N : ℝ) (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one (hNpos (N := N)) τ.im_pos
  have h1 := (hasDerivAt_pseries (betaC f γ) (betaC_summable f γ) hq).comp (τ : ℂ)
    (hasDerivAt_qParamN (N := N) τ)
  have hev : (Gq f γ ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      ((fun w => ∑' m, betaC f γ m * w ^ m) ∘ fun w => Function.Periodic.qParam (N : ℝ) w) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply, Gq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert h1 using 1
  set q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have key : ∀ m : ℕ, betaC f γ m * ((m : ℂ) * q ^ (m - 1)) * (2 * Real.pi * Complex.I / N * q) =
      2 * Real.pi * Complex.I * (bCoeff f γ m * q ^ m) := by
    intro m
    rcases m with _ | m
    · simp [betaC, bCoeff_zero]
    · simp only [betaC, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
      have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rw [pow_succ]
      field_simp
  show _ = (∑' m, betaC f γ m * ((m : ℂ) * q ^ (m - 1))) * (2 * Real.pi * Complex.I / N * q)
  rw [← tsum_mul_right, funext key, tsum_mul_left, (hasSum_fSlash f γ τ).tsum_eq]

theorem mdiff_Gq (γ : SL(2, ℤ)) : MDiff (Gq f γ) := fun τ =>
  UpperHalfPlane.mdifferentiableAt_iff.2 (hasDerivAt_Gq f γ τ).differentiableAt

theorem D_Gq (γ : SL(2, ℤ)) : Derivative.normalizedDerivOfComplex (Gq f γ) = fSlash f γ := by
  funext τ
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_Gq f γ τ).deriv]
  field_simp

theorem eichler_slash (γ : SL(2, ℤ)) :
    (ZInQ.GZHL3.eichler f ∣[(0 : ℤ)] γ) = fun τ => ZInQ.GZHL3.eichler f (γ • τ) := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  simp

theorem D_eichler_slash (γ : SL(2, ℤ)) :
    Derivative.normalizedDerivOfComplex (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) = fSlash f γ := by
  rw [← eichler_slash, Derivative.normalizedDerivOfComplex_SL_slash (mdiff_eichler f), D_eichler]
  funext τ
  simp [fSlash]

theorem mdiff_eichler_slash (γ : SL(2, ℤ)) : MDiff (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) := by
  rw [← eichler_slash, ModularForm.SL_slash]
  exact (mdiff_eichler f).slash _ _

/-- **`φ_f(γτ) = K₀ + Σ_{m ≥ 1} b_m (N/m) q_N^m`**: the Eichler integral is holomorphic at every
cusp. -/
theorem exists_const_eichler (γ : SL(2, ℤ)) :
    ∃ K₀ : ℂ, ∀ τ : UpperHalfPlane, ZInQ.GZHL3.eichler f (γ • τ) = K₀ + Gq f γ τ := by
  set H : UpperHalfPlane → ℂ := fun τ => ZInQ.GZHL3.eichler f (γ • τ) - Gq f γ τ with hH
  have hmd : MDiff H := (mdiff_eichler_slash f γ).sub (mdiff_Gq f γ)
  have hD : Derivative.normalizedDerivOfComplex H = 0 := by
    rw [hH, show (fun τ => ZInQ.GZHL3.eichler f (γ • τ) - Gq f γ τ) =
      (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) - Gq f γ from rfl,
      Derivative.normalizedDerivOfComplex_sub _ _ (mdiff_eichler_slash f γ) (mdiff_Gq f γ),
      D_eichler_slash, D_Gq, sub_self]
  have hderiv : Set.EqOn (deriv (H ∘ UpperHalfPlane.ofComplex)) 0 {z : ℂ | 0 < z.im} := by
    intro w hw
    have h := congrFun hD ⟨w, hw⟩
    simp only [Derivative.normalizedDerivOfComplex, Pi.zero_apply] at h
    have h2 : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact (mul_eq_zero.1 h).resolve_left h2
  obtain ⟨a, ha⟩ := UpperHalfPlane.isOpen_upperHalfPlaneSet.exists_is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected (UpperHalfPlane.mdifferentiable_iff.1 hmd) hderiv
  refine ⟨a, fun τ => ?_⟩
  have := ha τ τ.im_pos
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at this
  rw [← this]; simp [hH]

/-- The antiderivative as a power series sum (analytic at `q = 0`). -/
def Gser (γ : SL(2, ℤ)) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (betaC f γ)

theorem Gser_radius (γ : SL(2, ℤ)) : 0 < (Gser f γ).radius := by
  have h := (Gser f γ).le_radius_of_summable_norm (r := (1 / 2 : NNReal)) (by
    have := betaC_summable_norm f γ (q := (1 / 2 : ℂ)) (by norm_num)
    refine this.congr fun m => ?_
    rw [Gser, FormalMultilinearSeries.ofScalars_norm]
    norm_num)
  exact lt_of_lt_of_le (by norm_num) h

theorem Gq_eq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    Gq f γ τ = (Gser f γ).sum (Function.Periodic.qParam (N : ℝ) τ) := by
  rw [Gser, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [Gq]

theorem analyticAt_Gser (γ : SL(2, ℤ)) : AnalyticAt ℂ (Gser f γ).sum 0 :=
  ((Gser f γ).hasFPowerSeriesOnBall (Gser_radius f γ)).analyticAt_of_mem
    (by rw [Metric.mem_eball, edist_self]; exact Gser_radius f γ)

end Cusp

/-- **Moderate growth from meromorphy at the cusp.** If `F(τ) = M(q_N(τ))` with `M` meromorphic at
`q = 0`, then `F(τ) = O(e^{2πk Im τ})` as `Im τ → ∞`. -/
theorem growth_of_meromorphicAt {N : ℕ} [NeZero N] {M : ℂ → ℂ} (hM : MeromorphicAt M 0)
    (F : UpperHalfPlane → ℂ) (hF : ∀ τ, F τ = M (Function.Periodic.qParam (N : ℝ) τ)) :
    ∃ k : ℕ, F =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im) := by
  obtain ⟨n, hn⟩ := hM
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hn.continuousAt 1 one_pos
  set C : ℝ := ‖(fun z => (z - 0) ^ n • M z) 0‖ + 1
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨n, Asymptotics.IsBigO.of_bound C ?_⟩
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨N * |Real.log δ| / (2 * Real.pi) + 1, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq]
  set q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hqn : ‖q‖ = Real.exp (-2 * Real.pi * τ.im / N) := by
    rw [Function.Periodic.norm_qParam (N : ℝ) (τ : ℂ)]; rfl
  have hqδ : ‖q‖ < δ := by
    rw [hqn]
    have hπ := Real.pi_pos
    have h1 : -2 * Real.pi * τ.im / N < Real.log δ := by
      have hA : N * |Real.log δ| / (2 * Real.pi) < τ.im := by linarith [hτ]
      rw [div_lt_iff₀ (by positivity) ] at hA
      have : -2 * Real.pi * τ.im / N < -|Real.log δ| := by
        rw [div_lt_iff₀ hNpos']; nlinarith
      linarith [neg_abs_le (Real.log δ)]
    calc Real.exp (-2 * Real.pi * τ.im / N) < Real.exp (Real.log δ) := Real.exp_lt_exp.2 h1
      _ = δ := Real.exp_log hδ
  have hb := hδb (x := q) (by rw [dist_zero_right]; exact hqδ)
  rw [dist_eq_norm] at hb
  have hb' : ‖(q - 0) ^ n • M q‖ ≤ C := by
    have := norm_sub_norm_le ((fun z => (z - 0) ^ n • M z) q) ((fun z => (z - 0) ^ n • M z) 0)
    simp only at this; linarith
  rw [sub_zero, norm_smul, norm_pow] at hb'
  have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
  rw [hF τ, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hM' : ‖M q‖ ≤ C / ‖q‖ ^ n := by
    rw [le_div_iff₀ (pow_pos hqpos n)]; linarith [mul_comm (‖q‖ ^ n) ‖M q‖]
  refine hM'.trans ?_
  rw [div_le_iff₀ (pow_pos hqpos n), hqn, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  have hC : 0 ≤ C := by positivity
  have h2 : 2 * Real.pi * n * τ.im + n * (-2 * Real.pi * τ.im / N) ≥ 0 := by
    have hτ0 : 0 < τ.im := τ.im_pos
    have h3 : n * (2 * Real.pi * τ.im / N) ≤ n * (2 * Real.pi * τ.im) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      rw [div_le_iff₀ hNpos']
      have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hτ0.le)
        (sub_nonneg.2 this)]
    have : n * (-2 * Real.pi * τ.im / N) = -(n * (2 * Real.pi * τ.im / N)) := by ring
    rw [this]; nlinarith
  calc C = C * 1 := (mul_one C).symm
    _ ≤ C * Real.exp (2 * Real.pi * n * τ.im + n * (-2 * Real.pi * τ.im / N)) := by
        gcongr; exact Real.one_le_exp h2


theorem meromorphicAt_wpb (L : PeriodPair) (b z₀ : ℂ) :
    MeromorphicAt (fun z => L.weierstrassP z - b) z₀ :=
  (meromorphicAt_wp L z₀).sub (MeromorphicAt.const _ _)

theorem meromorphicAt_psi (L : PeriodPair) (a₁ a₃ b z₀ : ℂ) :
    MeromorphicAt (fun z => (L.derivWeierstrassP z - a₁ * (L.weierstrassP z - b) - a₃) / 2) z₀ :=
  (((meromorphicAt_dwp L z₀).sub ((MeromorphicAt.const _ _).mul (meromorphicAt_wpb L b z₀))).sub
    (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)

/-- **`ParamCuspGrowth`, proved.** -/
theorem paramCuspGrowth : ParamCuspGrowth := by
  intro E _ N _ f L c _ γ
  obtain ⟨K₀, hK⟩ := exists_const_eichler f γ
  set Z : ℂ → ℂ := fun q => (c : ℂ) * K₀ + (c : ℂ) * (Gser f γ).sum q with hZdef
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_const.add (analyticAt_const.mul (analyticAt_Gser f γ))
  have hz : ∀ τ : UpperHalfPlane, zPar f c (γ • τ) = Z (Function.Periodic.qParam (N : ℝ) τ) := by
    intro τ; simp only [zPar, hK, Gq_eq, hZdef]; ring
  set b : ℂ := (E⁄ℂ).b₂ / 12 with hb
  refine ⟨growth_of_meromorphicAt (N := N) ((meromorphicAt_wpb L b _).comp_analyticAt hZ) _
      (fun τ => by simp only [xPar, hz, Function.comp_apply, hb]),
    growth_of_meromorphicAt (N := N)
      ((meromorphicAt_psi L (E⁄ℂ).a₁ (E⁄ℂ).a₃ b _).comp_analyticAt hZ) _
      (fun τ => by simp only [yPar, xPar, hz, Function.comp_apply, hb]),
    fun t => growth_of_meromorphicAt (N := N) ((meromorphicAt_phiT L (b + t) _).comp_analyticAt hZ)
      _ (fun τ => by
        show gPar E L f c t (γ • τ) = phiT L (b + t) (Z (Function.Periodic.qParam (N : ℝ) τ))
        unfold gPar phiT xPar
        rw [hz τ, sub_sub])⟩


end AnalyticGlue

/-! ## §9. The analytic glue `ParamQExpansion`, proved -/

section QExpansionGlue

open scoped Manifold ModularForm

/-! ## Taylor series at `0` as power series; the Weierstrass equation in `q` -/

section Taylor

open PowerSeries Nat

/-- The Taylor series of `f` at `0`. -/
def tay (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => ((n ! : ℂ))⁻¹ * iteratedDeriv n f 0

theorem coeff_tay (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (tay f) = ((n ! : ℂ))⁻¹ * iteratedDeriv n f 0 := by
  simp [tay]

theorem tay_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : tay f = tay g := by
  ext n; rw [coeff_tay, coeff_tay, h.iteratedDeriv_eq n]

theorem tay_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w + g w) = tay f + tay g := by
  ext n
  rw [coeff_tay, map_add, coeff_tay, coeff_tay,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt]
  ring

theorem tay_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w - g w) = tay f - tay g := by
  ext n
  rw [coeff_tay, map_sub, coeff_tay, coeff_tay,
    iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt]
  ring

theorem tay_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w * g w) = tay f * tay g := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_tay, coeff_tay]
  have hkn : k ≤ n := Nat.lt_succ_iff.1 hk
  have h := Nat.choose_mul_factorial_mul_factorial hkn
  have h1 : ((n ! : ℂ)) = (n.choose k : ℂ) * (k ! : ℂ) * ((n - k) ! : ℂ) := by exact_mod_cast h.symm
  have hk0 : ((k ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk0 : (((n - k) ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hc0 : ((n.choose k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [h1]
  field_simp

theorem tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rw [coeff_tay, iteratedDeriv_const, PowerSeries.coeff_C]
  split_ifs <;> simp_all

theorem tay_id : tay (fun w => w) = PowerSeries.X := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  split_ifs with h <;> simp [h]

theorem tay_deriv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) : tay (deriv f) = d⁄dX (tay f) := by
  ext n
  rw [coeff_tay, PowerSeries.coeff_derivative, coeff_tay, ← iteratedDeriv_succ']
  rw [Nat.factorial_succ]
  push_cast
  have : ((n ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- The Weierstrass equation for `Y = w²(℘(Z(w)) − b)` as a formal power series identity:
`(wY' − 2Y)² = (4(Y + bw²)³ − g₂w⁴(Y + bw²) − g₃w⁶)·A`. -/
def odePhi (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) (S : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  (X * d⁄dX S - 2 * S) ^ 2 -
    (4 * (S + C b * X ^ 2) ^ 3 - C g₂ * X ^ 4 * (S + C b * X ^ 2) - C g₃ * X ^ 6) * A

theorem X_mul_derivative_X_pow_mul (n : ℕ) (ε : ℂ⟦X⟧) :
    X * d⁄dX (X ^ n * ε) = X ^ n * (C (n : ℂ) * ε + X * d⁄dX ε) := by
  rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_X, smul_eq_mul,
    smul_eq_mul]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ, map_natCast]
    push_cast
    ring

/-- **Uniqueness of the formal solution with given constant term.** -/
theorem odePhi_unique (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) {S T : ℂ⟦X⟧} (hS : odePhi A b g₂ g₃ S = 0)
    (hT : odePhi A b g₂ g₃ T = 0) (h0 : constantCoeff S = constantCoeff T)
    (hne : constantCoeff S ≠ 0) (hA : constantCoeff A * constantCoeff S = 1) : S = T := by
  suffices h : ∀ n, ∀ m < n, PowerSeries.coeff m S = PowerSeries.coeff m T by
    ext m; exact h (m + 1) m (Nat.lt_succ_self m)
  intro n
  induction n with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact ih m hm
    obtain ⟨ε, hε⟩ : X ^ m ∣ S - T := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro k hk; rw [map_sub, ih k hk, sub_self]
    have hSe : S = T + X ^ m * ε := by rw [← hε]; ring
    have hdS : X * d⁄dX S = X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) := by
      rw [hSe, map_add, mul_add, X_mul_derivative_X_pow_mul]
    have key : odePhi A b g₂ g₃ S - odePhi A b g₂ g₃ T = X ^ m *
        ((X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) - 2 * S + (X * d⁄dX T - 2 * T)) *
          (C (m : ℂ) * ε + X * d⁄dX ε - 2 * ε) -
        A * (4 * ((S + C b * X ^ 2) ^ 2 + (S + C b * X ^ 2) * (T + C b * X ^ 2) +
          (T + C b * X ^ 2) ^ 2) - C g₂ * X ^ 4) * ε) := by
      unfold odePhi
      rw [hdS, hSe]
      ring
    set B := (X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) - 2 * S + (X * d⁄dX T - 2 * T)) *
          (C (m : ℂ) * ε + X * d⁄dX ε - 2 * ε) -
        A * (4 * ((S + C b * X ^ 2) ^ 2 + (S + C b * X ^ 2) * (T + C b * X ^ 2) +
          (T + C b * X ^ 2) ^ 2) - C g₂ * X ^ 4) * ε with hBdef
    rw [hS, hT, sub_zero] at key
    have hB : B = 0 := (mul_eq_zero.1 key.symm).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
    have hc := congrArg constantCoeff hB
    have hX0 : constantCoeff (X : ℂ⟦X⟧) = 0 := PowerSeries.constantCoeff_X
    simp only [hBdef, map_sub, map_add, map_mul, map_pow, hX0, PowerSeries.constantCoeff_C,
      map_ofNat, zero_mul, mul_zero, zero_pow (two_ne_zero), zero_add, add_zero, sub_zero,
      map_zero] at hc
    rw [← h0] at hc
    set s₀ := constantCoeff S
    set e₀ := constantCoeff ε
    have hz : (0 : ℂ) ^ m * (m : ℂ) = 0 := by rcases m with _ | m <;> simp
    have hc' : -4 * s₀ * e₀ * ((m : ℂ) - 2 + 3 * (constantCoeff A * s₀)) = 0 := by
      linear_combination hc + e₀ ^ 2 * (2 - (m : ℂ)) * hz
    rw [hA] at hc'
    have hm1 : ((m : ℂ) - 2 + 3 * 1) ≠ 0 := by
      have : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      convert this using 1; ring
    have he : e₀ = 0 := by
      rcases mul_eq_zero.1 hc' with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; apply hne; have : (-4 : ℂ) ≠ 0 := by norm_num
          exact (mul_eq_zero.1 h).resolve_left this
        · exact h
      · exact absurd h hm1
    have : PowerSeries.coeff m (S - T) = 0 := by
      rw [hε, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact he
    rw [map_sub, sub_eq_zero] at this
    exact this

theorem map_derivative (σ : ℂ →+* ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.map σ (d⁄dX S) = d⁄dX (PowerSeries.map σ S) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  simp

theorem map_odePhi (σ : ℂ →+* ℂ) (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.map σ (odePhi A b g₂ g₃ S) =
      odePhi (PowerSeries.map σ A) (σ b) (σ g₂) (σ g₃) (PowerSeries.map σ S) := by
  simp only [odePhi, map_sub, map_mul, map_pow, map_add, PowerSeries.map_X, PowerSeries.map_C,
    map_derivative, map_ofNat]

/-- **The fixed field of `Aut(ℂ)` is `ℚ`.** -/
theorem rat_of_fixed (z : ℂ) (hz : ∀ σ : ℂ ≃+* ℂ, σ z = z) : ∃ q : ℚ, (q : ℂ) = z := by
  obtain ⟨a, ha⟩ := T5Glue.fixedAlgebraic z (fun σ _ => hz σ)
  have hfix : ∀ ρ : Qbar ≃ₐ[ℚ] Qbar, ρ a = a := by
    intro ρ
    obtain ⟨σ, hσ⟩ := T5Glue.autExtends ρ
    apply ιC.injective
    rw [← hσ, ha, hz]
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 hfix
  exact ⟨q, by rw [← ha, ← hq]; simp⟩

end Taylor

/-! ## The `q`-expansion of `x∘φ` at `∞` -/

section QExp

open PowerSeries

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- `V(w) = Σ e_{n+1} wⁿ`, so that `φ_f = q·V(q)`. -/
def vSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => eCoeff f (n + 1))

def vFun : ℂ → ℂ := (vSeries f).sum

theorem vCoeff_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n => eCoeff f (n + 1) * q ^ n) := by
  have h := (summable_nat_add_iff 1).2 (eCoeff_summable f q hq)
  by_cases h0 : q = 0
  · subst h0; exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by
      simp at hn; simp [hn])
  · refine (h.mul_left q⁻¹).congr fun n => ?_
    rw [pow_succ]; field_simp

theorem vSeries_le_radius (r : NNReal) (hr : (r : ℝ) < 1) : (r : ENNReal) ≤ (vSeries f).radius := by
  apply (vSeries f).le_radius_of_tendsto (l := 0)
  have hr' : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr
  have ht := (vCoeff_summable f ((r : ℝ) : ℂ) hr').tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  refine ht.congr fun n => ?_
  simp [vSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]

theorem vSeries_mem_ball {w : ℂ} (hw : ‖w‖ < 1) : w ∈ Metric.eball (0 : ℂ) (vSeries f).radius := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖w‖₊ : ENNReal) < (r' : ENNReal) := by rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
    _ ≤ _ := vSeries_le_radius f r' hr2

theorem vSeries_radius_pos : 0 < (vSeries f).radius := by
  have := vSeries_mem_ball f (w := 0) (by simp)
  rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this

theorem vFun_hasFPS : HasFPowerSeriesOnBall (vFun f) (vSeries f) 0 (vSeries f).radius :=
  (vSeries f).hasFPowerSeriesOnBall (vSeries_radius_pos f)

theorem analyticAt_vFun : AnalyticAt ℂ (vFun f) 0 := (vFun_hasFPS f).analyticAt

theorem vFun_eq (q : ℂ) (hq : ‖q‖ < 1) : vFun f q = ∑' n, eCoeff f (n + 1) * q ^ n := by
  have hs := (vSeries f).hasSum (vSeries_mem_ball f hq)
  simp only [vSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hs.tsum_eq.symm

theorem eSum_eq_mul_vFun (q : ℂ) (hq : ‖q‖ < 1) : (eSeries f).sum q = q * vFun f q := by
  rw [eSum_eq_tsum, vFun_eq f q hq, ← tsum_mul_left,
    (eCoeff_summable f q hq).tsum_eq_zero_add]
  have h0 : eCoeff f 0 = 0 := by simp [eCoeff]
  rw [h0, zero_mul, zero_add]
  congr 1; funext n; rw [pow_succ]; ring

theorem eCoeff_one : eCoeff f 1 = 1 := by
  simp only [eCoeff, one_ne_zero, if_false, Nat.cast_one, div_one]
  exact f.isNorm

theorem vFun_zero : vFun f 0 = 1 := by
  rw [vFun_eq f 0 (by simp), tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp [eCoeff_one]

theorem coeff_tay_vFun (n : ℕ) : PowerSeries.coeff n (tay (vFun f)) = eCoeff f (n + 1) := by
  rw [coeff_tay]
  have h := (vFun_hasFPS f).factorial_smul 1 n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp only [vSeries, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    nsmul_eq_mul]
  have : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

variable (L : PeriodPair)

/-- `Z(w) = c·w·V(w)` (`= c φ_f` at `w = q`). -/
def zF (c : ℂ) (w : ℂ) : ℂ := c * w * vFun f w

/-- `Ŷ(w) = w²℘_{L−0}(Z(w)) + (c²V(w)²)⁻¹ − b w²` (`= w²(℘(Z(w)) − b)` for `w ≠ 0`). -/
def yF (c b : ℂ) (w : ℂ) : ℂ :=
  w ^ 2 * L.weierstrassPExcept 0 (zF f c w) + (c ^ 2 * vFun f w ^ 2)⁻¹ - b * w ^ 2

theorem analyticAt_vFun_of {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (vFun f) w :=
  (vFun_hasFPS f).analyticAt_of_mem (vSeries_mem_ball f hw)

theorem analyticAt_zF (c : ℂ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (zF f c) w := by
  have := analyticAt_vFun_of f hw
  unfold zF; fun_prop

theorem zF_zero (c : ℂ) : zF f c 0 = 0 := by simp [zF]

theorem analyticAt_yF {c : ℂ} (hc : c ≠ 0) (b : ℂ) : AnalyticAt ℂ (yF f L c b) 0 := by
  have hV := analyticAt_vFun f
  have hE : AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (zF f c w)) 0 := by
    exact (L.analyticAt_weierstrassPExcept 0).comp_of_eq (analyticAt_zF f c (by simp))
      (zF_zero f c)
  have hden : AnalyticAt ℂ (fun w => c ^ 2 * vFun f w ^ 2) 0 := by fun_prop
  have hne : c ^ 2 * vFun f 0 ^ 2 ≠ 0 := by rw [vFun_zero]; simpa using hc
  unfold yF
  exact ((analyticAt_id.pow 2).mul hE).add (hden.inv hne) |>.sub (analyticAt_const.mul
    (analyticAt_id.pow 2))

theorem yF_zero (c b : ℂ) : yF f L c b 0 = (c ^ 2)⁻¹ := by simp [yF, vFun_zero]

/-- A punctured ball around `0` on which `V ≠ 0` and `Z(w) ∉ L`. -/
theorem exists_good_ball {c : ℂ} (hc : c ≠ 0) :
    ∃ ε > 0, ε ≤ 1 / 2 ∧ ∀ w : ℂ, ‖w‖ < ε → vFun f w ≠ 0 ∧ (w ≠ 0 → zF f c w ∉ L.lattice) := by
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 (analyticAt_vFun f).continuousAt (1 / 2)
    (by norm_num)
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨min (min δ (r / (2 * ‖c‖))) (1 / 2), by positivity, min_le_right _ _, fun w hw => ?_⟩
  have hw1 : ‖w‖ < δ := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_left _ _))
  have hw2 : ‖w‖ < r / (2 * ‖c‖) := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_right _ _))
  have hV := hδb (x := w) (by rwa [dist_zero_right])
  rw [dist_eq_norm, vFun_zero] at hV
  have hVne : vFun f w ≠ 0 := by
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hV; norm_num at hV
  have hVle : ‖vFun f w‖ < 3 / 2 := by
    have := norm_le_norm_sub_add (vFun f w) 1
    rw [norm_one] at this; linarith
  refine ⟨hVne, fun hw0 hzL => ?_⟩
  have hz0 : zF f c w ≠ 0 := by
    unfold zF; exact mul_ne_zero (mul_ne_zero hc hw0) hVne
  have hzr : zF f c w ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, zF, norm_mul, norm_mul]
    calc ‖c‖ * ‖w‖ * ‖vFun f w‖ ≤ ‖c‖ * ‖w‖ * (3 / 2) := by gcongr
      _ < ‖c‖ * (r / (2 * ‖c‖)) * (3 / 2) := by gcongr
      _ = 3 / 4 * r := by field_simp; ring
      _ < r := by linarith
  exact hrb hzr ⟨hzL, hz0⟩

theorem yF_eq {c : ℂ} (hc : c ≠ 0) (b : ℂ) {w : ℂ} (hV : vFun f w ≠ 0) (hw : w ≠ 0) :
    yF f L c b w = w ^ 2 * (L.weierstrassP (zF f c w) - b) := by
  have h := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ (zF f c w)
  simp only [sub_zero, div_zero, one_div, zero_pow two_ne_zero, inv_zero] at h
  unfold yF
  rw [← h]
  simp only [zF]
  field_simp

theorem hasDerivAt_wp {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (analyticAt_wp L hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at hd

theorem constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tay]; simp

theorem tay_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    tay (fun w => f w ^ n) = (tay f) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; rw [tay_const]; rfl
  | succ n ih =>
    have e : (fun w => f w ^ (n + 1)) = fun w => f w ^ n * f w := by funext w; ring
    have h := tay_mul (f := fun w => f w ^ n) (g := f) (hf.pow n) hf
    beta_reduce at h
    rw [e, h, ih, pow_succ]

theorem tay_cmul (c : ℂ) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    tay (fun w => c * f w) = PowerSeries.C c * tay f := by
  rw [tay_mul analyticAt_const hf, tay_const]

theorem tay_X_pow (n : ℕ) : tay (fun w => w ^ n) = PowerSeries.X ^ n := by
  have := tay_pow (f := fun w => w) analyticAt_id n
  simpa [tay_id] using this

/-- On the punctured good ball: `wŶ' − 2Ŷ = w³ ℘'(Z(w)) Z'(w)`. -/
theorem yF_deriv_eq {c : ℂ} (hc : c ≠ 0) (b : ℂ) {ε : ℝ} (hε1 : ε ≤ 1 / 2)
    (hgood : ∀ w : ℂ, ‖w‖ < ε → vFun f w ≠ 0 ∧ (w ≠ 0 → zF f c w ∉ L.lattice)) {w : ℂ}
    (hw : ‖w‖ < ε) (hw0 : w ≠ 0) :
    w * deriv (yF f L c b) w - 2 * yF f L c b w =
      w ^ 3 * L.derivWeierstrassP (zF f c w) * deriv (zF f c) w := by
  obtain ⟨hV, hZL⟩ := hgood w hw
  have hzL := hZL hw0
  have hopen : IsOpen {v : ℂ | v ≠ 0 ∧ ‖v‖ < ε} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : yF f L c b =ᶠ[nhds w] fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b) := by
    filter_upwards [hopen.mem_nhds ⟨hw0, hw⟩] with v hv
    exact yF_eq f L hc b (hgood v hv.2).1 hv.1
  have hZw : HasDerivAt (zF f c) (deriv (zF f c) w) w :=
    (analyticAt_zF f c (by linarith : ‖w‖ < 1)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hd : HasDerivAt (fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b))
      (2 * w * (L.weierstrassP (zF f c w) - b) +
        w ^ 2 * (L.derivWeierstrassP (zF f c w) * deriv (zF f c) w)) w :=
    h1.mul (((hasDerivAt_wp L hzL).comp w hZw).sub_const b)
  rw [hev.deriv_eq, hd.deriv, yF_eq f L hc b hV hw0]
  ring

/-- **The Weierstrass equation in the variable `w`**, near `0`. -/
theorem yF_ode {c : ℂ} (hc : c ≠ 0) (b : ℂ) :
    (fun w => (w * deriv (yF f L c b) w - 2 * yF f L c b w) ^ 2) =ᶠ[nhds 0]
      fun w => (4 * (yF f L c b w + b * w ^ 2) ^ 3 - L.g₂ * w ^ 4 * (yF f L c b w + b * w ^ 2) -
        L.g₃ * w ^ 6) * deriv (zF f c) w ^ 2 := by
  obtain ⟨ε, hε, hε1, hgood⟩ := exists_good_ball f L hc
  have hY := analyticAt_yF f L hc b
  have hZ := analyticAt_zF f c (w := 0) (by simp)
  refine (AnalyticAt.frequently_eq_iff_eventually_eq (by fun_prop) (by
    have := hY.deriv; have := hZ.deriv; fun_prop)).1 ?_
  refine Filter.Eventually.frequently ?_
  have hball : Metric.ball (0 : ℂ) ε ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 hε
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hw0
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw0' : w ≠ 0 := hw0
  obtain ⟨hV, hZL⟩ := hgood w hw
  have hzL := hZL hw0'
  -- `Ŷ = w²(℘∘Z − b)` near `w`
  have hopen : IsOpen {v : ℂ | v ≠ 0 ∧ ‖v‖ < ε} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : yF f L c b =ᶠ[nhds w] fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b) := by
    filter_upwards [hopen.mem_nhds ⟨hw0', hw⟩] with v hv
    exact yF_eq f L hc b (hgood v hv.2).1 hv.1
  have hZw : HasDerivAt (zF f c) (deriv (zF f c) w) w :=
    (analyticAt_zF f c (by linarith : ‖w‖ < 1)).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b))
      (2 * w * (L.weierstrassP (zF f c w) - b) +
        w ^ 2 * (L.derivWeierstrassP (zF f c w) * deriv (zF f c) w)) w := by
    have h1 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    have h2 := ((hasDerivAt_wp L hzL).comp w hZw).sub_const b
    exact h1.mul h2
  rw [hev.deriv_eq, hd.deriv, yF_eq f L hc b hV hw0']
  have hsq := L.derivWeierstrassP_sq _ hzL
  set P := L.weierstrassP (zF f c w)
  set P' := L.derivWeierstrassP (zF f c w)
  set Z' := deriv (zF f c) w
  have e1 : w * (2 * w * (P - b) + w ^ 2 * (P' * Z')) - 2 * (w ^ 2 * (P - b)) = w ^ 3 * P' * Z' := by
    ring
  rw [e1]
  linear_combination (w ^ 6 * Z' ^ 2) * hsq

theorem C_two : (PowerSeries.C (2 : ℂ) : ℂ⟦X⟧) = 2 := map_ofNat _ 2
theorem C_four : (PowerSeries.C (4 : ℂ) : ℂ⟦X⟧) = 4 := map_ofNat _ 4

/-- **The formal Weierstrass equation for the Taylor series of `Ŷ`.** -/
theorem tay_yF_ode {c : ℂ} (hc : c ≠ 0) (b : ℂ) :
    odePhi (d⁄dX (tay (zF f c)) ^ 2) b L.g₂ L.g₃ (tay (yF f L c b)) = 0 := by
  set Y := yF f L c b with hYdef
  set Z := zF f c with hZdef
  have hY : AnalyticAt ℂ Y 0 := analyticAt_yF f L hc b
  have hdY := hY.deriv
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_zF f c (w := 0) (by simp)
  have hdZ := hZ.deriv
  have h := tay_congr (yF_ode f L hc b)
  -- left side
  have l1 := tay_pow (f := fun w => w * deriv Y w - 2 * Y w) (by fun_prop) 2
  have l2 := tay_sub (f := fun w => w * deriv Y w) (g := fun w => 2 * Y w) (by fun_prop)
    (by fun_prop)
  have l3 := tay_mul (f := fun w => w) (g := deriv Y) analyticAt_id hdY
  have l4 := tay_cmul 2 hY
  beta_reduce at l1 l2 l3 l4
  -- right side
  set U := fun w => Y w + b * w ^ 2 with hUdef
  have hU : AnalyticAt ℂ U 0 := by fun_prop
  have r1 := tay_mul (f := fun w => 4 * U w ^ 3 - L.g₂ * w ^ 4 * U w - L.g₃ * w ^ 6)
    (g := fun w => deriv Z w ^ 2) (by fun_prop) (by fun_prop)
  have r2 := tay_pow (f := deriv Z) hdZ 2
  have r3 := tay_sub (f := fun w => 4 * U w ^ 3 - L.g₂ * w ^ 4 * U w) (g := fun w => L.g₃ * w ^ 6)
    (by fun_prop) (by fun_prop)
  have r4 := tay_sub (f := fun w => 4 * U w ^ 3) (g := fun w => L.g₂ * w ^ 4 * U w)
    (by fun_prop) (by fun_prop)
  have r5 := tay_cmul 4 (f := fun w => U w ^ 3) (by fun_prop)
  have r6 := tay_pow hU 3
  have r7 := tay_mul (f := fun w => L.g₂ * w ^ 4) (g := U) (by fun_prop) hU
  have r8 := tay_cmul L.g₂ (f := fun w => w ^ 4) (by fun_prop)
  have r9 := tay_cmul L.g₃ (f := fun w => w ^ 6) (by fun_prop)
  have r10 := tay_add (f := Y) (g := fun w => b * w ^ 2) hY (by fun_prop)
  have r11 := tay_cmul b (f := fun w => w ^ 2) (by fun_prop)
  beta_reduce at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hUt : tay U = tay Y + PowerSeries.C b * X ^ 2 := by
    rw [hUdef, r10, r11, tay_X_pow]
  rw [l1, l2, l3, l4, tay_id, tay_deriv hY, C_two] at h
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, tay_X_pow, tay_X_pow, tay_deriv hZ, hUt, C_four] at h
  unfold odePhi
  rw [h, sub_self]

/-- `tay Z = c·X·tay V`. -/
theorem tay_zF (c : ℂ) : tay (zF f c) = C c * X * tay (vFun f) := by
  have hV := analyticAt_vFun f
  have e : zF f c = fun w => c * w * vFun f w := rfl
  have h1 := tay_mul (f := fun w => c * w) (g := vFun f) (by fun_prop) hV
  have h2 := tay_cmul c (f := fun w => w) analyticAt_id
  beta_reduce at h1 h2
  rw [e, h1, h2, tay_id]

theorem map_tay_vFun (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (vFun f)) = tay (vFun f) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_tay_vFun]
  obtain ⟨q, hq⟩ := hV (n + 1)
  rw [hq, map_ratCast]

theorem map_tay_zF (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) (c : ℚ) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (zF f c)) = tay (zF f c) := by
  rw [tay_zF, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_X, map_tay_vFun f hV σ,
    map_ratCast]

/-- **The Taylor series of `Ŷ` is fixed by `Aut(ℂ)`** (all data rational; uniqueness of the formal
solution). -/
theorem map_tay_yF (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) {c : ℚ} (hc : c ≠ 0) (b : ℚ) {g₂ g₃ : ℚ}
    (hg₂ : L.g₂ = g₂) (hg₃ : L.g₃ = g₃) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (yF f L c b)) = tay (yF f L c b) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hode := tay_yF_ode f L hc' b
  rw [hg₂, hg₃] at hode
  set A := d⁄dX (tay (zF f c)) ^ 2 with hAdef
  have hAfix : PowerSeries.map σ A = A := by
    rw [hAdef, map_pow, map_derivative, map_tay_zF f hV c σ]
  have hS : odePhi A b g₂ g₃ (PowerSeries.map σ (tay (yF f L c b))) = 0 := by
    have := congrArg (PowerSeries.map σ) hode
    rw [map_odePhi, map_zero, hAfix, map_ratCast, map_ratCast, map_ratCast] at this
    exact this
  refine (odePhi_unique A b g₂ g₃ hode hS ?_ ?_ ?_).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tay, yF_zero]
    rw [show ((c : ℂ) ^ 2)⁻¹ = (((c ^ 2)⁻¹ : ℚ) : ℂ) by push_cast; rfl, map_ratCast]
  · rw [constantCoeff_tay, yF_zero]; simpa using hc'
  · rw [hAdef, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative, tay_zF, constantCoeff_tay, yF_zero,
      show (C (c : ℂ) * X * tay (vFun f)) = C (c : ℂ) * (X * tay (vFun f)) by ring]
    simp only [zero_add, Nat.cast_zero, PowerSeries.coeff_C_mul, mul_one]
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tay, vFun_zero]
    field_simp

/-- **A rational `q`-expansion from a Taylor series fixed by `Aut(ℂ)`.** -/
theorem hasRatQExp_of_tay (g : UpperHalfPlane → ℂ) (W : ℂ → ℂ) (hW : AnalyticAt ℂ W 0)
    (hfix : ∀ σ : ℂ ≃+* ℂ, PowerSeries.map (σ : ℂ →+* ℂ) (tay W) = tay W) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hg : ∀ τ : UpperHalfPlane, ‖qC τ‖ < ε → qC τ ^ k * g τ = W (qC τ)) :
    HasRatQExp g := by
  have hrat : ∀ n, ∃ a : ℚ, (a : ℂ) = PowerSeries.coeff n (tay W) := fun n =>
    rat_of_fixed _ fun σ => by
      have := congrArg (PowerSeries.coeff n) (hfix σ)
      rwa [PowerSeries.coeff_map] at this
  choose a ha using hrat
  obtain ⟨r, hr, hAn⟩ := hW.exists_ball_analyticOnNhd
  set ρ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  refine ⟨k, a, |Real.log ρ| / (2 * Real.pi) + 1, fun τ hτ => ?_⟩
  have hq : ‖qC τ‖ < ρ := by
    rw [qC, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * τ).re = -(2 * Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hπ := Real.pi_pos
    have h1 : -(2 * Real.pi * τ.im) < Real.log ρ := by
      have hA : |Real.log ρ| / (2 * Real.pi) < τ.im := by linarith
      rw [div_lt_iff₀ (by positivity)] at hA
      linarith [neg_abs_le (Real.log ρ)]
    calc Real.exp (-(2 * Real.pi * τ.im)) < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 h1
      _ = ρ := Real.exp_log hρ
  have hqε : ‖qC τ‖ < ε := lt_of_lt_of_le hq (min_le_left _ _)
  have hqr : qC τ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq (min_le_right _ _)
  have hs := Complex.hasSum_taylorSeries_on_ball (hAn.differentiableOn) hqr
  rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = qC τ from rfl, hg τ hqε]
  convert hs using 1
  funext n
  rw [ha n, coeff_tay, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- The fixed-by-`Aut(ℂ)` property is inherited through a product with a fixed series. -/
theorem fixed_of_mul {T U R : ℂ⟦X⟧} (hU : U ≠ 0) (h : T * U = R) (σ : ℂ →+* ℂ)
    (hUf : PowerSeries.map σ U = U) (hRf : PowerSeries.map σ R = R) :
    PowerSeries.map σ T = T := by
  have := congrArg (PowerSeries.map σ) h
  rw [map_mul, hUf, hRf, ← h] at this
  exact mul_right_cancel₀ hU this

theorem hasDerivAt_zF_zero (c : ℂ) : HasDerivAt (zF f c) c 0 := by
  have hV := (analyticAt_vFun f).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_id (0 : ℂ)).const_mul c).mul hV
  convert h using 1
  · funext w; simp [zF]
  · simp [vFun_zero]

theorem eCoeff_rat (E : WeierstrassCurve ℚ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) (n : ℕ) :
    ∃ q : ℚ, eCoeff f n = q := by
  unfold eCoeff
  split_ifs with hn
  · exact ⟨0, by simp⟩
  · exact ⟨((E.LFunction n : ℤ) : ℚ) / n, by rw [hcoeff n hn]; push_cast; ring⟩

/-- **`ParamQExpansion`, proved.** -/
theorem paramQExpansion : ParamQExpansion := by
  intro E _ N _ f L c hs
  obtain ⟨-, hcoeff, hL, hc, -⟩ := hs
  have hV := eCoeff_rat f E hcoeff
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  -- rational constants
  set bq : ℚ := E.b₂ / 12
  have hb : (E⁄ℂ).b₂ / 12 = (bq : ℂ) := by
    simp [bq, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂]
  have hg₂ : L.g₂ = ((E.c₄ / 12 : ℚ) : ℂ) := by
    rw [hL.1]; simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
  have hg₃ : L.g₃ = ((E.c₆ / 216 : ℚ) : ℂ) := by
    rw [hL.2]; simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
  have ha₁ : (E⁄ℂ).a₁ = ((E.a₁ : ℚ) : ℂ) := by simp [WeierstrassCurve.baseChange]
  have ha₃ : (E⁄ℂ).a₃ = ((E.a₃ : ℚ) : ℂ) := by simp [WeierstrassCurve.baseChange]
  set Y := yF f L c bq with hYdef
  set Z := zF f c with hZdef
  have hY : AnalyticAt ℂ Y 0 := analyticAt_yF f L hc' _
  have hdY := hY.deriv
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_zF f c (w := 0) (by simp)
  have hdZ := hZ.deriv
  have hYfix : ∀ σ : ℂ →+* ℂ, PowerSeries.map σ (tay Y) = tay Y := fun σ =>
    map_tay_yF f L hV hc bq hg₂ hg₃ σ
  have hZfix : ∀ σ : ℂ →+* ℂ, PowerSeries.map σ (tay Z) = tay Z := fun σ => map_tay_zF f hV c σ
  obtain ⟨ε, hε, hε1, hgood⟩ := exists_good_ball f L hc'
  -- `zPar = Z(q)`
  have hz : ∀ τ : UpperHalfPlane, zPar f c τ = Z (qC τ) := by
    intro τ
    rw [zPar, eichler_eq, eSum_eq_mul_vFun f _ (norm_qC_lt_one τ.im_pos)]
    simp only [hZdef, zF]; ring
  have hx : ∀ τ : UpperHalfPlane, ‖qC τ‖ < ε → qC τ ^ 2 * xPar E L f c τ = Y (qC τ) := by
    intro τ hτ
    have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
    rw [xPar, hz, hb, hYdef, yF_eq f L hc' _ (hgood _ hτ).1 hq0]
  have hY0 : Y 0 = ((c : ℂ) ^ 2)⁻¹ := yF_zero f L _ _
  refine ⟨hasRatQExp_of_tay _ Y hY (fun σ => hYfix σ) 2 hε hx, ?_, fun t => ?_⟩
  · -- `y∘φ`
    set W : ℂ → ℂ := fun w => ((w * deriv Y w - 2 * Y w) * (deriv Z w)⁻¹ -
      (E.a₁ : ℂ) * w * Y w - (E.a₃ : ℂ) * w ^ 3) / 2 with hWdef
    have hdZ0 : deriv Z 0 ≠ 0 := by rw [(hasDerivAt_zF_zero f c).deriv]; exact hc'
    have hW : AnalyticAt ℂ W 0 := by
      have := hdZ.inv hdZ0
      rw [hWdef]; fun_prop
    have hev : (fun w => W w * (2 * deriv Z w)) =ᶠ[nhds 0]
        fun w => (w * deriv Y w - 2 * Y w) - ((E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) *
          deriv Z w := by
      filter_upwards [hdZ.continuousAt.eventually_ne hdZ0] with w hw
      rw [hWdef]; field_simp; ring
    have ht := tay_congr hev
    have l1 := tay_mul (f := W) (g := fun w => 2 * deriv Z w) hW (by fun_prop)
    have l2 := tay_cmul 2 hdZ
    have r1 := tay_sub (f := fun w => w * deriv Y w - 2 * Y w)
      (g := fun w => ((E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) * deriv Z w)
      (by fun_prop) (by fun_prop)
    have r2 := tay_sub (f := fun w => w * deriv Y w) (g := fun w => 2 * Y w) (by fun_prop)
      (by fun_prop)
    have r3 := tay_mul (f := fun w => w) (g := deriv Y) analyticAt_id hdY
    have r4 := tay_cmul 2 hY
    have r5 := tay_mul (f := fun w => (E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) (g := deriv Z)
      (by fun_prop) hdZ
    have r6 := tay_add (f := fun w => (E.a₁ : ℂ) * w * Y w) (g := fun w => (E.a₃ : ℂ) * w ^ 3)
      (by fun_prop) (by fun_prop)
    have r7 := tay_mul (f := fun w => (E.a₁ : ℂ) * w) (g := Y) (by fun_prop) hY
    have r8 := tay_cmul (E.a₁ : ℂ) (f := fun w => w) analyticAt_id
    have r9 := tay_cmul (E.a₃ : ℂ) (f := fun w => w ^ 3) (by fun_prop)
    beta_reduce at l1 l2 r1 r2 r3 r4 r5 r6 r7 r8 r9
    rw [l1, l2, r1, r2, r3, r4, r5, r6, r7, r8, r9, tay_id, tay_X_pow, tay_deriv hY,
      tay_deriv hZ] at ht
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hdZ.continuousAt.eventually_ne hdZ0)
    refine hasRatQExp_of_tay _ W hW (fun σ => fixed_of_mul ?_ ht σ ?_ ?_) 3 (lt_min hε hδ) ?_
    · intro h0
      have := congrArg PowerSeries.constantCoeff h0
      have h1 : PowerSeries.constantCoeff (d⁄dX (tay Z)) = deriv Z 0 := by
        rw [← tay_deriv hZ, constantCoeff_tay]
      rw [map_mul, PowerSeries.constantCoeff_C, h1, map_zero] at this
      exact hdZ0 ((mul_eq_zero.1 this).resolve_left two_ne_zero)
    · rw [map_mul, PowerSeries.map_C, map_derivative, hZfix, map_ofNat]
    · simp only [map_sub, map_mul, map_add, map_pow, PowerSeries.map_X, PowerSeries.map_C,
        map_derivative, hYfix, hZfix, map_ofNat, map_ratCast]
    · intro τ hτ
      have hτε : ‖qC τ‖ < ε := lt_of_lt_of_le hτ (min_le_left _ _)
      have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
      have hdZq : deriv Z (qC τ) ≠ 0 :=
        hδb (by rw [dist_zero_right]; exact lt_of_lt_of_le hτ (min_le_right _ _))
      have hderiv := yF_deriv_eq f L hc' bq hε1 hgood hτε hq0
      have hxq := hx τ hτε
      rw [yPar, hWdef]
      simp only
      rw [hderiv, ha₁, ha₃, hz τ, ← hxq]
      field_simp
      ring
  · -- `1/(x∘φ − t)`
    set W : ℂ → ℂ := fun w => w ^ 2 * (Y w - t * w ^ 2)⁻¹ with hWdef
    have hU0 : Y 0 - t * 0 ^ 2 ≠ 0 := by rw [hY0]; simpa using hc'
    have hUa : AnalyticAt ℂ (fun w => Y w - t * w ^ 2) 0 := by fun_prop
    have hW : AnalyticAt ℂ W 0 := by
      have := hUa.inv hU0
      rw [hWdef]; fun_prop
    have hev : (fun w => W w * (Y w - t * w ^ 2)) =ᶠ[nhds 0] fun w => w ^ 2 := by
      filter_upwards [hUa.continuousAt.eventually_ne hU0] with w hw
      rw [hWdef]; simp only; rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
    have ht := tay_congr hev
    have l1 := tay_mul (f := W) (g := fun w => Y w - t * w ^ 2) hW hUa
    have l2 := tay_sub (f := Y) (g := fun w => (t : ℂ) * w ^ 2) hY (by fun_prop)
    have l3 := tay_cmul (t : ℂ) (f := fun w => w ^ 2) (by fun_prop)
    beta_reduce at l1 l2 l3
    rw [l1, l2, l3, tay_X_pow] at ht
    refine hasRatQExp_of_tay _ W hW (fun σ => fixed_of_mul ?_ ht σ ?_ ?_) 0 hε ?_
    · intro h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
        constantCoeff_tay, map_zero] at this
      exact hU0 (by simpa using this)
    · rw [map_sub, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hYfix, map_ratCast]
    · rw [map_pow, PowerSeries.map_X]
    · intro τ hτ
      have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
      have hxq := hx τ hτ
      have hzL : zPar f c τ ∉ L.lattice := by rw [hz τ]; exact (hgood _ hτ).2 hq0
      rw [pow_zero, one_mul, gPar, if_neg hzL, hWdef]
      simp only
      rw [← hxq]
      have hq2 : qC τ ^ 2 ≠ 0 := pow_ne_zero 2 hq0
      rw [show qC τ ^ 2 * xPar E L f c τ - t * qC τ ^ 2 = qC τ ^ 2 * (xPar E L f c τ - t) by ring,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ hq2, one_mul]

end QExp

end QExpansionGlue

end ZInQ.GZHeegner

namespace ZInQ.GZHeegner

/-- **`HeegnerPointRational` from the main theorem of complex multiplication and the canonical model
of `X₀(N)` (printed form)**, everything else proved: `HeegnerClassJ` (`heegnerClassJ`),
`ParamRegular` (`paramRegular`), `ParamCuspGrowth` (`paramCuspGrowth`), `ParamQExpansion`
(`paramQExpansion`). -/
theorem heegnerPointRational_of_printed (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero) :
    ZInQ.GZHL3.HeegnerPointRational :=
  heegnerPointRational_of hCM hX paramRegular paramCuspGrowth paramQExpansion heegnerClassJ

/-- **gz-hl3's `hL3` with `HeegnerPointRational` replaced**: `GrossZagierHeegner` from gz-hl3's five
other leaves, `ShimuraMainCM` and `X0ModuliGaloisMero`. -/
theorem grossZagierHeegner_of_printed (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hSW : ZInQ.GZHL3.StrongWeilCurve) (hI : ZInQ.GZHL3.IsogenyLattice)
    (hGZ : ZInQ.GZHL3.GrossZagierFormula) (hGC : ZInQ.GZHL3.GrossConjugation)
    (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero) : ZInQ.GZDecomp.GrossZagierHeegner :=
  ZInQ.GZHL3.grossZagierHeegner_of_leaves hU hSW hI (heegnerPointRational_of_printed hCM hX)
    hGZ hGC

end ZInQ.GZHeegner
