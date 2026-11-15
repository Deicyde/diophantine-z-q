import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development: lattice algebra (Dirichlet composition, homothety vs `Γ₀(N)`). -/

noncomputable section

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open scoped MatrixGroups

namespace ZInQ.GZHeegner

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

end ZInQ.GZHeegner
