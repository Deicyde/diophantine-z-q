import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd.Recip

/-!
# heegner-32: the conductor-`d` composition and the reduction of `TwistTransportCd` to Chebotarev and genus theory

For a Heegner form `Q = [A, B, C]` of level `32 d²` and discriminant `D`, an ideal `J = ⟨a, (−b + √D)/2⟩` prime to
`d A`, gz-heegner's Dirichlet composite `Q' = [aA, B', C']` (`J·⟨1, τ_{Q'}⟩ = ⟨1, τ_Q⟩`) and `α a' ≡ ... `:
`J_d · ⟨1, τ_{Q'} + a'/d⟩ = ⟨1, τ_Q + α/d⟩` and the same with `1/32`, where `J_d = J ∩ 𝒪_d = ⟨a, d(−b + √D)/2⟩`
and `a a' ≡ α (mod d)` (`nb_lat`, `nb_latN`). With hx-used's level-32 Shimura reciprocity (from `hCM`) this gives
`TwistTransportCd` from two statements of algebraic number theory: Chebotarev in the ring class field of conductor
`d` (`RingClassJd`) and genus theory for `K(√d)` (`GenusSqrtD`).
-/

noncomputable section

set_option maxRecDepth 20000

open UpperHalfPlane Complex WeierstrassCurve
open scoped WeierstrassCurve.Affine MatrixGroups

namespace ZInQ.Heegner32

open ZInQ.GZWeil (gaussD)
open ZInQ.GZTheta (jacobiChar)
open ZInQ.GZDecomp (HeegnerHyp)
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint ιC)
open ZInQ.GZHeegner (sD jLat mem_span_pair_of span_pair_mul_span_pair mul_mem_span_pair_mul)

/-! ## §1. The lattice of `J ∩ 𝒪_d` and the neighbour lattices -/

/-- `⟨a, d(−b + √D)/2⟩ ⊂ ℂ`, the lattice of `J ∩ 𝒪_d` for `J = ⟨a, (−b + √D)/2⟩`. -/
def jLatd (D a b : ℤ) (d : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {(a : ℂ), (d : ℂ) * ((-(b : ℂ) + sD D) / 2)}

theorem zmem {M : Submodule ℤ ℂ} (c : ℤ) {x : ℂ} (hx : x ∈ M) : (c : ℂ) * x ∈ M := by
  have := M.smul_mem c hx
  rwa [zsmul_eq_mul] at this

/-- **The neighbour relation.** Data: `aτ' = −k + τ`, `w = (Ak + B − al) + Aτ`, `wτ' = (kl − C') − lτ`
(`w = (−b + √D)/2`; gz-heegner's composition identities), `A = d A₃`, `a a' = α + d j`, and a Bezout relation
`u a + v X = 1`, `X = d(2Ak + B − al) − A a a'`. Then `⟨a, d w⟩·⟨1, τ' + a'/d⟩ = ⟨1, τ + α/d⟩`. -/
theorem nb_lat {d : ℕ} (hd : (d : ℂ) ≠ 0) {τ τ' w : ℂ} {A B C' a k l α a' j A₃ u v : ℤ}
    (e1 : (a : ℂ) * τ' = -k + τ) (e2 : w = (A * k + B - a * l : ℤ) + (A : ℂ) * τ)
    (e3 : w * τ' = (k * l - C' : ℤ) - (l : ℂ) * τ) (hA3 : A = d * A₃) (hj : a * a' = α + d * j)
    (hbez : u * a + v * (d * (2 * A * k + B - a * l) - A * a * a') = 1) :
    Submodule.span ℤ {(a : ℂ), (d : ℂ) * w} * Submodule.span ℤ {1, τ' + (a' : ℂ) / d} =
      Submodule.span ℤ {1, τ + (α : ℂ) / d} := by
  have hjC : (a : ℂ) * a' = α + d * j := by exact_mod_cast hj
  have hA3C : (A : ℂ) = d * A₃ := by exact_mod_cast hA3
  have p2 : (a : ℂ) * (τ' + (a' : ℂ) / d) = (τ + (α : ℂ) / d) + (j - k : ℤ) := by
    rw [mul_add, e1]; field_simp; push_cast; linear_combination hjC
  have p3 : (d : ℂ) * w = (d * (A * k + B - a * l) - A * α : ℤ) + (d * A : ℤ) * (τ + (α : ℂ) / d) := by
    rw [e2]; push_cast; field_simp; ring
  have p4 : (d : ℂ) * w * (τ' + (a' : ℂ) / d) =
      (d * (k * l - C') + a' * (A * k + B - a * l) - (a' * A₃ * α - l * α) : ℤ) +
        (a' * A - d * l : ℤ) * (τ + (α : ℂ) / d) := by
    have : (d : ℂ) * w * (τ' + (a' : ℂ) / d) = d * (w * τ') + a' * w := by field_simp
    rw [this, e3, e2]; push_cast; rw [hA3C]; field_simp; ring
  apply le_antisymm
  · apply span_pair_mul_span_pair
    · exact mem_span_pair_of a 0 (by simp)
    · exact mem_span_pair_of (j - k) 1 (by rw [p2] <;> ring)
    · exact mem_span_pair_of (d * (A * k + B - a * l) - A * α) (d * A) (by rw [mul_one, p3] <;> ring)
    · exact mem_span_pair_of (d * (k * l - C') + a' * (A * k + B - a * l) - (a' * A₃ * α - l * α))
        (a' * A - d * l) (by rw [p4] <;> ring)
  · set M := Submodule.span ℤ {(a : ℂ), (d : ℂ) * w} * Submodule.span ℤ {1, τ' + (a' : ℂ) / d}
    have m1 : (a : ℂ) * 1 ∈ M := mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inl rfl)
    rw [mul_one] at m1
    have m2 : (a : ℂ) * (τ' + (a' : ℂ) / d) ∈ M :=
      mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inr rfl)
    have m3 : (d : ℂ) * w * 1 ∈ M := mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inl rfl)
    rw [mul_one] at m3
    have hone : (1 : ℂ) ∈ M := by
      have hbezC : (u : ℂ) * a + v * (d * (2 * A * k + B - a * l) - A * a * a') = 1 := by
        exact_mod_cast hbez
      have h : (1 : ℂ) = (u : ℤ) * (a : ℂ) + (v : ℤ) * ((d : ℂ) * w - ((d * A : ℤ) : ℂ) *
          ((a : ℂ) * (τ' + (a' : ℂ) / d))) := by
        rw [p2, p3]; push_cast
        linear_combination -hbezC - (v : ℂ) * (A : ℂ) * hjC
      rw [h]
      exact M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2)))
    rw [Submodule.span_le]
    rintro _ (rfl | h)
    · exact hone
    · rw [Set.mem_singleton_iff] at h; subst h
      have : τ + (α : ℂ) / d = (a : ℂ) * (τ' + (a' : ℂ) / d) - ((j - k : ℤ) : ℂ) * 1 := by
        rw [p2]; ring
      rw [this]
      exact M.sub_mem m2 (zmem _ hone)

/-- **The neighbour relation with the 32-structures**: `⟨a, d w⟩·⟨1/32, τ' + a'/d⟩ = ⟨1/32, τ + α/d⟩`
(`A = 32 A₂`). -/
theorem nb_latN {d : ℕ} (hd : (d : ℂ) ≠ 0) {τ τ' w : ℂ} {A B C' a k l α a' j A₃ A₂ u v : ℤ}
    (e1 : (a : ℂ) * τ' = -k + τ) (e2 : w = (A * k + B - a * l : ℤ) + (A : ℂ) * τ)
    (e3 : w * τ' = (k * l - C' : ℤ) - (l : ℂ) * τ) (hA3 : A = d * A₃) (hA2 : A = 32 * A₂)
    (hj : a * a' = α + d * j)
    (hbez : u * a + v * (d * (2 * A * k + B - a * l) - A * a * a') = 1) :
    Submodule.span ℤ {(a : ℂ), (d : ℂ) * w} * Submodule.span ℤ {1 / 32, τ' + (a' : ℂ) / d} =
      Submodule.span ℤ {1 / 32, τ + (α : ℂ) / d} := by
  have hjC : (a : ℂ) * a' = α + d * j := by exact_mod_cast hj
  have hA3C : (A : ℂ) = d * A₃ := by exact_mod_cast hA3
  have hA2C : (A : ℂ) = 32 * A₂ := by exact_mod_cast hA2
  have p1 : (a : ℂ) * (1 / 32) = (a : ℤ) * (1 / 32 : ℂ) := by ring
  have p2 : (a : ℂ) * (τ' + (a' : ℂ) / d) = (τ + (α : ℂ) / d) + (32 * (j - k) : ℤ) * (1 / 32 : ℂ) := by
    rw [mul_add, e1]; field_simp; push_cast; linear_combination 32 * hjC
  have p3 : (d : ℂ) * w * (1 / 32) = (d * (A * k + B - a * l) - A * α : ℤ) * (1 / 32 : ℂ) +
      (d * A₂ : ℤ) * (τ + (α : ℂ) / d) := by
    rw [e2]; push_cast; rw [hA2C]; field_simp; ring
  have p4 : (d : ℂ) * w * (τ' + (a' : ℂ) / d) =
      (32 * (d * (k * l - C') + a' * (A * k + B - a * l) - (a' * A₃ * α - l * α)) : ℤ) * (1 / 32 : ℂ) +
        (a' * A - d * l : ℤ) * (τ + (α : ℂ) / d) := by
    have : (d : ℂ) * w * (τ' + (a' : ℂ) / d) = d * (w * τ') + a' * w := by field_simp
    rw [this, e3, e2]; push_cast; rw [hA3C]; field_simp; ring
  apply le_antisymm
  · apply span_pair_mul_span_pair
    · exact mem_span_pair_of a 0 (by rw [p1] <;> ring)
    · exact mem_span_pair_of (32 * (j - k)) 1 (by rw [p2] <;> ring)
    · exact mem_span_pair_of (d * (A * k + B - a * l) - A * α) (d * A₂) (by rw [p3] <;> ring)
    · exact mem_span_pair_of (32 * (d * (k * l - C') + a' * (A * k + B - a * l) - (a' * A₃ * α - l * α)))
        (a' * A - d * l) (by rw [p4] <;> ring)
  · set M := Submodule.span ℤ {(a : ℂ), (d : ℂ) * w} * Submodule.span ℤ {1 / 32, τ' + (a' : ℂ) / d}
    have m1 : (a : ℂ) * (1 / 32) ∈ M := mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inl rfl)
    have m2 : (a : ℂ) * (τ' + (a' : ℂ) / d) ∈ M :=
      mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inr rfl)
    have m3 : (d : ℂ) * w * (1 / 32) ∈ M := mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inl rfl)
    have hone : (1 / 32 : ℂ) ∈ M := by
      have hbezC : (u : ℂ) * a + v * (d * (2 * A * k + B - a * l) - A * a * a') = 1 := by
        exact_mod_cast hbez
      have h : (1 / 32 : ℂ) = (u : ℤ) * ((a : ℂ) * (1 / 32)) + (v : ℤ) * ((d : ℂ) * w * (1 / 32) -
          ((d * A₂ : ℤ) : ℂ) * ((a : ℂ) * (τ' + (a' : ℂ) / d))) := by
        rw [p2, p3]; push_cast
        linear_combination (-1 / 32 : ℂ) * hbezC - (1 / 32 : ℂ) * (v : ℂ) * (A : ℂ) * hjC -
          (1 / 32 : ℂ) * (v : ℂ) * (d : ℂ) * ((j : ℂ) - k) * hA2C
      rw [h]
      exact M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2)))
    rw [Submodule.span_le]
    rintro _ (rfl | h)
    · exact hone
    · rw [Set.mem_singleton_iff] at h; subst h
      have : τ + (α : ℂ) / d = (a : ℂ) * (τ' + (a' : ℂ) / d) - ((32 * (j - k) : ℤ) : ℂ) * (1 / 32) := by
        rw [p2]; ring
      rw [this]
      exact M.sub_mem m2 (zmem _ hone)

/-! ## §2. gz-heegner's composition, with its data (copy of `GZHeegner.exists_compose`) -/

section Compose

open ZInQ.GZHeegner (gcd_eq_one_of_squarefree exists_bezout3 add_even_of_disc A_ne_zero sD_sq)

variable {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) {a b : ℤ}

theorem exists_compose' (hsq : Squarefree D) (ha : 0 < a) (hab : 4 * a ∣ b ^ 2 - D)
    (hcop : IsCoprime a Q.A) :
    ∃ (Q' : HeegnerForm N D) (k l : ℤ), Q'.A = a * Q.A ∧ Q'.B = Q.B + 2 * Q.A * k ∧
      Q.B + 2 * Q.A * k = -b + 2 * a * l ∧
      (a : ℂ) * Q'.tau = -k + Q.tau ∧
      (-(b : ℂ) + sD D) / 2 = ((Q.A * k + Q.B - a * l : ℤ) : ℂ) + (Q.A : ℂ) * Q.tau ∧
      (-(b : ℂ) + sD D) / 2 * Q'.tau = ((k * l - Q'.C : ℤ) : ℂ) - (l : ℂ) * Q.tau ∧
      2 * Q.A ∣ Q'.B - Q.B ∧ jLat D a b * Q'.lat = Q.lat ∧
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
  refine ⟨Q', k, l, rfl, hB', hkl, e1, by rw [e2]; push_cast; ring, by rw [e3]; push_cast; rfl,
    ⟨k, by simp [Q', hB']⟩, ?_, ?_⟩
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

/-! ## §3. The neighbour forms `τ_Q + α/d` -/

theorem sD_scale {D D₁ : ℤ} {d : ℕ} (hD₁ : D₁ = d ^ 2 * D) (hD : D < 0) : sD D₁ = d * sD D := by
  have hD' : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith
  simp only [sD, hD₁]
  push_cast
  rw [show (-((d : ℝ) ^ 2 * (D : ℝ))) = (d : ℝ) ^ 2 * (-(D : ℝ)) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast; ring

/-- **The form of `τ_Q + α/d`**: `[A d, (B − 2Aα/d) d, dC − Bα + Aα²/d]`, of level `32` and discriminant `d² D`,
primitive when `B` and `α` are prime to `d`. -/
theorem exists_nbForm {M : ℕ} {D : ℤ} (Q : HeegnerForm M D) {d : ℕ} (hd0 : 0 < d) {D₁ : ℤ}
    (hD₁ : D₁ = d ^ 2 * D) (h32 : (32 : ℤ) ∣ Q.A) (hdd : (d : ℤ) ^ 2 ∣ Q.A) (hBd : IsCoprime Q.B d)
    {α : ℤ} (hα : IsCoprime α d) :
    ∃ Q₁ : HeegnerForm 32 D₁, Q₁.tau = Q.tau + (α : ℂ) / d := by
  obtain ⟨A₃, hA₃⟩ := hdd
  have hQd := Q.disc
  set A := Q.A with hAdef
  set B := Q.B with hBdef
  set C := Q.C with hCdef
  have hdisc : ((B - 2 * (d * A₃) * α) * d) ^ 2 - 4 * (A * d) * (d * C - B * α + d * A₃ * α ^ 2) = D₁ := by
    rw [hD₁, ← hQd, hA₃]; ring
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd0
  have hprim : Int.gcd (Int.gcd (A * d) ((B - 2 * (d * A₃) * α) * d)) (d * C - B * α + d * A₃ * α ^ 2) = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    set g := Int.gcd (Int.gcd (A * d) ((B - 2 * (d * A₃) * α) * d)) (d * C - B * α + d * A₃ * α ^ 2)
    have hg1 : (g : ℤ) ∣ A * d := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have hg2 : (g : ℤ) ∣ (B - 2 * (d * A₃) * α) * d := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have hg3 : (g : ℤ) ∣ d * C - B * α + d * A₃ * α ^ 2 := Int.gcd_dvd_right _ _
    have hpg : (p : ℤ) ∣ g := by exact_mod_cast hdvd
    have h1 := hpg.trans hg1
    have h2 := hpg.trans hg2
    have h3 := hpg.trans hg3
    by_cases hpd : (p : ℤ) ∣ d
    · -- `p ∣ Bα`, impossible
      have hBa : (p : ℤ) ∣ B * α := by
        have : B * α = d * C + d * A₃ * α ^ 2 - (d * C - B * α + d * A₃ * α ^ 2) := by ring
        rw [this]
        exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hpd _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpd _) _)) h3
      rcases hpZ.dvd_or_dvd hBa with hB | hα'
      · exact hpZ.not_unit (hBd.isUnit_of_dvd' hB hpd)
      · exact hpZ.not_unit (hα.isUnit_of_dvd' hα' hpd)
    · have hpA : (p : ℤ) ∣ A := (hpZ.dvd_or_dvd h1).resolve_right hpd
      have hpB' : (p : ℤ) ∣ B - 2 * (d * A₃) * α := (hpZ.dvd_or_dvd h2).resolve_right hpd
      have hpA₃ : (p : ℤ) ∣ A₃ := by
        rw [hA₃] at hpA
        rcases hpZ.dvd_or_dvd hpA with h | h
        · exact absurd (hpZ.dvd_of_dvd_pow h) hpd
        · exact h
      have hpB : (p : ℤ) ∣ B := by
        have : B = (B - 2 * (d * A₃) * α) + 2 * (d * A₃) * α := by ring
        rw [this]
        exact dvd_add hpB' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpA₃ _) _) _)
      have hpdC : (p : ℤ) ∣ d * C := by
        have : d * C = (d * C - B * α + d * A₃ * α ^ 2) + B * α - d * A₃ * α ^ 2 := by ring
        rw [this]
        exact dvd_sub (dvd_add h3 (dvd_mul_of_dvd_left hpB _))
          (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpA₃ _) _)
      have hpC : (p : ℤ) ∣ C := (hpZ.dvd_or_dvd hpdC).resolve_left hpd
      have hprim := Q.primitive
      have : (p : ℤ) ∣ (Int.gcd (Int.gcd A B) C : ℤ) :=
        Int.dvd_coe_gcd (Int.dvd_coe_gcd hpA hpB) hpC
      rw [hprim, Nat.cast_one] at this
      exact hpZ.not_unit (isUnit_of_dvd_one this)
  let Q₁ : HeegnerForm 32 D₁ :=
    { A := A * d
      B := (B - 2 * (d * A₃) * α) * d
      C := d * C - B * α + d * A₃ * α ^ 2
      A_pos := mul_pos Q.A_pos hdpos
      N_dvd := dvd_mul_of_dvd_left h32 _
      disc := hdisc
      D_neg := by rw [hD₁]; exact mul_neg_of_pos_of_neg (by positivity) Q.D_neg
      primitive := hprim }
  refine ⟨Q₁, ?_⟩
  have hs := sD_scale hD₁ Q.D_neg
  have hA0 : (A : ℂ) ≠ 0 := ZInQ.GZHeegner.A_ne_zero Q
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hAC : (A : ℂ) = (d : ℂ) ^ 2 * A₃ := by exact_mod_cast hA₃
  show cmPoint (A * d) ((B - 2 * (d * A₃) * α) * d) D₁ = Q.tau
    + (α : ℂ) / d
  rw [ZInQ.GZHeegner.tau_eq, ← hBdef, ← hAdef]
  simp only [cmPoint]
  rw [show (Complex.I * (Real.sqrt (-(D₁ : ℝ)) : ℂ)) = sD D₁ from rfl, hs]
  push_cast
  have hA3ne : (A₃ : ℂ) ≠ 0 := by intro h; apply hA0; rw [hAC, h, mul_zero]
  rw [hAC]
  field_simp
  ring

/-! ## §4. Moving the neighbours along `Γ₀(32 d²)` -/

theorem phiC_add_int (τ : ℍ) (n : ℤ) (h : 0 < ((τ : ℂ) + n).im) :
    ZInQ.Contrib.TYZGenus.X0.phiC ⟨(τ : ℂ) + n, h⟩ = ZInQ.Contrib.TYZGenus.X0.phiC τ := by
  have hT : (ModularGroup.T ^ n : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 32 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T_zpow]
  have := phiC_gamma0 hT τ
  rw [← this]
  congr 1
  ext
  rw [UpperHalfPlane.modular_T_zpow_smul]
  simp [add_comm]

/-- **Intertwining.** For `γ = [p, q; r, s] ∈ Γ₀(32 d²)`, `(x, y)(τ + a'/d) = (x, y)(γτ + p²a'/d)`
(`T_{p²a'/d} γ T_{−a'/d} ∈ Γ₀(32)`). -/
theorem phiC_shift_gamma0 {d : ℕ} [NeZero d] {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (32 * d ^ 2)) (τ : ℍ) (x : ZMod d) :
    ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d τ x) =
      ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (γ • τ) (((γ 0 0 : ℤ) : ZMod d) ^ 2 * x)) := by
  set p := γ 0 0
  set q := γ 0 1
  set r := γ 1 0
  set s := γ 1 1
  have hdet : p * s - q * r = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨r₀, hr₀⟩ : ((32 * d ^ 2 : ℕ) : ℤ) ∣ r := ZInQ.GZHeegner.gamma0_dvd hγ
  push_cast at hr₀
  set a' : ℤ := (x.val : ℤ)
  set a'' : ℤ := (((p : ZMod d) ^ 2 * x).val : ℤ)
  obtain ⟨n, hn⟩ : (d : ℤ) ∣ a'' - p ^ 2 * a' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [a'', a']
  -- the conjugated matrix
  set P : ℤ := p + 32 * d * r₀ * a''
  set S : ℤ := s - 32 * d * r₀ * a'
  set Qe : ℤ := q + p * a' * q * 32 * d * r₀ + n * s - 32 * r₀ * a' * a''
  have hdetM : P * S - Qe * r = 1 := by
    simp only [P, S, Qe]
    rw [hr₀] at hdet ⊢
    have hn' : a'' = p ^ 2 * a' + d * n := by linarith
    rw [hn']
    linear_combination (32 * a' * d * p * r₀ + 1) * hdet
  let γ' : SL(2, ℤ) := ⟨!![P, Qe; r, S], by rw [Matrix.det_fin_two_of]; exact hdetM⟩
  have hγ' : γ' ∈ CongruenceSubgroup.Gamma0 32 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((r : ℤ) : ZMod 32) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hr₀]
    exact ⟨d ^ 2 * r₀, by push_cast; ring⟩
  rw [← phiC_gamma0 hγ' (shiftH d τ x)]
  congr 1
  ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_shiftH, coe_shiftH,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, algebraMap_int_eq, eq_intCast]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hden : ((r : ℤ) : ℂ) * (τ : ℂ) + (s : ℤ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [UpperHalfPlane.denom] using this
  have hden' : ((r : ℤ) : ℂ) * ((τ : ℂ) + (x.val : ℂ) / d) + (S : ℤ) ≠ 0 := by
    have e : ((r : ℤ) : ℂ) * ((τ : ℂ) + (x.val : ℂ) / d) + (S : ℤ) = (r : ℂ) * τ + s := by
      simp only [S, a']; push_cast; rw [hr₀]; push_cast; field_simp; ring
    rw [e]; exact_mod_cast hden
  have hdetC : (p : ℂ) * s - q * r = 1 := by exact_mod_cast hdet
  have hr₀C : (r : ℂ) = 32 * (d : ℂ) ^ 2 * r₀ := by exact_mod_cast hr₀
  have hnC : (a'' : ℂ) = p ^ 2 * a' + d * n := by exact_mod_cast (by linarith : a'' = p ^ 2 * a' + d * n)
  have hxa : ((x.val : ℕ) : ℂ) = (a' : ℂ) := by simp [a']
  have hxa'' : ((((p : ZMod d) ^ 2 * x).val : ℕ) : ℂ) = (a'' : ℂ) := by simp [a'']
  rw [hxa, hxa'']
  simp only [P, S, Qe]
  push_cast
  rw [show ((γ 0 0 : ℤ) : ℂ) = (p : ℂ) from rfl, show ((γ 0 1 : ℤ) : ℂ) = (q : ℂ) from rfl,
    show ((γ 1 0 : ℤ) : ℂ) = (r : ℂ) from rfl, show ((γ 1 1 : ℤ) : ℂ) = (s : ℂ) from rfl]
  rw [show ((r : ℂ) * ((τ : ℂ) + (a' : ℂ) / d) + ((s : ℂ) - 32 * d * r₀ * a')) = (r : ℂ) * τ + s by
    rw [hr₀C]; field_simp; ring]
  rw [div_add_div _ _ hden hd0, div_eq_div_iff hden (mul_ne_zero hden hd0)]
  rw [hnC]
  rw [hr₀C] at hdetC ⊢
  field_simp
  linear_combination (-(a' : ℂ) * p * (32 * (d : ℂ) ^ 2 * r₀ * τ + s)) * hdetC

/-! ## §5. The character `(·/d)` on `ℤ/d` -/

/-- `(x/d)` for `x ∈ ℤ/d`, as an integer. -/
def chiZ (d : ℕ) [NeZero d] (x : ZMod d) : ℤ := jacobiSym (x.val : ℤ) d

theorem chiZ_cast (d : ℕ) [NeZero d] (x : ZMod d) : ((chiZ d x : ℤ) : ℂ) = jacobiChar d x := rfl

theorem chiZ_mul (d : ℕ) [NeZero d] (x y : ZMod d) : chiZ d (x * y) = chiZ d x * chiZ d y := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [chiZ_cast, chiZ_cast, chiZ_cast, map_mul]

theorem chiZ_nonunit (d : ℕ) [NeZero d] {x : ZMod d} (hx : ¬IsUnit x) : chiZ d x = 0 := by
  apply Int.cast_injective (α := ℂ)
  rw [chiZ_cast, MulChar.map_nonunit _ hx, Int.cast_zero]

theorem chiZ_sq_unit (d : ℕ) [NeZero d] {x : ZMod d} (hx : IsUnit x) : chiZ d x * chiZ d x = 1 := by
  obtain ⟨u, rfl⟩ := hx
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [chiZ_cast, ← sq]
  exact ZInQ.GZTheta.jacobiChar_sq_unit d u

theorem chiZ_intCast (d : ℕ) [NeZero d] (a : ℤ) : chiZ d (a : ZMod d) = jacobiSym a d := by
  unfold chiZ
  rw [ZMod.val_intCast]; exact (jacobiSym.mod_left a d).symm

theorem isUnit_of_isCoprime {d : ℕ} [NeZero d] {a : ℤ} (h : IsCoprime a d) : IsUnit (a : ZMod d) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (u : ZMod d) ?_
  have := congrArg (fun z : ℤ => (z : ZMod d)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at this
  rw [mul_comm]; exact this

theorem isCoprime_of_primes {x y : ℤ} (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → False) :
    IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact h p hp ((Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left _ _))
    ((Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right _ _))

/-- Under the Heegner hypothesis for `32 d²`, `B` is prime to `d` for every form of discriminant `−m` with `d ∣ A`. -/
theorem isCoprime_B_d {d m : ℕ} [NeZero m] {A B C : ℤ} (hHH : HeegnerHyp (32 * d ^ 2) (-(m : ℤ)))
    (hdisc : B ^ 2 - 4 * A * C = -(m : ℤ)) (hdA : (d : ℤ) ∣ A) : IsCoprime B d := by
  apply isCoprime_of_primes
  intro p hp hpB hpd
  have hpN : p ∣ 32 * d ^ 2 := Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.1 hpd) two_ne_zero) _
  have hJ := hHH p hp hpN
  have hpm : (p : ℤ) ∣ (m : ℤ) := by
    have : (m : ℤ) = 4 * A * C - B ^ 2 := by linarith
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hpd.trans hdA) _) _)
      (dvd_pow hpB two_ne_zero)
  have : NeZero (-(m : ℤ)).natAbs := ⟨by simp [NeZero.ne m]⟩
  have h0 : jacobiSym (p : ℤ) (-(m : ℤ)).natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    intro hc
    have : p ∣ Int.gcd (p : ℤ) (m : ℤ) := Nat.dvd_gcd (dvd_refl p) (Int.natCast_dvd_natCast.1 hpm)
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rw [h0] at hJ
  exact absurd hJ (by norm_num)

/-! ## §6. Chebotarev and genus theory, and the reduction -/

open ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura
  ZInQ.Contrib.TYZDecomp.CurveA NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory

/-- **(Chebotarev in the ring class field of conductor `d`, with the Hermite basis.)** Every class of
`Pic(𝒪_d)`, `𝒪_d = ℤ + d𝒪_K`, `K = ℚ(√−m)`, contains an ideal `J` of `𝒪_K` prime to `d` with `J ∩ 𝒪_d` of basis
`⟨a, d(−b + √−m)/2⟩`, `4a ∣ b² + m`, `N(J) = a` prime to a given `M` and to `b`. (A prime of degree one outside a
finite set, Tau Ceti's Chebotarev theorem, as gz-heegner's `heegnerClassJ'` for `d = 1`.) -/
def RingClassJd : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → ∀ (d : ℕ) [NeZero d], ∀ M : ℤ, M ≠ 0 →
    ∀ cl : Pic (conductorOrder (QNeg m) d),
    ∃ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) d).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) d).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ IsCoprime a b ∧ Ideal.absNorm (J : Ideal (𝓞 (QNeg m))) = a.natAbs ∧
      idealLat m d J = jLatd (-(m : ℤ)) a b d ∧
      (((J : Ideal (𝓞 (QNeg m))) = ⊤ ∧ a = 1) ∨ ((J : Ideal (𝓞 (QNeg m))).IsMaximal ∧ a.natAbs.Prime))

/-- **(Genus theory: the Artin symbol of `√d` in the ring class field of conductor `d`.)** For `d ≡ 1 (mod 4)`
squarefree, `K(√d)` lies in the ring class field of `𝒪_d = ℤ + d𝒪_K`, and the Artin symbol of an ideal `J` prime
to `d` acts on `√d` by the Kronecker symbol of `N(J)`: if `σ ∈ Aut(ℂ)` acts on the ring class field (through the
normalized embedding `e`) as `Art(J)`, then `σ(√d) = (N(J)/d)·√d` (`√d = gaussD d`, the Gauss sum of `(·/d)`).
Source: genus theory for orders, Cox, *Primes of the form x² + ny²*, §6 and Thm 9.18; Lemmermeyer,
*Reciprocity laws*, Ch. 2 (numbers UNVERIFIED). -/
def GenusSqrtD : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → ∀ (d : ℕ) [NeZero d], d % 4 = 1 → Squarefree d →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (J : integralIdealsPrimeTo (conductorOrder (QNeg m) d).conductorModulus) (a : ℤ),
    0 < a → Ideal.absNorm (J : Ideal (𝓞 (QNeg m))) = a.natAbs → IsCoprime a (2 * d) →
    (((J : Ideal (𝓞 (QNeg m))) = ⊤ ∧ a = 1) ∨ ((J : Ideal (𝓞 (QNeg m))).IsMaximal ∧ a.natAbs.Prime)) →
    (∀ x : ringClassField (conductorOrder (QNeg m) d),
      σ (ιC (e x)) = ιC (e (ringClassArtinEquiv (conductorOrder (QNeg m) d)
        ((conductorOrder (QNeg m) d).picClass J) x))) →
    σ (gaussD d) = (jacobiSym a d : ℂ) * gaussD d

set_option maxHeartbeats 4000000 in
/-- **`TwistTransportCd` from the main theorem of CM, Chebotarev at conductor `d` and genus theory.** -/
theorem twistTransportCd_of_genus (hCM : T5Glue.ShimuraMainCM) (hJ : RingClassJd) (hG : GenusSqrtD) :
    TwistTransportCd := by
  intro d _ hd hsq m _ hmsq hm3 hm4 hHH β S hS σ hσK
  classical
  have hd4 : d % 4 = 1 := by omega
  have hd0 : 0 < d := by omega
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  obtain ⟨τg, hτg⟩ := T5Glue.exists_tau_of_sigma e he σ hσK
  obtain ⟨ρ, hρ⟩ := ZInQ.GZHeegner.exists_galQ_of_sigma σ
  have hρe : ∀ x, ρ (e x) = e (τg x) := fun x => ιC.injective (by rw [← hρ, hτg])
  set O := conductorOrder (QNeg m) d with hO
  set cl : Pic O := (ringClassArtinEquiv O).symm
    (AlgEquiv.restrictNormalHom (ringClassField O) τg) with hcl
  set M : ℤ := 2 * d * m * ∏ Q ∈ S, Q.A with hMdef
  have hM : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hd0.ne'))
      (by exact_mod_cast NeZero.ne m)) ?_
    exact Finset.prod_ne_zero_iff.2 fun Q _ => Q.A_pos.ne'
  obtain ⟨J, a₀, b, hJc, ha₀, hab, hcopM, hcopb, hNJ, hJlat, hcase⟩ := hJ m hmsq hm3 d M hM cl
  have hArt : ∀ x : ringClassField O, ρ (e x) = e (ringClassArtinEquiv O (O.picClass J) x) := by
    intro x
    rw [hJc, hρe, hcl, MulEquiv.apply_symm_apply]
    congr 1
    exact (AlgEquiv.restrictNormalHom_apply _ τg x).symm
  have hart : ∀ x : ringClassField O, σ (ιC (e x)) = ιC (e (ringClassArtinEquiv O (O.picClass J) x)) :=
    fun x => by rw [hρ, hArt]
  have hcop2d : IsCoprime a₀ (2 * d) := hcopM.of_mul_right_left.of_mul_right_left
  have hgen := hG m hmsq hm3 d hd4 hsq e he σ J a₀ ha₀ hNJ hcop2d hcase hart
  have hcopd : IsCoprime a₀ d := hcop2d.of_mul_right_right
  -- the level-32 transport at conductor `d` (hx-used's eta route, theta-wp8)
  have hsrx := X0EtaRoute.srAt_x_theta ThetaWP8.thetaWeierstrass8 hCM
  have hsry := X0EtaRoute.srAt_y_theta ThetaWP8.thetaWeierstrass8 hCM
  have transport : ∀ Q₁ Q₂ : HeegnerForm 32 (discOf m d), idealLat m d J * Q₂.lat = Q₁.lat →
      idealLat m d J * Q₂.latN = Q₁.latN →
      Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.Contrib.TYZGenus.X0.phiC Q₁.tauH) =
        ZInQ.Contrib.TYZGenus.X0.phiC Q₂.tauH := by
    intro Q₁ Q₂ h1 h2
    obtain ⟨x, x', hx, hx', hxx⟩ := hsrx m d hmsq e he J ρ hArt (discOf m d) rfl Q₁ Q₂ 1
      (by rw [ZInQ.GZHeegner.map_mulLeft_one]; exact h1)
      (by rw [ZInQ.GZHeegner.map_mulLeft_one]; exact h2)
    obtain ⟨y, y', hy, hy', hyy⟩ := hsry m d hmsq e he J ρ hArt (discOf m d) rfl Q₁ Q₂ 1
      (by rw [ZInQ.GZHeegner.map_mulLeft_one]; exact h1)
      (by rw [ZInQ.GZHeegner.map_mulLeft_one]; exact h2)
    beta_reduce at hx hx' hy hy'
    apply map_phiC
    · rw [← hx, hρ, hxx, hx']
    · rw [← hy, hρ, hyy, hy']
  have hsqD : Squarefree (-(m : ℤ)) :=
    ZInQ.GZHeegner.squarefree_neg_iff.2 (Int.squarefree_natCast.2 hmsq)
  have hdisc : discOf m d = (d : ℤ) ^ 2 * (-(m : ℤ)) := by
    simp only [discOf, if_pos hm3]; ring
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hunit0 : IsUnit (a₀ : ZMod d) := isUnit_of_isCoprime hcopd
  have hinvu : IsUnit ((a₀ : ZMod d)⁻¹) := by
    rw [← IsUnit.unit_spec hunit0, ZMod.inv_coe_unit]; exact Units.isUnit _
  -- per form
  have step : ∀ Q ∈ S, ∃ Q' : HeegnerForm (32 * d ^ 2) (-(m : ℤ)), ZInQ.GZHL3.HasResidue β Q' ∧
      jLat (-(m : ℤ)) a₀ b * Q'.lat = Q.lat ∧ jLat (-(m : ℤ)) a₀ b * Q'.latN = Q.latN ∧
      ∀ x : ZMod d, IsUnit x →
        Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d Q.tauH x)) =
          ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d Q'.tauH (x * (a₀ : ZMod d)⁻¹)) := by
    intro Q hQS
    have hdvdM : Q.A ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hQS) _
    have hcopQ : IsCoprime a₀ Q.A := IsCoprime.of_isCoprime_of_dvd_right hcopM hdvdM
    obtain ⟨Q', k, l, hA', hB', hkl, e1, e2, e3, hBB, hlat, hlatN⟩ :=
      exists_compose' Q hsqD ha₀ hab hcopQ
    have hres : ZInQ.GZHL3.HasResidue β Q' := by
      have h1 := hS.1 Q hQS
      obtain ⟨A₁, hA₁⟩ := Q.N_dvd
      show (2 * (32 * d ^ 2 : ℕ) : ℤ) ∣ Q'.B - β
      have : Q'.B - β = (Q'.B - Q.B) + (Q.B - β) := by ring
      rw [this]
      exact dvd_add (dvd_trans ⟨A₁, by rw [hA₁]; ring⟩ hBB) h1
    refine ⟨Q', hres, hlat, hlatN, fun x hx => ?_⟩
    obtain ⟨A₀, hA₀⟩ := Q.N_dvd
    push_cast at hA₀
    have h32 : (32 : ℤ) ∣ Q.A := ⟨d ^ 2 * A₀, by rw [hA₀]; ring⟩
    have hdd : (d : ℤ) ^ 2 ∣ Q.A := ⟨32 * A₀, by rw [hA₀]; ring⟩
    have h32' : (32 : ℤ) ∣ Q'.A := by rw [hA']; exact dvd_mul_of_dvd_right h32 _
    have hdd' : (d : ℤ) ^ 2 ∣ Q'.A := by rw [hA']; exact dvd_mul_of_dvd_right hdd _
    have hBd : IsCoprime Q.B d := isCoprime_B_d hHH Q.disc (dvd_trans (dvd_pow_self _ two_ne_zero) hdd)
    have hB'd : IsCoprime Q'.B d :=
      isCoprime_B_d hHH Q'.disc (dvd_trans (dvd_pow_self _ two_ne_zero) hdd')
    set y : ZMod d := x * (a₀ : ZMod d)⁻¹ with hy
    have hyu : IsUnit y := hx.mul hinvu
    have hxc : IsCoprime (x.val : ℤ) d := by
      obtain ⟨u, rfl⟩ := hx
      exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
    have hyc : IsCoprime (y.val : ℤ) d := by
      obtain ⟨u, hu⟩ := hyu
      rw [← hu]
      exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
    obtain ⟨Q₁, hQ₁⟩ := exists_nbForm Q hd0 hdisc h32 hdd hBd hxc
    obtain ⟨Q₂, hQ₂⟩ := exists_nbForm Q' hd0 hdisc h32' hdd' hB'd hyc
    -- `a₀ y ≡ x`
    obtain ⟨j, hj⟩ : ∃ j : ℤ, a₀ * (y.val : ℤ) = x.val + d * j := by
      have h : ((a₀ * (y.val : ℤ) : ℤ) : ZMod d) = ((x.val : ℤ) : ZMod d) := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hy, ← mul_assoc, mul_comm (a₀ : ZMod d),
          mul_assoc, ZMod.mul_inv_of_unit _ hunit0, mul_one]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
      obtain ⟨j, hj⟩ := h
      exact ⟨-j, by linarith⟩
    -- Bezout for `(a₀, X)`
    obtain ⟨u, v, huv⟩ : IsCoprime a₀ (d * (2 * Q.A * k + Q.B - a₀ * l) - Q.A * a₀ * y.val) := by
      have hX : d * (2 * Q.A * k + Q.B - a₀ * l) - Q.A * a₀ * y.val =
          (-(d * b)) + a₀ * (d * l - Q.A * y.val) := by linear_combination (d : ℤ) * hkl
      rw [hX, IsCoprime.add_mul_left_right_iff]
      exact (hcopd.mul_right hcopb).neg_right
    have hA3 : Q.A = d * (d * 32 * A₀) := by rw [hA₀]; ring
    have hA2 : Q.A = 32 * (d ^ 2 * A₀) := by rw [hA₀]; ring
    have hl1 := nb_lat hdC e1 e2 e3 hA3 hj huv
    have hl2 := nb_latN hdC e1 e2 e3 hA3 hA2 hj huv
    have hQ₁t : Q₁.tauH = shiftH d Q.tauH x := by
      ext; rw [coe_shiftH]; exact hQ₁
    have hQ₂t : Q₂.tauH = shiftH d Q'.tauH y := by
      ext; rw [coe_shiftH]; exact hQ₂
    rw [← hQ₁t, ← hQ₂t]
    apply transport
    · rw [hJlat, HeegnerForm.lat, HeegnerForm.lat, hQ₁, hQ₂]; exact hl1
    · rw [hJlat, HeegnerForm.latN, HeegnerForm.latN, hQ₁, hQ₂]
      have e32 : (1 / ((32 : ℕ) : ℂ)) = 1 / 32 := by norm_num
      rw [e32]; exact hl2
  choose! Q' hQ'res hQ'lat hQ'latN hQ'pt using step
  have hrep : ∀ Q ∈ S, ∃ R ∈ S, ZInQ.GZHL3.Gamma0Equiv (Q' Q) R := fun Q hQ => by
    obtain ⟨R, ⟨hR, hE⟩, -⟩ := hS.2 (Q' Q) (hQ'res Q hQ)
    exact ⟨R, hR, hE⟩
  choose! π hπS hπE using hrep
  have hπinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, π Q₁ = π Q₂ → Q₁ = Q₂ := by
    intro Q₁ h1 Q₂ h2 hπ
    have hE : ZInQ.GZHL3.Gamma0Equiv (Q' Q₁) (Q' Q₂) :=
      ZInQ.GZHL3.Reps.equiv_trans (hπE Q₁ h1)
        (by rw [hπ]; exact ZInQ.GZHL3.Reps.equiv_symm (hπE Q₂ h2))
    obtain ⟨j, -, hjL, hjN⟩ := ZInQ.GZHeegner.pairHom_of_equiv hE
    have hP : ZInQ.GZHeegner.PairHom Q₁ Q₂ j := by
      constructor
      · rw [← hQ'lat Q₁ h1, ← hQ'lat Q₂ h2, hjL, ZInQ.GZHeegner.mul_map_mulLeft]
      · rw [← hQ'latN Q₁ h1, ← hQ'latN Q₂ h2, hjN, ZInQ.GZHeegner.mul_map_mulLeft]
    have hE' := ZInQ.GZHeegner.equiv_of_pairHom hP
    obtain ⟨R, -, huniq⟩ := hS.2 Q₁ (hS.1 Q₁ h1)
    exact (huniq Q₁ ⟨h1, ZInQ.GZHL3.Reps.equiv_refl Q₁⟩).trans (huniq Q₂ ⟨h2, hE'⟩).symm
  refine ⟨π, fun Q hQ => hπS Q hQ, fun Q₁ h1 Q₂ h2 h => hπinj Q₁ h1 Q₂ h2 h, fun Q hQ => ?_⟩
  obtain ⟨γ, hγ, hγe⟩ := hπE Q hQ
  set p : ZMod d := ((γ 0 0 : ℤ) : ZMod d) with hpdef
  have hpu : IsUnit p := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
    obtain ⟨r₀, hr₀⟩ : ((32 * d ^ 2 : ℕ) : ℤ) ∣ γ 1 0 := ZInQ.GZHeegner.gamma0_dvd hγ
    refine IsUnit.of_mul_eq_one ((γ 1 1 : ℤ) : ZMod d) ?_
    have h := congrArg (fun z : ℤ => (z : ZMod d)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hr₀] at h
    push_cast at h
    simpa using h
  set c : ZMod d := p ^ 2 * (a₀ : ZMod d)⁻¹ with hc
  have hcu : IsUnit c := (hpu.pow 2).mul hinvu
  -- each summand
  have hsum : ∀ x : ZMod d, chiZ d x • Affine.Point.map (ZInQ.GZHeegner.sigA σ)
        (ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d Q.tauH x)) =
      (chiZ d (a₀ : ZMod d) * chiZ d (c * x)) •
        ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH (c * x)) := by
    intro x
    by_cases hx : IsUnit x
    · have hχ : chiZ d x = chiZ d (a₀ : ZMod d) * chiZ d (c * x) := by
        rw [chiZ_mul, chiZ_mul, show p ^ 2 = p * p by ring, chiZ_mul]
        have h1 := chiZ_sq_unit d hpu
        have h2 := chiZ_sq_unit d hunit0
        have h3 : chiZ d (a₀ : ZMod d) * chiZ d ((a₀ : ZMod d)⁻¹) = 1 := by
          rw [← chiZ_mul, ZMod.mul_inv_of_unit _ hunit0]
          unfold chiZ; rw [ZMod.val_one'' (by omega)]; simp
        linear_combination (-chiZ d x) * h1 - (chiZ d x * chiZ d p * chiZ d p) * h3
      rw [hχ, hQ'pt Q hQ x hx, phiC_shift_gamma0 hγ, hγe]
      congr 2
      simp only [hc, hpdef]; ring
    · have h0 : chiZ d x = 0 := chiZ_nonunit d hx
      have h0' : chiZ d (c * x) = 0 := chiZ_nonunit d (fun h => hx (by
        have := (hcu.unit⁻¹.isUnit).mul h
        rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this))
      rw [h0, h0']; simp
  unfold zTw
  rw [map_sum]
  simp_rw [map_zsmul]
  change ∑ x : ZMod d, chiZ d x • _ = _
  simp_rw [hsum, mul_smul]
  rw [← Finset.smul_sum]
  have hre : ∑ x : ZMod d, chiZ d (c * x) • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH (c * x)) =
      ∑ x : ZMod d, chiZ d x • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH x) :=
    Equiv.sum_comp (Units.mulLeft hcu.unit)
      (fun x => chiZ d x • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH x))
  rw [hre, chiZ_intCast]
  change jacobiSym a₀ d • zTw d (π Q).tauH = _
  have hJs : jacobiSym a₀ d = 1 ∨ jacobiSym a₀ d = -1 := by
    rcases jacobiSym.trichotomy a₀ d with h | h | h
    · exfalso
      rw [jacobiSym.eq_zero_iff] at h
      exact h.2 (Int.isCoprime_iff_gcd_eq_one.1 hcopd)
    · exact Or.inl h
    · exact Or.inr h
  have hg0 := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  rcases hJs with h | h
  · rw [h, one_smul, if_pos (by rw [hgen, h]; simp)]; rfl
  · rw [h, if_neg (by rw [hgen, h]; intro h'; exact hg0 (by push_cast at h'; linear_combination -h' / 2)),
      neg_one_zsmul]; rfl

/-- **`GZStatements.GrossZagierHeegnerCd` from `hCM`, Chebotarev at conductor `d`, genus theory and the two
printed Gross–Zagier statements.** -/
theorem grossZagierHeegnerCd_of_genus (hCM : T5Glue.ShimuraMainCM) (hJ : RingClassJd) (hG : GenusSqrtD)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_twist (twistTransportCd_of_genus hCM hJ hG) hGZ hGC

/-! ## §7. `RingClassJd`, proved (gz-heegner's `heegnerClassJ'` at conductor `d`) -/

section ClassJdProof

open TauCeti.GlobalNumberFields.NumberFieldOrder IsDedekindDomain ZInQ.RouteK.Redei
open ZInQ.GZHeegner (exists_coords_theta coe_thetaO kappa_theta_sub kappa_intCast kappa_lin theta_norm)

variable {m : ℕ} [NeZero m]

set_option maxRecDepth 20000 in
/-- **Chebotarev for the ring class field of conductor `f`** (gz-heegner's `exists_prime_picClass_eq1`, any `f`). -/
theorem exists_prime_picClass_eqf {f : ℕ} [NeZero f] (c : Pic (conductorOrder (QNeg m) f))
    (T : Set (HeightOneSpectrum (𝓞 (QNeg m)))) (hT : T.Finite) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 (QNeg m)), 𝔭 ∉ T ∧
      ¬ (conductorOrder (QNeg m) f).conductor ≤ 𝔭.asIdeal ∧
      ∀ hJ : 𝔭.asIdeal ∈ integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus,
        (conductorOrder (QNeg m) f).picClass ⟨_, hJ⟩ = c := by
  have hD := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (QNeg m)
    (ringClassField (conductorOrder (QNeg m) f))
    (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) f) c))
  have hδ : (Nat.card (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) f) c)).carrier : ℝ) /
      Nat.card (ringClassField (conductorOrder (QNeg m) f) ≃ₐ[QNeg m]
        ringClassField (conductorOrder (QNeg m) f)) ≠ 0 := by
    apply div_ne_zero
    · have : Nonempty (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) f) c)).carrier :=
        ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk
        (ringClassArtinEquiv (conductorOrder (QNeg m) f) c)).carrier)).ne'
    · exact_mod_cast (Nat.card_pos (α := ringClassField (conductorOrder (QNeg m) f) ≃ₐ[QNeg m]
        ringClassField (conductorOrder (QNeg m) f))).ne'
  have hinf := ((hD.infinite hδ).sdiff (hT.union (finite_conductor_primes (d := m) (f := f))))
  obtain ⟨𝔭, h𝔭, h𝔭T⟩ := hinf.nonempty
  rw [Set.mem_union, not_or] at h𝔭T
  refine ⟨𝔭, h𝔭T.1, h𝔭T.2, fun hJ => ?_⟩
  obtain ⟨⟨Q, hQp, hQo⟩, hF⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have hur := NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
    Ideal (𝓞 (QNeg m))).IsMaximal := 𝔭.isMaximal
  have : Q.LiesOver ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
    Ideal (𝓞 (QNeg m))) := hQo
  have hF' := isArithFrobAt_ringClassArtinEquiv_picClass (conductorOrder (QNeg m) f) ⟨_, hJ⟩ Q
  exact (ringClassArtinEquiv (conductorOrder (QNeg m) f)).injective (isArithFrobAt_eq_of_isUnramifiedAt hF' hF)

theorem im_thetaO (h3 : m % 4 = 3) : (((thetaO m h3 : 𝓞 (QNeg m)) : QNeg m)).im = 1 / 2 := by
  rw [coe_thetaO]

/-- **The lattice of `I ∩ 𝒪_f` for an ideal with basis `⟨a, θ − r⟩`.** -/
theorem idealLat_eq_jLatd (hsq : Squarefree m) (h3 : m % 4 = 3) {f : ℕ} [NeZero f]
    (I : Ideal (𝓞 (QNeg m))) (a r : ℤ)
    (ha : ((a : ℤ) : 𝓞 (QNeg m)) ∈ I) (hr : thetaO m h3 - (r : 𝓞 (QNeg m)) ∈ I)
    (hI : ∀ y ∈ I, ∃ u v : ℤ, y = (u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r)) :
    idealLat m f I = jLatd (-(m : ℤ)) a (2 * r - 1) f := by
  unfold idealLat jLatd
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨⟨n, z, hxz⟩, y, hyI, rfl⟩, rfl⟩
    obtain ⟨u, v, rfl⟩ := hI y hyI
    obtain ⟨z₀, z₁, rfl⟩ := exists_coords_theta hsq h3 z
    -- the `θ`-coordinate `v` is divisible by `f`
    have him := congrArg QuadraticAlgebra.im hxz
    simp only [map_add, map_mul, map_intCast, map_sub, map_natCast, RingOfIntegers.coe_eq_algebraMap] at him
    rw [← RingOfIntegers.coe_eq_algebraMap, coe_thetaO] at him
    simp [QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_natCast] at him
    have hv : v = f * z₁ := by
      have : (v : ℚ) = f * z₁ := by linarith
      exact_mod_cast this
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨u, z₁, ?_⟩
    have : ((((u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r) : 𝓞 (QNeg m))) : QNeg m) =
        (u : QNeg m) * (((a : 𝓞 (QNeg m)) : QNeg m)) +
          (v : QNeg m) * (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
    rw [this, kappa_lin, kappa_intCast, kappa_theta_sub, hv]
    simp [zsmul_eq_mul]
    ring
  · rw [Submodule.span_le]
    rintro _ (rfl | h)
    · refine Submodule.subset_span ⟨_, ⟨⟨a, 0, by simp⟩, _, ha, rfl⟩, kappa_intCast a⟩
    · rw [Set.mem_singleton_iff] at h; subst h
      refine Submodule.subset_span ⟨_, ⟨⟨0, thetaO m h3 - r, by simp⟩, (f : 𝓞 (QNeg m)) * (thetaO m h3 - r),
        Ideal.mul_mem_left _ _ hr, rfl⟩, ?_⟩
      · have : (((f : 𝓞 (QNeg m)) * (thetaO m h3 - r) : 𝓞 (QNeg m)) : QNeg m) =
            (f : QNeg m) * (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) := by
          simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
        rw [this, show ((f : QNeg m)) = (((f : ℤ) : ℚ) : QNeg m) by push_cast; rfl]
        have h2 := kappa_lin (m := m) (f : ℤ) 0 (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) 0
        simp only [Int.cast_natCast, Int.cast_zero, zero_mul, add_zero] at h2
        rw [show (((f : ℤ) : ℚ) : QNeg m) = (f : QNeg m) by push_cast; rfl, h2, kappa_theta_sub]

open ZInQ.Contrib.TYZGenus.RingClass in
/-- **`RingClassJd`, proved.** -/
theorem ringClassJd : RingClassJd := by
  intro m _ hsq h3 f _ M hM cl
  have hMm : M * m ≠ 0 := mul_ne_zero hM (by exact_mod_cast NeZero.ne m)
  have hT : {𝔭 : HeightOneSpectrum (𝓞 (QNeg m)) |
      Ideal.span {((M * m : ℤ) : 𝓞 (QNeg m))} ≤ 𝔭.asIdeal}.Finite := by
    have hne : Ideal.span {((M * m : ℤ) : 𝓞 (QNeg m))} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hMm
    exact (Ideal.finite_factors hne).subset fun 𝔭 h𝔭 => Ideal.dvd_iff_le.2 h𝔭
  obtain ⟨𝔭, h𝔭T, hcond, h𝔭c⟩ := exists_prime_picClass_eqf cl _ hT
  have hJ := mem_primeTo_of_not_le (d := m) (f := f) 𝔭 hcond
  have hM𝔭 : ((M * m : ℤ) : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h =>
    h𝔭T ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨p, hp, hlies⟩ := exists_prime_liesOver 𝔭.asIdeal 𝔭.ne_bot
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := m)
  have split : Ideal.absNorm 𝔭.asIdeal = p → ∃ (J : integralIdealsPrimeTo
      (conductorOrder (QNeg m) f).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) f).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ IsCoprime a b ∧ Ideal.absNorm (J : Ideal (𝓞 (QNeg m))) = a.natAbs ∧
      idealLat m f J = jLatd (-(m : ℤ)) a b f ∧
      (((J : Ideal (𝓞 (QNeg m))) = ⊤ ∧ a = 1) ∨ ((J : Ideal (𝓞 (QNeg m))).IsMaximal ∧ a.natAbs.Prime)) := by
    intro hN
    obtain ⟨r, hr⟩ := exists_int_sub_mem_of_absNorm 𝔭.asIdeal hp hN (thetaO m h3)
    have hpMm : ¬ (p : ℤ) ∣ M * m :=
      fun h => hM𝔭 ((intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal (M * m)).2 h)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hdiv : (4 * p : ℤ) ∣ (2 * r - 1) ^ 2 - (-(m : ℤ)) := by
      have hmem : (((r ^ 2 - r + ((m : ℤ) + 1) / 4) : ℤ) : 𝓞 (QNeg m)) ∈ 𝔭.asIdeal := by
        rw [← theta_norm h3 r]; exact Ideal.mul_mem_right _ _ hr
      obtain ⟨t, ht⟩ := (intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal _).1 hmem
      obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
      have hk' : ((m : ℤ) + 1) / 4 = k + 1 := by omega
      rw [hk'] at ht
      refine ⟨t, ?_⟩
      have hm : (m : ℤ) = 4 * k + 3 := by exact_mod_cast hk
      rw [hm]; linear_combination 4 * ht
    refine ⟨⟨𝔭.asIdeal, hJ⟩, p, 2 * r - 1, h𝔭c hJ, by exact_mod_cast hp.pos, hdiv, ?_, ?_, ?_, ?_,
      Or.inr ⟨𝔭.isMaximal, by simpa using hp⟩⟩
    · exact (Prime.irreducible hpZ).coprime_iff_not_dvd.2 (fun h => hpMm (dvd_mul_of_dvd_left h _))
    · refine (Prime.irreducible hpZ).coprime_iff_not_dvd.2 (fun hb => hpMm (dvd_mul_of_dvd_right ?_ _))
      have h4 : (p : ℤ) ∣ (2 * r - 1) ^ 2 - (-(m : ℤ)) := dvd_trans ⟨4, by ring⟩ hdiv
      have : (m : ℤ) = ((2 * r - 1) ^ 2 - (-(m : ℤ))) - (2 * r - 1) ^ 2 := by ring
      rw [this]
      exact dvd_sub h4 (dvd_pow hb two_ne_zero)
    · simp [hN]
    · apply idealLat_eq_jLatd hsq h3 𝔭.asIdeal p r
        (by exact_mod_cast natCast_mem_of_liesOver (p := p) 𝔭.asIdeal) hr
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
  · have h1 : (conductorOrder (QNeg m) f).picClass ⟨𝔭.asIdeal, hJ⟩ = 1 :=
      ((conductorOrder (QNeg m) f).picClass_eq_one_iff _).2
        ⟨p, Subalgebra.natCast_mem _ p, hP⟩
    rw [h𝔭c hJ] at h1
    subst h1
    refine ⟨1, 1, 1, map_one _, one_pos, ⟨((m : ℤ) + 1) / 4, by omega⟩, isCoprime_one_left,
      isCoprime_one_left, by simp [Ideal.one_eq_top], ?_, Or.inl ⟨by simp [Ideal.one_eq_top], rfl⟩⟩
    have h := idealLat_eq_jLatd (f := f) hsq h3 (⊤ : Ideal (𝓞 (QNeg m))) 1 1 Submodule.mem_top
      Submodule.mem_top (fun y _ => by
        obtain ⟨x₀, x₁, rfl⟩ := exists_coords_theta hsq h3 y
        exact ⟨x₀ + x₁, x₁, by push_cast; ring⟩)
    norm_num at h
    convert h using 2
    simp [Ideal.one_eq_top]
  · exact split hN

end ClassJdProof

/-- **`GZStatements.GrossZagierHeegnerCd` from `hCM`, genus theory and the two printed Gross–Zagier
statements** (Chebotarev at conductor `d` proved). -/
theorem grossZagierHeegnerCd_of_genus' (hCM : T5Glue.ShimuraMainCM) (hG : GenusSqrtD)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_genus hCM ringClassJd hG hGZ hGC

end ZInQ.Heegner32
