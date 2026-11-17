import Mathlib

/-!
# Lane RC12-odd: the fixed witness and the detecting stages (O.2) — the algebraic content

Manuscript (11/5), Appendix F, Proposition `ex:app-detector` and its proof (tex 8224–8405), with
the finite-field evaluation map of `ex:app-theta-form` (tex 8439–8461).

PROVED here (abstractly, over the data the text constructs):
* the finite-field Kummer map `κ_M(P) = F R − R` (`nR = P`) on `E(𝔽_{ℓ₀²})`: well defined, additive,
  valued in `E[n]`, kernel `n E(𝔽_{ℓ₀²})`, onto `E[n]` when `F − 1` is onto, Frobenius-equivariant;
  `λ_M = b κ_M` has Frobenius sign `+1` when `bC = b` (tex 8378–8390, 8439–8456) — `kummer*`;
* the cocycle algebra of `σ = hτ`: `c(σ²) = (1 + C)v`, `b c(σ²) = 2 b(v) = 2^{a+1}` (tex 8343–8356);
* `c_Q(h^d) = d c_Q(h)` on `H = ker ρ` (tex 8336–8339);
* the central-scalar coboundary `(z − 1)c(g) = (g − 1)c(z)` (tex 8321–8326);
* the determinant step `Fr ≡ C (mod 2^M)`, `det C = −1`, `det ρ(Fr) = ℓ₀` give `ℓ₀ ≡ −1 (mod 2^M)`
  and, for `M ≥ 2`, `ℓ₀ ≡ 3 (mod 4)`, `(m/ℓ₀) = (−1/ℓ₀)(h_*/ℓ₀) = 1` (tex 8371–8376, 8437–8438),
  and the inert condition `(D h_*/ℓ₀) = −1` used for Cornut–Jetchev's H.3 (tex 9205–9209).

Not formalized (kinds as stated in the report): the witness choice through Dokchitser–Dokchitser
Thm 1.8 and Bump–Friedberg–Hoffstein clauses (i)–(ii) pp. 543–544 (PRINT, lanes RC8/batch 3),
nontorsion of `P_{D_w}` via Cai–Shu–Tian Thm 1.1 (PRINT, stated elsewhere), the torsion multiplier
`B = ∏ #E(𝔽_{p_j^f})` and Serre's open image (GLUE/PRINT), Chebotarev (GLUE), and the Weil-pairing
identity `det ρ(Fr_{ℓ₀}) = ℓ₀` (GLUE). They enter below as hypotheses.
-/

namespace ZInQ.Manuscript.RC.Odd

/-! ### The finite-field Kummer map (tex 8378–8390, 8439–8456) -/

section Kummer

variable {A : Type*} [AddCommGroup A] (F : A →+ A) (n : ℕ)

/-- **PROVED.** `κ(P) = FR − R` does not depend on the division point `R` (`F` is the identity on
`E[n]`, since `Fr_{ℓ₀}² = 1` on `E[2^M]`). -/
theorem kummer_indep (htriv : ∀ t, n • t = 0 → F t = t) {R R' : A} (h : n • R = n • R') :
    F R - R = F R' - R' := by
  have h0 : n • (R - R') = 0 := by rw [smul_sub, h, sub_self]
  have := htriv _ h0
  rw [map_sub] at this
  rw [sub_eq_sub_iff_sub_eq_sub, this]

/-- **PROVED.** `κ(P) ∈ E[n]` for `P` fixed by `F`. -/
theorem kummer_mem_torsion {P R : A} (hP : F P = P) (hR : n • R = P) : n • (F R - R) = 0 := by
  rw [smul_sub, ← map_nsmul, hR, hP, sub_self]

/-- **PROVED.** Additivity: `R + R'` divides `P + P'`. -/
theorem kummer_add (R R' : A) : F (R + R') - (R + R') = (F R - R) + (F R' - R') := by
  rw [map_add]; abel

/-- **PROVED.** The kernel is `n E(k₀)`: `κ(P) = 0` iff `P = n R₀` with `R₀` fixed by `F`. -/
theorem kummer_eq_zero_iff (htriv : ∀ t, n • t = 0 → F t = t) {P R : A} (hR : n • R = P) :
    F R - R = 0 ↔ ∃ R₀, F R₀ = R₀ ∧ n • R₀ = P := by
  constructor
  · intro h; exact ⟨R, (sub_eq_zero.mp h), hR⟩
  · rintro ⟨R₀, hR₀, hnR₀⟩
    rw [kummer_indep F n htriv (hR.trans hnR₀.symm), hR₀, sub_self]

/-- **PROVED.** Surjectivity onto `E[n]`: if `F − 1` is onto (`F² − 1` is a nonzero separable
isogeny), every `S ∈ E[n]` is `κ(nR)` for `R` with `FR − R = S`. -/
theorem kummer_surj (hsurj : ∀ S, ∃ R, F R - R = S) {S : A} (hS : n • S = 0) :
    ∃ P R, F P = P ∧ n • R = P ∧ F R - R = S := by
  obtain ⟨R, hR⟩ := hsurj S
  refine ⟨n • R, R, ?_, rfl, hR⟩
  have : n • (F R - R) = 0 := by rw [hR, hS]
  rw [smul_sub, ← map_nsmul, sub_eq_zero] at this
  exact this

/-- **PROVED.** Frobenius equivariance `κ(Fr P) = Fr κ(P)` for `Fr` commuting with `F`
(tex 8388, 8453–8455). -/
theorem kummer_equivariant (Fr : A →+ A) (hcomm : ∀ x, Fr (F x) = F (Fr x)) (R : A) :
    F (Fr R) - Fr R = Fr (F R - R) := by
  rw [map_sub, hcomm]

/-- **PROVED.** Frobenius sign `+1`: if the row `b` satisfies `b ∘ Fr = b` on `E[n]` (`bC = b`), then
`λ = b κ` satisfies `λ(Fr P) = λ(P)` (tex 8389–8390, 8436, 8456). -/
theorem lambda_frobenius_sign {B : Type*} [AddCommGroup B] (Fr : A →+ A)
    (hcomm : ∀ x, Fr (F x) = F (Fr x)) (b : A →+ B)
    (hb : ∀ t, n • t = 0 → b (Fr t) = b t) {P R : A} (hP : F P = P) (hR : n • R = P) :
    b (F (Fr R) - Fr R) = b (F R - R) := by
  rw [kummer_equivariant F Fr hcomm, hb _ (kummer_mem_torsion F n hP hR)]

end Kummer

/-! ### The Kummer cocycle (tex 8308–8356) -/

section Cocycle

variable {Gp T : Type*} [Group Gp] [AddCommGroup T] (ρ : Gp →* AddMonoid.End T)

/-- A Kummer cocycle `c(gh) = c(g) + ρ(g) c(h)`. -/
def IsCocycle (c : Gp → T) : Prop := ∀ g h, c (g * h) = c g + ρ g (c h)

variable {ρ}

theorem IsCocycle.map_one {c : Gp → T} (hc : IsCocycle ρ c) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, _root_.map_one] at h
  exact add_eq_left.mp (show c 1 + c 1 = c 1 from h.symm)

/-- **PROVED (tex 8312, 8336–8339).** On `H = ker ρ` the cocycle is a homomorphism:
`c(h^d) = d · c(h)`. -/
theorem IsCocycle.pow_of_ker {c : Gp → T} (hc : IsCocycle ρ c) {h : Gp} (hh : ρ h = 1) (d : ℕ) :
    c (h ^ d) = d • c h := by
  induction d with
  | zero => simp [hc.map_one]
  | succ d ih =>
    rw [pow_succ, hc, ih, map_pow, hh, one_pow, AddMonoid.End.coe_one, id_eq, succ_nsmul]

/-- **PROVED (tex 8349–8355).** For `σ = hτ` with `ρ(h) = 1`, `ρ(τ) = C`, `τ² = 1`:
`ρ(σ) = C` and `c(σ²) = (1 + C) c(h)`; the `τ`-term `(1 + C) d_τ` vanishes because `τ² = 1`. -/
theorem IsCocycle.sigma_sq {c : Gp → T} (hc : IsCocycle ρ c) {h τ : Gp} (hh : ρ h = 1)
    (hτ : τ * τ = 1) :
    ρ (h * τ) = ρ τ ∧ c ((h * τ) * (h * τ)) = c h + ρ τ (c h) := by
  have hρ : ρ (h * τ) = ρ τ := by rw [map_mul, hh, one_mul]
  refine ⟨hρ, ?_⟩
  have hτ0 : c τ + ρ τ (c τ) = 0 := by rw [← hc, hτ, hc.map_one]
  rw [hc, hρ, hc, hh, AddMonoid.End.coe_one, id_eq, map_add]
  calc c h + c τ + (ρ τ (c h) + ρ τ (c τ)) = c h + ρ τ (c h) + (c τ + ρ τ (c τ)) := by abel
    _ = c h + ρ τ (c h) := by rw [hτ0, add_zero]

/-- **PROVED (tex 8346–8355).** With a row `b` fixed by `C` (`bC = b`) and `c(h) = v = 2^a t₀`,
`b(t₀) = 1`: `b c(σ²) = 2 b(v) = 2^{a+1}`. -/
theorem row_value {B : Type*} [CommRing B] (C : T →+ T) (b : T →+ B) (hb : ∀ x, b (C x) = b x)
    (t₀ : T) (ht₀ : b t₀ = 1) (a : ℕ) :
    b ((2 ^ a) • t₀ + C ((2 ^ a) • t₀)) = 2 ^ (a + 1) := by
  rw [map_add, hb, map_nsmul, ht₀, nsmul_eq_mul, mul_one, pow_succ]; push_cast; ring

/-- **PROVED.** The detecting valuation `c_w = a + 1`: `v₂(2^{a+1}) = a + 1`. -/
theorem padicValNat_cw (a : ℕ) : padicValNat 2 (2 ^ (a + 1)) = a + 1 := by
  rw [padicValNat.prime_pow]

/-- **PROVED (tex 8319–8326).** If `z` is central and acts by a scalar `ζ` with `ζ − 1` a unit,
every cocycle is a coboundary: `c(g) = ρ(g) w − w` with `w = (ζ − 1)^{−1} c(z)`, since
`(ζ − 1) c(g) = (ρ(g) − 1) c(z)`. -/
theorem IsCocycle.coboundary_of_central {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V]
    [Module K V] {ρ' : Gp →* (V →ₗ[K] V)} {c : Gp → V}
    (hc : ∀ g h, c (g * h) = c g + ρ' g (c h)) {z : Gp} (hz : ∀ g, z * g = g * z) {ζ : K}
    (hρz : ρ' z = ζ • LinearMap.id) (hζ : IsUnit (ζ - 1)) :
    ∃ w : V, ∀ g, c g = ρ' g w - w := by
  obtain ⟨u, hu⟩ := hζ
  refine ⟨(↑u⁻¹ : K) • c z, fun g => ?_⟩
  have h1 := hc z g
  have h2 := hc g z
  rw [hz g, h2, hρz, LinearMap.smul_apply, LinearMap.id_apply] at h1
  -- c g + ρ g (c z) = c z + ζ c g, so (ζ - 1) c g = ρ g (c z) - c z
  have key : (ζ - 1) • c g = ρ' g (c z) - c z := by
    rw [sub_smul, one_smul]; rw [← sub_eq_zero] at h1 ⊢
    rw [← neg_eq_zero, ← h1]; abel
  have : c g = (↑u⁻¹ : K) • ((ζ - 1) • c g) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [this, key, map_smul, smul_sub]

end Cocycle

/-! ### Determinant and residue signs at the detecting prime (tex 8371–8376, 8437–8438) -/

/-- **PROVED.** Congruent matrices have congruent determinants (`Fr ≡ C (mod 2^M)` gives
`det Fr ≡ det C`). -/
theorem det_congr {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') {n : Type*}
    [Fintype n] [DecidableEq n] {X Y : Matrix n n K} (h : f.mapMatrix X = f.mapMatrix Y) :
    f X.det = f Y.det := by
  rw [RingHom.map_det, RingHom.map_det, h]

/-- **PROVED (tex 8374, 8437).** If `ℓ₀ ≡ −1 (mod 2^M)` (determinant of `Fr_{ℓ₀} ≡ C`, `det C = −1`)
and `M ≥ 2`, then `ℓ₀ ≡ 3 (mod 4)`. -/
theorem mod_four_of_neg_one {ℓ₀ M : ℕ} (hM : 2 ≤ M) (h : ((ℓ₀ : ℤ) : ZMod (2 ^ M)) = -1) :
    ℓ₀ % 4 = 3 := by
  have h4 : (4 : ℕ) ∣ 2 ^ M := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 hM
  have := congrArg (ZMod.castHom h4 (ZMod 4)) h
  simp only [map_intCast, map_neg, map_one] at this
  have h' : ((ℓ₀ : ℤ) : ZMod 4) = ((3 : ℤ) : ZMod 4) := by rw [this]; decide
  rw [ZMod.intCast_eq_intCast_iff] at h'
  have := Int.ModEq.eq h'
  omega

/-- **PROVED (tex 8437–8438).** `(m/ℓ₀) = (−1/ℓ₀)(h_*/ℓ₀) = 1` for `m = −h_*`, `ℓ₀ ≡ 3 (mod 4)`,
`(h_*/ℓ₀) = −1`. -/
theorem legendre_m_eq_one {ℓ₀ : ℕ} [Fact ℓ₀.Prime] (h4 : ℓ₀ % 4 = 3) {hstar : ℤ}
    (hh : legendreSym ℓ₀ hstar = -1) : legendreSym ℓ₀ (-hstar) = 1 := by
  have hne : ℓ₀ ≠ 2 := by omega
  rw [show -hstar = (-1) * hstar by ring, legendreSym.mul, legendreSym.at_neg_one hne,
    ZMod.χ₄_nat_three_mod_four h4, hh]
  norm_num

/-- **PROVED (tex 9205–9209).** Cornut–Jetchev's H.3 in its inert case:
`(D h_*/ℓ₀) = (D/ℓ₀)(h_*/ℓ₀) = 1 · (−1) = −1`. -/
theorem legendre_inert {ℓ₀ : ℕ} [Fact ℓ₀.Prime] {D hstar : ℤ} (hD : legendreSym ℓ₀ D = 1)
    (hh : legendreSym ℓ₀ hstar = -1) : legendreSym ℓ₀ (D * hstar) = -1 := by
  rw [legendreSym.mul, hD, hh, one_mul]

end ZInQ.Manuscript.RC.Odd
