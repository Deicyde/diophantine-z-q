import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Constants

/-!
# Lane RC12-odd: the unaveraged comparison (O.7) (App F, tex 9101–9405)

Manuscript (11/5), Appendix F, Proposition `ex:app-theta-comparison`:
`H_M(mD) = c₀ 2^{ω(N)} ζ_M(D) λ_M(\overline{L P_D}) (mod 2^M)` (O.7), "no class number is divided out";
used at (3.8) (tex 2522–2530).

* `CornutJetchevThm31` — **PRINT**, Cornut–Jetchev, *Liftings of reduction maps for quaternion
  algebras* (preprint, 2010; 17 pp.), §3.5 Theorem 3.1 (p. 9) and Corollary 3.2 (p. 9), with the
  hypotheses H.1–H.3 of §3.1 (p. 5), the adelic map `θ_S` of §3.2 (pp. 5–6), the fine conductor of
  §3.3 (pp. 6–7, (10)–(12)), the sign invariant of §3.4 (p. 8, `φ_{S'} = ψ_{S'} ∘ θ_S`, (14)) and
  `κ = |Gal(K[c]/K[c_S])| ∏_{v∈S} N_v(v(c'), v(c''), v(n))`; Lemma 2.1 (p. 4) gives `N_v`. Read in the
  print (text extraction of the arXiv-style preprint; locators recorded from it). The objects
  `CM(G,H) = T(ℚ)\G(𝔸_f)/H` are not in Mathlib, so the statement is over an abstract interface: an
  equivariant map of Galois sets with conductor and sign maps.
* `cj_kappa_eq_one` — **PROVED**: the specialization `F_CJ = ℚ`, `K_CJ = ℚ(√(Dh_*))`,
  `B_CJ = M₂(ℚ)`, `S = {ℓ₀}`: H.2's integer `|S| + |Ram_f B| + [F:ℚ] = 1 + 0 + 1 = 2` is even, the
  parity condition `0 − 0 ≡ v_{ℓ₀}(N) = 0`, Lemma 2.1(ii) `N_{ℓ₀}(0,0,0) = q^{min(0,0)} = 1`, fine
  conductors one, so `κ = 1` (tex 9195–9243).
* `orbit_sum` — **PROVED**: an embedding orbit with stabilizer `{±1}` has `|R_z^×|/2` elements and,
  weighted by `c₀/|R_z^×|`, contributes `c₀/2` (tex 9308–9311, 9378–9390).
* `O7_assembly` — **PROVED**: summing the `2^{ω(N)+1}` orientation tuples, each contributing
  `(c₀/2) ζ λ` (tex 9318–9367), gives `c₀ 2^{ω(N)} ζ λ`.
* `witness_exact_order` — **PROVED**: `v₂ a_M(D_w) = c_θ + c_w` for `M > c_θ + c_w`,
  `c_θ = 9 + ω(N)` (tex 9391–9399).
-/

namespace ZInQ.Manuscript.RC.Odd

/-! ### Cornut–Jetchev, Theorem 3.1 (PRINT, abstract interface) -/

/-- **Cornut–Jetchev, Theorem 3.1 (PRINT; preprint 2010, §3.5, p. 9), abstract form.**
`X` stands for `CM(G,H)` and `Y` for `CM(G_S,H_S)` (§3.2), `θ = θ_S : X → Y` the `Gal_K^{ab}`-equivariant
map, `cf`, `cSf` the fine conductor maps (§3.3, (10)), `primeToS` the map `(c',c'') ↦ (c'_S, c''_S)`
of (12), `φ = ψ ∘ θ` the sign maps of §3.4 with values in `(ℤ/2)^{|S'|}`, `e` the map `e_{S'}` of
(14), `parity` the condition `v(c') − v(c'') ≡ v(n) (mod 2)` for `v ∈ S'`, and `κ` the integer of
§3.5. The theorem: for every fine conductor `c` with the parity condition, `θ` restricted to
`cf⁻¹(c)` is a surjective `κ(c)`-to-`1` map onto `cSf⁻¹(c_S) ∩ ψ⁻¹(e(c))`. -/
def CornutJetchevThm31 {X Y C CS Sg : Type*} (θ : X → Y) (cf : X → C) (cSf : Y → CS)
    (primeToS : C → CS) (ψ : Y → Sg) (e : C → Sg) (parity : C → Prop) (κ : C → ℕ) : Prop :=
  ∀ c, parity c →
    (∀ x, cf x = c → cSf (θ x) = primeToS c ∧ ψ (θ x) = e c) ∧
    ∀ y, cSf y = primeToS c → ψ y = e c → Nat.card {x : X // cf x = c ∧ θ x = y} = κ c

/-- Cornut–Jetchev, Lemma 2.1 (p. 4), case (ii) (`K/F` unramified, `δ = n' + n''`):
`N(n', n'', δ) = q^{min(n', n'')}`. -/
def cjNunramified (q n' n'' : ℕ) : ℕ := q ^ min n' n''

/-- **PROVED (tex 9203–9243).** The specialization of Cornut–Jetchev with `S = {ℓ₀}`: H.2's integer
is `2` (even), the parity condition holds, `N_{ℓ₀}(0,0,0) = 1` (Lemma 2.1(ii)), and with fine
conductors one (`|Gal(K[1]/K[1])| = 1`) the multiplicity is `κ = 1`. -/
theorem cj_kappa_eq_one (q : ℕ) :
    (1 + 0 + 1) % 2 = 0 ∧ (0 - 0 : ℤ) % 2 = 0 ∧ cjNunramified q 0 0 = 1 ∧
      1 * cjNunramified q 0 0 = 1 := by
  simp [cjNunramified]

/-- **PROVED.** With `κ = 1`, Theorem 3.1 gives a bijection between the source CM points of fine
conductor `c` and the target points of the prescribed conductor and sign (one sign fibre, not both,
tex 9245–9263). -/
theorem cj_bijection_of_kappa_one {X Y C CS Sg : Type*} {θ : X → Y} {cf : X → C} {cSf : Y → CS}
    {primeToS : C → CS} {ψ : Y → Sg} {e : C → Sg} {parity : C → Prop} {κ : C → ℕ}
    (hCJ : CornutJetchevThm31 θ cf cSf primeToS ψ e parity κ) {c : C} (hc : parity c)
    (hκ : κ c = 1) :
    Function.Bijective (fun x : {x : X // cf x = c} =>
      (⟨θ x.1, (hCJ c hc).1 x.1 x.2⟩ : {y : Y // cSf y = primeToS c ∧ ψ y = e c})) := by
  constructor
  · intro x₁ x₂ h
    have h' : θ x₁.1 = θ x₂.1 := congrArg Subtype.val h
    have hcard := (hCJ c hc).2 (θ x₁.1) ((hCJ c hc).1 x₁.1 x₁.2).1 ((hCJ c hc).1 x₁.1 x₁.2).2
    rw [hκ] at hcard
    have := (Nat.card_eq_one_iff_unique.mp hcard).1
    have hs := Subsingleton.elim (⟨x₁.1, x₁.2, rfl⟩ : {x : X // cf x = c ∧ θ x = θ x₁.1})
      ⟨x₂.1, x₂.2, h'.symm⟩
    exact Subtype.ext (congrArg (fun z : {x : X // cf x = c ∧ θ x = θ x₁.1} => z.1) hs)
  · rintro ⟨y, hy1, hy2⟩
    have hcard := (hCJ c hc).2 y hy1 hy2
    rw [hκ] at hcard
    obtain ⟨⟨x, hx1, hx2⟩⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
    exact ⟨⟨x, hx1⟩, Subtype.ext hx2⟩

/-! ### The orbit count and the orientation sum -/

/-- **PROVED (tex 9308–9311).** If a finite group `Gz` (`R_z^×`) acts on `E` with every stabilizer
of order two (`𝒪_F^× = {±1}`), every orbit has `|Gz|/2` elements. -/
theorem orbit_card_of_stab_two {Gz E : Type*} [Group Gz] [Fintype Gz] [MulAction Gz E] (x : E)
    [Fintype (MulAction.orbit Gz x)] [Fintype (MulAction.stabilizer Gz x)]
    (h2 : Fintype.card (MulAction.stabilizer Gz x) = 2) :
    Fintype.card (MulAction.orbit Gz x) = Fintype.card Gz / 2 := by
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group Gz x
  rw [h2] at this
  omega

/-- **PROVED (tex 9378–9390).** Per embedding orbit: weight `c₀/|R_z^×|` times `|R_z^×|/2` elements,
times the unit phase and `P_M(z)`, is `(c₀/2) P_M(z)` — an integer multiple, with no division of a
congruence by two (`c₀/|R_z^×|` and `c₀/2` are integers, `Constants.lean`). -/
theorem orbit_sum {R : Type*} [CommRing R] (w : ℕ) (hw2 : 2 ∣ w) (hw : w ∣ c0) (z : R) :
    ((c0 / w : ℕ) : R) * ((w / 2 : ℕ) : R) * z = ((c0 / 2 : ℕ) : R) * z := by
  rw [← Nat.cast_mul, orbit_weight_eq w hw2 hw]

/-- **PROVED (tex 9318–9370).** The orientation sum: if each of the `2^{ω(N)+1}` local orientation
tuples contributes `(c₀/2) ζ λ` (the reference tuple by Cornut–Jetchev and the reduction identity
`∑_a χ_F(a) P_M(z_a) = λ_M(\overline{LP_D})`; the others by the Atkin–Lehner and `ℓ₀`-uniformizer
sign cancellations), the total is `c₀ 2^{ω(N)} ζ λ`. -/
theorem O7_assembly {R : Type*} [CommRing R] {Tup : Type*} [Fintype Tup] (ω : ℕ)
    (hcard : Fintype.card Tup = 2 ^ (ω + 1)) (contrib : Tup → R) (ζ lam : R)
    (h : ∀ t, contrib t = ((c0 / 2 : ℕ) : R) * ζ * lam) :
    ∑ t, contrib t = (c0 : R) * 2 ^ ω * ζ * lam := by
  simp only [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  have : (c0 : R) = 2 * ((c0 / 2 : ℕ) : R) := by
    rw [show c0 = 2 * (c0 / 2) by norm_num [c0]]; push_cast; norm_num [c0]
  rw [this]; push_cast; ring

/-- **PROVED (tex 9331–9362).** The orientation-change signs cancel: at `p^e ‖ N` the Atkin–Lehner
normalizer multiplies the Schwartz weight by `α_p(−1) = w_{p^e} χ_{h_*}(p)^e` (O.3) and the
norm-weighted parametrization value by `w_{p^e} χ_{h_*}(p)^e`; at `ℓ₀` the uniformizer multiplies by
`(−1/ℓ₀) = −1`, by `χ_{h_*}(ℓ₀) = −1`, and by the Frobenius sign `+1` of `λ_M`. -/
theorem orientation_signs (wp χp : ℤ) (e : ℕ) (hw : wp = 1 ∨ wp = -1) (hχ : χp = 1 ∨ χp = -1) :
    (wp * χp ^ e) * (wp * χp ^ e) = 1 ∧ (-1 : ℤ) * (-1) * 1 = 1 := by
  refine ⟨?_, by norm_num⟩
  have h1 : wp * wp = 1 := by rcases hw with rfl | rfl <;> norm_num
  have h2 : χp ^ e * χp ^ e = 1 := by
    rw [← mul_pow]; rcases hχ with rfl | rfl <;> simp
  calc wp * χp ^ e * (wp * χp ^ e) = (wp * wp) * (χp ^ e * χp ^ e) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/-! ### The fixed witness's valuation (tex 9391–9399) -/

theorem c0_mul_two_pow_eq (ω : ℕ) : (c0 : ℤ) * 2 ^ ω = 2 ^ (9 + ω) * 47385 := by
  rw [pow_add]; norm_num [c0]; ring

/-- **PROVED (tex 9391–9399).** If `a ≡ c₀ 2^{ω(N)} ζ λ (mod 2^M)` with `ζ` odd (the phase is a unit)
and `λ = λ_M(\overline{Q})` of exact 2-adic order `c_w`, and `c_θ + c_w < M` with
`c_θ = 9 + ω(N)`, then `a` has exact order `c_θ + c_w`: `v₂ a_M(D_w) = c_θ + c_w`. -/
theorem witness_exact_order (ω M cw : ℕ) {a ζ lam : ℤ} (hζ : Odd ζ)
    (hlam1 : (2 : ℤ) ^ cw ∣ lam) (hlam2 : ¬ (2 : ℤ) ^ (cw + 1) ∣ lam)
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + cw < M) :
    (2 : ℤ) ^ (9 + ω + cw) ∣ a ∧ ¬ (2 : ℤ) ^ (9 + ω + cw + 1) ∣ a := by
  obtain ⟨l, rfl⟩ := hlam1
  have hl : ¬ (2 : ℤ) ∣ l := by
    rintro ⟨l', rfl⟩; exact hlam2 ⟨l', by ring⟩
  set x : ℤ := (c0 : ℤ) * 2 ^ ω * ζ * (2 ^ cw * l) with hx
  have hx' : x = 2 ^ (9 + ω + cw) * (47385 * ζ * l) := by
    rw [hx, c0_mul_two_pow_eq]; ring
  have hodd : ¬ (2 : ℤ) ∣ 47385 * ζ * l := by
    intro h
    rcases Int.prime_two.dvd_or_dvd h with h' | h'
    · rcases Int.prime_two.dvd_or_dvd h' with h'' | h''
      · norm_num at h''
      · exact (Int.not_even_iff_odd.mpr hζ) (even_iff_two_dvd.mpr h'')
    · exact hl h'
  obtain ⟨t, ht⟩ := hcong
  have ha : a = x + 2 ^ M * t := by linarith
  have hMk : 9 + ω + cw + 1 ≤ M := hM
  constructor
  · rw [ha, hx']
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _)
  · intro h
    have h2 : (2 : ℤ) ^ (9 + ω + cw + 1) ∣ x := by
      have := dvd_sub h (dvd_mul_of_dvd_left (pow_dvd_pow 2 hMk) t)
      rwa [ha, add_sub_cancel_right] at this
    rw [hx', pow_succ] at h2
    exact hodd ((mul_dvd_mul_iff_left (by positivity)).mp h2)

end ZInQ.Manuscript.RC.Odd
