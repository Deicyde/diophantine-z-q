import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
Theorem 5.3, Lane RC0: the calibration at an address, over the family curve `E_{ℓh}`

The calibration (Proposition `ex:arith-central-calibration`, tex 3987–4141) works at an address
`x` of the binary family, with `h = h_x`. Its Kummer data are
`G : GenuineKummerData K (Ecurve ℓ) h` for `K = QuadraticField k`, and the ordinary compact Kummer
complex `C_K` of its proof (tex 4006–4018) is the one of the twist `E^{(h)}` over `K`, the central
curve `centralCurve G`.

The family has one real sign (tex 1864–1869) and `h_0 = 1` (tex 2685–2688), so every `h_x` is
positive. For `h > 0` the twist by `h` of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` (tex 1761–1763) is,
literally as a Weierstrass curve, the curve `E_{ℓh}` of the same family. The arithmetic rank
statements of the calibration discharge are stated for a curve `Ecurve ℓ'` with `ℓ' : ℕ`; they
apply with `ℓ' = ℓ h`.

* `curve_qtwist`: `qtwist (curve t) d = curve (t d)`;
* `natCast_toNat_of_pos`, `etw_eq_ecurve_of_pos`: `E_ℓ^{(h)} = E_{ℓh}` for `h > 0`;
* `etw_mul_toNat_of_pos`: `E_{ℓh}^{(k)} = E_ℓ^{(hk)}` for `h > 0`;
* `centralCurve_eq_of_pos`: the central curve of `G` is the base change of `E_{ℓh}` to `K`;
* `isElliptic_ecurve_mul_of_pos`: `E_{ℓh}` is elliptic as soon as the data `G` exist;
* `centralRankOne_of_arithmetic_pos`: the integral rank-one statement at the address;
* `z2Corank_selmerTwoPower_congr`, `selmerCorankOneOverK_of_pos`: the Selmer input at the address
  is the address's own statement, corank one for `E^{(h)}` and corank zero for `E^{(hk)}`, the
  identity `s₂(E^{(h)}/K) = 1` in the form of tex 2616–2626;
* `isTotallyComplex_quadraticField_of_neg`: `QuadraticField k` is totally complex for `k < 0` (the
  final companion is a negative discriminant, tex 2595–2600, and `K` is imaginary, tex 2720);
* `not_isSquare_intCast_of_neg`, `diskTie_of_arithmetic_pos`: the disk-order statement at the
  address, with the field hypothesis and the non-square hypothesis supplied by `k < 0`.

Every declaration below is PROVED. The remaining inputs of the calibration discharge (finite
generation, the coefficient comparison, the Milne prints, integral self-duality) stay hypotheses.
Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.CalibrationShape

attribute [local instance] Nat.fact_prime_two

/-- **Twists of the family curves are family curves** (tex 1761–1763, 1829–1830): the twist by `d`
of `E_t : y² = x(x − t)(x + 3t)` is, literally as a Weierstrass curve, `E_{td}`. It is the
commuted form of the setup's `qtwist_curve`, proved here on the five coefficients.
Kind: PROVED. -/
theorem curve_qtwist (t d : ℚ) : qtwist (curve t) d = curve (t * d) := by
  ext <;> simp only [qtwist, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆] <;> ring

/-- For `h > 0` the rational number `h.toNat` is `h`. The addresses `h = h_x` of the family are
positive: one real sign (tex 1864–1869) and `h_0 = 1` (tex 2685–2688). Kind: PROVED. -/
theorem natCast_toNat_of_pos {h : ℤ} (hh : 0 < h) : ((h.toNat : ℕ) : ℚ) = (h : ℚ) := by
  have h' : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg hh.le
  exact_mod_cast h'

/-- **`E_ℓ^{(h)} = E_{ℓh}` for `h > 0`** (tex 1761–1763, 1829–1830): at a positive address
`h = h_x` (tex 1864–1869, 2685–2688) the twist `Etw ℓ h` is, literally, the curve `Ecurve (ℓ h)`
of the family. Kind: PROVED. -/
theorem etw_eq_ecurve_of_pos {ℓ : ℕ} {h : ℤ} (hh : 0 < h) : Etw ℓ h = Ecurve (ℓ * h.toNat) := by
  show qtwist (curve (ℓ : ℚ)) (h : ℚ) = curve ((ℓ * h.toNat : ℕ) : ℚ)
  rw [curve_qtwist, Nat.cast_mul, natCast_toNat_of_pos hh]

/-- **`E_{ℓh}^{(k)} = E_ℓ^{(hk)}` for `h > 0`**, literally: the companion twist of the address
curve is the twist `E^{(hk)}` of the calibration's hypotheses (tex 3988–3991), as in the
sum-and-difference identity at the address (tex 2616–2626). Kind: PROVED. -/
theorem etw_mul_toNat_of_pos {ℓ : ℕ} {h : ℤ} (hh : 0 < h) (k : ℤ) :
    Etw (ℓ * h.toNat) k = Etw ℓ (h * k) := by
  show qtwist (curve ((ℓ * h.toNat : ℕ) : ℚ)) (k : ℚ) = qtwist (curve (ℓ : ℚ)) ((h * k : ℤ) : ℚ)
  rw [curve_qtwist, curve_qtwist]
  congr 1
  rw [Nat.cast_mul, natCast_toNat_of_pos hh, Int.cast_mul]
  ring

/-- **The central curve at an address** (tex 3987–3991, 4006–4013): for Kummer data
`G : GenuineKummerData K (Ecurve ℓ) h` of an address with `h > 0`, the central twist
`E^{(h)} ⊗ K` is the base change of `E_{ℓh}` to `K = QuadraticField k`. This is the curve binding
of the calibration discharge's arithmetic rank statements with `ℓ' = ℓ h`. Kind: PROVED. -/
theorem centralCurve_eq_of_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h) :
    centralCurve G = (Ecurve (ℓ * h.toNat)).baseChange (QuadraticField k) := by
  have hW : G.W = (Ecurve ℓ).map (algebraMap ℚ (QuadraticField k)) := G.hW
  have hd : ((h : ℤ) : QuadraticField k) = algebraMap ℚ (QuadraticField k) (h : ℚ) :=
    (map_intCast (algebraMap ℚ (QuadraticField k)) h).symm
  have key : centralCurve G = (Etw ℓ h).baseChange (QuadraticField k) := by
    change twistK G.W ((h : ℤ) : QuadraticField k) =
      (twistK (Ecurve ℓ) (h : ℚ)).map (algebraMap ℚ (QuadraticField k))
    rw [hW, hd, twistK_map]
  rw [key, etw_eq_ecurve_of_pos hh]

/-- **`E_{ℓh}` is elliptic** for `h > 0` as soon as Kummer data of the address exist
(tex 1761–1765: `Δ = 2304 ℓ^6`): its base change to `K` is the central curve, which is elliptic.
This discharges the ellipticity instance of `centralRankOne_of_arithmetic_pos`. Kind: PROVED. -/
theorem isElliptic_ecurve_mul_of_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h) :
    (Ecurve (ℓ * h.toNat)).IsElliptic := by
  have hu : IsUnit ((Ecurve (ℓ * h.toNat)).baseChange (QuadraticField k)).Δ := by
    rw [← centralCurve_eq_of_pos hh G]
    exact (centralCurve_elliptic G).isUnit
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] at hu
  refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
  rw [h0, map_zero] at hu
  exact not_isUnit_zero hu

/-- **Integral rank one at an address** (tex 3987–4141; universal coefficients and self-duality,
tex 4006–4018): under the Selmer input `SelmerCorankOneOverK (ℓ h) k`, finite generation, `k` not a
square and the coefficient comparison for the curve `E_{ℓh}`, the integral first cohomology of the
compact central complex of `G` has rank one. It is `compactCentral_rank_one` at `ℓ' = ℓ h`,
through `centralCurve_eq_of_pos`. Kind: PROVED. -/
theorem centralRankOne_of_arithmetic_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(Ecurve (ℓ * h.toNat)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison (ℓ * h.toNat) k G.S
      (arithmeticCentralFull (ℓ * h.toNat) k G (centralCurve_eq_of_pos hh G)))
    (hSel : SelmerCorankOneOverK (ℓ * h.toNat) k) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 :=
  compactCentral_rank_one (ℓ * h.toNat) k G (centralCurve_eq_of_pos hh G) hfinite hk I hSel

/-- Equal curves have the same `2^∞`-Selmer corank statements (the coranks of tex 2616–2626).
The transport is by substitution of the curve, so it does not depend on how the Selmer
group's topological instances are recorded. Kind: PROVED. -/
theorem z2Corank_selmerTwoPower_congr {E E' : WeierstrassCurve ℚ} (hE : E = E') (r : ℕ) :
    Z2Corank (selmerTwoPower E) r ↔ Z2Corank (selmerTwoPower E') r := by
  subst hE
  exact Iff.rfl

/-- **The Selmer input is the address's own statement** (tex 2616–2626 for `E^{(h)}`, with the
calibration's hypotheses, tex 3988–3991, and the forward theorems at known simple zeros,
tex 4020–4021): for `h > 0`, `SelmerCorankOneOverK (ℓ h) k` holds exactly when `E^{(h)}` has
`2^∞`-Selmer corank one and `E^{(hk)}` has corank zero over `ℚ`. It follows from
`etw_eq_ecurve_of_pos` and `etw_mul_toNat_of_pos`. Kind: PROVED. -/
theorem selmerCorankOneOverK_of_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h) :
    SelmerCorankOneOverK (ℓ * h.toNat) k ↔
      (SelmerCorankOne (Etw ℓ h) ∧ Z2Corank (selmerTwoPower (Etw ℓ (h * k))) 0) :=
  and_congr (z2Corank_selmerTwoPower_congr (etw_eq_ecurve_of_pos hh).symm 1)
    (z2Corank_selmerTwoPower_congr (etw_mul_toNat_of_pos hh k) 0)

/-- **`ℚ(√k)` is totally complex for `k < 0`** (the final companion is a negative discriminant,
tex 2595–2600, and `K = ℚ(√k)` is imaginary, tex 2720): a real embedding would send the generator
`√k` to a real square root of the negative number `k`. This is the field hypothesis of the
calibration discharge's shape statements. Kind: PROVED. -/
theorem isTotallyComplex_quadraticField_of_neg {k : ℤ} (hk : k < 0) :
    NumberField.IsTotallyComplex (QuadraticField k) := by
  refine ⟨fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex.mp fun hv => ?_⟩
  let ψ := NumberField.InfinitePlace.embedding_of_isReal hv
  let α : QuadraticField k :=
    IntermediateField.AdjoinSimple.gen ℚ (RC53Assist.QuadraticDescent.sqrtK k)
  have hα : α ^ 2 = (k : QuadraticField k) := by
    apply (algebraMap (QuadraticField k) (SeparableClosure ℚ)).injective
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, map_intCast,
      RC53Assist.QuadraticDescent.sqrtK_sq, map_intCast]
  have h1 : ψ α ^ 2 = (k : ℝ) := by rw [← map_pow, hα, map_intCast]
  have h2 : (k : ℝ) < 0 := by exact_mod_cast hk
  linarith [sq_nonneg (ψ α)]

/-- A negative integer is not a square in `ℚ`; for the final companion `k < 0` (tex 2595–2600)
this is the non-square hypothesis `K = ℚ(√k) ≠ ℚ` of the calibration discharge. Kind: PROVED. -/
theorem not_isSquare_intCast_of_neg {k : ℤ} (hk : k < 0) : ¬ IsSquare (k : ℚ) := by
  rintro ⟨r, hr⟩
  have h2 : (k : ℚ) < 0 := by exact_mod_cast hk
  nlinarith [mul_self_nonneg r]

section DiskTie

attribute [local instance 10000]
  ZInQ.Contrib.RC53Assist.CalibrationShape.arithmeticFieldDecidableEq

/-- **The disk-order statement at an address** (tex 3987–4141; self-duality and the free parts,
tex 4015–4018): for `h > 0` and `k < 0`, `diskTie_of_arithmetic` applies to the Kummer data `G`
of the address with `ℓ' = ℓ h`. The field hypothesis and the non-square hypothesis come from
`k < 0` (tex 2595–2600, 2720); the other inputs are those of `diskTie_of_arithmetic`, the curve
binding being `centralCurve_eq_of_pos`. The point group of the central curve is formed with the
decidable equality on `K` used by `diskTie_of_arithmetic`. Kind: PROVED. -/
theorem diskTie_of_arithmetic_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h) (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(Ecurve (ℓ * h.toNat)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (I : KummerCoefficientComparison (ℓ * h.toNat) k G.S
      (arithmeticCentralFull (ℓ * h.toNat) k G (centralCurve_eq_of_pos hh G)))
    (hSel : SelmerCorankOneOverK (ℓ * h.toNat) k)
    (hdual : IntegralCentralKummerDuality G hfinite) :
    DiskTie G (centralDiskMatrix G hfinite 1).det (centralDiskMatrix G hfinite 2).det
      (centralDiskMatrix G hfinite 3).det :=
  diskTie_of_arithmetic (ℓ * h.toNat) k G (centralCurve_eq_of_pos hh G) hfinite hloc hglob
    hlocal hglobal (isTotallyComplex_quadraticField_of_neg hk) h2
    (not_isSquare_intCast_of_neg hk) I hSel hdual

end DiskTie

end ZInQ.Manuscript.RC.Wiring
