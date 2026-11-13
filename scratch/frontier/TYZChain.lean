import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.GZTheta.NewCMProof
import ZInQKernel.Contrib.GZTheta.New32
import ZInQKernel.Contrib.GZTheta.Final
import ZInQKernel.Contrib.GZDecomp.Decomp

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraRecip.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: Shimura reciprocity for Heegner points on `X₀(32) = A` (the leaf)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

This file states the one textbook leaf of task tyz-cm, **the main theorem of complex multiplication
for the Heegner points of `X₀(32)`, in Gross's form** (`ShimuraReciprocityPic`), over genuine
definitions:

* the order `O = ℤ + f𝓞_K` of `K = ℚ(√−m)` (ring-class's `conductorOrder`), its ring class field and
  Tau Ceti's Artin isomorphism `Pic(O) ≃* Gal(H_O/K)`, Picard classes of ideals of `𝓞_K` prime to
  `f` (Tau Ceti's `picClass`: the class of `J ∩ O`);
* the normalized complex embedding `κ : K → ℂ`, `√−m ↦ i√m` (`kappa`), and the lattice
  `κ(J ∩ O) ⊂ ℂ` of such an ideal (`idealLat`);
* cm-points' Heegner forms of level 32, their lattices `⟨1, τ_Q⟩`, `⟨1/32, τ_Q⟩` and Heegner points
  `heegnerPt Q ∈ A(ℚ̄)` through x0-32's `X0.phiC`.

The two targets of tyz-cm are derived from it in `ShimuraField.lean`
(`CM.CMFieldOfDefinition ringClassFieldD`) and `ShimuraZn.lean` (`Package.TYZSigmaFixesZn`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- The normalized complex embedding `κ : ℚ(√−m) → ℂ`, `a + b√−m ↦ a + b·i√m` (as a function). -/
def kappa (m : ℕ) (x : QNeg m) : ℂ := (x.re : ℂ) + (x.im : ℂ) * (I * (Real.sqrt m : ℂ))

/-- The set `J ∩ O ⊂ K` for an ideal `J` of `𝓞_K` and the order `O = ℤ + f𝓞_K`. -/
def idealMeetOrder (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Set (QNeg m) :=
  {x | x ∈ (conductorOrder (QNeg m) f).toSubalgebra ∧ ∃ y ∈ J, (y : QNeg m) = x}

/-- The lattice `κ(J ∩ O) ⊂ ℂ` (the `ℤ`-span of the image; `J ∩ O` is already a `ℤ`-module). -/
def idealLat (m f : ℕ) [NeZero m] [NeZero f] (J : Ideal (𝓞 (QNeg m))) : Submodule ℤ ℂ :=
  Submodule.span ℤ (kappa m '' idealMeetOrder m f J)

/-- The discriminant `f²·d_K` of `ℤ + f𝓞_K` in `K = ℚ(√−m)`, `m` squarefree:
`d_K = −m` for `m ≡ 3 (mod 4)` and `d_K = −4m` otherwise. -/
def discOf (m f : ℕ) : ℤ := if m % 4 = 3 then -((f : ℤ) ^ 2 * m) else -(4 * (f : ℤ) ^ 2 * m)

/-- **Leaf SHIMURA-PIC (main theorem of complex multiplication for Heegner points of `X₀(32)`,
Gross's form).** Let `K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K` the order of discriminant `D`,
`H_O` its ring class field, and `e : Kˢ → ℚ̄` an embedding inducing on `K` the normalized complex
embedding `√−m ↦ i√m` (through cm-points' `ιC : ℚ̄ → ℂ`). Let `J` be an ideal of `𝓞_K` prime to
`f`, and `ρ ∈ Gal(ℚ̄/ℚ)` an automorphism acting on `e(H_O)` as the Artin symbol of the class of
`J ∩ O`. Then for Heegner forms `Q, Q'` of level 32 and discriminant `D` whose pairs of lattices
satisfy `κ(J ∩ O)·(⟨1,τ_{Q'}⟩, ⟨1/32,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)` for one `c ∈ ℂ`
(i.e. `(L', L'_N) = c·(J∩O)⁻¹(L, L_N)`), `ρ` maps the Heegner point of `Q` to that of `Q'`:
`Art(𝔟)(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔟⁻¹𝔞])`.

Sources (refereed; theorem numbers UNVERIFIED, from memory, no network on this host):
the main theorem of complex multiplication, Shimura, *Introduction to the arithmetic theory of
automorphic functions* (1971), Thm. 5.4 (`E^{[s,K]} ≅ ℂ/s⁻¹𝔞`, with the action on torsion
`f(t)^σ = f'(s⁻¹t)`, which gives the action on the cyclic subgroup `L_N/L`); Silverman, *Advanced
topics in the arithmetic of elliptic curves*, GTM 151, Thm. II.8.2; Gross, *Heegner points on
`X₀(N)`*, in *Modular forms* (Durham 1983), 1984, §3 (`σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`);
Cox, *Primes of the form x² + ny²*, Thm. 11.1 and Cor. 11.37 (the `j`-part). Normalization: the
idele `s` with `s_𝔭` a uniformizer has `[s, K] = ` arithmetic Frobenius (Tau Ceti's Artin map), so
`Art(J)` corresponds to `s⁻¹𝔞 = J⁻¹𝔞`. The theorem holds for every lattice pair (Shimura's form
needs no condition on the orders of `L` and `L_N`), so no Heegner condition `(f, 32) = 1` is
needed. It is stated through x0-32's eta-quotient model `X0.phiC` and cm-points' `ιC`, so it is
true because (and only if) that model is the `ℚ`-rational modular parametrization of `X₀(32)`
(x0-32's leaves `X0.X0AnalyticModel`; Shimura 1971 Ch. 6–7 for the canonical model). -/
def ShimuraReciprocityPic : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm 32 D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      galPt ρ (heegnerPt Q) = heegnerPt Q'

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraZn.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: `σ_{1+2ϖ}` fixes `z_n` (TYZ Corollary 3.9 / Theorem 3.6) from Shimura reciprocity

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

**Main result** (`tyzSigmaFixesZn_of`): cm-points' leaf `Package.TYZSigmaFixesZn` follows from the
textbook leaf `ShimuraReciprocityPic` (main theorem of CM for Heegner points of `X₀(32)`, Gross's
form; `ShimuraRecip.lean`) and x0-32's leaf `X0.EtaModelFricke` (`φ(−1/(32τ)) = T − φ(τ)`).
Every TYZ- and `X₀(32)`-specific step is proved here:

* `σ_{1+2ϖ}` is the Artin symbol of `𝔟 = (3 + 2√−n)𝓞_K ∩ O_{n,4}` (ring-class's `sigmaClass_eq`);
  `𝔟 = ℤ⟨6 + 4√−n, 3 − 4n + 8√−n⟩` (`idealMeetOrder_alpha`, via `𝓞_K = ℤ[√−n]`, `int_coords`);
* with `Q_n = [16(n+1), −8, 1]` (TYZ's form) and `Q'_n = [16(n+9), −8(2n+15), 4n+25]` (`tyzForm'`),
  `𝔟·(⟨1,τ_{Q'}⟩, ⟨1/32,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)` with
  `c = ((5n+9) − 2(n+3)√−n)/(n+9)` (`idealLat_alpha_mul`, `idealLat_alpha_mulN`; proved in
  `K = ℚ(√−n)`, `latK`, `latNK`, and transported by `κ`), so the leaf gives
  `σ_{1+2ϖ}(f₀(P_n)) = f₀(P'_n)`;
* `τ_{Q'} = N₀ τ_Q`, `N₀τ = (14τ − 1)/(32τ − 2) = S W S W τ` (`tau'_eq`), and
  `φ(N₀τ) = φ(τ) + (0,0)` (`phiC_N0`, from `φ(τ + 1/2) = −φ(τ)` and the Fricke leaf), so
  `σ_{1+2ϖ}(f₀(P_n)) = f₀(P_n) + (0,0)`;
* `σ_{1+2ϖ}` fixes `i` (`fixes_iQ_of_sigma`, from ring-class's `L_n(i) ⊆ H'_n`) and
  `[i](0,0) = (0,0)`, so `z_n = (1 − [i])f₀(P_n)` is fixed;
* the embedding `ℚ̄ ⊃ K` used by `ActsAsArtin4` is arbitrary; `exists_normalized_embed` passes to
  one inducing `√−n ↦ i√n` (conjugation inverts Artin symbols; `σ_{1+2ϖ}` has order 2).

The identity `φ(τ_{Q'}) = φ(τ_Q) + (0,0)` and the lattice identity were found and checked
numerically first (`scratch/tyz-cm/twist*.py`, `coeffs*.py`; 18 values of `n`, 37 digits).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

theorem sqrt_mul_self_C (m : ℕ) : (Real.sqrt m : ℂ) * Real.sqrt m = m := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg m)]; simp

/-- `i√m` as a root of `X² + m` in `ℂ`. -/
def kappaRoot (m : ℕ) : {u : ℂ // u * u = (-(m : ℚ)) • (1 : ℂ) + (0 : ℚ) • u} :=
  ⟨I * Real.sqrt m, by
    rw [show I * (Real.sqrt m : ℂ) * (I * Real.sqrt m) = (I * I) * (Real.sqrt m * Real.sqrt m) by ring,
      I_mul_I, sqrt_mul_self_C]
    simp [Rat.smul_def]⟩

/-- `κ` as a `ℚ`-algebra map. -/
def kappaAlg (m : ℕ) : QNeg m →ₐ[ℚ] ℂ := QuadraticAlgebra.lift (kappaRoot m)

theorem kappaAlg_apply (m : ℕ) (x : QNeg m) : kappaAlg m x = kappa m x := by
  simp [kappaAlg, kappa, kappaRoot, Rat.smul_def]

/-- `κ` as a `ℤ`-algebra map. -/
def kappaZ (m : ℕ) : QNeg m →ₐ[ℤ] ℂ := (kappaAlg m).restrictScalars ℤ

/-- `κ` as a `ℤ`-linear map. -/
def kappaLin (m : ℕ) : QNeg m →ₗ[ℤ] ℂ := (kappaZ m).toLinearMap

theorem kappaLin_apply (m : ℕ) (x : QNeg m) : kappaLin m x = kappa m x := kappaAlg_apply m x

/-! ### Integer coordinates in `𝓞_K` for `n ≡ 1 (mod 4)` squarefree -/

theorem int_coords {n : ℕ} [NeZero n] (hn : n % 4 = 1) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ u v : ℤ, (y : QNeg n).re = u ∧ (y : QNeg n).im = v := by
  obtain ⟨a, ha⟩ := exists_two_re y
  obtain ⟨b, hb⟩ := exists_two_re (y * sqrtNeg n)
  have hN := normZ_eq_re_im y
  set N := Algebra.norm ℤ y
  set r := (y : QNeg n).re
  set s := (y : QNeg n).im
  have hb' : 2 * (-(n : ℚ) * s) = b := by
    rw [← hb]; simp [coe_sqrtNeg, s]
  -- t = 2s, n t = -b
  have hnt : (n : ℚ) * (2 * s) = -b := by linarith
  have h4 : (a : ℚ) ^ 2 + n * (2 * s) ^ 2 = 4 * N := by
    rw [hN, ← ha]; ring
  have hdiv : (n : ℤ) ∣ b ^ 2 := by
    refine ⟨a ^ 2 * 0 + (4 * N - a ^ 2), ?_⟩
    have : (b : ℚ) ^ 2 = n * (4 * N - a ^ 2) := by
      have : (b : ℚ) ^ 2 = (n * (2 * s)) ^ 2 := by rw [hnt]; ring
      rw [this]; linear_combination (n : ℚ) * h4
    exact_mod_cast (by rw [this]; ring : (b : ℚ) ^ 2 = n * (a ^ 2 * 0 + (4 * N - a ^ 2)))
  have hsqZ : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hsq
  obtain ⟨t, ht⟩ := (hsqZ.dvd_pow_iff_dvd two_ne_zero).1 hdiv
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hs2 : 2 * s = -t := by
    have : (n : ℚ) * (2 * s) = n * (-t) := by rw [hnt, ht]; push_cast; ring
    exact mul_left_cancel₀ hn0 this
  have hZ : a ^ 2 + (n : ℤ) * t ^ 2 = 4 * N := by
    have : (a : ℚ) ^ 2 + n * t ^ 2 = 4 * N := by rw [← h4, hs2]; ring
    exact_mod_cast this
  have hn4 : (n : ℤ) % 4 = 1 := by exact_mod_cast hn
  have hat : 2 ∣ a ∧ 2 ∣ t := by
    have hm : ∀ x : ℤ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      intro x; rcases Int.emod_two_eq_zero_or_one x with h | h
      · left; obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h; ring_nf; omega
      · right; obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
        subst hk; ring_nf; omega
    have hpar : ∀ x : ℤ, x ^ 2 % 4 = 0 → 2 ∣ x := by
      intro x hx; by_contra h
      obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
      subst hk; ring_nf at hx; omega
    have e1 : ((n : ℤ) * t ^ 2) % 4 = (t ^ 2) % 4 := by
      rw [Int.mul_emod, hn4, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]
    have e2 : (a ^ 2 + (n : ℤ) * t ^ 2) % 4 = 0 := by rw [hZ]; simp
    rcases hm a with h1 | h1 <;> rcases hm t with h2 | h2
    · exact ⟨hpar a h1, hpar t h2⟩
    · omega
    · omega
    · omega
  obtain ⟨⟨a', rfl⟩, ⟨t', rfl⟩⟩ := hat
  refine ⟨a', -t', ?_, ?_⟩
  · have : 2 * r = 2 * a' := by rw [ha]; push_cast; ring
    linarith
  · have : 2 * s = 2 * (-t') := by rw [hs2]; push_cast; ring
    push_cast; linarith


/-! ### `𝔟 ∩ O_{n,4}` for `𝔟 = (3 + 2√−n)` -/

section Alpha
open QuadraticAlgebra
variable {n : ℕ} [NeZero n]

/-- `6 + 4√−n = 2α`. -/
def g0 (n : ℕ) : QNeg n := ⟨6, 4⟩
/-- `3 − 4n + 8√−n = α(1 + 2√−n)`. -/
def g1 (n : ℕ) : QNeg n := ⟨3 - 4 * n, 8⟩

theorem coeO_two : ((2 : 𝓞 (QNeg n)) : QNeg n) = 2 := rfl
theorem coeO_three : ((3 : 𝓞 (QNeg n)) : QNeg n) = 3 := rfl

theorem coe_alpha : ((alpha n : 𝓞 (QNeg n)) : QNeg n) = ⟨3, 2⟩ := by
  rw [alpha]; push_cast [coe_sqrtNeg, coeO_two, coeO_three]; ext <;> simp

theorem mem_O4_iff' (x : QNeg n) :
    x ∈ (conductorOrder (QNeg n) 4).toSubalgebra ↔ ∃ a : ℤ, ∃ y : 𝓞 (QNeg n), x = a + 4 * (y : QNeg n) := by
  rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra]; norm_num

theorem idealMeetOrder_alpha (hn : n % 4 = 1) (hsq : Squarefree n) :
    idealMeetOrder n 4 (Ideal.span {alpha n}) =
      (Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) : Set (QNeg n)) := by
  ext x
  simp only [idealMeetOrder, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair, mem_O4_iff']
  constructor
  · rintro ⟨⟨a, z, hz⟩, y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨u, v, hu, hv⟩ := int_coords hn hsq w
    obtain ⟨p, q, hp, hq⟩ := int_coords hn hsq z
    have him := congrArg QuadraticAlgebra.im hz
    push_cast [coe_alpha] at him
    simp only [im_mul, hu, hv, im_add, im_intCast, im_mul, hp, hq] at him
    simp at him
    have h4 : 2 * u + 3 * v = 4 * q := by
      have : (2 * u + 3 * v : ℚ) = 4 * q := by linarith
      exact_mod_cast this
    refine ⟨q - v, 2 * q - u - v, ?_⟩
    push_cast [coe_alpha]
    ext
    · simp [g0, g1, hu, hv]
      have : (2 * u + 3 * v : ℚ) = 4 * q := by exact_mod_cast h4
      linear_combination (2 * (n : ℚ) - 3) * this
    · simp [g0, g1, hu, hv]
      have : (2 * u + 3 * v : ℚ) = 4 * q := by exact_mod_cast h4
      linear_combination (-5 : ℚ) * this
  · rintro ⟨c, d, rfl⟩
    refine ⟨⟨6 * c + d * (3 - 4 * n), (c + 2 * d : ℤ) * sqrtNeg n, ?_⟩,
      (2 * c + d + 2 * d * sqrtNeg n : 𝓞 (QNeg n)) * alpha n,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
    · push_cast [coe_sqrtNeg, coeO_two]; ext <;> simp [g0, g1] <;> ring
    · push_cast [coe_sqrtNeg, coe_alpha, coeO_two]; ext <;> simp [g0, g1] <;> ring

end Alpha

/-! ### The lattice identity in `K` -/

section LatK
open QuadraticAlgebra Pointwise
variable {n : ℕ} [NeZero n]

/-- `τ_Q = (1 + √−n)/(4(n+1))` for TYZ's form `[16(n+1), −8, 1]`. -/
def tauK (n : ℕ) : QNeg n := ⟨1 / (4 * (n + 1)), 1 / (4 * (n + 1))⟩
/-- `τ_{Q'} = (2n + 15 + √−n)/(4(n+9))` for `Q' = [16(n+9), −8(2n+15), 4n+25]`. -/
def tauK' (n : ℕ) : QNeg n := ⟨(2 * n + 15) / (4 * (n + 9)), 1 / (4 * (n + 9))⟩
/-- `1/32 ∈ K`. -/
def oneN (n : ℕ) : QNeg n := ⟨1 / 32, 0⟩
omit [NeZero n] in
@[simp] theorem oneN_re : (oneN n).re = 1 / 32 := rfl
omit [NeZero n] in
@[simp] theorem oneN_im : (oneN n).im = 0 := rfl
/-- The homothety factor `c = ((5n+9) − 2(n+3)√−n)/(n+9)`. -/
def cK (n : ℕ) : QNeg n := ⟨(5 * n + 9) / (n + 9), -2 * (n + 3) / (n + 9)⟩

omit [NeZero n] in
theorem mem_span_mul_four {S T : Set (QNeg n)} (s₀ s₁ t₀ t₁ : QNeg n) (hs₀ : s₀ ∈ S) (hs₁ : s₁ ∈ S)
    (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) {x : QNeg n} (a b c d : ℤ)
    (h : x = a • (s₀ * t₀) + b • (s₀ * t₁) + c • (s₁ * t₀) + d • (s₁ * t₁)) :
    x ∈ Submodule.span ℤ (S * T) := by
  rw [h]
  have hm : ∀ {s t : QNeg n}, s ∈ S → t ∈ T → s * t ∈ Submodule.span ℤ (S * T) :=
    fun hs ht => Submodule.subset_span (Set.mul_mem_mul hs ht)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hm hs₀ ht₀)) (Submodule.smul_mem _ _ (hm hs₀ ht₁)))
    (Submodule.smul_mem _ _ (hm hs₁ ht₀))) (Submodule.smul_mem _ _ (hm hs₁ ht₁))

omit [NeZero n] in
theorem mem_span_pair_of {a b x : QNeg n} (p q : ℤ) (h : x = p • a + q • b) :
    x ∈ Submodule.span ℤ ({a, b} : Set (QNeg n)) :=
  Submodule.mem_span_pair.2 ⟨p, q, h.symm⟩

theorem latK (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) * Submodule.span ℤ {1, tauK' n} =
      Submodule.span ℤ {cK n * 1, cK n * tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h9 : (8 * (k : ℚ) + 5 + 9) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact mem_span_pair_of (-2) 32 (by ext <;> simp [g0, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-1) 14 (by ext <;> simp [g0, cK, tauK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-7) (-64 * k) (by ext <;> simp [g1, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-3) (-32 * k - 3)
        (by ext <;> simp [g1, cK, tauK, tauK'] <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact mem_span_mul_four (g0 _) (g1 _) 1 (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(112 * k + 70)) (256 * k + 160) (-32 * k - 3) (64 * k)
        (by ext <;> simp [g0, g1, cK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_mul_four (g0 _) (g1 _) 1 (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(8 * k + 5)) (16 * k + 10) 3 (-7)
        (by ext <;> simp [g0, g1, cK, tauK, tauK'] <;> field_simp <;> ring)

theorem latNK (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) * Submodule.span ℤ {oneN n, tauK' n} =
      Submodule.span ℤ {cK n * oneN n, cK n * tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h9 : (8 * (k : ℚ) + 5 + 9) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact mem_span_pair_of (-2) 1 (by ext <;> simp [g0, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-32) 14 (by ext <;> simp [g0, cK, tauK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-7) (-2 * k) (by ext <;> simp [g1, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-96) (-32 * k - 3)
        (by ext <;> simp [g1, cK, tauK, tauK'] <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact mem_span_mul_four (g0 _) (g1 _) (oneN _) (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(112 * k + 70)) (8 * k + 5) (-32 * k - 3) (2 * k)
        (by ext <;> simp [g0, g1, cK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_mul_four (g0 _) (g1 _) (oneN _) (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(8 * k + 5) * 32) ((8 * k + 5) * 2) 96 (-7)
        (by ext <;> simp [g0, g1, cK, tauK, tauK'] <;> field_simp <;> ring)

end LatK



section X0Id
open WeierstrassCurve.Affine

theorem curveAC_a₁ : X0.curveAC.a₁ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₃ : X0.curveAC.a₃ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem negY_AC (x y : ℂ) : X0.curveAC.toAffine.negY x y = -y := by
  rw [negY, curveAC_a₁, curveAC_a₃]; ring

/-- **`φ(τ + 1/2) = −φ(τ)`** (from x0-32's `xC_add_half`, `yC_add_half`). -/
theorem phiC_add_half (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 2) :
    X0.phiC τ' = -X0.phiC τ := by
  have hx : X0.xC τ' = X0.xC τ := by rw [h, X0.xC_add_half]
  have hy : X0.yC τ' = -X0.yC τ := by rw [h, X0.yC_add_half]
  unfold X0.phiC
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact (nonsingular_neg ..).2 hns
    rw [dite_eq_left hns, dite_eq_left hns', Point.neg_some, Point.some.injEq, negY_AC]
    exact ⟨hx, hy⟩
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact fun h' => hns ((nonsingular_neg ..).1 h')
    rw [dite_eq_right hns, dite_eq_right hns', neg_zero]

/-- `(0, 0) ∈ A(ℂ)`. -/
theorem nonsingular_00C : X0.curveAC.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h0 : X0.curveAC.a₂ = 0 ∧ X0.curveAC.a₆ = 0 := by
    simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  rw [h4, curveAC_a₁, curveAC_a₃, h0.1, h0.2]
  refine ⟨by norm_num, Or.inl ?_⟩
  norm_num

def pt00C : X0.PtAC := .some 0 0 nonsingular_00C

theorem ptTC_add_self : X0.ptTC + X0.ptTC = pt00C := by
  have hy : (-4 : ℂ) ≠ X0.curveAC.toAffine.negY 2 (-4) := by rw [negY_AC]; norm_num
  rw [X0.ptTC, Point.add_self_of_Y_ne hy, pt00C, Point.some.injEq]
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h2 : X0.curveAC.a₂ = 0 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have hs : X0.curveAC.toAffine.slope 2 2 (-4) (-4) = -2 := by
    rw [slope_of_Y_ne rfl hy]
    simp only [negY, curveAC_a₁, curveAC_a₃, h2, h4]; norm_num
  simp only [addX, addY, negAddY, negY, hs, curveAC_a₁, h2, curveAC_a₃]
  constructor <;> norm_num

theorem neg_pt00C : -pt00C = pt00C := by
  rw [pt00C, Point.neg_some, Point.some.injEq, negY_AC]; simp

/-- `τ ↦ −1/(32τ)` on `ℍ`. -/
def frickeH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-1 / (32 * (τ : ℂ)), by
    have h32 : (32 : ℂ) * τ = ((32 : ℕ) : ℂ) * τ := by norm_num
    have hm := X0.mul_mem_upperHalfPlaneSet (d := 32) (by norm_num) τ
    rw [← h32] at hm
    have := UpperHalfPlane.im_inv_neg_coe_pos ⟨_, hm⟩
    simpa [div_eq_mul_inv, neg_inv] using this⟩

/-- `τ ↦ τ + 1/2` on `ℍ`. -/
def halfH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 2, by
    show 0 < ((τ : ℂ) + 1 / 2).im
    simpa using τ.im_pos⟩

/-- **`φ(N₀τ) = φ(τ) + (0, 0)`** for `N₀ = S W S W`, `N₀τ = (14τ − 1)/(32τ − 2)`, from the Fricke
leaf `X0.EtaModelFricke` (`φ(Wτ) = T − φ(τ)`) and `φ(τ + 1/2) = −φ(τ)`; `2T = (0,0)`. -/
theorem phiC_N0 (hF : X0.EtaModelFricke) (τ τ' : UpperHalfPlane)
    (h : (τ' : ℂ) = (14 * τ - 1) / (32 * τ - 2)) : X0.phiC τ' = X0.phiC τ + pt00C := by
  set τ₁ := frickeH τ
  set τ₂ := halfH τ₁
  set τ₃ := frickeH τ₂
  have hτ' : (τ' : ℂ) = (halfH τ₃ : ℂ) := by
    rw [h]
    show _ = -1 / (32 * ((-1 / (32 * (τ : ℂ))) + 1 / 2)) + 1 / 2
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hτ1 : (16 * (τ : ℂ) - 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact τ.im_pos.ne' this
    have hτ2 : (32 * (τ : ℂ) - 2) ≠ 0 := by
      intro h0; apply hτ1; linear_combination h0 / 2
    have hτ3 : (-2 + (τ : ℂ) * 32) ≠ 0 := by
      intro h0; apply hτ2; linear_combination h0
    field_simp
    ring_nf
    field_simp
    ring
  have e1 : X0.phiC τ₁ + X0.phiC τ = X0.ptTC := hF τ τ₁ rfl
  have e2 : X0.phiC τ₂ = -X0.phiC τ₁ := phiC_add_half τ₁ τ₂ rfl
  have e3 : X0.phiC τ₃ + X0.phiC τ₂ = X0.ptTC := hF τ₂ τ₃ rfl
  have e4 : X0.phiC τ' = -X0.phiC τ₃ := phiC_add_half τ₃ τ' hτ'
  rw [e4, eq_sub_of_add_eq e3, e2, eq_sub_of_add_eq e1]
  rw [← neg_pt00C, ← ptTC_add_self]
  abel

end X0Id

section Assembly
open QuadraticAlgebra Pointwise WeierstrassCurve.Affine

/-- **`Q'_n = [16(n+9), −8(2n+15), 4n+25]`**, a Heegner form of level 32 and discriminant `−64n`
(`n ≡ 5 mod 8`), with `τ_{Q'} = N₀ τ_{Q_n}` (`tau'_eq`) and lattice pair `𝔟⁻¹`-homothetic to that of
TYZ's form `Q_n` (`idealLat_alpha_mul`, `idealLat_alpha_mulN`). -/
def tyzForm' (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 16 * (n + 9)
  B := -8 * (2 * n + 15)
  C := 4 * n + 25
  A_pos := by positivity
  N_dvd := by
    have : (n : ℤ) % 8 = 5 := by exact_mod_cast hn
    omega
  disc := by ring
  D_neg := by
    have : (0 : ℤ) < n := by omega
    linarith
  primitive := by
    have hA : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        16 * ((n : ℤ) + 9) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_left ..)
    have hB : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        -8 * (2 * n + 15) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
    have hC : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        4 * n + 25 := Int.gcd_dvd_right ..
    have h1 : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        1 := by
      have e : (1 : ℤ) = -(n + 6) * (16 * (n + 9)) - 2 * (n + 6) * (-8 * (2 * n + 15)) +
          (-4 * n - 23) * (4 * n + 25) := by ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _))
        (dvd_mul_of_dvd_right hC _)
    exact Nat.dvd_one.mp (by exact_mod_cast h1)

theorem sqrt_64n (n : ℕ) : Real.sqrt (-(((-64 * n : ℤ)) : ℝ)) = 8 * Real.sqrt n := by
  rw [show -(((-64 * n : ℤ)) : ℝ) = 8 ^ 2 * n by push_cast; ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem tyzForm_tau (n : ℕ) (hn : n % 8 = 5) : (tyzForm n hn).tau = kappa n (tauK n) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [HeegnerForm.tau, cmPoint, tyzForm, kappa, tauK, sqrt_64n]
  push_cast
  field_simp
  ring

theorem tyzForm'_tau (n : ℕ) (hn : n % 8 = 5) : (tyzForm' n hn).tau = kappa n (tauK' n) := by
  have h9 : ((n : ℂ) + 9) ≠ 0 := by exact_mod_cast (show n + 9 ≠ 0 by omega)
  simp only [HeegnerForm.tau, cmPoint, tyzForm', kappa, tauK', sqrt_64n]
  push_cast
  field_simp
  ring

theorem tauK'_mul (n : ℕ) [NeZero n] : tauK' n * (32 * tauK n - 2) = 14 * tauK n - 1 := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h9 : ((n : ℚ) + 9) ≠ 0 := by positivity
  ext <;> simp [tauK, tauK'] <;> field_simp <;> ring

theorem tau'_eq (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    ((tyzForm' n hn).tauH : ℂ) = (14 * ((tyzForm n hn).tauH : ℂ) - 1) / (32 * (tyzForm n hn).tauH - 2) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = kappaAlg n (tauK n) := by
    rw [kappaAlg_apply, ← tyzForm_tau n hn]; rfl
  have hτ' : ((tyzForm' n hn).tauH : ℂ) = kappaAlg n (tauK' n) := by
    rw [kappaAlg_apply, ← tyzForm'_tau n hn]; rfl
  have hne : (32 * ((tyzForm n hn).tauH : ℂ) - 2) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  rw [eq_div_iff hne, hτ', hτ]
  have := congrArg (kappaAlg n) (tauK'_mul n)
  simpa [map_ofNat] using this

theorem kappaLin_one (n : ℕ) : kappaLin n 1 = 1 := map_one (kappaZ n)

theorem kappa_oneN (n : ℕ) : kappaLin n (oneN n) = 1 / ((32 : ℕ) : ℂ) := by
  rw [kappaLin_apply, kappa]; simp

theorem lat_eq_map {D : ℤ} (Q : HeegnerForm 32 D) (n : ℕ) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.lat = (Submodule.span ℤ {1, t}).map (kappaLin n) := by
  rw [HeegnerForm.lat, Submodule.map_span, Set.image_pair, kappaLin_one, kappaLin_apply, ht]

theorem latN_eq_map {D : ℤ} (Q : HeegnerForm 32 D) (n : ℕ) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.latN = (Submodule.span ℤ {oneN n, t}).map (kappaLin n) := by
  rw [HeegnerForm.latN, Submodule.map_span, Set.image_pair, kappa_oneN, kappaLin_apply, ht]

theorem map_mulLeft_span_pair (n : ℕ) (c a b : QNeg n) :
    ((Submodule.span ℤ {a, b}).map (kappaLin n)).map (LinearMap.mulLeft ℤ (kappa n c)) =
      (Submodule.span ℤ {c * a, c * b}).map (kappaLin n) := by
  simp only [Submodule.map_span, Set.image_pair, LinearMap.mulLeft_apply, kappaLin_apply]
  rw [← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply,
    map_mul, map_mul]

theorem idealLat_alpha (n : ℕ) [NeZero n] (hn : n % 4 = 1) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) = (Submodule.span ℤ {g0 n, g1 n}).map (kappaLin n) := by
  rw [idealLat, idealMeetOrder_alpha hn hsq, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
    Submodule.span_image, Submodule.span_eq]

theorem idealLat_alpha_mul (n : ℕ) [NeZero n] (hn : n % 8 = 5) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) * (tyzForm' n hn).lat =
      (tyzForm n hn).lat.map (LinearMap.mulLeft ℤ (kappa n (cK n))) := by
  rw [idealLat_alpha n (by omega) hsq, lat_eq_map _ n _ (tyzForm'_tau n hn),
    lat_eq_map _ n _ (tyzForm_tau n hn), map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul,
    latK (n / 8) (by omega)]

theorem idealLat_alpha_mulN (n : ℕ) [NeZero n] (hn : n % 8 = 5) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) * (tyzForm' n hn).latN =
      (tyzForm n hn).latN.map (LinearMap.mulLeft ℤ (kappa n (cK n))) := by
  rw [idealLat_alpha n (by omega) hsq, latN_eq_map _ n _ (tyzForm'_tau n hn),
    latN_eq_map _ n _ (tyzForm_tau n hn), map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul,
    latNK (n / 8) (by omega)]

end Assembly


section Main
open QuadraticAlgebra WeierstrassCurve.Affine Polynomial

theorem omega_sq' (n : ℕ) : (QuadraticAlgebra.omega : QNeg n) ^ 2 = -(n : QNeg n) := by
  ext <;> simp [sq]

/-- An automorphism of `ℚ̄` negating a square root of `−m`, `m > 0`. -/
theorem exists_galQ_neg {m : ℕ} (hm : 0 < m) {r : Qbar} (hr : r ^ 2 = -(m : Qbar)) :
    ∃ γ : GalQ, γ r = -r := by
  have hirr : Irreducible (X ^ 2 + C (m : ℚ)) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_add_C]; norm_num
    · intro x hx
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx
      have : (0 : ℚ) < x ^ 2 + m := by positivity
      linarith
  have hmon : (X ^ 2 + C (m : ℚ)).Monic := monic_X_pow_add_C _ two_ne_zero
  have hroot : aeval r (X ^ 2 + C (m : ℚ)) = 0 := by simp [hr]
  have hmin : minpoly ℚ r = X ^ 2 + C (m : ℚ) := (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  have halg : IsAlgebraic ℚ r := ⟨_, hmon.ne_zero, hroot⟩
  have hev : aeval (-r) (minpoly ℚ r) = 0 := by rw [hmin]; simp [hr]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root halg hev
  exact ⟨σ, by rw [← neg_neg r, map_neg, hσ, neg_neg]⟩

set_option maxRecDepth 10000 in
/-- **A normalized embedding for `ρ`**: if `ρ` acts on `H_{n,4}` as `σ_{1+2ϖ}` (through ring-class's
`embed n`), it acts as the Artin symbol of `[(3+2√−n) ∩ O_{n,4}]` through an embedding `e` with
`ιC(e(√−n)) = i√n` (`e = embed n` or `γ ∘ embed n`; `σ_{1+2ϖ}` has order 2, so conjugation, which
inverts Artin symbols, does not change it). -/
theorem exists_normalized_embed (n : ℕ) [NeZero n] {ρ : GalQ}
    (hρ : Package.ActsAsArtin4 ρ n (sigmaClass n)) :
    ∃ e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) ∧
      ∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4)
          ((conductorOrder (QNeg n) 4).picClass ⟨_, alphaIdeal_mem⟩) x) := by
  set r := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(n : Qbar) := by
    simp only [r, ← map_pow, omega_sq', map_neg, map_natCast]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : ιC r ^ 2 = (I * (Real.sqrt n : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, sqrt_mul_self_C]; simp
  have hcls : sigmaClass n = (O4 n).picClass ⟨_, alphaIdeal_mem⟩ := sigmaClass_eq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · refine ⟨embed n, h, fun x => ?_⟩
    have := hρ x
    rw [hcls] at this
    exact this
  · obtain ⟨γ, hγ⟩ := exists_galQ_neg hn0 hr
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0] at hr
      have : (n : Qbar) = 0 := by linear_combination hr
      exact NeZero.ne n (by exact_mod_cast this)
    have hγinv : γ⁻¹ r = -r := by
      apply γ.injective
      show γ (γ.symm r) = γ (-r)
      rw [AlgEquiv.apply_symm_apply, map_neg, hγ, neg_neg]
    have hne : γ⁻¹ r ≠ r := by
      rw [hγinv]; intro h'
      apply hr0
      have : (2 : Qbar) * r = 0 := by linear_combination -h'
      simpa using this
    have hconj := RingClassBridge.actsAsArtin4_conj (γ := γ⁻¹) hne hρ
    have hinv : (sigmaClass n)⁻¹ = sigmaClass n :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, sigmaClass_sq])
    rw [hinv, inv_inv, hcls] at hconj
    refine ⟨γ.toAlgHom.comp (embed n), ?_, fun x => ?_⟩
    · show ιC (γ r) = _
      rw [hγ, map_neg, h, neg_neg]
    · have := hconj x
      simp only [AlgEquiv.mul_apply] at this
      show ρ (γ (embed n x)) = γ (embed n _)
      rw [← this]
      show _ = γ (γ.symm (ρ (γ (embed n x))))
      rw [AlgEquiv.apply_symm_apply]

/-- `ρ` acting as `σ_{1+2ϖ}` fixes `i` (`i ∈ L_n(i) ⊆ H'_n`, ring-class's `Lni_le_Hprimebar`). -/
theorem fixes_iQ_of_sigma (n : ℕ) [NeZero n] (hn : n % 4 = 1) (hsq : Squarefree n) {ρ : GalQ}
    (hρ : Package.ActsAsArtin4 ρ n (sigmaClass n)) : ρ iQ = iQ := by
  have hi : iQ ∈ Hprimebar n := Lni_le_Hprimebar hn hsq (Package.iQ_mem_Lni n)
  rw [Hprimebar_eq_map] at hi
  obtain ⟨x, hx, hxi⟩ := hi
  have hx' : x ∈ Hprime n := hx
  rw [Hprime, IntermediateField.lift, IntermediateField.mem_map] at hx'
  obtain ⟨y, hy, rfl⟩ := hx'
  have hfix : artin4 n (sigmaClass n) y = y :=
    (IntermediateField.mem_fixedField_iff _ _).1 hy _ (Subgroup.mem_zpowers _)
  rw [← hxi]
  have := hρ y
  rw [hfix] at this
  exact this

theorem toC_pt00 : toC Package.pt00 = pt00C := by
  simp [toC, Package.pt00, pt00C, Point.map]

/-- **`TYZSigmaFixesZn` from the Shimura reciprocity leaf and x0-32's Fricke leaf.** -/
theorem tyzSigmaFixesZn_of (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke) :
    Package.TYZSigmaFixesZn := by
  intro n hn0 hn hsq ρ hρ
  have hn4 : n % 4 = 1 := by omega
  have hi := fixes_iQ_of_sigma n hn4 hsq hρ
  obtain ⟨e, he, hρe⟩ := exists_normalized_embed n hρ
  have hD : -64 * (n : ℤ) = discOf n 4 := by
    rw [discOf, ite_eq_right (by omega)]; push_cast; ring
  have hrec := hS n 4 hsq e he ⟨_, alphaIdeal_mem⟩ ρ hρe (-64 * n) hD (tyzForm n hn)
    (tyzForm' n hn) (kappa n (cK n)) (idealLat_alpha_mul n hn hsq) (idealLat_alpha_mulN n hn hsq)
  have hphi : X0.phiC (tyzForm' n hn).tauH = X0.phiC (tyzForm n hn).tauH + pt00C :=
    phiC_N0 hF _ _ (tau'_eq n hn)
  simp only [tyzZn, tyzHeegnerPt, hn, ↓reduceDIte]
  by_cases h : ∃ P : PtA, toC P = X0.phiC (tyzForm n hn).tauH
  · have h' : heegnerPt (tyzForm' n hn) = heegnerPt (tyzForm n hn) + Package.pt00 := by
      apply heegnerPt_eq
      rw [map_add, toC_heegnerPt _ h, toC_pt00, hphi]
    rw [map_sub, galPt_iPt ρ hi, hrec, h', iPt_add, Package.iPt_pt00]
    abel
  · have h0 : heegnerPt (tyzForm n hn) = 0 := by simp only [heegnerPt, h, ↓reduceDIte]
    rw [h0, Package.iPt_zero, sub_zero, galPt_zero]

end Main

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraField.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: the CM leaf `CM.CMFieldOfDefinition ringClassFieldD` from the main theorem of CM

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Main result: `cmFieldOfDefinition_of (hS : ShimuraReciprocityPic) :
CM.CMFieldOfDefinition RingClass.ringClassFieldD` — every Heegner point of discriminant `D` on
`X₀(32) = A` (through x0-32's `X0.phiC`) has coordinates in the ring class field of discriminant
`D`, given the textbook leaf `ShimuraReciprocityPic` (main theorem of complex multiplication in
Gross's form, `ShimuraRecip.lean`). Also `cmFieldTYZ_of_shimura`: the TYZ package leaf
`Package.CMFieldOfDefinitionTYZ`, through ring-class's bridge `cmFieldTYZ_of_ringClassD`.

Proof: the case `J = 𝓞_K` (trivial Picard class) of the leaf, with `ρ` any automorphism of `ℚ̄`
fixing `H_O`; the lattices `⟨1, τ_Q⟩` and `⟨1/32, τ_Q⟩` of every Heegner form of discriminant
`D = disc(O)` are stable under `κ(O)` (`kappa_order`: `κ(O) ⊆ ℤ + ℤ·Aτ_Q`, a parity computation
with the half-integral coordinates of `𝓞_K`), so `κ(O)·L = L` and the leaf gives
`ρ(P_Q) = P_Q`; infinite Galois theory (`ℚ̄^{Gal(ℚ̄/H)} = H`) finishes.
No Heegner condition `(f, 32) = 1` is used.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

section Coords
variable {m : ℕ} [NeZero m]

/-- **Half-integral coordinates in `𝓞_K`**, `K = ℚ(√−m)`, `m` squarefree: `2 re = a`, `2 im = t`
with `a, t ∈ ℤ` and `a² + m t² ≡ 0 (mod 4)` (`a² + m t² = 4 N(y)`). -/
theorem two_coords (hsq : Squarefree m) (y : 𝓞 (QNeg m)) :
    ∃ a t N : ℤ, 2 * (y : QNeg m).re = a ∧ 2 * (y : QNeg m).im = t ∧ a ^ 2 + m * t ^ 2 = 4 * N := by
  obtain ⟨a, ha⟩ := exists_two_re y
  obtain ⟨b, hb⟩ := exists_two_re (y * sqrtNeg m)
  have hN := normZ_eq_re_im y
  set N := Algebra.norm ℤ y
  set s := (y : QNeg m).im
  have hb' : 2 * (-(m : ℚ) * s) = b := by
    rw [← hb]; simp [coe_sqrtNeg, s]
  have hnt : (m : ℚ) * (2 * s) = -b := by linarith
  have h4 : (a : ℚ) ^ 2 + m * (2 * s) ^ 2 = 4 * N := by
    rw [hN, ← ha]; ring
  have hdiv : (m : ℤ) ∣ b ^ 2 := by
    refine ⟨4 * N - a ^ 2, ?_⟩
    have : (b : ℚ) ^ 2 = m * (4 * N - a ^ 2) := by
      have : (b : ℚ) ^ 2 = (m * (2 * s)) ^ 2 := by rw [hnt]; ring
      rw [this]; linear_combination (m : ℚ) * h4
    exact_mod_cast this
  have hsqZ : Squarefree (m : ℤ) := Int.squarefree_natCast.mpr hsq
  obtain ⟨t, ht⟩ := (hsqZ.dvd_pow_iff_dvd two_ne_zero).1 hdiv
  have hn0 : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hs2 : 2 * s = -t := by
    have : (m : ℚ) * (2 * s) = m * (-t) := by rw [hnt, ht]; push_cast; ring
    exact mul_left_cancel₀ hn0 this
  refine ⟨a, -t, N, ha, by rw [hs2]; push_cast; ring, ?_⟩
  have : (a : ℚ) ^ 2 + m * (-t : ℤ) ^ 2 = 4 * N := by rw [← h4, hs2]; push_cast; ring
  exact_mod_cast this

theorem sq_mod_four (x : ℤ) : x ^ 2 % 4 = 0 ∧ 2 ∣ x ∨ x ^ 2 % 4 = 1 ∧ ¬ 2 ∣ x := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · left; obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h
    refine ⟨?_, dvd_mul_right 2 k⟩; ring_nf; omega
  · right; obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    subst hk; refine ⟨by ring_nf; omega, by omega⟩

omit [NeZero m] in
/-- Parity of the half-coordinates: for `m ≡ 3 (mod 4)`, `a ≡ t (mod 2)`. -/
theorem parity_three {a t N : ℤ} (hm : (m : ℤ) % 4 = 3) (h : a ^ 2 + m * t ^ 2 = 4 * N) :
    (2 ∣ a ↔ 2 ∣ t) := by
  have e1 : ((m : ℤ) * t ^ 2) % 4 = (3 * t ^ 2) % 4 := by rw [Int.mul_emod, hm]; omega
  have e2 : (a ^ 2 + (m : ℤ) * t ^ 2) % 4 = 0 := by rw [h]; simp
  rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · exact ⟨fun _ => h2', fun _ => h1'⟩
  · omega
  · omega
  · exact ⟨fun h => absurd h h1', fun h => absurd h h2'⟩

omit [NeZero m] in
/-- For `m ≢ 3 (mod 4)` squarefree, `a` and `t` are even. -/
theorem parity_other {a t N : ℤ} (hsq : Squarefree m) (hm : ¬ (m : ℤ) % 4 = 3)
    (h : a ^ 2 + m * t ^ 2 = 4 * N) : 2 ∣ a ∧ 2 ∣ t := by
  have hm0 : ¬ (m : ℤ) % 4 = 0 := by
    intro h0
    have h4 : (2 : ℕ) * 2 ∣ m := by
      have : (4 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero h0
      exact_mod_cast this
    exact absurd (hsq 2 h4) (by decide)
  have hm12 : (m : ℤ) % 4 = 1 ∨ (m : ℤ) % 4 = 2 := by omega
  have e2 : (a ^ 2 + (m : ℤ) * t ^ 2) % 4 = 0 := by rw [h]; simp
  rcases hm12 with hm1 | hm2
  · have e1 : ((m : ℤ) * t ^ 2) % 4 = (t ^ 2) % 4 := by
      rw [Int.mul_emod, hm1, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]
    rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact ⟨h1', h2'⟩
    all_goals omega
  · have e1 : ((m : ℤ) * t ^ 2) % 4 = (2 * t ^ 2) % 4 := by rw [Int.mul_emod, hm2]; omega
    rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact ⟨h1', h2'⟩
    all_goals omega

end Coords

section Order
variable {m f : ℕ} [NeZero m] [NeZero f]

theorem heegner_A_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (Q.A : ℂ) ≠ 0 := by
  exact_mod_cast Q.A_pos.ne'

/-- `s = i√(−D)` satisfies `s² = D`. -/
theorem sqD_sq {D : ℤ} (hD : D < 0) : (I * (Real.sqrt (-(D : ℝ)) : ℂ)) ^ 2 = D := by
  have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith
  rw [mul_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
  push_cast; ring

/-- `Aτ_Q² + Bτ_Q + C = 0`. -/
theorem heegner_tau_quad {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    (Q.A : ℂ) * Q.tau ^ 2 + Q.B * Q.tau + Q.C = 0 := by
  have hA := heegner_A_ne_zero Q
  have hs := sqD_sq Q.D_neg
  have hdisc : ((Q.B : ℂ)) ^ 2 - 4 * Q.A * Q.C = D := by exact_mod_cast Q.disc
  simp only [HeegnerForm.tau, cmPoint]
  field_simp
  linear_combination hs - hdisc

/-- `Aτ_Q = (−B + i√(−D))/2`. -/
theorem heegner_A_mul_tau {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    (Q.A : ℂ) * Q.tau = (-(Q.B : ℂ) + I * (Real.sqrt (-(D : ℝ)) : ℂ)) / 2 := by
  have hA := heegner_A_ne_zero Q
  simp only [HeegnerForm.tau, cmPoint]
  field_simp

theorem sqrt_neg_discOf (m f : ℕ) :
    Real.sqrt (-((discOf m f : ℤ) : ℝ)) =
      (if m % 4 = 3 then (f : ℝ) else 2 * f) * Real.sqrt m := by
  unfold discOf
  split_ifs with h
  · rw [show -(((-((f : ℤ) ^ 2 * m) : ℤ)) : ℝ) = (f : ℝ) ^ 2 * m by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · rw [show -(((-(4 * (f : ℤ) ^ 2 * m) : ℤ)) : ℝ) = (2 * f : ℝ) ^ 2 * m by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **`κ(O) ⊆ ℤ + ℤ·Aτ_Q`** for a form `Q` of discriminant `D = disc(O)`, `O = ℤ + f𝓞_K`. -/
theorem kappa_order (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∃ u v : ℤ, kappa m o = u + v * ((Q.A : ℂ) * Q.tau) := by
  rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra] at ho
  obtain ⟨a, y, rfl⟩ := ho
  obtain ⟨a', t, Nn, ha, ht, hN⟩ := two_coords hsq y
  have hk : kappa m ((a : QNeg m) + f * (y : QNeg m)) =
      a + f * (((a' : ℂ) / 2) + ((t : ℂ) / 2) * (I * Real.sqrt m)) := by
    rw [← kappaAlg_apply, map_add, map_mul, map_intCast, map_natCast, kappaAlg_apply, kappa,
      show (y : QNeg m).re = (a' : ℚ) / 2 by linarith, show (y : QNeg m).im = (t : ℚ) / 2 by linarith]
    push_cast; ring
  have hsD : Real.sqrt (-(D : ℝ)) = (if m % 4 = 3 then (f : ℝ) else 2 * f) * Real.sqrt m := by
    rw [hD, sqrt_neg_discOf]
  rw [hk, heegner_A_mul_tau Q, hsD]
  have hdisc : Q.B ^ 2 - 4 * Q.A * Q.C = discOf m f := Q.disc.trans hD
  by_cases h3 : m % 4 = 3
  · simp only [h3, ite_true]
    have hm3 : (m : ℤ) % 4 = 3 := by exact_mod_cast h3
    have hpar := parity_three hm3 hN
    -- f ≡ B (mod 2)
    have hfB : 2 ∣ (f : ℤ) * a' + t * Q.B := by
      unfold discOf at hdisc; rw [if_pos h3] at hdisc
      have hBf : 2 ∣ (Q.B : ℤ) + f := by
        have h2 : (2 : ℤ) ∣ Q.B ^ 2 + (f : ℤ) ^ 2 * m := ⟨2 * Q.A * Q.C, by linear_combination hdisc⟩
        rcases Int.emod_two_eq_zero_or_one Q.B with hB | hB <;>
          rcases Int.emod_two_eq_zero_or_one (f : ℤ) with hf | hf
        · omega
        · exfalso
          obtain ⟨b, hb⟩ : ∃ b, Q.B = 2 * b := ⟨Q.B / 2, by omega⟩
          obtain ⟨c, hc⟩ : ∃ c, (f : ℤ) = 2 * c + 1 := ⟨f / 2, by omega⟩
          obtain ⟨e, he⟩ : ∃ e, (m : ℤ) = 4 * e + 3 := ⟨m / 4, by omega⟩
          rw [hb, hc, he] at h2
          obtain ⟨w, hw⟩ := h2
          have : (2 : ℤ) * (w - 2 * b ^ 2 - (2 * c ^ 2 + 2 * c) * (4 * e + 3) - 2 * e - 1) = 1 := by
            linear_combination (-1 : ℤ) * hw
          omega
        · exfalso
          obtain ⟨b, hb⟩ : ∃ b, Q.B = 2 * b + 1 := ⟨Q.B / 2, by omega⟩
          obtain ⟨c, hc⟩ : ∃ c, (f : ℤ) = 2 * c := ⟨f / 2, by omega⟩
          rw [hb, hc] at h2
          obtain ⟨w, hw⟩ := h2
          have : (2 : ℤ) * (2 * b ^ 2 + 2 * b + 2 * c ^ 2 * m - w) = -1 := by linear_combination hw
          omega
        · omega
      by_cases ha2 : 2 ∣ a'
      · obtain ⟨a'', rfl⟩ := ha2
        obtain ⟨t'', rfl⟩ := hpar.1 ⟨a'', rfl⟩
        exact ⟨f * a'' + t'' * Q.B, by ring⟩
      · have ht2 : ¬ 2 ∣ t := fun h => ha2 (hpar.2 h)
        obtain ⟨a'', ha''⟩ : ∃ a'', a' = 2 * a'' + 1 := ⟨a' / 2, by omega⟩
        obtain ⟨t'', ht''⟩ : ∃ t'', t = 2 * t'' + 1 := ⟨t / 2, by omega⟩
        obtain ⟨g, hg⟩ := hBf
        subst ha'' ht''
        exact ⟨f * a'' + t'' * Q.B + g, by linear_combination hg⟩
    obtain ⟨k, hk⟩ := hfB
    refine ⟨a + k, t, ?_⟩
    have hk' : ((f : ℂ) * a' + t * Q.B) = 2 * k := by exact_mod_cast hk
    push_cast
    linear_combination (1 / 2 : ℂ) * hk'
  · simp only [h3, ite_false]
    have hm3 : ¬ (m : ℤ) % 4 = 3 := by exact_mod_cast h3
    obtain ⟨⟨a'', rfl⟩, ⟨t'', rfl⟩⟩ := parity_other hsq hm3 hN
    have hB : 2 ∣ Q.B := by
      unfold discOf at hdisc; rw [if_neg h3] at hdisc
      have : (Q.B : ℤ) ^ 2 = 4 * (Q.A * Q.C - f ^ 2 * m) := by linear_combination hdisc
      have h4 : (2 : ℤ) ∣ Q.B ^ 2 := ⟨2 * (Q.A * Q.C - f ^ 2 * m), by rw [this]; ring⟩
      exact Int.prime_two.dvd_of_dvd_pow h4
    obtain ⟨b, hb⟩ := hB
    refine ⟨a + f * a'' + t'' * b, t'', ?_⟩
    have hb' : (Q.B : ℂ) = 2 * b := by exact_mod_cast hb
    rw [hb']
    push_cast
    ring

/-- **`κ(O)·⟨1, τ_Q⟩ ⊆ ⟨1, τ_Q⟩`.** -/
theorem kappa_mul_mem_lat (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ}
    (Q : HeegnerForm N D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.lat, kappa m o * x ∈ Q.lat := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  have h1 : kappa m o * 1 ∈ Q.lat := by
    rw [mul_one, huv, HeegnerForm.lat]
    exact Submodule.mem_span_pair.2 ⟨u, v * Q.A, by push_cast; simp [zsmul_eq_mul]; ring⟩
  have hτ : kappa m o * Q.tau ∈ Q.lat := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.lat]
    refine Submodule.mem_span_pair.2 ⟨-(v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.lat] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

/-- **`κ(O)·⟨1/32, τ_Q⟩ ⊆ ⟨1/32, τ_Q⟩`** (uses `32 ∣ A`). -/
theorem kappa_mul_mem_latN (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f)
    (Q : HeegnerForm 32 D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.latN, kappa m o * x ∈ Q.latN := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  obtain ⟨A', hA'⟩ := Q.N_dvd
  have hA'C : (Q.A : ℂ) = 32 * A' := by exact_mod_cast hA'
  have h1 : kappa m o * (1 / ((32 : ℕ) : ℂ)) ∈ Q.latN := by
    rw [huv, HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨u, v * A', ?_⟩
    simp only [zsmul_eq_mul]
    rw [hA'C]
    push_cast
    ring
  have hτ : kappa m o * Q.tau ∈ Q.latN := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨-(32 * v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.latN] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

theorem one_mem_idealMeetOrder : (1 : QNeg m) ∈ idealMeetOrder m f ⊤ :=
  ⟨Subalgebra.one_mem _, 1, Submodule.mem_top, by simp⟩

/-- `κ(⊤ ∩ O)·L = L` for a lattice `L` stable under `κ(O)`. -/
theorem idealLat_top_mul {L : Submodule ℤ ℂ}
    (hL : ∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L, kappa m o * x ∈ L) :
    idealLat m f ⊤ * L = L := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro a ha x hx
    rw [idealLat] at ha
    induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨o, ho, rfl⟩ := hz
      exact hL o ho.1 x hx
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [add_mul]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hz
  · intro x hx
    have h1 : (1 : ℂ) ∈ idealLat m f ⊤ := by
      have : kappa m 1 = 1 := by simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      rw [← this]
      exact Submodule.subset_span ⟨1, one_mem_idealMeetOrder, rfl⟩
    simpa using Submodule.mul_mem_mul h1 hx

end Order

section FieldOfDefinition
open Polynomial

theorem exists_normalized_embed_any (m : ℕ) [NeZero m] :
    ∃ e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) := by
  set r := embed m (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(m : Qbar) := by
    simp only [r, ← map_pow, omega_sq', map_neg, map_natCast]
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hC : ιC r ^ 2 = (I * (Real.sqrt m : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, sqrt_mul_self_C]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · exact ⟨embed m, h⟩
  · obtain ⟨γ, hγ⟩ := exists_galQ_neg hm0 hr
    refine ⟨γ.toAlgHom.comp (embed m), ?_⟩
    show ιC (γ r) = _
    rw [hγ, map_neg, h, neg_neg]

theorem disc_mod_four {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : D % 4 = 0 ∨ D % 4 = 1 := by
  rw [← Q.disc, show 4 * Q.A * Q.C = 4 * (Q.A * Q.C) by ring]
  rcases sq_mod_four Q.B with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- **`CM.CMFieldOfDefinition ringClassFieldD` from the Shimura reciprocity leaf**: the case
`J = 𝓞_K` (trivial class, `ρ` fixing `H_O`) of `ShimuraReciprocityPic`, with `κ(O)·L = L` for the
lattices of every Heegner form (`kappa_order`), and infinite Galois theory (`ℚ̄^{Gal(ℚ̄/H)} = H`). -/
theorem cmFieldOfDefinition_of (hS : ShimuraReciprocityPic) : CMFieldOfDefinition ringClassFieldD := by
  intro D Q
  have hDneg := Q.D_neg
  have h4 := disc_mod_four Q
  obtain ⟨b, hb, hsq⟩ := sqfPart_spec D.natAbs
  have hspec := condD_spec h4 hDneg
  have hDa : (D.natAbs : ℤ) = -D := by omega
  have hm0 : sqfPart D.natAbs ≠ 0 := fun h => by rw [h, mul_zero] at hb; omega
  have hf0 : condD D ≠ 0 := by
    intro h; rw [h] at hspec; split_ifs at hspec <;> simp at hspec <;> omega
  have : NeZero (sqfPart D.natAbs) := ⟨hm0⟩
  have : NeZero (condD D) := ⟨hf0⟩
  set m := sqfPart D.natAbs with hm
  set f := condD D with hf
  have hD : D = discOf m f := by
    unfold discOf
    split_ifs at hspec ⊢ with h3
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
  have hK : ringClassFieldD D = ringClassFieldBar m f := by rw [ringClassFieldD, if_pos hDneg]
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  have hfix : ∀ ρ ∈ (ringClassFieldD D).fixingSubgroup, galPt ρ (heegnerPt Q) = heegnerPt Q := by
    intro ρ hρ
    have hρe : ∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass 1) x) := by
      intro x
      rw [map_one, map_one, AlgEquiv.one_apply]
      have hx : e x ∈ ringClassFieldD D := by
        rw [hK, ← ringClassFieldBar_eq_map m f e]
        exact ⟨x, x.2, rfl⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ _ hx
    have hone : ((1 : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
        Ideal (𝓞 (QNeg m))) = ⊤ := by
      rw [OneMemClass.coe_one, Ideal.one_eq_top]
    have hmul : LinearMap.mulLeft ℤ (1 : ℂ) = LinearMap.id := by ext; simp
    refine hS m f hsq e he 1 ρ hρe D hD Q Q 1 ?_ ?_
    · rw [hone, hmul, Submodule.map_id]
      exact idealLat_top_mul (fun o ho => kappa_mul_mem_lat hsq hD Q ho)
    · rw [hone, hmul, Submodule.map_id]
      exact idealLat_top_mul (fun o ho => kappa_mul_mem_latN hsq hD Q ho)
  have hmem : ∀ x : Qbar, (∀ ρ ∈ (ringClassFieldD D).fixingSubgroup, ρ x = x) →
      x ∈ ringClassFieldD D := by
    intro x hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup (ringClassFieldD D)]
    exact fun ρ => hx ρ.1 ρ.2
  rw [mem_ptsOver_iff]
  rcases hP : heegnerPt Q with _ | ⟨x, y, h⟩
  · trivial
  · refine ⟨hmem x fun ρ hρ => ?_, hmem y fun ρ hρ => ?_⟩
    · have := hfix ρ hρ
      rw [hP] at this
      obtain ⟨h', hh'⟩ := galPt_some ρ h
      rw [hh', WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.1
    · have := hfix ρ hρ
      rw [hP] at this
      obtain ⟨h', hh'⟩ := galPt_some ρ h
      rw [hh', WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.2

end FieldOfDefinition

/-- **The TYZ package leaf `Package.CMFieldOfDefinitionTYZ` from the main theorem of CM**
(through ring-class's `cmFieldTYZ_of_ringClassD`). -/
theorem cmFieldTYZ_of_shimura (hS : ShimuraReciprocityPic) :
    ZInQ.Contrib.TYZGenus.Package.CMFieldOfDefinitionTYZ :=
  RingClassBridge.cmFieldTYZ_of_ringClassD (cmFieldOfDefinition_of hS)

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **Reading A of TYZ Theorem 3.5 with both CM leaves replaced by the main theorem of CM**:
from the three `𝓛`-leaves, `ShimuraReciprocityPic` (main theorem of CM, Gross's form), x0-32's
leaf `X0.EtaModelFricke`, TYZ Lemma 3.18 (literal) and the bundled `GenusPointLeafCM`
(`CMFieldOfDefinition ringClassFieldD` by `cmFieldOfDefinition_of`, `TYZSigmaFixesZn` by
`tyzSigmaFixesZn_of` of `ShimuraZn.lean`). -/
theorem tyzThm35ReadingA_of_shimura (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke)
    (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29 (cmFieldOfDefinition_of hS)
    (tyzSigmaFixesZn_of hS hF) h318 hG

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: Shimura reciprocity for modular functions on `Γ₀(N)` (the leaf) and its `X₀(32)` instance

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

`ShimuraRecip.lean` states the main theorem of complex multiplication for Heegner points of
`X₀(32)` in Gross's form (`ShimuraReciprocityPic`) directly over x0-32's eta-quotient
parametrization `X0.phiC`. This file separates the general theorem from the `X₀(32)`-specific
input:

* `IsRatModFn N g`: `g : ℍ → ℂ` is a modular function for `Γ₀(N)`, holomorphic on `ℍ`,
  meromorphic at every cusp, with rational `q`-expansion at `∞`, i.e. an element of `ℚ(X₀(N))`
  with no poles on `ℍ`;
* the leaf `ShimuraReciprocityModFn` (Gross's form of the main theorem of CM for the values of
  such functions at Heegner points of level `N`); it does not mention the eta model;
* `shimuraReciprocityPic_of`: `ShimuraReciprocityPic` from the leaf and
  `IsRatModFn 32 x`, `IsRatModFn 32 y` for x0-32's coordinate functions;
* `isRatModFn_xC_of`, `isRatModFn_yC_of`: those two facts from x0-32's leaf
  `X0.EtaModelInvariant` (`Γ₀(32)`-invariance), the `q`-expansion facts `XQExpRational`,
  `YQExpRational` and the cusp-growth fact `EtaCuspGrowth` (proved or reduced in later files).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- **`g : ℍ → ℂ` is an element of `ℚ(X₀(N))` without poles on `ℍ`**: `g` is invariant under
`Γ₀(N)`; at every cusp `γ∞` (`γ ∈ SL₂(ℤ)`) it has at most a pole (`g(γτ) = O(e^{2πk Im τ})` as
`Im τ → ∞`); and its `q`-expansion at `∞` is a Laurent series in `q = e^{2πiτ}` with rational
coefficients converging on all of `ℍ` (`q^k g(τ) = Σ_{n ≥ 0} a_n qⁿ`, `a_n ∈ ℚ`), which also makes
`g` holomorphic on `ℍ`. By the `q`-expansion principle these are exactly the functions of
`ℚ(X₀(N)) = ℚ(j, j_N)` that are regular on `ℍ` (Shimura 1971, Prop. 6.9 and Thm. 6.23 for the
rational structure; Diamond–Shurman, *A first course in modular forms*, §7.5–7.7; UNVERIFIED
numbers). -/
def IsRatModFn (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ), ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ k * g τ)

/-- **Leaf SHIMURA-MODFN (main theorem of complex multiplication for the values of modular
functions on `X₀(N)` at Heegner points; Gross's form).** Let `g ∈ ℚ(X₀(N))` be regular on `ℍ`
(`IsRatModFn N g`). Let `K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K` the order of discriminant
`D`, `H_O` its ring class field, `e : Kˢ → ℚ̄` inducing on `K` the normalized embedding
`√−m ↦ i√m` (through cm-points' `ιC : ℚ̄ → ℂ`), `J` an ideal of `𝓞_K` prime to `f`, and
`ρ ∈ Gal(ℚ̄/ℚ)` acting on `e(H_O)` as the Artin symbol of the class of `J ∩ O`. For Heegner forms
`Q, Q'` of level `N` and discriminant `D` with
`κ(J ∩ O)·(⟨1,τ_{Q'}⟩, ⟨1/N,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/N,τ_Q⟩)` for one `c ∈ ℂ`, the values
`g(τ_Q)`, `g(τ_{Q'})` are algebraic and `ρ` maps the first to the second.

Content: `τ_Q` is the point `(ℂ/L, L_N/L)` of `X₀(N)`, `L = ⟨1, τ_Q⟩`, `L_N = ⟨1/N, τ_Q⟩`. By the
main theorem of CM (Shimura 1971, Thm. 5.4; Silverman, *Advanced topics*, GTM 151, Thm. II.8.2),
for `σ ∈ Aut(ℂ)` extending `ρ`, `(ℂ/L, L_N/L)^σ ≅ (ℂ/𝔟⁻¹L, 𝔟⁻¹L_N/𝔟⁻¹L)`, `𝔟 = J ∩ O` (the idele
`s` of `J` has `[s, K] = Art(J)` and `s⁻¹L = 𝔟⁻¹L`, `s⁻¹L_N = 𝔟⁻¹L_N`, since `J` is prime to the
conductor); the right side is `τ_{Q'}`. Since `X₀(N)_ℚ` (the model with function field the
functions with rational `q`-expansion) is the coarse moduli space of pairs `(E, C)` (Shimura 1971,
§6.7 and Thm. 6.23; Deligne–Rapoport; Diamond–Shurman, Ch. 7; UNVERIFIED numbers),
`σ(g(x)) = g(σ(x))` for `g ∈ ℚ(X₀(N))` regular at `x`. Gross, *Heegner points on `X₀(N)`*, in
*Modular forms* (Durham 1983), 1984, §3, states the combination as
`σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`. Refereed (textbook / survey); theorem numbers UNVERIFIED
(from memory, no network on this host). Normalization: Tau Ceti's Artin map sends the class of a
prime to the arithmetic Frobenius, and `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)` (Cox, *Primes of the form
x² + ny²*, Cor. 11.37, UNVERIFIED). No Heegner condition `(f, N) = 1` or `gcd(A/N, B, NC) = 1` is
needed. -/
def ShimuraReciprocityModFn : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

/-! ## From the leaf to `ShimuraReciprocityPic` -/

section Pic
open WeierstrassCurve.Affine

theorem nonsingular_iff_C {a b : Qbar} :
    X0.curveAC.toAffine.Nonsingular (ιC a) (ιC b) ↔ curveAbar.toAffine.Nonsingular a b :=
  baseChange_nonsingular (W := curveA) (f := ιCA) ιCA.injective a b

theorem nonsingular_iff_gal (ρ : GalQ) {a b : Qbar} :
    curveAbar.toAffine.Nonsingular (ρ a) (ρ b) ↔ curveAbar.toAffine.Nonsingular a b :=
  baseChange_nonsingular (W := curveA) (f := ρ.toAlgHom) ρ.injective a b

open Classical in
/-- **The Heegner point from algebraic preimages of its coordinates.** -/
theorem heegnerPt_of_alg {D : ℤ} (Q : HeegnerForm 32 D) {a b : Qbar}
    (ha : ιC a = X0.xC Q.tauH) (hb : ιC b = X0.yC Q.tauH) :
    heegnerPt Q = if h : curveAbar.toAffine.Nonsingular a b then .some a b h else 0 := by
  split_ifs with h
  · apply heegnerPt_eq
    have h' : X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact nonsingular_iff_C.2 h
    simp only [toC, X0.phiC, h', ↓reduceDIte]
    simp only [Point.map_some, Point.some.injEq]
    exact ⟨ha, hb⟩
  · apply heegnerPt_eq
    have h' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact fun h'' => h (nonsingular_iff_C.1 h'')
    simp only [X0.phiC, h', ↓reduceDIte, map_zero]

/-- **`ShimuraReciprocityPic` from the general leaf and the rationality of `x, y`.** -/
theorem shimuraReciprocityPic_of (hS : ShimuraReciprocityModFn)
    (hx : IsRatModFn 32 fun τ => X0.xC τ) (hy : IsRatModFn 32 fun τ => X0.yC τ) :
    ShimuraReciprocityPic := by
  intro m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨a, a', ha, ha', haa⟩ := hS 32 _ hx m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨b, b', hb, hb', hbb⟩ := hS 32 _ hy m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  rw [heegnerPt_of_alg Q ha hb, heegnerPt_of_alg Q' ha' hb', ← haa, ← hbb]
  by_cases h : curveAbar.toAffine.Nonsingular a b
  · have h' : curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := (nonsingular_iff_gal ρ).2 h
    simp only [h, h', ↓reduceDIte]
    rfl
  · have h' : ¬ curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := fun h'' =>
      h ((nonsingular_iff_gal ρ).1 h'')
    simp only [h, h', ↓reduceDIte, map_zero]

end Pic

/-! ## The `X₀(32)`-specific input -/

/-- **`q`-expansion of `x` (rational).** `q²·x(τ) = Σ_{n ≥ 0} a_n qⁿ` on `ℍ` with `a_n ∈ ℚ`
(indeed `a_n ∈ ℤ`, `x = q⁻² + 2 + …`): `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2` and
`η(dτ) = q^{d/24}∏(1 − q^{dn})`, `(2·2 + 16 − 4 − 2·32)/24 = −2`. Elementary (glue). -/
def XQExpRational : Prop :=
  ∃ a : ℕ → ℚ, ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ 2 * X0.xC τ)

/-- **`q`-expansion of `y` (rational).** `q³·y(τ) = Σ_{n ≥ 0} b_n qⁿ` on `ℍ` with `b_n ∈ ℚ`
(`y = −q⁻³ + …`): `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)`, `(32 + 32 − 8 − 128)/24 = −3`.
Elementary (glue). -/
def YQExpRational : Prop :=
  ∃ b : ℕ → ℚ, ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (b n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ 3 * X0.yC τ)

/-- **Leaf X0-CUSPGROWTH (`x, y` are meromorphic at every cusp of `Γ₀(32)`).** For every
`γ ∈ SL₂(ℤ)`, `x(γτ)` and `y(γτ)` are `O(e^{2πk Im τ})` as `Im τ → ∞`, for some `k`.
Source: eta quotients are meromorphic at all cusps, with Ligozat's order formula
`ord_{c/d} = (N/24)·Σ_δ gcd(d,δ)² r_δ / (gcd(d, N/d)·d·δ)` (Ligozat 1975, op. cit.; Ono, *The web
of modularity*, CBMS 102, Thm. 1.65; UNVERIFIED numbers); x0-32 VERIFIED the orders
(poles only at `∞`). Follows from `|η(γw)| = |cw + d|^{1/2}|η(w)|` (`γ ∈ SL₂(ℤ)`) and the product
expansion. Textbook (refereed). -/
def EtaCuspGrowth : Prop :=
  ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ k : ℕ,
    (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[UpperHalfPlane.atImInfty] (fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
    (fun τ : UpperHalfPlane => X0.yC (γ • τ : UpperHalfPlane)) =O[UpperHalfPlane.atImInfty] (fun τ => Real.exp (2 * Real.pi * k * τ.im))

theorem isRatModFn_xC_of (hI : X0.EtaModelInvariant) (hG : EtaCuspGrowth) (hq : XQExpRational) :
    IsRatModFn 32 fun τ => X0.xC τ := by
  refine ⟨fun γ hγ τ => (hI γ hγ τ).1, fun γ => ?_, ⟨2, hq⟩⟩
  obtain ⟨k, hk, -⟩ := hG γ
  exact ⟨k, hk⟩

theorem isRatModFn_yC_of (hI : X0.EtaModelInvariant) (hG : EtaCuspGrowth) (hq : YQExpRational) :
    IsRatModFn 32 fun τ => X0.yC τ := by
  refine ⟨fun γ hγ τ => (hI γ hγ τ).2, fun γ => ?_, ⟨3, hq⟩⟩
  obtain ⟨k, -, hk⟩ := hG γ
  exact ⟨k, hk⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))`**, x0-32's
`Γ₀(32)`-invariance leaf, cusp growth and the rational `q`-expansions of `x, y`. -/
theorem cmFieldOfDefinition_of_modFn (hS : ShimuraReciprocityModFn) (hI : X0.EtaModelInvariant)
    (hG : EtaCuspGrowth) (hx : XQExpRational) (hy : YQExpRational) :
    CMFieldOfDefinition ringClassFieldD :=
  cmFieldOfDefinition_of
    (shimuraReciprocityPic_of hS (isRatModFn_xC_of hI hG hx) (isRatModFn_yC_of hI hG hy))

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraQExp.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: the rational `q`-expansions of x0-32's coordinate functions `x, y` (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Proves `XQExpRational` and `YQExpRational` (`ShimuraModFn.lean`): `q²·x(τ)` and `q³·y(τ)` are
power series in `q = e^{2πiτ}` with rational coefficients, converging on all of `ℍ`.

Method: a function holomorphic on the unit disc whose Taylor coefficients at `0` are rational
has a rational `q`-expansion on the disc (`Complex.hasSum_taylorSeries_on_ball`). Functions with
rational iterated derivatives at `0` (`IsRatAt`) are closed under sums, products and inverses
(Leibniz rule); the products `p_d(q) = ∏ₙ (1 − q^{d(n+1)})` are `IsRatAt`, because the iterated
derivatives at `0` of the finite products are rational and stabilize, and they converge to those
of `p_d` (locally uniform convergence of the products, Weierstrass). Then
`q²x = p₂²p₁₆/(p₄p₃₂²) + 2q²` and `q³y = −p₈⁴p₁₆²/(p₄²p₃₂⁴)` (`η(dτ) = q^{d/24}p_d(q)`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology Metric

/-! ## Functions with rational Taylor coefficients at `0` -/

/-- `ℚ ⊆ ℂ` as a subfield. -/
abbrev Qc : Subfield ℂ := (algebraMap ℚ ℂ).fieldRange

/-- `F` is `C^∞` at `0` and its iterated derivatives at `0` are rational. -/
def IsRatAt (F : ℂ → ℂ) : Prop :=
  (∀ n : ℕ, ContDiffAt ℂ n F 0) ∧ ∀ n : ℕ, iteratedDeriv n F 0 ∈ Qc

theorem natCast_mem_Qc (n : ℕ) : (n : ℂ) ∈ Qc := ⟨n, by simp⟩

theorem ratCast_mem_Qc (r : ℚ) : (r : ℂ) ∈ Qc := ⟨r, by simp⟩

theorem isRatAt_const (r : ℚ) : IsRatAt fun _ => (r : ℂ) := by
  refine ⟨fun n => contDiffAt_const, fun n => ?_⟩
  rcases n with _ | n
  · simp
  · simp [iteratedDeriv_const]

theorem isRatAt_pow (k : ℕ) : IsRatAt fun q : ℂ => q ^ k := by
  refine ⟨fun n => (contDiff_id.pow k).contDiffAt, fun n => ?_⟩
  rw [iteratedDeriv_fun_pow_zero (𝕜 := ℂ)]
  split_ifs <;> exact natCast_mem_Qc _

theorem IsRatAt.add {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) :
    IsRatAt fun q => F q + G q := by
  refine ⟨fun n => (hF.1 n).add (hG.1 n), fun n => ?_⟩
  rw [iteratedDeriv_fun_add (hF.1 n) (hG.1 n)]
  exact Subfield.add_mem _ (hF.2 n) (hG.2 n)

theorem IsRatAt.mul {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) :
    IsRatAt fun q => F q * G q := by
  refine ⟨fun n => (hF.1 n).mul (hG.1 n), fun n => ?_⟩
  rw [iteratedDeriv_fun_mul (hF.1 n) (hG.1 n)]
  exact Subfield.sum_mem _ fun i _ =>
    Subfield.mul_mem _ (Subfield.mul_mem _ (natCast_mem_Qc _) (hF.2 i)) (hG.2 _)

theorem IsRatAt.neg {F : ℂ → ℂ} (hF : IsRatAt F) : IsRatAt fun q => -F q := by
  have := (isRatAt_const (-1)).mul hF
  simpa using this

theorem IsRatAt.pow {F : ℂ → ℂ} (hF : IsRatAt F) (k : ℕ) : IsRatAt fun q => F q ^ k := by
  induction k with
  | zero => simpa using isRatAt_const 1
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem IsRatAt.inv {F : ℂ → ℂ} (hF : IsRatAt F) (h0 : F 0 ≠ 0) :
    IsRatAt fun q => (F q)⁻¹ := by
  have hG : ∀ n : ℕ, ContDiffAt ℂ n (fun q => (F q)⁻¹) 0 := fun n => (hF.1 n).inv h0
  refine ⟨hG, fun n => ?_⟩
  -- `F · F⁻¹ = 1` near `0`
  have hev : (fun q => F q * (F q)⁻¹) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
    have hc : ContinuousAt F 0 := (hF.1 0).continuousAt
    filter_upwards [hc.eventually_ne h0] with q hq
    exact mul_inv_cancel₀ hq
  have hF0 : iteratedDeriv 0 F 0 ∈ Qc := hF.2 0
  rw [iteratedDeriv_zero] at hF0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [iteratedDeriv_zero]
      exact Subfield.inv_mem _ hF0
    · have hL := hev.iteratedDeriv_eq (n + 1)
      rw [iteratedDeriv_fun_mul (hF.1 _) (hG _), Finset.sum_range_succ'] at hL
      have h1 : iteratedDeriv (n + 1) (fun _ : ℂ => (1 : ℂ)) 0 = 0 := by
        rw [iteratedDeriv_succ']; simp
      rw [h1] at hL
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
        Nat.sub_zero] at hL
      -- `F 0 · G⁽ⁿ⁺¹⁾(0) = −Σ …`
      have hS : (∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℂ) *
          iteratedDeriv (i + 1) F 0 * iteratedDeriv (n + 1 - (i + 1)) (fun q => (F q)⁻¹) 0) ∈ Qc :=
        Subfield.sum_mem _ fun i hi =>
          Subfield.mul_mem _ (Subfield.mul_mem _ (natCast_mem_Qc _) (hF.2 _))
            (ih _ (by have := Finset.mem_range.1 hi; omega))
      set S := ∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℂ) *
          iteratedDeriv (i + 1) F 0 * iteratedDeriv (n + 1 - (i + 1)) (fun q => (F q)⁻¹) 0
      set G := iteratedDeriv (n + 1) (fun q => (F q)⁻¹) 0
      have h2 : F 0 * G = -S := by linear_combination hL
      have heq : G = -(F 0)⁻¹ * S := by
        calc G = (F 0)⁻¹ * (F 0 * G) := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
          _ = -(F 0)⁻¹ * S := by rw [h2]; ring
      rw [heq]
      exact Subfield.mul_mem _ (Subfield.neg_mem _ (Subfield.inv_mem _ hF0)) hS

theorem IsRatAt.div {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) (h0 : G 0 ≠ 0) :
    IsRatAt fun q => F q / G q := by
  simpa [div_eq_mul_inv] using hF.mul (hG.inv h0)

/-- Iterated derivatives of locally uniform limits of holomorphic functions converge. -/
theorem tendsto_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (n : ℕ) :
    ∀ {Fs : ℕ → ℂ → ℂ} {F : ℂ → ℂ}, TendstoLocallyUniformlyOn Fs F atTop U →
      (∀ M, DifferentiableOn ℂ (Fs M) U) →
      Tendsto (fun M => iteratedDeriv n (Fs M) z) atTop (𝓝 (iteratedDeriv n F z)) := by
  induction n with
  | zero =>
    intro Fs F h _
    simpa using h.tendsto_at hz
  | succ n ih =>
    intro Fs F h hd
    simp only [iteratedDeriv_succ']
    exact ih (h.deriv (Eventually.of_forall hd) hU) fun M => (hd M).deriv hU

/-- If `F_M → F` locally uniformly on the unit disc, the `F_M` are holomorphic and `IsRatAt`, and
for each `n` the `n`-th derivatives at `0` are eventually constant, then `F` has rational
iterated derivatives at `0`. -/
theorem iteratedDeriv_mem_of_limit {Fs : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn Fs F atTop (ball (0 : ℂ) 1))
    (hd : ∀ M, DifferentiableOn ℂ (Fs M) (ball (0 : ℂ) 1)) (hR : ∀ M, IsRatAt (Fs M))
    (hst : ∀ n, ∀ᶠ M in atTop, iteratedDeriv n (Fs M) 0 = iteratedDeriv n (Fs n) 0) (n : ℕ) :
    iteratedDeriv n F 0 ∈ Qc := by
  have ht := tendsto_iteratedDeriv isOpen_ball (mem_ball_self one_pos) n h hd
  have hc : Tendsto (fun M => iteratedDeriv n (Fs M) 0) atTop (𝓝 (iteratedDeriv n (Fs n) 0)) :=
    tendsto_const_nhds.congr' (by filter_upwards [hst n] with M hM; exact hM.symm)
  rw [tendsto_nhds_unique ht hc]
  exact (hR n).2 n

/-! ## The products `p_d(q) = ∏ₙ (1 − q^{d(n+1)})` -/

/-- The finite product `∏_{i < M} (1 − (q^d)^{i+1})`. -/
def finP (d M : ℕ) (q : ℂ) : ℂ := ∏ i ∈ Finset.range M, (1 - (q ^ d) ^ (i + 1))

/-- `p_d(q) = F(q^d)`, `F = X0.prodF`. -/
def pd (d : ℕ) (q : ℂ) : ℂ := X0.prodF (q ^ d)

theorem finP_succ (d M : ℕ) :
    finP d (M + 1) = fun q => finP d M q * ((1 : ℚ) + -(q ^ (d * (M + 1)))) := by
  funext q
  simp [finP, Finset.prod_range_succ, ← pow_mul, sub_eq_add_neg]

theorem isRatAt_finP (d M : ℕ) : IsRatAt (finP d M) := by
  induction M with
  | zero =>
    have : finP d 0 = fun _ => ((1 : ℚ) : ℂ) := by funext q; simp [finP]
    rw [this]; exact isRatAt_const 1
  | succ M ih =>
    rw [finP_succ]
    exact ih.mul ((isRatAt_const 1).add (isRatAt_pow _).neg)

theorem differentiable_finP (d M : ℕ) : Differentiable ℂ (finP d M) := by
  unfold finP
  fun_prop

/-- Stability: `(finP d (M+1))⁽ⁿ⁾(0) = (finP d M)⁽ⁿ⁾(0)` for `n < d(M+1)`. -/
theorem iteratedDeriv_finP_succ (d M n : ℕ) (hn : n < d * (M + 1)) :
    iteratedDeriv n (finP d (M + 1)) 0 = iteratedDeriv n (finP d M) 0 := by
  rw [finP_succ]
  have h1 := (isRatAt_finP d M).1 n
  have h2 : ContDiffAt ℂ n (fun q : ℂ => ((1 : ℚ) : ℂ) + -q ^ (d * (M + 1))) 0 :=
    (((isRatAt_const 1).add (isRatAt_pow _).neg).1 n)
  rw [iteratedDeriv_fun_mul h1 h2]
  have hk : d * (M + 1) ≠ 0 := by omega
  have hz : ∀ i : ℕ, i ≤ n → i ≠ 0 →
      iteratedDeriv i (fun q : ℂ => ((1 : ℚ) : ℂ) + -q ^ (d * (M + 1))) 0 = 0 := by
    intro i hi hi0
    rw [iteratedDeriv_fun_add contDiffAt_const ((contDiff_id.pow _).neg.contDiffAt),
      iteratedDeriv_fun_neg, iteratedDeriv_const,
      iteratedDeriv_fun_pow_zero (𝕜 := ℂ)]
    rw [if_neg hi0, if_neg (show i ≠ d * (M + 1) by omega)]
    simp
  rw [Finset.sum_eq_single_of_mem n (by simp) ?_]
  · simp [hk]
  · intro i hi hne
    have hi' := Finset.mem_range.1 hi
    rw [hz (n - i) (by omega) (by omega), mul_zero]

theorem pd_zero (d : ℕ) (hd : 0 < d) : pd d 0 = 1 := by
  simp [pd, X0.prodF, zero_pow hd.ne']

theorem prodF_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : X0.prodF q ≠ 0 := by
  unfold X0.prodF
  simp_rw [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -q ^ (n + 1)) (fun i => ?_) ?_
  · intro h
    have : q ^ (i + 1) = 1 := by linear_combination -h
    have h1 : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [this, norm_one] at h1
    exact lt_irrefl _ h1
  · simpa [norm_pow] using (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg _) hq)

theorem pow_mem_ball {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) {d : ℕ} (hd : 0 < d) :
    q ^ d ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hq ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hd.ne'

theorem pd_ne_zero {d : ℕ} (hd : 0 < d) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : pd d q ≠ 0 :=
  prodF_ne_zero (mem_ball_zero_iff.1 (pow_mem_ball hq hd))

theorem differentiableOn_pd {d : ℕ} (hd : 0 < d) : DifferentiableOn ℂ (pd d) (ball (0 : ℂ) 1) := by
  have := ModularForm.differentiableOn_tprod_one_sub_pow.comp (differentiable_pow d).differentiableOn
    (fun q hq => pow_mem_ball hq hd)
  exact this

theorem tendsto_finP {d : ℕ} (hd : 0 < d) :
    TendstoLocallyUniformlyOn (finP d) (pd d) atTop (ball (0 : ℂ) 1) := by
  have h := (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.comp
    (fun q : ℂ => q ^ d) (fun q hq => pow_mem_ball hq hd)
      (continuous_pow d).continuousOn).tendstoLocallyUniformlyOn_finsetRange
  exact h

theorem isRatAt_pd {d : ℕ} (hd : 0 < d) : IsRatAt (pd d) := by
  have hc : ∀ n : ℕ, ContDiffAt ℂ n (pd d) 0 := fun n =>
    ((differentiableOn_pd hd).contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  refine ⟨hc, iteratedDeriv_mem_of_limit (tendsto_finP hd)
    (fun M => (differentiable_finP d M).differentiableOn) (isRatAt_finP d) (fun n => ?_)⟩
  rw [eventually_atTop]
  refine ⟨n, fun M hM => ?_⟩
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [iteratedDeriv_finP_succ d M n (by nlinarith), ih]

/-! ## Rational `q`-expansions on the unit disc -/

/-- **A holomorphic function on the unit disc with rational Taylor coefficients at `0` has a
rational power series expansion on the disc.** -/
theorem exists_rat_hasSum {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hR : IsRatAt F) :
    ∃ a : ℕ → ℚ, ∀ q ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => (a n : ℂ) * q ^ n) (F q) := by
  choose r hr using fun n => hR.2 n
  refine ⟨fun n => r n / n.factorial, fun q hq => ?_⟩
  have := Complex.hasSum_taylorSeries_on_ball hd hq
  refine this.congr_fun fun n => ?_
  rw [← hr n]
  simp only [sub_zero, smul_eq_mul, Rat.cast_div, Rat.cast_natCast, eq_ratCast]
  ring

/-- `q²x(τ)` as a function of `q`. -/
def Fx (q : ℂ) : ℂ := pd 2 q ^ 2 * pd 16 q / (pd 4 q * pd 32 q ^ 2) + 2 * q ^ 2

/-- `q³y(τ)` as a function of `q`. -/
def Fy (q : ℂ) : ℂ := -(pd 8 q ^ 4 * pd 16 q ^ 2 / (pd 4 q ^ 2 * pd 32 q ^ 4))

theorem isRatAt_Fx : IsRatAt Fx := by
  have h2 : IsRatAt (pd 2) := isRatAt_pd (by norm_num)
  have h4 : IsRatAt (pd 4) := isRatAt_pd (by norm_num)
  have h16 : IsRatAt (pd 16) := isRatAt_pd (by norm_num)
  have h32 : IsRatAt (pd 32) := isRatAt_pd (by norm_num)
  have hN : IsRatAt fun q => pd 2 q ^ 2 * pd 16 q := (h2.pow 2).mul h16
  have hD : IsRatAt fun q => pd 4 q * pd 32 q ^ 2 := h4.mul (h32.pow 2)
  have hD0 : pd 4 0 * pd 32 0 ^ 2 ≠ 0 := by
    rw [pd_zero 4 (by norm_num), pd_zero 32 (by norm_num)]; norm_num
  have hT : IsRatAt fun q : ℂ => ((2 : ℚ) : ℂ) * q ^ 2 := (isRatAt_const 2).mul (isRatAt_pow 2)
  have h := (hN.div hD hD0).add hT
  have e : Fx = fun q => pd 2 q ^ 2 * pd 16 q / (pd 4 q * pd 32 q ^ 2) + ((2 : ℚ) : ℂ) * q ^ 2 := by
    funext q; simp [Fx]
  rw [e]; exact h

theorem isRatAt_Fy : IsRatAt Fy := by
  have h8 : IsRatAt (pd 8) := isRatAt_pd (by norm_num)
  have h4 : IsRatAt (pd 4) := isRatAt_pd (by norm_num)
  have h16 : IsRatAt (pd 16) := isRatAt_pd (by norm_num)
  have h32 : IsRatAt (pd 32) := isRatAt_pd (by norm_num)
  have hN : IsRatAt fun q => pd 8 q ^ 4 * pd 16 q ^ 2 := (h8.pow 4).mul (h16.pow 2)
  have hD : IsRatAt fun q => pd 4 q ^ 2 * pd 32 q ^ 4 := (h4.pow 2).mul (h32.pow 4)
  have hD0 : pd 4 0 ^ 2 * pd 32 0 ^ 4 ≠ 0 := by
    rw [pd_zero 4 (by norm_num), pd_zero 32 (by norm_num)]; norm_num
  exact (hN.div hD hD0).neg

theorem differentiableOn_Fx : DifferentiableOn ℂ Fx (ball (0 : ℂ) 1) := by
  have h2 := differentiableOn_pd (d := 2) (by norm_num)
  have h4 := differentiableOn_pd (d := 4) (by norm_num)
  have h16 := differentiableOn_pd (d := 16) (by norm_num)
  have h32 := differentiableOn_pd (d := 32) (by norm_num)
  unfold Fx
  refine DifferentiableOn.add ?_ (((differentiable_pow 2).differentiableOn).const_mul 2)
  refine DifferentiableOn.div ((h2.pow 2).mul h16) (h4.mul (h32.pow 2)) fun q hq => ?_
  exact mul_ne_zero (pd_ne_zero (by norm_num) hq) (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))

theorem differentiableOn_Fy : DifferentiableOn ℂ Fy (ball (0 : ℂ) 1) := by
  have h8 := differentiableOn_pd (d := 8) (by norm_num)
  have h4 := differentiableOn_pd (d := 4) (by norm_num)
  have h16 := differentiableOn_pd (d := 16) (by norm_num)
  have h32 := differentiableOn_pd (d := 32) (by norm_num)
  unfold Fy
  refine DifferentiableOn.neg ?_
  refine DifferentiableOn.div ((h8.pow 4).mul (h16.pow 2)) ((h4.pow 2).mul (h32.pow 4))
    fun q hq => ?_
  exact mul_ne_zero (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))
    (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))

/-! ## Back to `τ ∈ ℍ` -/

theorem qParam_natMul (d : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((d : ℂ) * z) = cexp (2 * Real.pi * I * z) ^ d := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem q_mem_ball (τ : UpperHalfPlane) : cexp (2 * Real.pi * I * τ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_exp]
  have h1 : (2 * (Real.pi : ℂ) * I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h1]
  have := τ.im_pos
  have h2 : -(2 * Real.pi * τ.im) < 0 := by nlinarith [Real.pi_pos]
  calc Real.exp _ < Real.exp 0 := Real.exp_lt_exp.2 h2
    _ = 1 := Real.exp_zero

theorem pF_eq_pd (d : ℕ) (z : ℂ) : X0.pF d z = pd d (cexp (2 * Real.pi * I * z)) := by
  simp only [X0.pF, pd, qParam_natMul]

theorem q2_xC (τ : UpperHalfPlane) :
    cexp (2 * Real.pi * I * τ) ^ 2 * X0.xC τ = Fx (cexp (2 * Real.pi * I * τ)) := by
  rw [X0.xC_decomp]
  have h2 := pF_eq_pd 2 τ
  have h4 := pF_eq_pd 4 τ
  have h16 := pF_eq_pd 16 τ
  have h32 := pF_eq_pd 32 τ
  simp only [X0.pF, Nat.cast_ofNat] at h2 h4 h16 h32
  rw [h2, h4, h16, h32, Fx]
  have hq : cexp (2 * Real.pi * I * τ) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem q3_yC (τ : UpperHalfPlane) :
    cexp (2 * Real.pi * I * τ) ^ 3 * X0.yC τ = Fy (cexp (2 * Real.pi * I * τ)) := by
  have hb := q_mem_ball τ
  have hw := X0.wz_ne_zero τ
  have hB : X0.pF 4 τ ^ 2 * X0.pF 32 τ ^ 4 ≠ 0 := by
    rw [pF_eq_pd, pF_eq_pd]
    exact mul_ne_zero (pow_ne_zero _ (pd_ne_zero (by norm_num) hb))
      (pow_ne_zero _ (pd_ne_zero (by norm_num) hb))
  have hyd : X0.yC τ = -(X0.pF 8 τ ^ 4 * X0.pF 16 τ ^ 2 / (X0.pF 4 τ ^ 2 * X0.pF 32 τ ^ 4)) /
      X0.wz τ ^ 72 := by
    unfold X0.yC
    rw [X0.etaD_eq'', X0.etaD_eq'', X0.etaD_eq'', X0.etaD_eq'']
    field_simp
  rw [hyd, Fy, ← pF_eq_pd, ← pF_eq_pd, ← pF_eq_pd, ← pF_eq_pd, ← X0.wz_pow_24]
  field_simp

/-- **`XQExpRational`, proved.** -/
theorem xQExpRational : XQExpRational := by
  obtain ⟨a, ha⟩ := exists_rat_hasSum differentiableOn_Fx isRatAt_Fx
  exact ⟨a, fun τ => by rw [q2_xC]; exact ha _ (q_mem_ball τ)⟩

/-- **`YQExpRational`, proved.** -/
theorem yQExpRational : YQExpRational := by
  obtain ⟨b, hb⟩ := exists_rat_hasSum differentiableOn_Fy isRatAt_Fy
  exact ⟨b, fun τ => by rw [q3_yC]; exact hb _ (q_mem_ball τ)⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))`, x0-32's
`Γ₀(32)`-invariance leaf and the cusp-growth leaf** (the `q`-expansions are proved). -/
theorem cmFieldOfDefinition_of_modFn' (hS : ShimuraReciprocityModFn) (hI : X0.EtaModelInvariant)
    (hG : EtaCuspGrowth) : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_modFn hS hI hG xQExpRational yQExpRational

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraCusp.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: x0-32's coordinate functions `x, y` are meromorphic at every cusp (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Proves `EtaCuspGrowth` (`ShimuraModFn.lean`): for every `γ ∈ SL₂(ℤ)`, `x(γτ)` and `y(γτ)` are
`O(e^{12π Im τ})` as `Im τ → ∞`.

Method.
* `H(w) = |η(w)|⁴ Im w` is `SL₂(ℤ)`-invariant: `Δ = η²⁴` is a cusp form of weight 12 for
  `SL₂(ℤ)` (Mathlib's `CuspForm.discriminant`), so `|η(γw)|²⁴ = |cw + d|¹²|η(w)|²⁴`, and
  `Im(γw) = Im w/|cw + d|²`.
* For `δ ≥ 1`: `diag(δ, 1)·γ = γ'·[[g, t], [0, e]]` with `γ' ∈ SL₂(ℤ)`, `ge = δ` (Hermite), so
  `δ·γτ = γ'w` with `w = (gτ + t)/e`, `Im τ/δ ≤ Im w ≤ δ Im τ`. Hence
  `|η(δγτ)|⁴·δ·Im(γτ) = H(w)`: the automorphy factors cancel.
* For `Im w ≥ 1`: `m⁴e^{−π Im w/3} ≤ H(w) ≤ M⁴` (`η = q^{1/24}F(q)`, `m ≤ |F| ≤ M` on the compact
  disc `|q| ≤ e^{−2π}`).
* `|x(γτ) − 2|⁴·H(w₄)H(w₃₂)² = 64·H(w₂)²H(w₁₆)` and `|y(γτ)|⁴·H(w₄)²H(w₃₂)⁴ = 16·H(w₈)⁴H(w₁₆)²`,
  giving `|x − 2|⁴ ≤ K e^{68π Im τ/3}`, `|y|⁴ ≤ K e^{136π Im τ/3}`, both `≤ K e^{48π Im τ}`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology Metric
open UpperHalfPlane hiding I

open scoped MatrixGroups

/-! ## The invariant `H(w) = |η(w)|⁴ Im w` -/

/-- `H(w) = |η(w)|⁴·Im w`. -/
def Hinv (w : UpperHalfPlane) : ℝ := ‖ModularForm.eta (w : ℂ)‖ ^ 4 * w.im

theorem Hinv_nonneg (w : UpperHalfPlane) : 0 ≤ Hinv w := by
  unfold Hinv; have := w.im_pos; positivity

theorem eta_pow_smul (γ : SL(2, ℤ)) (w : UpperHalfPlane) :
    ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ) ^ 24 =
      denom γ w ^ 12 * ModularForm.eta (w : ℂ) ^ 24 := by
  have h := SlashInvariantForm.slash_action_eqn'' (k := 12) CuspForm.discriminant
    (γ := (γ : GL (Fin 2) ℝ)) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) w
  simp only [CuspForm.coe_discriminant, ModularForm.discriminant] at h
  rw [ModularGroup.sl_moeb]
  exact h

/-- **`H` is `SL₂(ℤ)`-invariant.** -/
theorem Hinv_smul (γ : SL(2, ℤ)) (w : UpperHalfPlane) : Hinv (γ • w) = Hinv w := by
  have h24 := congrArg (‖·‖) (eta_pow_smul γ w)
  simp only [norm_pow, norm_mul] at h24
  have him := ModularGroup.im_smul_eq_div_normSq γ w
  rw [Complex.normSq_eq_norm_sq] at him
  have hd : ‖denom γ w‖ ≠ 0 := norm_ne_zero_iff.2 (denom_ne_zero _ _)
  refine (pow_left_inj₀ (Hinv_nonneg _) (Hinv_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 ?_
  unfold Hinv
  rw [him]
  have e1 : (‖ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ)‖ ^ 4 *
      (w.im / ‖denom γ w‖ ^ 2)) ^ 6 =
      ‖ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ)‖ ^ 24 * w.im ^ 6 / ‖denom γ w‖ ^ 12 := by
    field_simp
  rw [e1, h24]
  field_simp

/-! ## The Hermite decomposition `diag(δ, 1)·γ = γ'·[[g, t], [0, e]]` -/

theorem exists_hermite (a b c d δ : ℤ) (hdet : a * d - b * c = 1) (hδ : 0 < δ) :
    ∃ p u s v g t e : ℤ, p * v - u * s = 1 ∧ p * g = δ * a ∧ p * t + u * e = δ * b ∧
      s * g = c ∧ s * t + v * e = d ∧ 0 < g ∧ 0 < e ∧ g * e = δ := by
  set g : ℤ := (Int.gcd (δ * a) c : ℤ) with hg
  have hg0 : 0 < g := by
    rw [hg]
    have : Int.gcd (δ * a) c ≠ 0 := by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      have ha : a = 0 := by
        rcases mul_eq_zero.1 h.1 with h' | h'
        · omega
        · exact h'
      rw [ha, h.2] at hdet; simp at hdet
    positivity
  obtain ⟨p, hp⟩ : (g : ℤ) ∣ δ * a := Int.gcd_dvd_left _ _
  obtain ⟨s, hs⟩ : (g : ℤ) ∣ c := Int.gcd_dvd_right _ _
  have hcop : Int.gcd p s = 1 := by
    have h := Int.gcd_div_gcd_div_gcd (i := δ * a) (j := c) (by rw [hg] at hg0; exact_mod_cast hg0)
    have e1 : δ * a / (Int.gcd (δ * a) c : ℤ) = p := by
      rw [← hg, hp]; exact Int.mul_ediv_cancel_left _ hg0.ne'
    have e2 : c / (Int.gcd (δ * a) c : ℤ) = s := by
      rw [← hg, hs]; exact Int.mul_ediv_cancel_left _ hg0.ne'
    rwa [e1, e2] at h
  have hb := Int.gcd_eq_gcd_ab p s
  rw [hcop] at hb
  set v := Int.gcdA p s
  set u := -Int.gcdB p s
  have hB : p * v - u * s = 1 := by simp only [u]; linear_combination -hb
  refine ⟨p, u, s, v, g, v * δ * b - u * d, -s * δ * b + p * d, hB, by linear_combination -hp,
    by linear_combination δ * b * hB, by linear_combination -hs, by linear_combination d * hB,
    hg0, ?_, ?_⟩
  · have : g * (-s * δ * b + p * d) = δ := by
      linear_combination (δ * b) * hs - d * hp + δ * hdet
    by_contra hneg
    push_neg at hneg
    nlinarith
  · linear_combination (δ * b) * hs - d * hp + δ * hdet

/-- **`δ·γτ = γ'w` with `Im τ/δ ≤ Im w ≤ δ Im τ`.** -/
theorem exists_smul_decomp {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ (γ' : SL(2, ℤ)) (w : UpperHalfPlane), (δ : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ' • w : UpperHalfPlane) : ℂ) ∧ τ.im / δ ≤ w.im ∧ w.im ≤ δ * τ.im := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨p, u, s, v, g, t, e, hB, hp, hpt, hs, hst, hg0, he0, hge⟩ :=
    exists_hermite (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) δ hdet (by exact_mod_cast hδ)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have heR : (0 : ℝ) < e := by exact_mod_cast he0
  have hgeR : (g : ℝ) * e = δ := by exact_mod_cast hge
  have hwim : 0 < (((g : ℂ) * τ + t) / e).im := by
    have : (((g : ℂ) * τ + t) / e).im = g * τ.im / e := by
      rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
      simp
    rw [this]; have := τ.im_pos; positivity
  let w : UpperHalfPlane := ⟨((g : ℂ) * τ + t) / e, hwim⟩
  have hwim' : w.im = g * τ.im / e := by
    show (((g : ℂ) * τ + t) / e).im = _
    rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
    simp
  let γ' : SL(2, ℤ) := ⟨!![p, u; s, v], by rw [Matrix.det_fin_two_of]; exact hB⟩
  refine ⟨γ', w, ?_, ?_, ?_⟩
  · rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      algebraMap_int_eq, eq_intCast, Int.cast_id]
    have hden : ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
      have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      simpa [ModularGroup.denom_apply] using this
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    have h1 : ((p : ℝ) : ℂ) * (w : ℂ) + ((u : ℝ) : ℂ) =
        δ * (((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ)) / e := by
      show ((p : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((u : ℝ) : ℂ) = _
      field_simp
      have hp' : (p : ℂ) * g = δ * γ 0 0 := by exact_mod_cast hp
      have hpt' : (p : ℂ) * t + u * e = δ * γ 0 1 := by exact_mod_cast hpt
      push_cast
      linear_combination (τ : ℂ) * hp' + hpt'
    have h2 : ((s : ℝ) : ℂ) * (w : ℂ) + ((v : ℝ) : ℂ) =
        (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) / e := by
      show ((s : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((v : ℝ) : ℂ) = _
      field_simp
      have hs' : (s : ℂ) * g = γ 1 0 := by exact_mod_cast hs
      have hst' : (s : ℂ) * t + v * e = γ 1 1 := by exact_mod_cast hst
      push_cast
      linear_combination (τ : ℂ) * hs' + hst'
    rw [h1, h2]
    field_simp
  · rw [hwim', div_le_div_iff₀ (by exact_mod_cast hδ) heR]
    have := τ.im_pos
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg0
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have h3 : (e : ℝ) ≤ g * δ := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 this.le
    nlinarith
  · rw [hwim', div_le_iff₀ heR]
    have := τ.im_pos
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have hgd : (g : ℝ) ≤ δ := by nlinarith
    have h3 : (g : ℝ) ≤ δ * e := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 this.le
    nlinarith

/-- **`|η(δγτ)|⁴·δ·Im(γτ) = H(w)`** with `Im τ/δ ≤ Im w ≤ δ Im τ`. -/
theorem etaD_norm_eq {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ w : UpperHalfPlane, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
      Hinv w ∧ τ.im / δ ≤ w.im ∧ w.im ≤ δ * τ.im := by
  obtain ⟨γ', w, hw, h1, h2⟩ := exists_smul_decomp hδ γ τ
  refine ⟨w, ?_, h1, h2⟩
  rw [← Hinv_smul γ' w]
  unfold Hinv X0.etaD
  rw [hw]
  congr 1
  have := congrArg Complex.im hw
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero] at this
  exact this

/-! ## Bounds for `H` -/

theorem eta_eq_prodF (z : ℂ) :
    ModularForm.eta z = Function.Periodic.qParam 24 z * X0.prodF (cexp (2 * Real.pi * I * z)) := by
  unfold ModularForm.eta X0.prodF
  simp_rw [ModularForm.eta_q_eq_pow]

theorem norm_qParam24_pow4 (w : UpperHalfPlane) :
    ‖Function.Periodic.qParam 24 (w : ℂ)‖ ^ 4 = Real.exp (-(Real.pi * w.im / 3)) := by
  rw [Function.Periodic.qParam, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_q_le (w : UpperHalfPlane) (hw : 1 ≤ w.im) :
    ‖cexp (2 * Real.pi * I * (w : ℂ))‖ ≤ Real.exp (-(2 * Real.pi)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (2 * (Real.pi : ℂ) * I * (w : ℂ)).re = -(2 * Real.pi * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  nlinarith [Real.pi_pos]

theorem exists_prodF_bounds :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ q : ℂ, ‖q‖ ≤ Real.exp (-(2 * Real.pi)) →
      m ≤ ‖X0.prodF q‖ ∧ ‖X0.prodF q‖ ≤ M := by
  set r := Real.exp (-(2 * Real.pi))
  have hr1 : r < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  have hc : ContinuousOn (fun q => ‖X0.prodF q‖) (closedBall (0 : ℂ) r) :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.mono hsub).norm
  have hne : (closedBall (0 : ℂ) r).Nonempty := ⟨0, by simp [r, (Real.exp_pos _).le]⟩
  obtain ⟨q0, hq0, hmin⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMinOn hne hc
  obtain ⟨q1, hq1, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn hne hc
  have hpos : 0 < ‖X0.prodF q0‖ :=
    norm_pos_iff.2 (prodF_ne_zero (by simpa using (mem_closedBall_zero_iff.1 hq0).trans_lt hr1))
  refine ⟨‖X0.prodF q0‖, ‖X0.prodF q0‖ + ‖X0.prodF q1‖, hpos, by positivity, fun q hq => ?_⟩
  have hq' : q ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.2 hq
  refine ⟨hmin hq', ?_⟩
  have := hmax hq'
  simp only [Set.mem_setOf_eq] at this
  linarith

theorem Hinv_bounds :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ w : UpperHalfPlane, 1 ≤ w.im →
      m * Real.exp (-(Real.pi * w.im / 3)) ≤ Hinv w ∧ Hinv w ≤ M := by
  obtain ⟨m, M, hm, hM, hb⟩ := exists_prodF_bounds
  refine ⟨m ^ 4, M ^ 4, by positivity, by positivity, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hb _ (norm_q_le w hw)
  have hH : Hinv w = Real.exp (-(Real.pi * w.im / 3)) *
      ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * w.im := by
    unfold Hinv
    rw [eta_eq_prodF, norm_mul, mul_pow, norm_qParam24_pow4]
  rw [hH]
  have hE := Real.exp_pos (-(Real.pi * w.im / 3))
  constructor
  · have : m ^ 4 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 :=
      pow_le_pow_left₀ hm.le h1 4
    have hP : 0 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 := by positivity
    calc m ^ 4 * Real.exp (-(Real.pi * w.im / 3))
        ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * Real.exp (-(Real.pi * w.im / 3)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = Real.exp (-(Real.pi * w.im / 3)) * ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * 1 :=
          by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  · -- `t·e^{−πt/3} ≤ t·e^{−t} ≤ 1`
    have hP : ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 ≤ M ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 4
    have ht : Real.exp (-(Real.pi * w.im / 3)) * w.im ≤ 1 := by
      have h3 : Real.exp (-(Real.pi * w.im / 3)) ≤ Real.exp (-w.im) := by
        apply Real.exp_le_exp.2
        have := Real.pi_gt_three
        nlinarith
      have h4 : w.im + 1 ≤ Real.exp w.im := Real.add_one_le_exp _
      have h5 : Real.exp (-w.im) * Real.exp w.im = 1 := by
        rw [← Real.exp_add]; simp
      have h6 : Real.exp (-w.im) * w.im ≤ 1 := by nlinarith [Real.exp_pos (-w.im)]
      nlinarith
    have hP0 : 0 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 := by positivity
    calc Real.exp (-(Real.pi * w.im / 3)) * ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * w.im
        = ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 *
          (Real.exp (-(Real.pi * w.im / 3)) * w.im) := by ring
      _ ≤ M ^ 4 * 1 := by gcongr
      _ = M ^ 4 := mul_one _

/-! ## Assembly -/

/-- For `Im τ ≥ 32` and `δ ∣ 32`: bounds on `A_δ = |η(δγτ)|⁴` through `H(w_δ)`. -/
theorem etaD_bounds {m M : ℝ} (hb : ∀ w : UpperHalfPlane, 1 ≤ w.im →
      m * Real.exp (-(Real.pi * w.im / 3)) ≤ Hinv w ∧ Hinv w ≤ M) (hm : 0 < m)
    {δ : ℕ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (hτ : 32 ≤ τ.im) :
    ∃ Hδ : ℝ, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) = Hδ ∧
      m * Real.exp (-(Real.pi * (δ * τ.im) / 3)) ≤ Hδ ∧ Hδ ≤ M := by
  obtain ⟨w, hw, h1, h2⟩ := etaD_norm_eq hδ γ τ
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hw1 : 1 ≤ w.im := by
    refine le_trans ?_ h1
    rw [le_div_iff₀ hδR]
    have : (δ : ℝ) ≤ 32 := by exact_mod_cast hδ32
    linarith
  obtain ⟨hl, hu⟩ := hb w hw1
  refine ⟨Hinv w, hw, le_trans ?_ hl, hu⟩
  gcongr

theorem bigO_of_pow4 {f : UpperHalfPlane → ℂ} {K : ℝ} (hK : 0 ≤ K) (c : ℂ)
    (h : ∀ τ : UpperHalfPlane, 32 ≤ τ.im →
      ‖f τ - c‖ ^ 4 ≤ K * Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) ^ 4) :
    f =O[atImInfty] fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  refine Asymptotics.IsBigO.of_bound (K + 1 + ‖c‖) ?_
  rw [Filter.eventually_iff, atImInfty_mem]
  refine ⟨32, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
  set E := Real.exp (2 * Real.pi * (6 : ℕ) * τ.im)
  have hE1 : 1 ≤ E := Real.one_le_exp (by have := τ.im_pos; positivity)
  rw [abs_of_pos (Real.exp_pos _)]
  have h1 : ‖f τ - c‖ ≤ (K + 1) * E := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) ?_
    calc ‖f τ - c‖ ^ 4 ≤ K * E ^ 4 := h τ hτ
      _ ≤ (K + 1) ^ 4 * E ^ 4 := by
          gcongr
          exact (by linarith : K ≤ K + 1).trans (le_self_pow₀ (by linarith) (by norm_num))
      _ = ((K + 1) * E) ^ 4 := by ring
  calc ‖f τ‖ = ‖(f τ - c) + c‖ := by ring_nf
    _ ≤ ‖f τ - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (K + 1) * E + ‖c‖ * E := by gcongr; nlinarith [norm_nonneg c]
    _ = (K + 1 + ‖c‖) * E := by ring

theorem exp_combine (T : ℝ) (hT : 0 ≤ T) (a : ℝ) (ha : a ≤ 144) :
    Real.exp (Real.pi * a * T / 3) ≤ Real.exp (2 * Real.pi * (6 : ℕ) * T) ^ 4 := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  push_cast
  have := Real.pi_pos
  nlinarith [mul_nonneg this.le hT]

/-- **`x(γτ) = O(e^{12π Im τ})`.** -/
theorem xC_growth (γ : SL(2, ℤ)) :
    (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_bounds
  refine bigO_of_pow4 (K := 64 * M ^ 3 / m ^ 3) (by positivity) 2 fun τ hτ => ?_
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  set I0 := (γ • τ).im
  have hI : 0 < I0 := (γ • τ).im_pos
  obtain ⟨H2, e2, -, u2⟩ := etaD_bounds hb hm (δ := 2) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H16, e16, -, u16⟩ := etaD_bounds hb hm (δ := 16) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H4, e4, l4, -⟩ := etaD_bounds hb hm (δ := 4) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H32, e32, l32, -⟩ := etaD_bounds hb hm (δ := 32) (by norm_num) (by norm_num) γ τ hτ
  have n2 := X0.etaD_ne_zero (d := 2) (by norm_num) (γ • τ)
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n16 := X0.etaD_ne_zero (d := 16) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hx : X0.xC z - 2 = X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2) := by
    unfold X0.xC; ring
  rw [hx]
  set a2 := ‖X0.etaD 2 z‖
  set a4 := ‖X0.etaD 4 z‖
  set a16 := ‖X0.etaD 16 z‖
  set a32 := ‖X0.etaD 32 z‖
  have p4 : 0 < a4 := norm_pos_iff.2 n4
  have p32 : 0 < a32 := norm_pos_iff.2 n32
  have hnorm : ‖X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2)‖ =
      a2 ^ 2 * a16 / (a4 * a32 ^ 2) := by
    simp only [norm_div, norm_mul, norm_pow, a2, a4, a16, a32]
  rw [hnorm]
  -- the identity `|x − 2|⁴·H₄H₃₂² = 64·H₂²H₁₆`
  have hid : (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 * (H4 * H32 ^ 2) = 64 * (H2 ^ 2 * H16) := by
    rw [← e2, ← e4, ← e16, ← e32]
    push_cast
    field_simp
    ring
  have hT := τ.im_pos
  set T := τ.im
  have hL : m * Real.exp (-(Real.pi * (4 * T) / 3)) * (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2
      ≤ H4 * H32 ^ 2 := by
    have hl4 : m * Real.exp (-(Real.pi * ((4 : ℕ) * T) / 3)) ≤ H4 := l4
    have hl32 : m * Real.exp (-(Real.pi * ((32 : ℕ) * T) / 3)) ≤ H32 := l32
    push_cast at hl4 hl32
    have : 0 ≤ m * Real.exp (-(Real.pi * (32 * T) / 3)) := by positivity
    have h4' : 0 ≤ H4 := by rw [← e4]; positivity
    gcongr
  have hU : H2 ^ 2 * H16 ≤ M ^ 2 * M := by
    have h2' : 0 ≤ H2 := by rw [← e2]; positivity
    have h16' : 0 ≤ H16 := by rw [← e16]; positivity
    gcongr
  have hLpos : 0 < m * Real.exp (-(Real.pi * (4 * T) / 3)) *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2 := by positivity
  have hX0 : 0 ≤ (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 := by positivity
  have hbound : (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 ≤
      64 * (M ^ 2 * M) / (m * Real.exp (-(Real.pi * (4 * T) / 3)) *
        (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2) := by
    rw [le_div_iff₀ hLpos]
    calc _ ≤ (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 * (H4 * H32 ^ 2) := by gcongr
      _ = 64 * (H2 ^ 2 * H16) := hid
      _ ≤ 64 * (M ^ 2 * M) := by gcongr
  refine hbound.trans ?_
  have hexp : 64 * (M ^ 2 * M) / (m * Real.exp (-(Real.pi * (4 * T) / 3)) *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2) =
      64 * M ^ 3 / m ^ 3 * Real.exp (Real.pi * 68 * T / 3) := by
    have hE : Real.exp (Real.pi * 68 * T / 3) = (Real.exp (-(Real.pi * (4 * T) / 3)) *
        Real.exp (-(Real.pi * (32 * T) / 3)) ^ 2)⁻¹ := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]; congr 1; ring
    rw [hE]
    field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (exp_combine T hT.le 68 (by norm_num)) (by positivity)

/-- **`y(γτ) = O(e^{12π Im τ})`.** -/
theorem yC_growth (γ : SL(2, ℤ)) :
    (fun τ : UpperHalfPlane => X0.yC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_bounds
  refine bigO_of_pow4 (K := 16 * M ^ 6 / m ^ 6) (by positivity) 0 fun τ hτ => ?_
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  obtain ⟨H8, e8, -, u8⟩ := etaD_bounds hb hm (δ := 8) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H16, e16, -, u16⟩ := etaD_bounds hb hm (δ := 16) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H4, e4, l4, -⟩ := etaD_bounds hb hm (δ := 4) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H32, e32, l32, -⟩ := etaD_bounds hb hm (δ := 32) (by norm_num) (by norm_num) γ τ hτ
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hI : 0 < (γ • τ).im := (γ • τ).im_pos
  rw [sub_zero]
  set a8 := ‖X0.etaD 8 z‖
  set a4 := ‖X0.etaD 4 z‖
  set a16 := ‖X0.etaD 16 z‖
  set a32 := ‖X0.etaD 32 z‖
  have p4 : 0 < a4 := norm_pos_iff.2 n4
  have p32 : 0 < a32 := norm_pos_iff.2 n32
  have hnorm : ‖X0.yC z‖ = a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4) := by
    unfold X0.yC
    simp only [norm_neg, norm_div, norm_mul, norm_pow, a8, a4, a16, a32]
  rw [hnorm]
  have hid : (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 * (H4 ^ 2 * H32 ^ 4) =
      16 * (H8 ^ 4 * H16 ^ 2) := by
    rw [← e8, ← e4, ← e16, ← e32]
    push_cast
    field_simp
    ring
  have hT := τ.im_pos
  set T := τ.im
  have hL : (m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4 ≤ H4 ^ 2 * H32 ^ 4 := by
    have hl4 : m * Real.exp (-(Real.pi * ((4 : ℕ) * T) / 3)) ≤ H4 := l4
    have hl32 : m * Real.exp (-(Real.pi * ((32 : ℕ) * T) / 3)) ≤ H32 := l32
    push_cast at hl4 hl32
    have : 0 ≤ m * Real.exp (-(Real.pi * (32 * T) / 3)) := by positivity
    have : 0 ≤ m * Real.exp (-(Real.pi * (4 * T) / 3)) := by positivity
    gcongr
  have hU : H8 ^ 4 * H16 ^ 2 ≤ M ^ 4 * M ^ 2 := by
    have h8' : 0 ≤ H8 := by rw [← e8]; positivity
    have h16' : 0 ≤ H16 := by rw [← e16]; positivity
    gcongr
  have hLpos : 0 < (m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4 := by positivity
  have hbound : (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 ≤
      16 * (M ^ 4 * M ^ 2) / ((m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
        (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4) := by
    rw [le_div_iff₀ hLpos]
    calc _ ≤ (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 * (H4 ^ 2 * H32 ^ 4) := by gcongr
      _ = 16 * (H8 ^ 4 * H16 ^ 2) := hid
      _ ≤ 16 * (M ^ 4 * M ^ 2) := by gcongr
  refine hbound.trans ?_
  have hexp : 16 * (M ^ 4 * M ^ 2) / ((m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4) =
      16 * M ^ 6 / m ^ 6 * Real.exp (Real.pi * 136 * T / 3) := by
    have hE : Real.exp (Real.pi * 136 * T / 3) = (Real.exp (-(Real.pi * (4 * T) / 3)) ^ 2 *
        Real.exp (-(Real.pi * (32 * T) / 3)) ^ 4)⁻¹ := by
      rw [show ∀ x : ℝ, x ^ 4 = x * x * x * x from fun x => by ring, sq, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
      congr 1; ring
    rw [hE]
    field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (exp_combine T hT.le 136 (by norm_num)) (by positivity)

/-- **`EtaCuspGrowth`, proved**: `x, y` are meromorphic at every cusp (`k = 6`). -/
theorem etaCuspGrowth : EtaCuspGrowth := fun γ => ⟨6, xC_growth γ, yC_growth γ⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))` and x0-32's
`Γ₀(32)`-invariance leaf** (cusp growth and the `q`-expansions are proved). -/
theorem cmFieldOfDefinition_of_modFn_inv (hS : ShimuraReciprocityModFn)
    (hI : X0.EtaModelInvariant) :
    ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_modFn' hS hI etaCuspGrowth

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of ZInQKernel/Contrib/TYZGenus/ShimuraMain.lean @ 66d92d11 (imports dropped) =====

/-!
# tyz-cm: main results — the CM leaf from the field-of-definition theorem for `ℚ(X₀(N))`

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

* Leaf `CMValueRingClass` (Shimura): the values at Heegner points of discriminant `D` of the
  functions of `ℚ(X₀(N))` that are regular on `ℍ` lie in the ring class field of discriminant `D`.
* `cmFieldOfDefinition_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
  CM.CMFieldOfDefinition ringClassFieldD` — **the main result of tyz-cm**.
* `cmValueRingClass_of_modFn : ShimuraReciprocityModFn → CMValueRingClass` (the trivial-class
  case of Gross's form of the main theorem of CM), so the main result also holds with
  `ShimuraReciprocityModFn` in place of `CMValueRingClass` (`cmFieldOfDefinition_of_modFn_inv`,
  `ShimuraCusp.lean`).
* `shimuraReciprocityPic_of_modFn : ShimuraReciprocityModFn → X0.EtaModelInvariant →
  ShimuraReciprocityPic` (the leaf of `ShimuraRecip.lean`, used by `ShimuraZn.lean`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- **Leaf CM-VALUE (field of definition of Heegner points of `X₀(N)`; Shimura).** For every
`g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`) and every Heegner form `Q` of level `N` and
discriminant `D` (a primitive positive definite `[A, B, C]`, `N ∣ A`, `B² − 4AC = D`), the value
`g(τ_Q)` is algebraic and lies in the ring class field `H_D` of the order of discriminant `D`
(`ringClassFieldD D ⊂ ℚ̄`, through cm-points' embedding `ιC : ℚ̄ → ℂ`).

Content: `τ_Q` is the point `(ℂ/L, L_N/L)` of `X₀(N)`, `L = ⟨1, τ_Q⟩` a proper `O_D`-lattice and
`L_N = ⟨1/N, τ_Q⟩` a lattice for an order `O' ⊇ O_D`; by the main theorem of complex
multiplication every `σ ∈ Aut(ℂ/H_D)` fixes the isomorphism class of the pair (its idele lies in
`K^× Ô_D^×`), and since `X₀(N)_ℚ` is the coarse moduli space of such pairs, `σ` fixes
`g(τ_Q)`; so `g(τ_Q) ∈ H_D`.
Sources (refereed, textbook; numbers UNVERIFIED, from memory): Shimura, *Introduction to the
arithmetic theory of automorphic functions* (1971), Thm. 5.7 (`K(j(𝔞)) = H_O`), Prop. 6.9 /
Thm. 6.23 (`ℚ(X₀(N)) = ℚ(j, j_N)`, rational structure) and §6.8 (values at CM points); Gross,
*Heegner points on `X₀(N)`* (Durham 1983), 1984, §1–§3; Cox, *Primes of the form x² + ny²*,
Thm. 11.1 and §11.C (`j(τ), j(Nτ)` at CM points). No Heegner condition `(f, N) = 1` is needed
(`H_{O'} ⊆ H_D`). This statement is weaker than `ShimuraReciprocityModFn`
(`cmValueRingClass_of_modFn`). -/
def CMValueRingClass : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (D : ℤ) (Q : HeegnerForm N D), ∃ a ∈ ringClassFieldD D, ιC a = g Q.tauH

/-! ## The main result -/

/-- **The CM leaf `CM.CMFieldOfDefinition ringClassFieldD` from the field-of-definition theorem
for `ℚ(X₀(N))` and x0-32's `Γ₀(32)`-invariance leaf.** -/
theorem cmFieldOfDefinition_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
    CMFieldOfDefinition ringClassFieldD := by
  intro D Q
  obtain ⟨a, haH, ha⟩ := hV 32 _ (isRatModFn_xC_of hI etaCuspGrowth xQExpRational) D Q
  obtain ⟨b, hbH, hb⟩ := hV 32 _ (isRatModFn_yC_of hI etaCuspGrowth yQExpRational) D Q
  rw [heegnerPt_of_alg Q ha hb]
  split_ifs with h
  · rw [mem_ptsOver_iff]
    exact ⟨haH, hbH⟩
  · exact AddSubgroup.zero_mem _

/-- **The TYZ package leaf `Package.CMFieldOfDefinitionTYZ`** from the same two leaves. -/
theorem cmFieldTYZ_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
    ZInQ.Contrib.TYZGenus.Package.CMFieldOfDefinitionTYZ :=
  RingClassBridge.cmFieldTYZ_of_ringClassD (cmFieldOfDefinition_of_cmValue hV hI)

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **Reading A of TYZ Theorem 3.5 with the CM field-of-definition leaf discharged** by
`CMValueRingClass` and `X0.EtaModelInvariant` (ring-class's
`tyzThm35ReadingA_of_cmLeaves_ringClassD`; `TYZSigmaFixesZn` stays a hypothesis: task
cm-numeric). -/
theorem tyzThm35ReadingA_of_cmValue (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hV : CMValueRingClass) (hI : X0.EtaModelInvariant)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29
    (cmFieldOfDefinition_of_cmValue hV hI) hs h318 hG

/-! ## `CMValueRingClass` from Gross's form of the main theorem of CM -/

section General
variable {m f : ℕ} [NeZero m] [NeZero f]

/-- **`κ(O)·⟨1/N, τ_Q⟩ ⊆ ⟨1/N, τ_Q⟩`** for a Heegner form of level `N` (uses `N ∣ A`). -/
theorem kappa_mul_mem_latN_gen (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ}
    (Q : HeegnerForm N D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.latN, kappa m o * x ∈ Q.latN := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  obtain ⟨A', hA'⟩ := Q.N_dvd
  have hN0 : (N : ℂ) ≠ 0 := by
    have hA := Q.A_pos
    intro h
    have : (N : ℤ) = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hA'
    omega
  have hA'C : (Q.A : ℂ) = N * A' := by exact_mod_cast hA'
  have h1 : kappa m o * (1 / (N : ℂ)) ∈ Q.latN := by
    rw [huv, HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨u, v * A', ?_⟩
    simp only [zsmul_eq_mul]
    rw [hA'C]
    push_cast
    field_simp
  have hτ : kappa m o * Q.tau ∈ Q.latN := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨-(N * v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.latN] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

end General

/-- **`CMValueRingClass` from `ShimuraReciprocityModFn`** (the trivial class `J = 𝓞_K`). -/
theorem cmValueRingClass_of_modFn (hS : ShimuraReciprocityModFn) : CMValueRingClass := by
  intro N g hg D Q
  have hDneg := Q.D_neg
  have h4 := disc_mod_four Q
  obtain ⟨b, hb, hsq⟩ := sqfPart_spec D.natAbs
  have hspec := condD_spec h4 hDneg
  have hDa : (D.natAbs : ℤ) = -D := by omega
  have hm0 : sqfPart D.natAbs ≠ 0 := fun h => by rw [h, mul_zero] at hb; omega
  have hf0 : condD D ≠ 0 := by
    intro h; rw [h] at hspec; split_ifs at hspec <;> simp at hspec <;> omega
  have : NeZero (sqfPart D.natAbs) := ⟨hm0⟩
  have : NeZero (condD D) := ⟨hf0⟩
  set m := sqfPart D.natAbs with hm
  set f := condD D with hf
  have hD : D = discOf m f := by
    unfold discOf
    split_ifs at hspec ⊢ with h3
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
  have hK : ringClassFieldD D = ringClassFieldBar m f := by rw [ringClassFieldD, if_pos hDneg]
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  set J1 : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus := 1 with hJ1
  have hone : (J1 : Ideal (𝓞 (QNeg m))) = ⊤ := by
    rw [hJ1, OneMemClass.coe_one, Ideal.one_eq_top]
  have hmul : LinearMap.mulLeft ℤ (1 : ℂ) = LinearMap.id := by ext; simp
  have hL : idealLat m f J1 * Q.lat = Q.lat.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_lat hsq hD Q ho)
  have hLN : idealLat m f J1 * Q.latN = Q.latN.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_latN_gen hsq hD Q ho)
  -- the action hypothesis for `ρ` fixing `H`
  have hρe : ∀ ρ ∈ (ringClassFieldD D).fixingSubgroup,
      ∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J1) x) := by
    intro ρ hρ x
    rw [hJ1, map_one, map_one, AlgEquiv.one_apply]
    have hx : e x ∈ ringClassFieldD D := by
      rw [hK, ← ringClassFieldBar_eq_map m f e]
      exact ⟨x, x.2, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ _ hx
  obtain ⟨a, -, ha, -, -⟩ := hS N g hg m f hsq e he J1 1 (hρe 1 (Subgroup.one_mem _)) D hD Q Q 1
    hL hLN
  refine ⟨a, ?_, ha⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (ringClassFieldD D)]
  intro ρ
  obtain ⟨a1, a2, h1, h2, h12⟩ := hS N g hg m f hsq e he J1 ρ (hρe ρ.1 ρ.2) D hD Q Q 1 hL hLN
  have e1 : a1 = a := ιCA.injective (h1.trans ha.symm)
  have e2 : a2 = a := ιCA.injective (h2.trans ha.symm)
  rw [← e1]
  conv_rhs => rw [e1, ← e2]
  exact h12

/-- **`ShimuraReciprocityPic` from `ShimuraReciprocityModFn` and x0-32's invariance leaf.** -/
theorem shimuraReciprocityPic_of_modFn (hS : ShimuraReciprocityModFn)
    (hI : X0.EtaModelInvariant) : ShimuraReciprocityPic :=
  shimuraReciprocityPic_of hS (isRatModFn_xC_of hI etaCuspGrowth xQExpRational)
    (isRatModFn_yC_of hI etaCuspGrowth yQExpRational)

end ZInQ.Contrib.TYZGenus.Shimura

end  -- closes the file's top-level `noncomputable section`

-- ===== verbatim body of scratch/cm-bridge/Bridge.lean @ 68d27814 (imports dropped) =====

/-!
# cm-bridge: cm-numeric's class-7 file rewired to ring class field theory

Task cm-bridge (2026-11-13). Report: `docs/research/cm-bridge.md`; log: `scratch/cm-bridge/log.md`.

§0–§9 are a verbatim copy of cm-numeric's `scratch/cm-numeric/Class7.lean` (namespace renamed
`CMNumeric → CMBridge`; every `Prop` unchanged, checked by `rfl` in §0 against cm-points'
`Package`). §10 onwards are new: they discharge, from ring-class's theorems
(`ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`, `RingClassGenus.lean`), the leaves
`IInH4`, `HprimeNormal` (ring-class), `IInHprime` (`Lni_le_Hprimebar`), `CMFieldOfDefinition7`
(from the general `CM.CMFieldOfDefinition ringClassFieldD`, `ringClassFieldD_neg`), and state the
main theorem with only the remaining leaves. §11 proves cm-numeric's leaf `GenusFieldLeLni` (genus
field of `ℚ(√−e)`, `e ≡ 7 (mod 8)`, inside `L_e(i)`; Bauer + genus characters). §12 reduces TYZ Lemma
3.21(4) (`Lemma321Seven`) to TYZ Theorem 3.6(3) (`TYZThm36Seven`, a leaf about the pinned class-7 CM
point) and the glue `BetaOnGenus7`; §13 proves `BetaOnGenus7` (the genus field is `K_n(√p* : p ∣ n)`,
the Artin symbols act on `√p*` by the genus characters, `N𝔭₂ = 2`). Final theorem:
`tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.CMBridge

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b

/-! ## §0. Verbatim copies of the Props of this task (checked equal by `rfl`) -/

namespace Copy

/-- Verbatim copy of `CM.CMFieldOfDefinition`. -/
def CMFieldOfDefinition (H : ℤ → IntermediateField ℚ Qbar) : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), heegnerPt Q ∈ ptsOver (H D)

/-- Verbatim copy of `Package.TYZSigmaFixesZn`. -/
def TYZSigmaFixesZn : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzZn n) = tyzZn n

/-- Verbatim copy of `Package.Lemma318Literal`. -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

/-- Verbatim copy of `Package.GenusPtsDefined`. -/
def GenusPtsDefined (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver (Hn n)

/-- Verbatim copy of `Package.Thm35First`. -/
def Thm35First (ℓ : ℕ → ℤ) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))

/-- Verbatim copy of `Package.Lemma321`. -/
def Lemma321 (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1)

/-- Verbatim copy of `Package.GenusPointLeafCM`. -/
def GenusPointLeafCM (ℓ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA),
    (∀ e ∈ n.divisors, e % 8 = 7 → Z7 e ∈ ptsOver (Lni e)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧
      (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε (tyzGenusPt Φ Z7) n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 →
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG 1))

theorem cmFieldOfDefinition_eq : CMFieldOfDefinition = CM.CMFieldOfDefinition := rfl
theorem tyzSigmaFixesZn_eq : TYZSigmaFixesZn = Package.TYZSigmaFixesZn := rfl
theorem lemma318Literal_eq : Lemma318Literal = Package.Lemma318Literal := rfl
theorem genusPtsDefined_eq : GenusPtsDefined = Package.GenusPtsDefined := rfl
theorem thm35First_eq : Thm35First = Package.Thm35First := rfl
theorem lemma321_eq : Lemma321 = Package.Lemma321 := rfl
theorem genusPointLeafCM_eq : GenusPointLeafCM = Package.GenusPointLeafCM := rfl

end Copy

/-! ## §1. TYZ's class-7 CM point -/

/-- TYZ's `δ` (L1205: "an integer such that `δ² ≡ −n (mod 128)`"), pinned as the least `δ ∈ [0, 128)`
with `δ² + n ≡ 0 (mod 128)` (junk `0` if there is none; there is one for `n ≡ 7 (mod 8)`,
`tyzDelta_spec`). Numerically the CM point depends only on `δ mod 64`, and `δ ↦ −δ` conjugates it
(`class7.out`). -/
def tyzDelta (n : ℕ) : ℕ :=
  ((List.range 128).find? fun d => (d * d + n) % 128 == 0).getD 0

theorem tyzDelta_mod (n : ℕ) : tyzDelta n = tyzDelta (n % 128) := by
  unfold tyzDelta
  congr 2
  funext d
  rw [Nat.add_mod (d * d) n, Nat.add_mod (d * d) (n % 128), Nat.mod_mod]

theorem tyzDelta_spec_aux : ∀ m < 128, m % 8 = 7 → (tyzDelta m * tyzDelta m + m) % 128 = 0 := by
  decide +kernel

theorem tyzDelta_spec {n : ℕ} (hn : n % 8 = 7) : (tyzDelta n * tyzDelta n + n) % 128 = 0 := by
  have h := tyzDelta_spec_aux (n % 128) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [← tyzDelta_mod] at h
  rw [Nat.add_mod, ← Nat.mod_mod n 128, ← Nat.add_mod]
  rw [Nat.add_mod] at h
  simpa [Nat.mod_mod] using h

theorem tyzDelta_dvd {n : ℕ} (hn : n % 8 = 7) :
    (128 : ℤ) ∣ (n : ℤ) + (tyzDelta n : ℤ) ^ 2 := by
  have h := Nat.dvd_of_mod_eq_zero (tyzDelta_spec hn)
  have h' : ((128 : ℕ) : ℤ) ∣ ((tyzDelta n * tyzDelta n + n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
  push_cast at h'
  rw [pow_two, add_comm]
  exact h'

/-- **TYZ's class-7 Heegner form** `[(n+δ²)/4, δ, 1]` (level 32, discriminant `−n`): the fixed point
of TYZ's embedding `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]` (L1203–1205) solves `(n+δ²)h² + 4δh + 4 = 0`. -/
def tyzForm7 (n : ℕ) (hn : n % 8 = 7) : HeegnerForm 32 (-(n : ℤ)) where
  A := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 4
  B := tyzDelta n
  C := 1
  A_pos := by
    have := tyzDelta_dvd hn
    have h0 : (0 : ℤ) ≤ (tyzDelta n : ℤ) ^ 2 := by positivity
    have h7 : (7 : ℤ) ≤ n := by have : 7 ≤ n := by omega
                                exact_mod_cast this
    omega
  N_dvd := by
    have := tyzDelta_dvd hn
    omega
  disc := by
    have := tyzDelta_dvd hn
    omega
  D_neg := by
    have : (0 : ℤ) < n := by have : 0 < n := by omega
                             exact_mod_cast this
    omega
  primitive := by simp

/-- **`z_n = f_n(P_n)` for `n ≡ 7 (mod 8)`** (TYZ L1196: `f_n = i₀`), the Heegner point of
`tyzForm7 n` on `A = X₀(32)` (junk `0` otherwise). -/
def tyzZ7 (n : ℕ) : PtA :=
  if hn : n % 8 = 7 then heegnerPt (tyzForm7 n hn) else 0

/-! ## §2. Artin symbols of an arbitrary order, lifted to `ℚ̄` -/

section ArtinO

variable (d : ℕ) [NeZero d] (O : NumberFieldOrder (QNeg d))

/-- `ρ ∈ Gal(ℚ̄/ℚ)` acts on the ring class field of `O` (inside `ℚ̄` through ring-class's `embed d`)
as Tau Ceti's Artin symbol of `c ∈ Pic(O)` (for `O = O4 d` the same shape as `Package.ActsAsArtin4`). -/
def ActsAsArtinO (ρ : GalQ) (c : Pic O) : Prop :=
  ∀ x : ringClassField O, ρ (embed d (x : SeparableClosure (QNeg d))) =
    embed d ((ringClassArtinEquiv O c x : ringClassField O) : SeparableClosure (QNeg d))

/-- The ring class field restricted to `ℚ`-scalars. -/
abbrev RQ : IntermediateField ℚ (SeparableClosure (QNeg d)) := (ringClassField O).restrictScalars ℚ

/-- The ring automorphism of the ring class field (as `ℚ`-subfield) given by `g`. -/
def gQO (g : Gal(ringClassField O/QNeg d)) : RQ d O ≃+* RQ d O := g.toRingEquiv

/-- The induced automorphism of its image in `ℚ̄`. -/
def gBarO (g : Gal(ringClassField O/QNeg d)) : (RQ d O).map (embed d) ≃ₐ[ℚ] (RQ d O).map (embed d) :=
  AlgEquiv.ofRingEquiv (f := ((IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv.symm.trans
    ((gQO d O g).trans (IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv)))
    (fun q => by simp)

/-- **Every element of `Gal(ring class field / K_d)` is induced by an automorphism of `ℚ̄`** (the
proof of cm-points' `exists_actsAsArtin4`, for an arbitrary order). -/
theorem exists_actsAsArtinO (c : Pic O) : ∃ ρ : GalQ, ActsAsArtinO d O ρ c := by
  let χ := gBarO d O (ringClassArtinEquiv O c)
  refine ⟨AlgEquiv.ofBijective (χ.toAlgHom.liftNormal Qbar) (AlgHom.normal_bijective _ _ _ _), ?_⟩
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) =
      algebraMap ((RQ d O).map (embed d)) Qbar (IntermediateField.equivMap (RQ d O) (embed d) x) := rfl
  rw [AlgEquiv.ofBijective_apply, hx, AlgHom.liftNormal_commutes]
  have e : χ (IntermediateField.equivMap (RQ d O) (embed d) x) =
      IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c x) := by
    simp only [χ, gBarO, gQO, AlgEquiv.ofRingEquiv_apply]
    change IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c
      ((IntermediateField.equivMap (RQ d O) (embed d)).symm
        (IntermediateField.equivMap (RQ d O) (embed d) x))) = _
    have h := AlgEquiv.symm_apply_apply (IntermediateField.equivMap (RQ d O) (embed d))
      (show ↥(RQ d O) from x)
    exact congrArg (fun y : ↥(RQ d O) => IntermediateField.equivMap (RQ d O) (embed d)
      (show ↥(RQ d O) from ringClassArtinEquiv O c (show ↥(ringClassField O) from y))) h
  show algebraMap _ Qbar (χ (IntermediateField.equivMap (RQ d O) (embed d) x)) = _
  rw [e]
  rfl

end ArtinO

/-! ## §3. The class-7 genus point -/

/-- The maximal order of `K_d = ℚ(√−d)`; its ring class field is ring-class's `hilbertField d`. -/
abbrev OK (d : ℕ) [NeZero d] : NumberFieldOrder (QNeg d) := maximalNumberFieldOrder (QNeg d)

/-- A fixed lift to `ℚ̄` of the Artin symbol of `c ∈ Cl(K_d)` on the Hilbert class field. -/
def liftMax (d : ℕ) [NeZero d] (c : Pic (OK d)) : GalQ := (exists_actsAsArtinO d (OK d) c).choose

theorem liftMax_spec (d : ℕ) [NeZero d] (c : Pic (OK d)) : ActsAsArtinO d (OK d) (liftMax d c) c :=
  (exists_actsAsArtinO d (OK d) c).choose_spec

/-- `2Cl_d = Cl(K_d)²` as a finite set. -/
def sqClasses (d : ℕ) [NeZero d] : Finset (Pic (OK d)) :=
  ((picSquares (OK d) : Subgroup (Pic (OK d))) : Set (Pic (OK d))).toFinite.toFinset

/-- **TYZ's class-7 genus point** `Z(e) = Σ_{t ∈ 2Cl_e} z_e^t` (L1316–1318 with `σ = 1`, L1268;
`Φ₀ = 2Cl_e` since `H'_e = H_e`, Prop 3.2(3)), each `t` realized by `liftMax`. On `A(H_e)` the value
does not depend on the lifts (`z_e ∈ A(H_e)` is the leaf `CMFieldOfDefinition7`). Junk `0` at `e = 0`. -/
def Z7 (e : ℕ) : PtA :=
  if h : e = 0 then 0 else
    haveI : NeZero e := ⟨h⟩
    ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e)

/-! ## §4. TYZ's sets `Φ₀` for class 5, pinned -/

/-- `T` is a choice of TYZ's `Φ₀` for `e ≡ 5 (mod 8)` (L1316–1317): every `ρ ∈ T` acts on `H_{e,4}`
as the Artin symbol of a square class (so its restriction to `H'_e` lies in `2Cl'_e`), and over each
element of `2Cl_e = Cl(K_e)²` (acting on the Hilbert class field) lies exactly one `ρ ∈ T`; i.e. `T`
represents `2Cl'_e/⟨σ⟩ ≅ 2Cl_e` (L1270–1272). -/
def IsPhi0 (e : ℕ) [NeZero e] (T : Finset GalQ) : Prop :=
  (∀ ρ ∈ T, ∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧
    ∀ c' ∈ picSquares (OK e), ∃! ρ, ρ ∈ T ∧ ActsAsArtinO e (OK e) ρ c'

open Classical in
/-- **TYZ's `Φ₀` for class 5, pinned by choice** (the `∅` branches are never taken for `e ≠ 0`:
`phi0_spec : IsPhi0 e (Phi0 e)`, §9, from the extension of automorphisms `H_e → H_{e,4}`; TYZ
L1270–1276). TYZ: Lemma 3.21 holds for any choice (L2547–2554). -/
def Phi0 (e : ℕ) : Finset GalQ :=
  if h0 : e = 0 then ∅ else
    haveI : NeZero e := ⟨h0⟩
    if h : ∃ T : Finset GalQ, IsPhi0 e T then h.choose else ∅

/-- **TYZ's genus points, every one pinned**: `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)` for `e ≡ 5 (mod 8)` and
`Z7 e` otherwise. -/
def tyzZ : ℕ → PtA := tyzGenusPt Phi0 Z7

theorem tyzZ_five {e : ℕ} (he : e % 8 = 5) : tyzZ e = genusSum (Phi0 e) (tyzZn e) := by
  simp only [tyzZ, tyzGenusPt, he, ↓reduceIte]

theorem tyzZ_seven {e : ℕ} (he : e % 8 = 7) : tyzZ e = Z7 e := by
  have : ¬ e % 8 = 5 := by omega
  simp only [tyzZ, tyzGenusPt, this, ↓reduceIte]

/-! ## §5. The leaves about the pinned genus points -/

/-- The Hilbert class field `H_d ⊂ ℚ̄` (`⊥` at `d = 0`). -/
def hilbertBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((hilbertField d).restrictScalars ℚ).map (embed d)

/-- **Leaf CM-2-7 (field of definition of TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
`z_n` (the Heegner point of `[(n+δ²)/4, δ, 1]`, maximal order, discriminant `−n`) is defined over the
Hilbert class field `H_n`. Classical case of Shimura's reciprocity law (conductor 1, prime to `N`):
Gross, *Heegner points on X₀(N)* (1984) §1–3; Gross–Zagier (1986) II §1; Shimura (1971) Thm. 5.7
(UNVERIFIED numbers); TYZ Prop. 3.2(3) (`H'_n = H_n`, L1260, VERIFIED read). Refereed. Numerically
the coordinates generate exactly `H_n` for n = 7, …, 71 (`class7.out`). Instance of
`CM.CMFieldOfDefinition` at `D = −n`, `H(−n) = H_n`. -/
def CMFieldOfDefinition7 : Prop :=
  ∀ n : ℕ, n % 8 = 7 → Squarefree n → tyzZ7 n ∈ ptsOver (hilbertBar n)

/-- **Leaf TYZ-2558 (field of definition of the class-7 genus point)**: for squarefree `e ≡ 7
(mod 8)`, `Z(e) ∈ A(L_e(i))`, `L_e(i) = ℚ(i, √p : p ∣ e)`. TYZ L2558 ("`H_n' = H_n` and thus `Z(n)` is
already defined over `L_n`", n ≡ 7), from `z_n ∈ A(H_n)` and genus theory (the subfield of `H_e` fixed
by `2Cl_e` is the genus field `ℚ(√p* : p ∣ e) ⊆ L_e(i)`, L2525). Refereed. Proved as glue below
(`class7GenusPtDefined_of`). Numerically the coordinates of `Z(e)` lie in `ℚ(√p* : p ∣ e)` for 12
values of `e` (`lemma321_7.out`). -/
def Class7GenusPtDefined : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → Z7 e ∈ ptsOver (Lni e)

/-- **Leaf TYZ-3.21(4) (pinned)**: for squarefree `e ≡ 7 (mod 8)` and every `σ` acting on the
quadratic fields as `β₁` (`IsBetaOneLift`), `Z(e)^{σ} + Z(e) = g(e)·τ(1/2)`. TYZ Lemma 3.21(4)
(L2514–2516, "for any lifting"); since `Z(e) ∈ A(L_e(i))` (multiquadratic) the action of `σ` on it
only depends on `IsBetaOneLift`, so this follows from TYZ's statement with `Class7GenusPtDefined`.
Refereed. VERIFIED numerically for e = 7, 15, …, 103 (12 values, `lemma321_7.out`). -/
def Lemma321Seven : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → ∀ σ : GalQ, IsBetaOneLift σ →
    galPt σ (Z7 e) + Z7 e = (gNat e : ℤ) • tauG 1

/-- **Leaf TYZ-3.21(1) (pinned)**: for squarefree `n ≡ 5 (mod 8)` there is `σ` with
`IsBetaOneLift σ` such that `Z(e)^{σ} + Z(e) ∈ g(e)τ((1−i)/2) + ℤτ(1)` for every `e ∣ n`,
`e ≡ 5 (mod 8)`, `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)`. TYZ Lemma 3.21(1) (L2496–2512, for any lifting `β'`
and any choice of `Φ₀`, L2547–2554). Refereed. VERIFIED numerically for n = 5, 13, 37 with both
choices `Φ₀ = {1}, {σ}` and 8 lifts each (`lemma321_5.out`; uses ShimuraReciprocity). -/
def Lemma321Five : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      ∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (tyzZ e) + tyzZ e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2

/-! ## §6. Glue: the split of `GenusPointLeafCM` -/

theorem lemma321_of (h5 : Lemma321Five) (h7 : Lemma321Seven) : Lemma321 tyzZ := by
  intro n hn hsq
  obtain ⟨σ, hσ, h5'⟩ := h5 n hn hsq
  refine ⟨σ, hσ, h5', fun e he he7 => ?_⟩
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  rw [tyzZ_seven he7]
  exact h7 e he7 hse σ hσ

theorem genusPtsDefined_tyzZ (hz : TYZZnOverHprime) (hN : HprimeNormal) (h7 : Class7GenusPtDefined) :
    GenusPtsDefined HHprime tyzZ :=
  genusPtsDefined_of hz hN Phi0 tyzZ (fun e he => tyzZ_five he)
    (fun e he hsq => by rw [tyzZ_seven he]; exact h7 e he hsq)

/-- **`GenusPointLeafCM` from the pinned leaves** (witnesses `Φ := Phi0`, `Z7 := Z7`). -/
theorem genusPointLeafCM_of_pinned {ℓ : ℕ → ℤ} (h7 : Class7GenusPtDefined)
    (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) : GenusPointLeafCM ℓ := by
  intro n hn hsq
  obtain ⟨ε, hε, hP⟩ := h35 n hn hsq
  obtain ⟨σ, hσ, h5, h7'⟩ := h321 n hn hsq
  refine ⟨Phi0, Z7, fun e he he7 => h7 e he7 (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)),
    ⟨ε, hε, hP⟩, σ, hσ, h5, h7'⟩

/-- **`GenusPointLeaf` via cm-points' `genusPointLeaf_of_split`**, for the pinned genus points. -/
theorem genusPointLeaf_of_pinned {ℓ : ℕ → ℤ} (hz : TYZZnOverHprime) (hN : HprimeNormal)
    (h7 : Class7GenusPtDefined) (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) :
    GenusPointLeaf ℓ HHprime :=
  genusPointLeaf_of_split (genusPtsDefined_tyzZ hz hN h7) h35 h321

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, every genus point pinned.** The premise `TYZThm35ReadingA` from the three
`𝓛`-leaves, the CM leaves `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`,
TYZ Lemma 3.18 (literal) and the closed leaves about the pinned genus points `tyzZ`:
`Class7GenusPtDefined` (TYZ L2458), `Thm35First ℓ tyzZ` (TYZ Thm 3.3/3.5), `Lemma321Five`
(TYZ Lemma 3.21(1)) and `Lemma321Seven` (TYZ Lemma 3.21(4)). No existential over genus points
remains. -/
theorem tyzThm35ReadingA_of_pinned (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_ringClass h11 h1 h29 tyzZ hN ((lemma318_iff_literal HHprime).mpr h318)
    (genusPtsDefined_tyzZ (tyzZnOverHprime_of hcm hi hs) hN h7) h35 (lemma321_of h5 h7')

open ZInQ.Contrib.TYZDecomp in
/-- The same, through cm-points' `tyzThm35ReadingA_of_cmLeaves` (consistency check: the pinned
leaves imply cm-points' bundled `GenusPointLeafCM`). -/
theorem tyzThm35ReadingA_of_pinned' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves h11 h1 h29 hcm hi hs hN h318
    fun ℓ hℓ => genusPointLeafCM_of_pinned h7 (h35 ℓ hℓ) (lemma321_of h5 h7')

/-! ## §7. `TYZSigmaFixesZn` from the shape of the Galois action (computation) -/

/-- `τ(1) = (0, 0)` is fixed by `[i]`, so `(1 − [i])` kills it. -/
theorem sub_iPt_pt00 : pt00 - iPt pt00 = 0 := by rw [iPt_pt00, sub_self]

/-- Points of `H'_d ⊂ ℚ̄` are fixed by every `ρ` acting on `H_{d,4}` as `σ_{1+2ϖ}` (the easy
direction of the Galois correspondence; converse: cm-points' `mem_Hprimebar_of_fixed`). -/
theorem fixed_of_mem_Hprimebar (d : ℕ) [NeZero d] {x : Qbar} (hx : x ∈ Hprimebar d) (ρ : GalQ)
    (hρ : ActsAsArtin4 ρ d (sigmaClass d)) : ρ x = x := by
  rw [Hprimebar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ H4 d := Hprime_le_H4 d hy
  have h1 : ρ (embed d y) =
      embed d ((artin4 d (sigmaClass d) ⟨y, hy'⟩ : H4 d) : SeparableClosure (QNeg d)) := hρ ⟨y, hy'⟩
  change ρ (embed d y) = embed d y
  rw [h1]
  congr 1
  have hy3 : (⟨y, hy'⟩ : H4 d).1 ∈ IntermediateField.lift
      (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d)))) := hy
  have hy2 := (IntermediateField.mem_lift _).mp hy3
  rw [IntermediateField.mem_fixedField_iff] at hy2
  exact congrArg Subtype.val (hy2 _ (Subgroup.mem_zpowers _))

/-- **Leaf GT' (`i ∈ H'_n`)**: for squarefree `n ≡ 5 (mod 8)`, `i ∈ H'_n`. Genus theory (`i` lies in
the genus field of `ℚ(√−n)`, hence in `H_n`; Cox Thm 6.1, UNVERIFIED number) and `H_n ⊆ H'_n` (TYZ
Prop. 3.2(1): `σ_{1+2ϖ} ∈ Gal(H_{n,4}/H_n)`, L1253–1256). Refereed (textbook + TYZ). -/
def IInHprime : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ Hprimebar n

/-- **Leaf TYZ-3.7(1)+SR (the Galois action of `σ_{1+2ϖ}` on `f₀(P_n)` is translation by
`τ(1) = (0,0)`)**. Consequence of TYZ's Proposition `heckeaction5`(1) (L1488–1490: `Q^{1+2ϖ} = Q + τ(1)`
for every `Q ∈ X_U(ℂ)`; proposition number UNVERIFIED) and Shimura's reciprocity law at the CM point
`P_n` (`σ_t P_n = P_n^t`), `f₀` being defined over `ℚ`. Refereed. VERIFIED numerically for
n = 5, 13, 21, 29, 37 (3 primes each, `sigma5.out`, through `CM.ShimuraReciprocity`, whose direction is
VERIFIED in `shimura.out`). Unlike `TYZSigmaFixesZn` (printed as TYZ Thm 3.6(1), L1413) it does not
involve the `[i]`-sign of `CM.tyzZn`. -/
def TYZSigmaShiftsF0 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzHeegnerPt n) = tyzHeegnerPt n + pt00

/-- **`TYZSigmaFixesZn` from `TYZSigmaShiftsF0` and `i ∈ H'_n`** (glue): `ρ` fixes `i`, so it commutes
with `[i]`, and `(1 − [i])(f₀ + (0,0)) = (1 − [i])f₀`. -/
theorem tyzSigmaFixesZn_of (hsh : TYZSigmaShiftsF0) (hi : IInHprime) : TYZSigmaFixesZn := by
  intro n hn0 hn hsq ρ hρ
  have hρi : ρ iQ = iQ := fixed_of_mem_Hprimebar n (hi n hn hsq) ρ hρ
  have e := hsh n hn0 hn hsq ρ hρ
  unfold tyzZn
  rw [map_sub, galPt_iPt ρ hρi, e, iPt_add, iPt_pt00]
  abel

/-! ## §8. `Class7GenusPtDefined` from the CM field of definition and genus theory -/

section Class7Descent

/-- `galPt` is multiplicative: `(στ)(P) = σ(τ(P))`. -/
theorem galPt_mul (σ τ : GalQ) (P : PtA) : galPt (σ * τ) P = galPt σ (galPt τ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some (σ * τ) h
    obtain ⟨h2, e2⟩ := galPt_some τ h
    obtain ⟨h3, e3⟩ := galPt_some σ h2
    rw [e1, e2, e3, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨AlgEquiv.mul_apply σ τ x, AlgEquiv.mul_apply σ τ y⟩

/-- Two automorphisms agreeing on `K` act identically on `A(K)`. -/
theorem galPt_congr {K : IntermediateField ℚ Qbar} {ρ ρ' : GalQ} (h : ∀ x ∈ K, ρ x = ρ' x)
    {P : PtA} (hP : P ∈ ptsOver K) : galPt ρ P = galPt ρ' P := by
  rw [mem_ptsOver_iff] at hP
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some ρ hxy
    obtain ⟨h2, e2⟩ := galPt_some ρ' hxy
    rw [e1, e2, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨h x hP.1, h y hP.2⟩

variable (d : ℕ) [NeZero d]

theorem hilbertBar_eq : hilbertBar d = ((hilbertField d).restrictScalars ℚ).map (embed d) := by
  simp only [hilbertBar, NeZero.ne d, ↓reduceDIte]

variable {d}

theorem actsO_mem {ρ : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c) {x : Qbar}
    (hx : x ∈ hilbertBar d) : ρ x ∈ hilbertBar d := by
  rw [hilbertBar_eq] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  change ρ (embed d y) ∈ _
  rw [h1]
  exact ⟨_, (ringClassArtinEquiv (OK d) c ⟨y, hy⟩).2, rfl⟩

theorem actsO_agree {ρ ρ' : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c) : ∀ x ∈ hilbertBar d, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  have h2 : ρ' (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ' ⟨y, hy⟩
  change ρ (embed d y) = ρ' (embed d y)
  rw [h1, h2]

theorem actsO_mul {ρ ρ' : GalQ} {c c' : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c') : ActsAsArtinO d (OK d) (ρ * ρ') (c * c') := by
  intro x
  rw [AlgEquiv.mul_apply, hρ' x, hρ (ringClassArtinEquiv (OK d) c' x), map_mul, AlgEquiv.mul_apply]

theorem mem_sqClasses {c : Pic (OK d)} : c ∈ sqClasses d ↔ c ∈ picSquares (OK d) := by
  simp [sqClasses]

theorem sum_sqClasses_mul {s : Pic (OK d)} (hs : s ∈ picSquares (OK d)) (f : Pic (OK d) → PtA) :
    ∑ c ∈ sqClasses d, f (s * c) = ∑ c ∈ sqClasses d, f c := by
  refine Finset.sum_nbij' (fun c => s * c) (fun c => s⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem hs hc
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem ((picSquares (OK d)).inv_mem hs) hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem Z7_eq (e : ℕ) [NeZero e] : Z7 e = ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e) := by
  simp only [Z7, NeZero.ne e, ↓reduceDIte]

theorem Z7_mem {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) :
    Z7 e ∈ ptsOver (hilbertBar e) := by
  rw [Z7_eq]
  exact (ptsOver _).sum_mem fun c _ =>
    galPt_mem (liftMax e c) (fun x hx => actsO_mem (liftMax_spec e c) hx) hz

/-- **The lifts of `2Cl_e` fix `Z(e)`** (reindexing the genus sum; the lifts act on `A(H_e)` through
their Artin symbols). -/
theorem galPt_Z7 {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) {s : Pic (OK e)}
    (hs : s ∈ picSquares (OK e)) : galPt (liftMax e s) (Z7 e) = Z7 e := by
  rw [Z7_eq, map_sum]
  have : ∀ c ∈ sqClasses e, galPt (liftMax e s) (galPt (liftMax e c) (tyzZ7 e)) =
      galPt (liftMax e (s * c)) (tyzZ7 e) := fun c _ => by
    rw [← galPt_mul]
    exact galPt_congr (actsO_agree (actsO_mul (liftMax_spec e s) (liftMax_spec e c))
      (liftMax_spec e (s * c))) hz
  rw [Finset.sum_congr rfl this, sum_sqClasses_mul hs (fun c => galPt (liftMax e c) (tyzZ7 e))]

/-- The genus field `G_d ⊂ ℚ̄` of `K_d` (ring-class's `genusField` of the maximal order: the subfield
of `H_d` fixed by `2Cl_d`), `⊥` at `d = 0`. -/
def genusBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((genusField (OK d)).restrictScalars ℚ).map (embed d)

/-- **Galois descent `H_d → G_d`**: a point of `H_d ⊂ ℚ̄` fixed by the lifts of `2Cl_d` lies in the
genus field. -/
theorem mem_genusBar_of_fixed {x : Qbar} (hx : x ∈ hilbertBar d)
    (hfix : ∀ s ∈ picSquares (OK d), liftMax d s x = x) : x ∈ genusBar d := by
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hg : genusBar d = ((genusField (OK d)).restrictScalars ℚ).map (embed d) := by
    simp only [genusBar, NeZero.ne d, ↓reduceDIte]
  rw [hg]
  refine ⟨y, ?_, rfl⟩
  show y ∈ genusField (OK d)
  rw [genusField, show y = (⟨y, hy⟩ : ringClassField (OK d)).1 from rfl, IntermediateField.mem_lift,
    IntermediateField.mem_fixedField_iff]
  rintro f ⟨s, hs, rfl⟩
  have h1 : liftMax d s (embed d y) = embed d ((ringClassArtinEquiv (OK d) s ⟨y, hy⟩ :
      ringClassField (OK d)) : SeparableClosure (QNeg d)) := liftMax_spec d s ⟨y, hy⟩
  have h0 : liftMax d s (embed d y) = embed d y := hfix s hs
  rw [h0] at h1
  exact Subtype.ext ((embed d).injective h1).symm

/-- **Leaf GT-7 (genus theory)**: for squarefree `e ≡ 7 (mod 8)` the genus field of `ℚ(√−e)` (the
subfield of the Hilbert class field fixed by `Cl²`) lies in `L_e(i) = ℚ(i, √p : p ∣ e)`; it is
`ℚ(√p* : p ∣ e)`, `p* = (−1)^{(p−1)/2} p` (Gauss; Cox, *Primes of the form x² + ny²*, Thm. 6.1 and
§6.C, UNVERIFIED numbers; TYZ L2525 uses it). Refereed (textbook). -/
def GenusFieldLeLni : Prop := ∀ e : ℕ, e % 8 = 7 → Squarefree e → genusBar e ≤ Lni e

/-- **`Class7GenusPtDefined` is glue** from the field of definition of TYZ's class-7 CM point
(`CMFieldOfDefinition7`, Gross/Shimura) and genus theory (`GenusFieldLeLni`). -/
theorem class7GenusPtDefined_of (hcm : CMFieldOfDefinition7) (hg : GenusFieldLeLni) :
    Class7GenusPtDefined := by
  intro e he hsq
  have : NeZero e := ⟨by omega⟩
  have hz := hcm e he hsq
  have hZ := Z7_mem hz
  have hfix : ∀ s ∈ picSquares (OK e), galPt (liftMax e s) (Z7 e) = Z7 e :=
    fun s hs => galPt_Z7 hz hs
  rw [mem_ptsOver_iff] at hZ ⊢
  revert hZ hfix
  rcases Z7 e with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hZ hfix
    have hc : ∀ s ∈ picSquares (OK e), liftMax e s x = x ∧ liftMax e s y = y := by
      intro s hs
      have e1 := hfix s hs
      obtain ⟨h', e'⟩ := galPt_some (liftMax e s) h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e1
      exact e1
    exact ⟨hg e he hsq (mem_genusBar_of_fixed hZ.1 fun s hs => (hc s hs).1),
      hg e he hsq (mem_genusBar_of_fixed hZ.2 fun s hs => (hc s hs).2)⟩

end Class7Descent

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, finest form**: as `tyzThm35ReadingA_of_pinned`, with `Class7GenusPtDefined`
replaced by the textbook leaves `CMFieldOfDefinition7` and `GenusFieldLeLni`. -/
theorem tyzThm35ReadingA_of_pinnedLeaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (hcm7 : CMFieldOfDefinition7)
    (hg : GenusFieldLeLni) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinned h11 h1 h29 hcm hi hs hN h318 (class7GenusPtDefined_of hcm7 hg) h35 h5 h7'


/-! ## §9. Existence of TYZ's `Φ₀` (so `Phi0` is never the junk value) -/

section Phi0Exists

variable (e : ℕ) [NeZero e]

theorem hle : hilbertField e ≤ H4 e := hilbertLeH4 e inferInstance

instance : Normal (QNeg e) (SeparableClosure (QNeg e)) := inferInstance

/-- **Every element of `Gal(H_e/K_e)` extends to `Gal(H_{e,4}/K_e)`**: for `d' ∈ Cl(K_e)` there is
`c₄ ∈ Pic(O_{e,4})` whose Artin symbol restricts to that of `d'` on `H_e ⊆ H_{e,4}`. -/
theorem exists_restrict (d' : Pic (OK e)) : ∃ c4 : Pic (O4 e), ∀ x : hilbertField e,
    ((artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) : SeparableClosure (QNeg e)) =
      ((ringClassArtinEquiv (OK e) d' x : hilbertField e) : SeparableClosure (QNeg e)) := by
  let g := ringClassArtinEquiv (OK e) d'
  let τ : SeparableClosure (QNeg e) ≃ₐ[QNeg e] SeparableClosure (QNeg e) :=
    AlgEquiv.ofBijective (g.toAlgHom.liftNormal (SeparableClosure (QNeg e)))
      (AlgHom.normal_bijective _ _ _ _)
  refine ⟨(artin4 e).symm (AlgEquiv.restrictNormal τ (H4 e)), fun x => ?_⟩
  rw [MulEquiv.apply_symm_apply]
  have h1 := AlgEquiv.restrictNormal_commutes τ (H4 e) ⟨x, hle e x.2⟩
  have h2 := AlgHom.liftNormal_commutes g.toAlgHom (SeparableClosure (QNeg e)) x
  exact h1.trans h2

theorem exists_phi0_elem {c' : Pic (OK e)} (hc : c' ∈ picSquares (OK e)) :
    ∃ ρ : GalQ, (∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧ ActsAsArtinO e (OK e) ρ c' := by
  obtain ⟨d', rfl⟩ := hc
  obtain ⟨c4, hc4⟩ := exists_restrict e d'
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtin4 e (c4 ^ 2)
  refine ⟨ρ, ⟨c4 ^ 2, ⟨c4, rfl⟩, hρ⟩, fun x => ?_⟩
  have h := hρ ⟨x, hle e x.2⟩
  change ρ (embed e (x : SeparableClosure (QNeg e))) = _ at h
  rw [h]
  congr 1
  have hx1 := hc4 x
  have hx2 := hc4 (ringClassArtinEquiv (OK e) d' x)
  simp only [powMonoidHom_apply, pow_two, map_mul, AlgEquiv.mul_apply]
  rw [show (artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) =
      ⟨_, hle e (ringClassArtinEquiv (OK e) d' x).2⟩ from Subtype.ext hx1]
  exact hx2

open Classical in
/-- A fixed `ρ` for each square class (`exists_phi0_elem`). -/
def phi0Elem (c' : Pic (OK e)) : GalQ :=
  if h : c' ∈ picSquares (OK e) then (exists_phi0_elem e h).choose else 1

theorem artinO_inj {ρ : GalQ} {c c' : Pic (OK e)} (h : ActsAsArtinO e (OK e) ρ c)
    (h' : ActsAsArtinO e (OK e) ρ c') : c = c' := by
  apply (ringClassArtinEquiv (OK e)).injective
  ext x
  have := (h x).symm.trans (h' x)
  rw [(embed e).injective this]

/-- **TYZ's `Φ₀` exists** (TYZ L1270–1276), so `Phi0 e` satisfies `IsPhi0`. -/
theorem exists_isPhi0 : ∃ T : Finset GalQ, IsPhi0 e T := by
  classical
  refine ⟨(sqClasses e).image (phi0Elem e), ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc'
    rw [phi0Elem, dite_eq_left hc']
    exact (exists_phi0_elem e hc').choose_spec.1
  · intro c' hc'
    have hspec : ∀ c ∈ picSquares (OK e), ActsAsArtinO e (OK e) (phi0Elem e c) c := fun c hc => by
      rw [phi0Elem, dite_eq_left hc]
      exact (exists_phi0_elem e hc).choose_spec.2
    refine ⟨phi0Elem e c', ⟨Finset.mem_image.mpr ⟨c', mem_sqClasses.mpr hc', rfl⟩, hspec c' hc'⟩, ?_⟩
    rintro ρ ⟨hρ, hρc⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc
    rw [artinO_inj e (hspec c hc) hρc]

theorem phi0_spec : IsPhi0 e (Phi0 e) := by
  classical
  have h := exists_isPhi0 e
  simp only [Phi0, NeZero.ne e, ↓reduceDIte, h]
  exact h.choose_spec

end Phi0Exists


/-! ## §10. Rewiring to ring-class's theorems (cm-bridge) -/

section Rewire

open ZInQ.Contrib.TYZGenus.RingClassBridge

/-- **`i ∈ H'_n`** (cm-numeric's leaf `IInHprime`), proved: `i ∈ L_n(i) ⊆ H'_n` (ring-class's
`Lni_le_Hprimebar`, genus theory via Bauer + quadratic reciprocity). -/
theorem iInHprime : IInHprime := by
  intro n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  exact Lni_le_Hprimebar (by omega) hsq (iQ_mem_Lni n)

/-- **`CMFieldOfDefinition7` from the general CM leaf** `CM.CMFieldOfDefinition ringClassFieldD`
(instance `D = −n`, `Q = tyzForm7 n`): the ring class field of discriminant `−n` is the Hilbert
class field for squarefree `n ≡ 3 (mod 4)` (ring-class's `ringClassFieldD_neg`). -/
theorem cmFieldOfDefinition7_of (h : CM.CMFieldOfDefinition ringClassFieldD) :
    CMFieldOfDefinition7 := by
  intro n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have h1 := h (-(n : ℤ)) (tyzForm7 n hn)
  have hr := ringClassFieldD_neg (d := n) (by omega) hsq
  simp only [tyzZ7, hn, ↓reduceDIte]
  rw [hilbertBar_eq]
  convert h1 using 2
  exact hr.symm

/-- `TYZSigmaFixesZn` from the printed Hecke-action identity alone (`IInHprime` is now proved). -/
theorem tyzSigmaFixesZn_of' (hsh : TYZSigmaShiftsF0) : TYZSigmaFixesZn :=
  tyzSigmaFixesZn_of hsh iInHprime

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after the rewiring** (`GenusFieldLeLni` still a hypothesis): reading A of TYZ
Theorem 3.5 from the three `𝓛`-leaves, the general CM leaf `CM.CMFieldOfDefinition ringClassFieldD`,
`TYZSigmaShiftsF0` (TYZ Prop. 3.7(1) + Shimura reciprocity), TYZ Lemma 3.18 (literal),
`GenusFieldLeLni` (genus theory), `Thm35First ℓ tyzZ` (TYZ Thm 3.3/3.5), `Lemma321Five`,
`Lemma321Seven` (TYZ Lemma 3.21(1),(4)). `IInH4`, `HprimeNormal`, `IInHprime`,
`CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7` and `TYZSigmaFixesZn` are gone. -/
theorem tyzThm35ReadingA_of_rewired (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime) (hg : GenusFieldLeLni)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinnedLeaves h11 h1 h29 (cmFieldTYZ_of_ringClassD hcm) iInH4
    (tyzSigmaFixesZn_of' hsh) hprimeNormal h318 (cmFieldOfDefinition7_of hcm) hg h35 h5 h7'

end Rewire


/-! ## §11. `GenusFieldLeLni` proved (genus theory for `n ≡ 3 (mod 4)`)

For squarefree `n ≡ 3 (mod 4)`: a prime `𝔭 ∤ 2n` of `K_n` that splits completely in
`K_n(i, √p : p ∣ n)` has `−1` and every `p ∣ n` square mod `𝔭`, so `|O/𝔭| ≡ 1 (mod 4)` and
`(|O/𝔭| / p) = 1` (quadratic reciprocity, `FiniteField.isSquare_odd_prime_iff`); all genus
characters `χ_p` vanish on `[𝔭]`, so `[𝔭] ∈ Cl²` (`picSquares_eq_iInf_ker_chi`), i.e. `𝔭` splits in the
genus field. Bauer's theorem (`le_of_splitSet_diff_subset`) gives `G_n ⊆ K_n(i, √p : p ∣ n)`, and the
latter maps into `L_n(i)` (it contains `√−n = ±i∏√p`). -/

section GenusSeven

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

/-- The Picard class (Tau Ceti) of an ideal for the maximal order is its ideal class. -/
theorem picClass_maximal {K : Type} [Field K] [NumberField K]
    (J : integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    (maximalNumberFieldOrder K).picClass J =
      (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  rw [picClass_apply, ← ClassGroup.mk_mk0 K]
  congr 1
  apply Units.ext
  rw [coe_integralIdealsAwayConductorToInvertible_apply, FractionalIdeal.coe_mk0]
  congr 1
  ext x
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨(⟨x.1, x.2⟩ : 𝓞 K), (maximalNumberFieldOrder K).mem_toRingOfIntegers.mpr x.2⟩, hx, rfl⟩



variable {n : ℕ} [NeZero n]

/-- The square-root generators of `L_n(i)`: `−1` and the primes `p ∣ n`. -/
def sqrtSet (n : ℕ) : Finset ℤ := insert (-1) (n.primeFactors.image (fun p : ℕ => (p : ℤ)))

/-- `K_n(i, √p : p ∣ n) ⊆ K_nˢ`. -/
def genusAmb (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.adjoin (QNeg n) (sqrtK (QNeg n) '' (sqrtSet n : Set ℤ))

theorem adjSqrt_le_genusAmb {a : ℤ} (ha : a ∈ sqrtSet n) : adjSqrt (QNeg n) a ≤ genusAmb n :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 ha)))

instance : FiniteDimensional (QNeg n) (genusAmb n) :=
  IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact isIntegral_sqrtK _ a

instance : Normal (QNeg n) (genusAmb n) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [genusAmb, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h : g (sqrtK (QNeg n) a) ^ 2 = sqrtK (QNeg n) a ^ 2 := by
    rw [← map_pow, sqrtK_sq, map_intCast]
  have hmem : sqrtK (QNeg n) a ∈ genusAmb n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact hmem
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact neg_mem hmem

instance : IsGalois (QNeg n) (genusAmb n) := IsGalois.mk

/-- **Genus characters at a prime split in `K_n(i, √p : p ∣ n)`**: if `−1` and every `p ∣ n` are
squares modulo `𝔭 ∌ 2n`, then `χ_q([𝔭]) = 1` for every `q ∣ n` (`|O/𝔭| ≡ 1 (mod 4)` and
`(|O/𝔭| / q) = (q / |O/𝔭|) = 1`, quadratic reciprocity in Mathlib's finite-field form). -/
theorem chi_eq_one_of_isSquare (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hm1 : IsSquare (((-1 : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (hp : ∀ p ∈ n.primeFactors, IsSquare (((p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hchar : ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 := fun hc => h2 (by
    have : ((2 : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hqF : ((q : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 0 := by
    intro h0
    apply h2n
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors q.2
    have h1 : ((q : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    have e2 : 2 * n = 2 * m * (q : ℕ) := by rw [mul_assoc, mul_comm m, ← hm]
    rw [show ((2 * n : ℕ) : 𝓞 (QNeg n)) = ((2 * m * q : ℕ) : 𝓞 (QNeg n)) from congrArg _ e2,
      Nat.cast_mul]
    exact 𝔭.asIdeal.mul_mem_left _ h1
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  rw [Int.cast_neg, Int.cast_one, FiniteField.isSquare_neg_one_iff] at hm1
  have h4 : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) % 4 = 1 := by omega
  have hsqq := hp q q.2
  rw [Int.cast_natCast, FiniteField.isSquare_odd_prime_iff hchar hq2, ZMod.χ₄_nat_one_mod_four h4] at hsqq
  simp only [Int.cast_one, one_mul] at hsqq
  have hsquare : IsSquare ((Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) : ℕ) : ZMod q) := by
    by_contra hns
    exact hsqq (quadraticChar_neg_one_iff_not_isSquare.2 hns)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    have hpr : (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)).Prime := hk
    rw [hcard] at hd
    have := (Nat.prime_dvd_prime_iff_eq hqp hpr).1 (hqp.dvd_of_dvd_pow hd)
    apply hqF
    rw [this]
    exact ringChar.Nat.cast_ringChar
  have hb : ZInQ.RouteK.legBit q ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) = 0 := by
    unfold ZInQ.RouteK.legBit
    rw [if_pos]
    rw [hN, Int.cast_natCast]
    exact hsquare
  have hc := chi_mk0 n hn hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, hb]
  rfl

/-- Transfer along `conductorOrder K 1 = maximal order`, then genus theory
(`picSquares_eq_iInf_ker_chi`). -/
theorem picClass_mem_picSquares (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n)
    (O : NumberFieldOrder (QNeg n)) (hO : O = maximalNumberFieldOrder (QNeg n))
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal _)⁰)
    (hchi : ∀ q, chi n q (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩) = 1) :
    O.picClass J ∈ picSquares O := by
  subst hO
  rw [picClass_maximal J hJ0, picSquares_eq_iInf_ker_chi n hn hsq h1]
  exact Subgroup.mem_iInf.2 fun q => hchi q

/-- **The genus field of `K_n`, `n ≡ 3 (mod 4)` squarefree, lies in `K_n(i, √p : p ∣ n)`** (Bauer). -/
theorem genusField_le_genusAmb (hn : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) ≤ genusAmb n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hG : genusField (maximalNumberFieldOrder (QNeg n)) =
      ringSubfield (picSquares (conductorOrder (QNeg n) 1)) := by
    rw [← conductorOrder_one]; rfl
  rw [hG]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  rw [mem_splitSet_iff (conductorOrder (QNeg n) 1) _ ⟨_, hJ⟩ 𝔭 rfl]
  have hsplit : ∀ a ∈ sqrtSet n, 𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) a) := fun a ha =>
    splitSet_anti (adjSqrt_le_genusAmb ha) h𝔭
  have hm1 := (mem_splitSet_adjSqrt_iff 𝔭 (a := -1) (by
    intro h; apply h2
    have : -((2 * (-1) : ℤ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := 𝔭.asIdeal.neg_mem h
    simpa using this)).1 (hsplit (-1) (Finset.mem_insert_self _ _))
  have hp : ∀ p ∈ n.primeFactors,
      IsSquare (((p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)) := by
    intro p hp
    refine (mem_splitSet_adjSqrt_iff 𝔭 (a := p) ?_).1
      (hsplit p (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)))
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * (p : ℤ) : ℤ) : 𝓞 (QNeg n)) * (n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]; push_cast; ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  exact picClass_mem_picSquares hodd hsq h1 _ (conductorOrder_one _) ⟨_, hJ⟩
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot)
    (chi_eq_one_of_isSquare hodd hsq 𝔭 h2n hm1 hp)

/-! ### From `K_nˢ` to `ℚ̄` -/

theorem embed_sqrtK_mem_Lni {a : ℤ} (ha : a ∈ sqrtSet n) : embed n (sqrtK (QNeg n) a) ∈ Lni n := by
  apply IntermediateField.subset_adjoin
  have hs : embed n (sqrtK (QNeg n) a) ^ 2 = (a : Qbar) := by rw [← map_pow, sqrtK_sq, map_intCast]
  rcases Finset.mem_insert.1 ha with rfl | ha
  · left; simpa using hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    right; exact ⟨p, hp, by simpa using hs⟩

theorem embed_omega_mem_Lni (hsq : Squarefree n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) ∈ Lni n := by
  have hroot : ∀ p ∈ n.primeFactors, ∃ r : Qbar, r ^ 2 = (p : Qbar) := fun p _ =>
    IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose r hr using hroot
  set y := iQ * ∏ p ∈ n.primeFactors.attach, r p.1 p.2
  have hy : y ∈ Lni n := mul_mem (iQ_mem_Lni n) (prod_mem fun p _ =>
    IntermediateField.subset_adjoin _ _ (Or.inr ⟨p.1, p.2, hr _ _⟩))
  have hy2 : y ^ 2 = -(n : Qbar) := by
    rw [mul_pow, iQ_sq, ← Finset.prod_pow]
    have : ∏ p ∈ n.primeFactors.attach, r p.1 p.2 ^ 2 = ∏ p ∈ n.primeFactors.attach, ((p.1 : ℕ) : Qbar) :=
      Finset.prod_congr rfl fun p _ => hr _ _
    rw [this, Finset.prod_attach n.primeFactors (fun p => ((p : ℕ) : Qbar)), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
    ring
  have hw2 : (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ^ 2 =
      -(n : Qbar) := by
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hw2.trans hy2.symm) with h | h
  · rw [h]; exact hy
  · rw [h]; exact neg_mem hy

theorem embed_algebraMap_mem_Lni (hsq : Squarefree n) (k : QNeg n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k) ∈ Lni n := by
  rw [algebraMap_eq_re_im, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact add_mem (IntermediateField.algebraMap_mem _ _)
    (mul_mem (IntermediateField.algebraMap_mem _ _) (embed_omega_mem_Lni hsq))

/-- `L_n(i)` pulled back to `K_nˢ`, as a field over `K_n`. -/
def LniK (n : ℕ) [NeZero n] (hsq : Squarefree n) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  { ((Lni n).comap (embed n)) with
    algebraMap_mem' := fun k => embed_algebraMap_mem_Lni hsq k }

theorem mem_LniK (hsq : Squarefree n) {x : SeparableClosure (QNeg n)} :
    x ∈ LniK n hsq ↔ embed n x ∈ Lni n := Iff.rfl

theorem genusAmb_le_LniK (hsq : Squarefree n) : genusAmb n ≤ LniK n hsq := by
  rw [genusAmb, IntermediateField.adjoin_le_iff]
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_LniK hsq).2 (embed_sqrtK_mem_Lni ha)

/-- **Genus theory for `n ≡ 7 (mod 8)`** (cm-numeric's leaf `GenusFieldLeLni`), proved. -/
theorem genusFieldLeLni : GenusFieldLeLni := by
  intro e he hsq
  haveI : NeZero e := ⟨by omega⟩
  have hle := (genusField_le_genusAmb (n := e) (by omega) hsq (by omega)).trans
    (genusAmb_le_LniK hsq)
  simp only [genusBar, NeZero.ne e, ↓reduceDIte]
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_LniK hsq).1 (hle hx)



end GenusSeven

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after §10–§11**: as `tyzThm35ReadingA_of_rewired`, with `GenusFieldLeLni` proved. -/
theorem tyzThm35ReadingA_of_cmLeaves7 (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_rewired h11 h1 h29 hcm hsh h318 genusFieldLeLni h35 h5 h7'


/-! ## §12. `Lemma321Seven` reduced to TYZ Theorem 3.6(3) and the action of `β₁` on the genus field

TYZ's proof of Lemma 3.21(4) (L2547–2566): `Z(n)` is defined over the genus field `L_n`; on `L_n(i)`
any lift `β'` of `β₁` acts as `σ_ϖ ∘ c` (`c` complex conjugation), and `σ_ϖ = σ_{ϖ^5}` on `L_n`; so
`Z(n)^{β'} = Z(n)^{σ_{ϖ^5} ∘ c}`, and Theorem 3.6(3) (`z̄_n + z_n^{σ_{ϖ^5}} = τ(1/2)`) gives the
result after summing over `2Cl_n`. Here `σ_{ϖ^5}` (geometric normalization, L1247–1250) acts on the
Hilbert class field `H_n` as the arithmetic Artin symbol of `[𝔭₂]^{−5}`, `𝔭₂` TYZ's place `v₂`. -/

section Seven

open ZInQ.Contrib.TYZGenus.RingClassBridge
open scoped nonZeroDivisors

/-- `γ ∈ Gal(ℚ̄/ℚ)` is complex conjugation for `CM`'s fixed embedding `ιC : ℚ̄ → ℂ`. -/
def IsComplexConj (γ : GalQ) : Prop := ∀ x : Qbar, ιC (γ x) = starRingEnd ℂ (ιC x)

/-- **Complex conjugation exists in `Gal(ℚ̄/ℚ)`** (the image of `ιC` is normal over `ℚ`). -/
theorem exists_complexConj : ∃ γ : GalQ, IsComplexConj γ := by
  let f : Qbar →ₐ[ℚ] ℂ := ιCA
  let e : Qbar ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : Normal ℚ f.fieldRange := Normal.of_algEquiv e
  have hr : ∀ y ∈ f.fieldRange, conjQ y ∈ f.fieldRange := by
    intro y hy
    have h := AlgHom.fieldRange_of_normal (E := f.fieldRange) (conjQ.comp f.fieldRange.val)
    rw [← h]
    exact ⟨⟨y, hy⟩, rfl⟩
  let c : f.fieldRange →ₐ[ℚ] f.fieldRange :=
    (conjQ.comp f.fieldRange.val).codRestrict f.fieldRange.toSubalgebra fun y => hr y.1 y.2
  have hc : Function.Involutive c := fun y => Subtype.ext (by
    show conjQ (conjQ (y : ℂ)) = y
    simp [conjQ_apply])
  let c' : f.fieldRange ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofBijective c hc.bijective
  refine ⟨e.trans (c'.trans e.symm), fun x => ?_⟩
  have h1 : ∀ y : f.fieldRange, f (e.symm y) = y := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  show f (e.symm (c' (e x))) = starRingEnd ℂ (f x)
  rw [h1]
  rfl

theorem ιC_injective : Function.Injective ιC := ιC.injective

theorem IsComplexConj.mul_self {γ : GalQ} (hγ : IsComplexConj γ) (x : Qbar) : γ (γ x) = x :=
  ιC_injective (by rw [hγ, hγ, Complex.conj_conj])

theorem IsComplexConj.inv_apply {γ : GalQ} (hγ : IsComplexConj γ) (x : Qbar) : γ⁻¹ x = γ x := by
  apply γ.injective
  rw [hγ.mul_self]
  exact γ.apply_symm_apply x

/-- Complex conjugation moves `√−n`. -/
theorem IsComplexConj.ne_omega {γ : GalQ} (hγ : IsComplexConj γ) (n : ℕ) [NeZero n] :
    γ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ≠
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) := by
  set w := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  intro h
  have hw2 : w ^ 2 = -(n : Qbar) := by
    simp only [w]
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  have hc : starRingEnd ℂ (ιC w) = ιC w := by rw [← hγ, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 hc
  have h2 : (r : ℂ) ^ 2 = -(n : ℂ) := by rw [← hr, ← map_pow, hw2]; simp
  have h3 : r ^ 2 = -(n : ℝ) := by exact_mod_cast h2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith [sq_nonneg r]

/-- TYZ's place `v₂` for `n ≡ 7 (mod 8)` (Theorem 3.6(3), L1424–1425: the place above 2 with
`v₂(√−n − δ) ≥ 6`): the prime `𝔭₂ = (2, (√−n − δ)/2)` of `𝓞_{K_n}`, `δ = tyzDelta n`,
`(√−n − δ)/2 = θ − (δ+1)/2`, `θ = (1 + √−n)/2`. (`⊤` if `n % 4 ≠ 3`.) The binary form of `[𝔭₂]` is
`[2, δ mod 4, ·]` (used in `thm36_7.py`). -/
def p2Ideal (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) :=
  if h : n % 4 = 3 then
    Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
  else ⊤

theorem p2Ideal_mem (n : ℕ) [NeZero n] : p2Ideal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  unfold p2Ideal
  split_ifs with h
  · intro h0
    have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h -
        (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))} := Ideal.subset_span (by simp)
    rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
    exact two_ne_zero h2
  · exact top_ne_bot

/-- The class `[𝔭₂] ∈ Cl(K_n) = Pic(𝓞_{K_n})`. -/
def p2Class (n : ℕ) [NeZero n] : Pic (OK n) :=
  (ClassGroup.mk0 ⟨p2Ideal n, p2Ideal_mem n⟩ : ClassGroup (𝓞 (QNeg n)))

/-- **Leaf TYZ-3.6(3) (Galois action on TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
complex conjugation `γ` and any `ρ ∈ Gal(ℚ̄/ℚ)` acting on the Hilbert class field `H_n` as the
(arithmetic) Artin symbol of `[𝔭₂]^{−5}`: `γ(z_n) + ρ(z_n) = τ(1/2)`. TYZ Theorem 3.6(3) (L1424–1427,
VERIFIED read): `z̄_n + z_n^{σ_{ϖ^5}} = τ(1/2)` with `ϖ ∈ K_{n,2}`, `v₂(ϖ) = 1`, `v₂'(ϖ) = 0`, and `σ`
the geometric Artin map (L1247–1250), so `σ_{ϖ^5}|_{H_n} = Art([𝔭₂])^{−5}`. Refereed. Numerically
VERIFIED for the 12 squarefree `n ≡ 7 (mod 8)`, `7 ≤ n ≤ 103` (`thm36_7.out`); the opposite sign
`[𝔭₂]^{+5}` fails for 7 of them. -/
def TYZThm36Seven : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Squarefree n → ∀ γ ρ : GalQ, IsComplexConj γ →
    ActsAsArtinO n (OK n) ρ ((p2Class n)⁻¹ ^ 5) →
      galPt γ (tyzZ7 n) + galPt ρ (tyzZ7 n) = tauG 1

/-- **Glue BETA-7 (`β₁` on the genus field)**: for squarefree `n ≡ 7 (mod 8)`, a lift `σ` of
`β₁ = r_∞(−1)r₂(−2)`, complex conjugation `γ` and `ρ` acting on `H_n` as `Art([𝔭₂]^{−5})`, `σ` and
`γ ∘ ρ` agree on the genus field `G_n = ℚ(√p* : p ∣ n)`. TYZ L2526–2531 ("the action of `β_j'` on
`L_n(i)` is the same as that of `σ_ϖ ∘ c`") plus `σ_ϖ = σ_{ϖ^5}` on `L_n` (exponent 2). Glue: on
`√p*` both sides act by `(2/p)·sgn(p*)` (`betaOneSign`; Art`[𝔭₂]` acts on `√p*` by the genus character
`χ_p([𝔭₂]) = (N𝔭₂/p) = (2/p)`), and `G_n ⊆ K_n(√p* : p ∣ n)` (Gauss). Proved in §13 (`betaOnGenus7`). -/
def BetaOnGenus7 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Squarefree n → ∀ σ γ ρ : GalQ, IsBetaOneLift σ →
    IsComplexConj γ → ActsAsArtinO n (OK n) ρ ((p2Class n)⁻¹ ^ 5) →
      ∀ x ∈ genusBar n, σ x = γ (ρ x)

/-- Restriction of ring class Artin symbols to the Hilbert class field, on elements. -/
theorem coe_artin_restrict {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (c : Pic O) (x : ringClassField (maximalNumberFieldOrder K)) :
    ((ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) :
        ringClassField O) : SeparableClosure K) =
      ((ringClassArtinEquiv (maximalNumberFieldOrder K) (picToMax O c) x :
        ringClassField (maximalNumberFieldOrder K)) : SeparableClosure K) := by
  rw [← restrict_ringClassArtinEquiv, ← IntermediateField.coe_inclusion (ringClassField_maximal_le O),
    restrictNormalHom_inclusion_apply]

variable {d : ℕ} [NeZero d]

theorem hilbertBar_eq_bar : hilbertBar d = ringClassFieldBar d 1 := by
  rw [hilbertBar_eq, ringClassFieldBar_eq, conductorOrder_one]

theorem map_mem_hilbertBar (τ : GalQ) {x : Qbar} (hx : x ∈ hilbertBar d) : τ x ∈ hilbertBar d := by
  haveI : Normal ℚ (hilbertBar d) := by rw [hilbertBar_eq_bar]; exact normal_ringClassFieldBar d 1
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance τ) ⟨x, hx, rfl⟩

/-- Restriction `H_{d,4} → H_d` of Artin symbols, in `ℚ̄`. -/
theorem actsO_of_acts4 {ρ : GalQ} {c4 : Pic (O4 d)} (h : ActsAsArtin4 ρ d c4) :
    ActsAsArtinO d (OK d) ρ (picToMax (O4 d) c4) := by
  intro x
  have h1 := h (IntermediateField.inclusion (ringClassField_maximal_le (O4 d)) x)
  rw [IntermediateField.coe_inclusion] at h1
  rw [h1, coe_artin_restrict]

/-- **Complex conjugation inverts the Artin symbols of `H_d`** (from ring-class's
`actsAsArtin4_conj` for `H_{d,4}` and restriction). -/
theorem actsO_conj {γ ρ : GalQ} (hγ : IsComplexConj γ) {c : Pic (OK d)}
    (hρ : ActsAsArtinO d (OK d) ρ c) : ActsAsArtinO d (OK d) (γ * ρ * γ⁻¹) c⁻¹ := by
  obtain ⟨c4, rfl⟩ := picToMax_surjective (O4 d) c
  obtain ⟨ρ4, h4⟩ := exists_actsAsArtin4 d c4
  have hc := actsO_of_acts4 (actsAsArtin4_conj (hγ.ne_omega d) h4)
  rw [map_inv] at hc
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) ∈ hilbertBar d := by
    rw [hilbertBar_eq]; exact ⟨x, x.2, rfl⟩
  rw [← hc x]
  simp only [AlgEquiv.mul_apply]
  congr 1
  exact actsO_agree hρ (actsO_of_acts4 h4) _ (map_mem_hilbertBar _ hx)

theorem Z7_mem_genusBar {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) :
    Z7 e ∈ ptsOver (genusBar e) := by
  have hZ := Z7_mem hz
  have hfix : ∀ s ∈ picSquares (OK e), galPt (liftMax e s) (Z7 e) = Z7 e :=
    fun s hs => galPt_Z7 hz hs
  rw [mem_ptsOver_iff] at hZ ⊢
  revert hZ hfix
  rcases Z7 e with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hZ hfix
    have hc : ∀ s ∈ picSquares (OK e), liftMax e s x = x ∧ liftMax e s y = y := by
      intro s hs
      have e1 := hfix s hs
      obtain ⟨h', e'⟩ := galPt_some (liftMax e s) h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e1
      exact e1
    exact ⟨mem_genusBar_of_fixed hZ.1 fun s hs => (hc s hs).1,
      mem_genusBar_of_fixed hZ.2 fun s hs => (hc s hs).2⟩

theorem sum_sqClasses_inv (f : Pic (OK d) → PtA) :
    ∑ c ∈ sqClasses d, f c⁻¹ = ∑ c ∈ sqClasses d, f c := by
  refine Finset.sum_nbij' (fun c => c⁻¹) (fun c => c⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).inv_mem hc
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).inv_mem hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem card_sqClasses : (sqClasses d).card = gNat d := by
  rw [gNat, dif_neg (NeZero.ne d), gCl_eq_card_picSquares, sqClasses,
    ← Nat.card_eq_card_finite_toFinset]
  rfl

/-- **`Lemma321Seven` from TYZ Theorem 3.6(3) and glue BETA-7** (plus the CM field of definition). -/
theorem lemma321Seven_of (hcm : CMFieldOfDefinition7) (h36 : TYZThm36Seven)
    (hb : BetaOnGenus7) : Lemma321Seven := by
  intro e he hsq σ hσ
  haveI : NeZero e := ⟨by omega⟩
  obtain ⟨γ, hγ⟩ := exists_complexConj
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtinO e (OK e) ((p2Class e)⁻¹ ^ 5)
  have hz := hcm e he hsq
  set z := tyzZ7 e
  have hleaf := h36 e inferInstance he hsq γ ρ hγ hρ
  have hρz : galPt ρ z = tauG 1 - galPt γ z := by rw [← hleaf]; abel
  have hZ := Z7_mem_genusBar hz
  have h1 : galPt σ (Z7 e) = galPt (γ * ρ) (Z7 e) :=
    galPt_congr (fun x hx => by rw [AlgEquiv.mul_apply]; exact hb e inferInstance he hsq σ γ ρ hσ hγ hρ x hx) hZ
  have hτ : ∀ τ' : GalQ, galPt τ' (tauG 1) = tauG 1 := fun τ' => by
    rw [tauG_apply, one_smul]; exact galPt_ptT τ'
  have hterm : ∀ c ∈ sqClasses e, galPt (γ * ρ) (galPt (liftMax e c) z) =
      tauG 1 - galPt (liftMax e c⁻¹) z := by
    intro c _
    -- `ρ t_c z = t_c ρ z` on `A(H_e)`
    have hcomm : galPt ρ (galPt (liftMax e c) z) = galPt (liftMax e c) (galPt ρ z) := by
      rw [← galPt_mul, ← galPt_mul]
      exact galPt_congr (actsO_agree (actsO_mul hρ (liftMax_spec e c))
        (by rw [mul_comm]; exact actsO_mul (liftMax_spec e c) hρ)) hz
    rw [galPt_mul, hcomm, hρz, map_sub, map_sub, hτ, hτ, ← galPt_mul, ← galPt_mul]
    congr 1
    -- `γ t_c γ = γ t_c γ⁻¹` acts as `Art(c⁻¹)` on `H_e`
    have hconj := actsO_conj hγ (liftMax_spec e c)
    have hγinv : γ⁻¹ = γ := by ext x; exact hγ.inv_apply x
    have hg : γ * liftMax e c * γ = γ * liftMax e c * γ⁻¹ := by rw [hγinv]
    rw [hg]
    exact galPt_congr (actsO_agree hconj (liftMax_spec e c⁻¹)) hz
  rw [h1, Z7_eq, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    sum_sqClasses_inv (fun c => galPt (liftMax e c) z), card_sqClasses, ← natCast_zsmul]
  abel

end Seven


/-! ## §13. Towards glue BETA-7: the genus field is `K_n(√p* : p ∣ n)` -/

section BetaSeven

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

/-- `p* = (−1)^{(p−1)/2} p` for odd `p`. -/
def pstar (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

/-- **Quadratic reciprocity, finite-field form with `p*`**: in a finite field `F` of odd
characteristic `≠ p`, `p*` is a square iff `|F|` is a square mod `p`. -/
theorem isSquare_pstar_iff {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpF : ringChar F ≠ p) :
    IsSquare ((pstar p : ℤ) : F) ↔ IsSquare ((Fintype.card F : ℕ) : ZMod p) := by
  classical
  obtain ⟨k, hk, hcard⟩ := FiniteField.card F (ringChar F)
  have hpF0 : ((p : ℕ) : F) ≠ 0 := by
    intro h
    exact hpF ((Nat.prime_dvd_prime_iff_eq hk hp.out).1 ((ringChar.spec F p).1 h))
  have hq0 : ((Fintype.card F : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    rw [hcard] at hd
    exact hpF ((Nat.prime_dvd_prime_iff_eq hp.out hk).1 (hp.out.dvd_of_dvd_pow hd)).symm
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := hp.out.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with he | ho
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 (even_iff_two_dvd.1 he)).symm hp2
    · omega
  have hq4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  have hχp : quadraticChar (ZMod p) (-1) = ZMod.χ₄ p := by
    rw [quadraticChar_neg_one (by rwa [ZMod.ringChar_zmod_n]), ZMod.card]
  have key : quadraticChar F ((pstar p : ℤ) : F) = quadraticChar (ZMod p) (Fintype.card F) := by
    have hodd' := quadraticChar_odd_prime hF hp2 hpF
    unfold pstar
    rcases hp4 with h | h
    · rw [if_pos h, Int.cast_natCast, hodd', map_mul]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_one_mod_four h, one_mul]
    · rw [if_neg (by omega), Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, map_mul, hodd',
        map_mul, quadraticChar_neg_one hF]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_three_mod_four h]; ring
  have hps0 : ((pstar p : ℤ) : F) ≠ 0 := by
    unfold pstar; split_ifs <;> simpa using hpF0
  rw [← quadraticChar_one_iff_isSquare hps0, ← quadraticChar_one_iff_isSquare hq0, key]


section Star

variable {n : ℕ} [NeZero n]

/-- `{p* : p ∣ n}`. -/
def pstarSet (n : ℕ) : Finset ℤ := n.primeFactors.image pstar

/-- `K_n(√p* : p ∣ n) ⊆ K_nˢ` (the genus field, `genusField_le_genusStar`). -/
def genusStar (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.adjoin (QNeg n) (sqrtK (QNeg n) '' (pstarSet n : Set ℤ))

theorem adjSqrt_le_genusStar {a : ℤ} (ha : a ∈ pstarSet n) : adjSqrt (QNeg n) a ≤ genusStar n :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 ha)))

instance : FiniteDimensional (QNeg n) (genusStar n) :=
  IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact isIntegral_sqrtK _ a

instance : Normal (QNeg n) (genusStar n) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [genusStar, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h : g (sqrtK (QNeg n) a) ^ 2 = sqrtK (QNeg n) a ^ 2 := by
    rw [← map_pow, sqrtK_sq, map_intCast]
  have hmem : sqrtK (QNeg n) a ∈ genusStar n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact hmem
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact neg_mem hmem

instance : IsGalois (QNeg n) (genusStar n) := IsGalois.mk

theorem pstar_mem_or (p : ℕ) : pstar p = p ∨ pstar p = -p := by
  unfold pstar; split_ifs <;> simp

/-- The residue field at `𝔭 ∌ 2n` has characteristic `≠ 2` and `≠ p` for `p ∣ n`. -/
theorem residue_facts (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) {p : ℕ} (hp : p ∈ n.primeFactors) :
    letI := Ideal.Quotient.field 𝔭.asIdeal
    ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 ∧ ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ p := by
  letI := Ideal.Quotient.field 𝔭.asIdeal
  have hmem : ∀ k : ℕ, k ∣ 2 * n → ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ k := by
    intro k hk hc
    apply h2n
    obtain ⟨m, hm⟩ := hk
    have h0 : ((k : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h1 : ((k : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    rw [show ((2 * n : ℕ) : 𝓞 (QNeg n)) = ((k * m : ℕ) : 𝓞 (QNeg n)) from congrArg _ hm, Nat.cast_mul]
    exact 𝔭.asIdeal.mul_mem_right _ h1
  exact ⟨hmem 2 ⟨n, rfl⟩, hmem p (Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) 2)⟩

/-- Genus characters at a prime split in `K_n(√p* : p ∣ n)`. -/
theorem chi_eq_one_of_isSquare_pstar (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hp : ∀ p ∈ n.primeFactors, IsSquare (((pstar p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hsquare := (isSquare_pstar_iff hchar hq2 hcharq).1 (hp q q.2)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hb : ZInQ.RouteK.legBit q ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) = 0 := by
    unfold ZInQ.RouteK.legBit
    rw [if_pos]
    rw [hN, Int.cast_natCast]
    exact hsquare
  have hc := chi_mk0 n hn hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, hb]
  rfl

end Star


variable {n : ℕ} [NeZero n]

/-- **The genus field of `K_n`, `n ≡ 3 (mod 4)` squarefree, lies in `K_n(√p* : p ∣ n)`** (Bauer, as
`genusField_le_genusAmb`, with `p*` square mod `𝔭` for all `p ∣ n` ⇒ all genus characters trivial). -/
theorem genusField_le_genusStar (hn : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) ≤ genusStar n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hG : genusField (maximalNumberFieldOrder (QNeg n)) =
      ringSubfield (picSquares (conductorOrder (QNeg n) 1)) := by
    rw [← conductorOrder_one]; rfl
  rw [hG]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  rw [mem_splitSet_iff (conductorOrder (QNeg n) 1) _ ⟨_, hJ⟩ 𝔭 rfl]
  have hp : ∀ p ∈ n.primeFactors,
      IsSquare (((pstar p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)) := by
    intro p hp
    refine (mem_splitSet_adjSqrt_iff 𝔭 (a := pstar p) ?_).1
      (splitSet_anti (adjSqrt_le_genusStar (Finset.mem_image_of_mem _ hp)) h𝔭)
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) * ((if p % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  exact picClass_mem_picSquares hodd hsq h1 _ (conductorOrder_one _) ⟨_, hJ⟩
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot)
    (chi_eq_one_of_isSquare_pstar hodd hsq 𝔭 h2n hp)

/-- Norms in `𝓞_{K_n}`, `n ≡ 3 (mod 4)` squarefree, `p ∣ n`: `4N(β) ≡ t² (mod p)`. -/
theorem norm_sq_mod_prime3 (hsq : Squarefree n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (β : 𝓞 (QNeg n)) : ∃ t : ℤ, (p : ℤ) ∣ 4 * Algebra.norm ℤ β - t ^ 2 := by
  obtain ⟨s, hs⟩ := exists_two_re β
  obtain ⟨m, hm⟩ := exists_two_re (β * sqrtNeg n)
  have hN := normZ_eq_re_im β
  have hre : ((β * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (β : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  rw [hre] at hm
  refine ⟨s, ?_⟩
  set w := 4 * Algebra.norm ℤ β - s ^ 2
  have hw : (n : ℤ) * w = m ^ 2 := by
    have : ((n : ℤ) * w : ℚ) = (m : ℚ) ^ 2 := by
      simp only [w]; push_cast
      rw [hN, ← hs, ← hm]; ring
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨n', hn'⟩ := hpn
  have hpn' : ¬ (p : ℤ) ∣ n' := by
    intro h
    obtain ⟨k, rfl⟩ := Int.natCast_dvd_natCast.1 h
    have := hsq p ⟨k, by rw [hn']; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpm : (p : ℤ) ∣ m := by
    apply hpZ.dvd_of_dvd_pow (n := 2)
    rw [← hw, hn']; push_cast
    exact ⟨n' * w, by ring⟩
  obtain ⟨m', rfl⟩ := hpm
  have h2 : (p : ℤ) * (n' * w) = (p : ℤ) * (p * m' ^ 2) := by
    rw [hn'] at hw; push_cast at hw; linear_combination hw
  have h3 : (n' : ℤ) * w = p * m' ^ 2 := mul_left_cancel₀ hpZ.ne_zero h2
  have h4 : (p : ℤ) ∣ n' * w := ⟨m' ^ 2, h3⟩
  rcases hpZ.dvd_or_dvd h4 with h | h
  · exact absurd h hpn'
  · exact h

/-- **Genus theory, `n ≡ 3 (mod 4)`**: `K_n(√p*) ⊆ H_n` for every prime `p ∣ n` (Bauer: a principal
prime `𝔭 = β𝓞_K ∤ 2n` has `4N𝔭 ≡ t² (mod p)`, so `p*` is a square mod `𝔭` by `isSquare_pstar_iff`). -/
theorem adjSqrt_pstar_le_hilbertField (hn : n % 4 = 3) (hsq : Squarefree n) {p : ℕ}
    (hp : p ∈ n.primeFactors) :
    adjSqrt (QNeg n) (pstar p) ≤ hilbertField n := by
  rw [hilbertField_eq_ringSubfield]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (conductorOrder (QNeg n) 1) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, -, hspan⟩ := h1
  have hq : Nat.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo
      (conductorOrder (QNeg n) 1).conductorModulus) : Ideal (𝓞 (QNeg n)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hnn := normZ_nonneg (n := n) β
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hp
    omega
  haveI := Fact.mk hpp
  have h2a : ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) * ((if p % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_adjSqrt_iff 𝔭 h2a]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharp⟩ := residue_facts 𝔭 h2n hp
  rw [isSquare_pstar_iff hchar hp2 hcharp]
  have hcard : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Nat.card_eq_fintype_card, hq]
  rw [hcard]
  obtain ⟨t, ht⟩ := norm_sq_mod_prime3 hsq hpp (Nat.dvd_of_mem_primeFactors hp) β
  set N : ZMod p := (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod p)
  have h4 : (4 : ZMod p) * N = (t : ZMod p) ^ 2 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ht
    have hN : N = ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
      simp only [N]; rw [← Int.cast_natCast, hc]
    rw [hN]
    push_cast at h0
    linear_combination h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h')
  have e : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact ⟨t * 2⁻¹, by linear_combination (2⁻¹ * 2⁻¹ : ZMod p) * h4 + (-N * (1 + 2 * 2⁻¹)) * e⟩

end BetaSeven

/-! ### Assembly of glue BETA-7 from genus theory -/

section BetaAssembly

open ZInQ.RouteK.Redei
open scoped nonZeroDivisors

/-- **Glue GT-H (genus theory, `n ≡ 3 (mod 4)`)**: `√p* ∈ H_n` for every prime `p ∣ n` (Gauss; Cox,
*Primes of the form x² + ny²*, Thm. 6.1, UNVERIFIED number). -/
def SqrtPstarInHilbert : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 4 = 3 → Squarefree n → ∀ p ∈ n.primeFactors,
    adjSqrt (QNeg n) (pstar p) ≤ hilbertField n

/-- **Glue GT-ART (genus characters as Artin characters)**: for squarefree `n ≡ 3 (mod 4)`, `p ∣ n`
and `c ∈ Cl(K_n)`, the Artin symbol of `c` acts on `√p* ∈ H_n` by the genus character `χ_p(c)`
(`RouteK.Redei.chi`, `χ_p([𝔞]) = (N𝔞 / p)`). Classical (Gauss genus theory; Frobenius on `K_n(√p*)`
plus quadratic reciprocity). -/
def ArtinPstarChi : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 4 = 3 → Squarefree n → ∀ (q : n.primeFactors) (c : Pic (OK n))
    (hs : sqrtK (QNeg n) (pstar q) ∈ hilbertField n),
    ((ringClassArtinEquiv (OK n) c ⟨_, hs⟩ : hilbertField n) : SeparableClosure (QNeg n)) =
      (if chi n q c = 1 then 1 else -1) * sqrtK (QNeg n) (pstar q)

/-- **Glue NORM-2**: `N𝔭₂ = 2` for `n ≡ 7 (mod 8)` (computation). -/
def NormP2 : Prop := ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Ideal.absNorm (p2Ideal n) = 2

/-- Complex conjugation on a square root of a nonzero integer `D`: `γ(√D) = sgn(D)·√D`. -/
theorem IsComplexConj.apply_sqrt {γ : GalQ} (hγ : IsComplexConj γ) {D : ℤ} (hD : D ≠ 0) {r : Qbar}
    (hr : r ^ 2 = (D : Qbar)) : γ r = (if D < 0 then -1 else 1) * r := by
  apply ιC_injective
  rw [hγ]
  have hz : ιC r ^ 2 = (D : ℂ) := by rw [← map_pow, hr, map_intCast]
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at hre him
  split_ifs with hneg
  · have h0 : (ιC r).re = 0 := by
      rcases mul_eq_zero.1 (show (ιC r).re * (ιC r).im = 0 by linarith) with h | h
      · exact h
      · exfalso
        rw [h] at hre
        have : (0 : ℝ) ≤ (ιC r).re * (ιC r).re := mul_self_nonneg _
        have : (D : ℝ) < 0 := by exact_mod_cast hneg
        linarith
    rw [map_mul, map_neg, map_one, neg_one_mul, Complex.ext_iff, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, h0]
    exact ⟨by simp, rfl⟩
  · have h0 : (ιC r).im = 0 := by
      rcases mul_eq_zero.1 (show (ιC r).re * (ιC r).im = 0 by linarith) with h | h
      · exfalso
        rw [h] at hre
        have : (0 : ℝ) ≤ (ιC r).im * (ιC r).im := mul_self_nonneg _
        have : (0 : ℝ) < D := by
          have : (0 : ℤ) < D := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hD)
          exact_mod_cast this
        linarith
      · exact h
    rw [map_mul, map_one, one_mul, Complex.ext_iff, Complex.conj_re, Complex.conj_im, h0]
    exact ⟨rfl, by simp⟩

/-- The equalizer of `f ∘ embed` and `g ∘ embed`, as a field over `K_n` when `f`, `g` agree on `K_n`. -/
def eqField (n : ℕ) [NeZero n] (f g : GalQ)
    (hK : ∀ k : QNeg n, f (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      g (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k))) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  { AlgHom.equalizer ((f : Qbar →ₐ[ℚ] Qbar).comp (embed n)) ((g : Qbar →ₐ[ℚ] Qbar).comp (embed n)) with
    algebraMap_mem' := hK
    inv_mem' := fun x hx => by
      show f (embed n x⁻¹) = g (embed n x⁻¹)
      simp only [map_inv₀]
      exact congrArg _ hx }

theorem mem_eqField {n : ℕ} [NeZero n] {f g : GalQ} {hK} {x : SeparableClosure (QNeg n)} :
    x ∈ eqField n f g hK ↔ f (embed n x) = g (embed n x) := Iff.rfl

theorem sqf_neg {x : ℤ} (h : Squarefree x) : Squarefree (-x) := fun y hy => h y ((dvd_neg).1 hy)

theorem squarefree_pstar {p : ℕ} (hp : p.Prime) : Squarefree (pstar p) := by
  have h : Squarefree (p : ℤ) := Int.squarefree_natCast.2 hp.squarefree
  unfold pstar; split_ifs
  · exact h
  · exact sqf_neg h

theorem betaOneSign_pstar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    betaOneSign (pstar p) = (if pstar p < 0 then -1 else 1) *
      (if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1) := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.mk hp).out).2 hp2
  unfold betaOneSign oddPartSqfree pstar
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · have h4 : p % 4 = 1 := by omega
    simp only [h4, if_true, h, true_or]
    have : ¬ (2 : ℤ) ∣ (p : ℤ) := by omega
    simp only [this, if_false]
    have : (p : ℤ) % 8 = 1 := by omega
    simp [this]
  · have h4 : ¬ p % 4 = 1 := by omega
    simp only [h4, if_false]
    have : ¬ (2 : ℤ) ∣ -(p : ℤ) := by omega
    simp only [this, if_false]
    have : (-(p : ℤ)) % 8 = 5 := by omega
    simp [this, h]
  · have h4 : p % 4 = 1 := by omega
    simp only [h4, if_true]
    have : ¬ (2 : ℤ) ∣ (p : ℤ) := by omega
    simp only [this, if_false]
    have : (p : ℤ) % 8 = 5 := by omega
    simp [this, h]
  · have h4 : ¬ p % 4 = 1 := by omega
    simp only [h4, if_false]
    have : ¬ (2 : ℤ) ∣ -(p : ℤ) := by omega
    simp only [this, if_false]
    have : (-(p : ℤ)) % 8 = 1 := by omega
    simp [this, h]

/-- **Glue GT-H proved.** -/
theorem sqrtPstarInHilbert : SqrtPstarInHilbert := fun _ _ hn hsq _ hp =>
  adjSqrt_pstar_le_hilbertField hn hsq hp

theorem mul_two_inv_pow_five : ∀ x : Multiplicative (ZMod 2), x⁻¹ ^ 5 = x := by decide

/-- **Glue BETA-7 from genus theory** (`SqrtPstarInHilbert`, `ArtinPstarChi`, `NormP2`). -/
theorem betaOnGenus7_of (hsH : SqrtPstarInHilbert) (hart : ArtinPstarChi) (hnorm : NormP2) :
    BetaOnGenus7 := by
  intro n _ hn hsq σ γ ρ hσ hγ hρ x hx
  have h3 : n % 4 = 3 := by omega
  simp only [genusBar, NeZero.ne n, ↓reduceDIte] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyS : y ∈ genusStar n := genusField_le_genusStar h3 hsq (by omega) hy
  have hfixK : ∀ k : QNeg n, ρ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k) := by
    intro k
    have h := hρ (algebraMap (QNeg n) (hilbertField n) k)
    rw [AlgEquiv.commutes] at h
    exact h
  set w := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hw2 : w ^ 2 = ((-(n : ℤ) : ℤ) : Qbar) := by
    simp only [w]
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  have hn0 : (-(n : ℤ)) ≠ 0 := by have := NeZero.ne n; omega
  have hsqn : Squarefree (-(n : ℤ)) := sqf_neg (Int.squarefree_natCast.2 hsq)
  have hbn : betaOneSign (-(n : ℤ)) = -1 := by
    unfold betaOneSign oddPartSqfree
    have h2 : ¬ (2 : ℤ) ∣ -(n : ℤ) := by omega
    have h8 : (-(n : ℤ)) % 8 = 1 := by omega
    have hlt : -(n : ℤ) < 0 := by omega
    simp [h2, h8, hlt, NeZero.ne n]
  have hσw : σ w = -w := by
    rw [hσ _ hsqn w hw2, hbn]; simp
  have hγw : γ w = -w := by
    rw [hγ.apply_sqrt hn0 hw2, if_pos (by omega)]; simp
  have hK : ∀ k : QNeg n, σ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) =
      (γ * ρ) (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k)) := by
    intro k
    rw [AlgEquiv.mul_apply, hfixK, algebraMap_eq_re_im, map_add, map_mul, AlgHom.commutes,
      AlgHom.commutes, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_add, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes]
    show _ + _ * σ w = _ + _ * γ w
    rw [hσw, hγw]
  have hle : genusStar n ≤ eqField n σ (γ * ρ) hK := by
    rw [genusStar, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hp
      omega
    have hs : sqrtK (QNeg n) (pstar p) ∈ hilbertField n :=
      hsH n inferInstance h3 hsq p hp (IntermediateField.mem_adjoin_simple_self _ _)
    set r := embed n (sqrtK (QNeg n) (pstar p))
    have hr2 : r ^ 2 = ((pstar p : ℤ) : Qbar) := by
      simp only [r]; rw [← map_pow, sqrtK_sq, map_intCast]
    have hps0 : pstar p ≠ 0 := by unfold pstar; split_ifs <;> simp [hpp.ne_zero]
    rw [SetLike.mem_coe, mem_eqField, AlgEquiv.mul_apply]
    have hρr : ρ r = (if chi n ⟨p, hp⟩ (((p2Class n)⁻¹ ^ 5 : Pic (OK n))) = 1 then 1 else -1) * r := by
      have h1 := hρ ⟨_, hs⟩
      rw [hart n inferInstance h3 hsq ⟨p, hp⟩ _ hs] at h1
      rw [show r = embed n (sqrtK (QNeg n) (pstar p)) from rfl, h1, map_mul]
      split_ifs <;> simp [r]
    have hchi : chi n ⟨p, hp⟩ (((p2Class n)⁻¹ ^ 5 : Pic (OK n))) = chi n ⟨p, hp⟩ (p2Class n) := by
      erw [map_pow, map_inv, mul_two_inv_pow_five]
    have hp2' : ¬ p ∣ Ideal.absNorm (p2Ideal n) := by
      rw [hnorm n inferInstance hn]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h)
    have hchi2 : chi n ⟨p, hp⟩ (p2Class n) =
        Multiplicative.ofAdd (ZInQ.RouteK.legBit p ((2 : ℕ) : ℤ)) := by
      have := chi_mk0 n (Nat.odd_iff.mpr (by omega)) hsq ⟨p, hp⟩ ⟨p2Ideal n, p2Ideal_mem n⟩ hp2'
      rw [hnorm n inferInstance hn] at this
      exact this
    have hleg : (chi n ⟨p, hp⟩ (p2Class n) = 1) ↔ (p % 8 = 1 ∨ p % 8 = 7) := by
      haveI := Fact.mk hpp
      rw [hchi2, ← ZMod.exists_sq_eq_two_iff hp2]
      unfold ZInQ.RouteK.legBit
      split_ifs with h
      · simp only [ofAdd_zero, true_iff]; simpa using h
      · simp only [Nat.cast_ofNat, Int.cast_ofNat] at h
        simp only [h, iff_false]
        decide
    rw [hρr, map_mul, hγ.apply_sqrt hps0 hr2, hσ _ (squarefree_pstar hpp) r hr2,
      betaOneSign_pstar hpp hp2, hchi]
    by_cases hc : p % 8 = 1 ∨ p % 8 = 7
    · rw [if_pos (hleg.2 hc), if_pos hc]
      split_ifs <;> simp
    · rw [if_neg (fun h => hc (hleg.1 h)), if_neg hc]
      split_ifs <;> simp
  have := hle hyS
  rw [mem_eqField, AlgEquiv.mul_apply] at this
  exact this

end BetaAssembly

/-! ### Glue GT-ART proved: the Artin symbols act on `√p*` by the genus characters -/

section ArtinChi

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- The subfield of `H_n` cut out by `S ≤ Cl(K_n)`. -/
abbrev maxSubfield (S : Subgroup (Pic (OK n))) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.lift
    (IntermediateField.fixedField (S.map (ringClassArtinEquiv (OK n)).toMonoidHom))

instance (S : Subgroup (Pic (OK n))) : FiniteDimensional (QNeg n) (maxSubfield S) :=
  LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv _).toLinearEquiv

instance (S : Subgroup (Pic (OK n))) : IsGalois (QNeg n) (maxSubfield S) := by
  have : (S.map (ringClassArtinEquiv (OK n)).toMonoidHom).Normal := Subgroup.normal_of_comm _
  exact IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv _)

theorem mem_primeTo_max (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal) :
    𝔭.asIdeal ∈ integralIdealsPrimeTo (OK n).conductorModulus := by
  have := mem_primeTo_of_not_le (f := 1) 𝔭 h
  rwa [conductorOrder_one] at this

/-- The genus character as a subgroup of `Cl(K_n) = Pic(𝓞_{K_n})`. -/
abbrev kerChi (q : n.primeFactors) : Subgroup (Pic (OK n)) := (chi n q).ker

/-- Away from `2n`: `𝔭` splits in the fixed field of `ker χ_q` iff it splits in `K_n(√q*)`. -/
theorem splitSet_kerChi_iff (hn : n % 4 = 3) (hsq : Squarefree n) (q : n.primeFactors)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal)
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) :
    𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
      𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q)) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hJ := mem_primeTo_max 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (OK n).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  have h2a : ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors q.2
    have e2 : 2 * n = 2 * (q : ℕ) * n' := by rw [mul_assoc, ← hn']
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) *
          ((if (q : ℕ) % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_iff (OK n) _ ⟨_, hJ⟩ 𝔭 rfl]
  change chi n q ((OK n).picClass ⟨_, hJ⟩) = 1 ↔ _
  rw [picClass_maximal ⟨_, hJ⟩ (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot),
    mem_splitSet_adjSqrt_iff 𝔭 h2a]
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
      (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hc := chi_mk0 n hodd hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, isSquare_pstar_iff hchar hq2 hcharq]
  unfold ZInQ.RouteK.legBit
  rw [hN, Int.cast_natCast]
  split_ifs with h
  · simp only [ofAdd_zero, true_iff]; exact h
  · simp only [h, iff_false]; decide

/-- **The fixed field of `ker χ_q` is `K_n(√q*)`** (Bauer, both directions). -/
theorem maxSubfield_kerChi (hn : n % 4 = 3) (hsq : Squarefree n) (q : n.primeFactors) :
    maxSubfield (kerChi q) = adjSqrt (QNeg n) (pstar q) := by
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 (QNeg n)),
      𝔭 ∉ {𝔭 : HeightOneSpectrum (𝓞 (QNeg n)) | (conductorOrder (QNeg n) 1).conductor *
        Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≤ 𝔭.asIdeal} →
      (𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
        𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q))) := fun 𝔭 hT =>
    splitSet_kerChi_iff hn hsq q 𝔭 (fun h => hT (le_trans Ideal.mul_le_left h))
      (fun h => hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h)))
  apply le_antisymm
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).2 h𝔭
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).1 h𝔭

/-- **Glue GT-ART proved.** -/
theorem artinPstarChi : ArtinPstarChi := by
  intro n _ hn hsq q c hs
  set s := sqrtK (QNeg n) (pstar q)
  set g := ringClassArtinEquiv (OK n) c
  set s' : hilbertField n := ⟨s, hs⟩
  have hs2 : s' ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
    apply Subtype.ext
    show s ^ 2 = algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n)
    rw [sqrtK_sq, map_intCast]
  have hg2 : ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 = s ^ 2 := by
    have h0 : (g s') ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
      rw [← map_pow, hs2, AlgEquiv.commutes]
    have h' := congrArg Subtype.val h0
    change ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 =
      algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n) at h'
    rw [h', map_intCast, sqrtK_sq]
  have hmemE : s ∈ maxSubfield (kerChi q) := by
    rw [maxSubfield_kerChi hn hsq q]; exact IntermediateField.mem_adjoin_simple_self _ _
  have hfix_iff : g s' = s' ↔ chi n q c = 1 := by
    constructor
    · intro hfix
      have hle : adjSqrt (QNeg n) (pstar q) ≤
          IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers g)) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact mem_lift_fixedField_zpowers g s' hfix
      rw [← maxSubfield_kerChi hn hsq q] at hle
      have hle' : IntermediateField.fixedField ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom) ≤
          IntermediateField.fixedField (Subgroup.zpowers g) := fun x hx =>
        (IntermediateField.mem_lift x).1 (hle ((IntermediateField.mem_lift x).2 hx))
      have hZ : Subgroup.zpowers g ≤ (kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom := by
        rw [← IntermediateField.fixingSubgroup_fixedField
          ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom)]
        exact (IntermediateField.le_iff_le _ _).1 (le_trans hle' le_rfl)
      obtain ⟨c', hc', hce⟩ := Subgroup.mem_map.1 (hZ (Subgroup.mem_zpowers g))
      rw [(ringClassArtinEquiv (OK n)).injective hce] at hc'
      exact hc'
    · intro hc
      have h1 := (IntermediateField.mem_lift s').1 hmemE
      rw [IntermediateField.mem_fixedField_iff] at h1
      exact h1 g (Subgroup.mem_map_of_mem _ hc)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hg2 with h | h
  · have hc : chi n q c = 1 := hfix_iff.1 (Subtype.ext h)
    rw [h, if_pos hc, one_mul]
  · have hc : chi n q c ≠ 1 := by
      intro hc
      have h' := congrArg Subtype.val (hfix_iff.2 hc)
      rw [h] at h'
      have h2 : (2 : SeparableClosure (QNeg n)) * s = 0 := by
        change -s = s at h'; linear_combination -h'
      have hs0 : s ≠ 0 := by
        intro h0
        have := sqrtK_sq (QNeg n) (pstar q)
        rw [← show s = sqrtK (QNeg n) (pstar q) from rfl, h0] at this
        have hp0 : pstar q ≠ 0 := by
          unfold pstar; split_ifs <;> simp [(Nat.prime_of_mem_primeFactors q.2).ne_zero]
        simp at this
        exact hp0 (by exact_mod_cast this.symm)
      rcases mul_eq_zero.1 h2 with h2 | h2
      · exact two_ne_zero h2
      · exact hs0 h2
    rw [h, if_neg hc]; ring

end ArtinChi

/-! ### Glue NORM-2 proved: `N𝔭₂ = 2` -/

section NormTwo

open ZInQ.RouteK.Redei

/-- An element of `𝓞_{K_n}` (`n` odd) with imaginary part `±1/2` is not divisible by `2`. -/
theorem not_two_dvd_of_im {n : ℕ} [NeZero n] (hn : n % 2 = 1) {v : 𝓞 (QNeg n)}
    (hv : (v : QNeg n).im = 1 / 2 ∨ (v : QNeg n).im = -1 / 2) : ¬ ∃ w : 𝓞 (QNeg n), v = 2 * w := by
  rintro ⟨w, rfl⟩
  obtain ⟨k, hk⟩ := exists_two_re (w * sqrtNeg n)
  have hre : ((w * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (w : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  have him : ((2 * w : 𝓞 (QNeg n)) : QNeg n).im = 2 * (w : QNeg n).im := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_ofNat]
    simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [hre] at hk
  rw [him] at hv
  have hn' : (n : ℚ) = 2 * (n / 2 : ℕ) + 1 := by
    have : n = 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  rcases hv with h | h
  · have hw : (w : QNeg n).im = 1 / 4 := by linarith
    rw [hw] at hk
    have : (k : ℚ) = -(n : ℚ) / 2 := by linarith
    have h3 : ((n : ℤ) : ℚ) = ((-2 * k : ℤ) : ℚ) := by push_cast; linarith
    have h4 : (n : ℤ) = -2 * k := Int.cast_injective h3
    omega
  · have hw : (w : QNeg n).im = -1 / 4 := by linarith
    rw [hw] at hk
    have : (k : ℚ) = (n : ℚ) / 2 := by linarith
    have h3 : ((n : ℤ) : ℚ) = ((2 * k : ℤ) : ℚ) := by push_cast; linarith
    have h4 : (n : ℤ) = 2 * k := Int.cast_injective h3
    omega

/-- **Glue NORM-2 proved**: `(2) = 𝔭₂ 𝔭̄₂` with `𝔭₂, 𝔭̄₂ ≠ (1)`, so `N𝔭₂ = 2`. -/
theorem normP2 : NormP2 := by
  intro n _ hn
  have h3 : n % 4 = 3 := by omega
  have hδ := tyzDelta_spec hn
  set δ := tyzDelta n
  have hδodd : δ % 2 = 1 := by
    rcases Nat.even_or_odd δ with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso; rw [hk] at hδ; ring_nf at hδ; omega
    · omega
  set m := (δ + 1) / 2
  have hm : 2 * m = δ + 1 := by omega
  set N1 := (δ * δ + n) / 8
  have hN1 : 8 * N1 = δ * δ + n := by omega
  set θ := thetaO n h3
  set u : 𝓞 (QNeg n) := θ - (m : 𝓞 (QNeg n))
  set ub : 𝓞 (QNeg n) := 1 - θ - (m : 𝓞 (QNeg n))
  have hprod : u * ub = 2 * (N1 : 𝓞 (QNeg n)) := by
    have h2θ := two_mul_thetaO n h3
    have hω := omegaO_sq n
    have hmc : (2 : 𝓞 (QNeg n)) * m = δ + 1 := by exact_mod_cast hm
    have hNc : (8 : 𝓞 (QNeg n)) * N1 = δ * δ + n := by exact_mod_cast hN1
    have h8 : (4 : 𝓞 (QNeg n)) * (u * ub) = 8 * (N1 : 𝓞 (QNeg n)) := by
      rw [hNc]
      simp only [u, ub]
      linear_combination (1 - omegaO n - 2 * θ) * h2θ + ((δ : 𝓞 (QNeg n)) + 2 * m - 1) * hmc - hω
    have h4 : (4 : 𝓞 (QNeg n)) * (u * ub) = 4 * (2 * (N1 : 𝓞 (QNeg n))) := by rw [h8]; ring
    have h40 : (4 : 𝓞 (QNeg n)) ≠ 0 := fun h => by
      have h' := congrArg (algebraMap (𝓞 (QNeg n)) (QNeg n)) h
      rw [map_ofNat, map_zero] at h'
      norm_num at h'
    exact mul_left_cancel₀ h40 h4
  have hodd : n % 2 = 1 := by omega
  have himu : (u : QNeg n).im = 1 / 2 := by
    simp only [u, θ, map_sub, RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq, map_natCast]
    simp
  have himub : (ub : QNeg n).im = -1 / 2 := by
    simp only [ub, θ, map_sub, RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq, map_natCast,
      map_one]
    simp [QuadraticAlgebra.im_one]; norm_num
  have hP : p2Ideal n = Ideal.span {2, u} := by
    simp only [p2Ideal, h3, ↓reduceDIte]; rfl
  have hmul : Ideal.span {2, u} * Ideal.span {2, ub} = Ideal.span {(2 : 𝓞 (QNeg n))} := by
    apply le_antisymm
    · rw [Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hx
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hy
      rw [Ideal.mem_span_singleton]
      refine ⟨a * c * 2 + a * d * ub + b * c * u + b * d * N1, ?_⟩
      linear_combination (b * d) * hprod
    · rw [Ideal.span_singleton_le_iff_mem]
      have h1 : u * 2 ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have h2 : 2 * ub ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have h4 : 2 * 2 ∈ Ideal.span {2, u} * Ideal.span {2, ub} :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have := add_mem (add_mem h1 h2) (Ideal.mul_mem_right (m : 𝓞 (QNeg n)) _ h4)
      convert this using 1
      simp only [u, ub]; ring
  have hne1 : Ideal.span {2, u} ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (QNeg n)) ∈ Ideal.span {2, u} := by rw [h]; trivial
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h1
    apply not_two_dvd_of_im hodd (Or.inr himub)
    refine ⟨a * ub + b * N1, ?_⟩
    linear_combination (-ub) * hab + b * hprod
  have hne2 : Ideal.span {2, ub} ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (QNeg n)) ∈ Ideal.span {2, ub} := by rw [h]; trivial
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h1
    apply not_two_dvd_of_im hodd (Or.inl himu)
    refine ⟨a * u + b * N1, ?_⟩
    linear_combination (-u) * hab + b * hprod
  have hN2 : Ideal.absNorm (Ideal.span {(2 : 𝓞 (QNeg n))}) = 4 := by
    rw [Ideal.absNorm_span_singleton]
    have h := normZ_eq_re_im (2 : 𝓞 (QNeg n))
    have hr : ((2 : 𝓞 (QNeg n)) : QNeg n).re = 2 := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl
    have hi : ((2 : 𝓞 (QNeg n)) : QNeg n).im = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl
    rw [hr, hi] at h
    have : Algebra.norm ℤ (2 : 𝓞 (QNeg n)) = 4 := by exact_mod_cast (by linarith : ((Algebra.norm ℤ (2 : 𝓞 (QNeg n)) : ℤ) : ℚ) = 4)
    rw [this]; rfl
  have hab := congrArg Ideal.absNorm hmul
  rw [map_mul, hN2] at hab
  have ha1 : Ideal.absNorm (Ideal.span {2, u}) ≠ 1 := fun h => hne1 (Ideal.absNorm_eq_one_iff.1 h)
  have hb1 : Ideal.absNorm (Ideal.span {2, ub}) ≠ 1 := fun h => hne2 (Ideal.absNorm_eq_one_iff.1 h)
  rw [hP]
  set a := Ideal.absNorm (Ideal.span {2, u})
  set b := Ideal.absNorm (Ideal.span {2, ub})
  have ha4 : a ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
  interval_cases a <;> omega

end NormTwo

/-- **Glue BETA-7 proved** (from genus theory: `sqrtPstarInHilbert`, `artinPstarChi`, `normP2`). -/
theorem betaOnGenus7 : BetaOnGenus7 := betaOnGenus7_of sqrtPstarInHilbert artinPstarChi normP2

/-- **`Lemma321Seven` from TYZ Theorem 3.6(3)** (and the CM field of definition); no glue left. -/
theorem lemma321Seven_of' (hcm : CMFieldOfDefinition7) (h36 : TYZThm36Seven) : Lemma321Seven :=
  lemma321Seven_of hcm h36 betaOnGenus7

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem after §10–§12** (`Lemma321Seven` replaced by TYZ Thm 3.6(3) + glue BETA-7). -/
theorem tyzThm35ReadingA_of_cmLeaves7' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD)
    (hsh : TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h36 : TYZThm36Seven) (hb : BetaOnGenus7) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves7 h11 h1 h29 hcm hsh h318 h35 h5
    (lemma321Seven_of (cmFieldOfDefinition7_of hcm) h36 hb)


open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem of cm-bridge (final leaves).** Reading A of TYZ Theorem 3.5
(`ZInQ.Literature.TYZThm35ReadingA`) from:
* the three `𝓛`-leaves of tyz-decomp: `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`;
* the CM leaf `CM.CMFieldOfDefinition ringClassFieldD` (Heegner points of discriminant `D` on
  `A = X₀(32)` are defined over the ring class field of discriminant `D`; task tyz-cm works on it);
* `TYZSigmaShiftsF0` (TYZ Prop. 3.7(1), L1488–1490, + Shimura reciprocity at `P_n`);
* `Lemma318Literal HHprime` (TYZ Lemma `torsion2`, L2230: torsion of `A(ℍ'_n)`);
* `Thm35First ℓ tyzZ` (TYZ Theorem 3.3/3.5 for the pinned genus points);
* `Lemma321Five` (TYZ Lemma 3.21(1), L2508–2510);
* `TYZThm36Seven` (TYZ Theorem 3.6(3), L1424–1427).
Proved here (no longer hypotheses): `IInH4`, `HprimeNormal` (ring-class), `IInHprime`,
`CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7`, `TYZSigmaFixesZn`, `GenusFieldLeLni`, and
`Lemma321Seven` (from `TYZThm36Seven` with the glue `BetaOnGenus7`, proved from genus theory). -/
theorem tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : CM.CMFieldOfDefinition ringClassFieldD) (hsh : TYZSigmaShiftsF0)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h36 : TYZThm36Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves7 h11 h1 h29 hcm hsh h318 h35 h5
    (lemma321Seven_of' (cmFieldOfDefinition7_of hcm) h36)

end ZInQ.Contrib.TYZGenus.CMBridge

/-! ## Axiom audit (output in `scratch/cm-bridge/audit-out.txt`) -/
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzDelta_spec
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms exists_actsAsArtinO
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusPointLeafCM_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusPointLeaf_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinned
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinned'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzSigmaFixesZn_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms galPt_Z7
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms class7GenusPtDefined_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_pinnedLeaves
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms Copy.genusPointLeafCM_eq
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms phi0_spec
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms iInHprime
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms cmFieldOfDefinition7_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_rewired
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms genusFieldLeLni
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_cmLeaves7
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms exists_complexConj
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321Seven_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_cmLeaves7'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms sqrtPstarInHilbert
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms betaOnGenus7_of
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms artinPstarChi
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms normP2
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms lemma321Seven_of'
open ZInQ.Contrib.TYZGenus.CMBridge in
#print axioms tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven

end  -- closes the file's top-level `noncomputable section`

-- ===== frontier: composition (this task) =====

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.GZTheta.Frontier

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-- **Newness of the theta series of `ψ_d` at level `32 d²`.** -/
theorem newCM : NewCM := by
  intro d _ hd4 hsq F hF
  have hc : ∀ n, (qExpansion 1 (cmForm etaForm32 d)).coeff n = heckeCoeff d n :=
    qExpansion_cmForm_coeff qExpansion_etaForm32_coeff d
  have hFeq : F = cmForm etaForm32 d := by
    apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)
    ext n
    show (qExpansion 1 F).coeff n = (qExpansion 1 (cmForm etaForm32 d)).coeff n
    rw [hF, hc]
  rw [hFeq]
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway_cmForm qExpansion_etaForm32_coeff d hd4 hsq
  obtain ⟨M, hM0, hMN, g, hgχ, hgev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      E.mem_charSpace E.ne_zero (a := fun p hp hpN => E.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun p hp hpN => E.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  have hg1 : g.χ = 1 := by
    rw [hEχ] at hgχ
    ext u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hMN u
    have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hgχ
    simpa using this
  have hE1 : (qExpansion 1 E.toCuspForm).coeff 1 = 1 := by rw [hE, hc 1, heckeCoeff_one]
  have hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p := by
    intro p hp hp2d
    have hpN : Nat.Coprime p (32 * d ^ 2) := by
      by_contra h
      exact hp2d ((dvd_two_mul_iff_not_coprime hp).mpr h)
    have e1 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN)
    have e2 := E.qExpansion_coeff_eq_eigenvalue hE1 ⟨p, hp.pos⟩ hpN
    rw [hE, hc] at e2
    change coeff g p = _ at e1
    rw [e1, hgev p hp hpN]
    exact e2.symm
  have hMeq : M = 32 * d ^ 2 := level_eq_of_assoc hd4 hsq hMN g hg1 hgood
  subst hMeq
  have hmem : cmForm etaForm32 d ∈ cuspFormCharSpace 2 g.χ := by
    rw [hg1, ← hEχ, ← hE]; exact E.mem_charSpace
  have hfg := g.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul hmem
    (fun p hp hpN => by
      have := E.heckeTCuspNat_eq_eigenvalue_smul hp hpN
      rw [hE] at this
      rw [this, ← hgev p hp hpN])
  rw [hfg, hc 1, heckeCoeff_one, one_smul]
  exact g.isNew

/-- **The leaf `HeckeThetaNewform`** (L1 of gz-decomp), with no hypotheses. -/
theorem heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_newCM newCM

end ZInQ.GZTheta.Frontier

namespace ZInQ.Frontier

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package ZInQ.Contrib.TYZGenus.RingClass

/-- **TYZ reading A from the open TYZ Props of the finest reduction** (tyz-cm's
`cmFieldOfDefinition_of_cmValue` and cm-bridge's final theorem). -/
theorem tyzThm35ReadingA_of_open (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hV : ZInQ.Contrib.TYZGenus.Shimura.CMValueRingClass)
    (hI : ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant)
    (hsh : ZInQ.Contrib.TYZGenus.CMBridge.TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five)
    (h36 : ZInQ.Contrib.TYZGenus.CMBridge.TYZThm36Seven) :
    ZInQ.Literature.TYZThm35ReadingA :=
  ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven
    h11 h1 h29 (ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValue hV hI) hsh h318 h35 h5 h36

/-- **`ZInQ.FrozenTarget` from H, the 10 open TYZ Props and the 2 open GZ Props.** -/
theorem frozenTarget_of_open (hH : ZInQ.SixContactMin)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hV : ZInQ.Contrib.TYZGenus.Shimura.CMValueRingClass)
    (hI : ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant)
    (hsh : ZInQ.Contrib.TYZGenus.CMBridge.TYZSigmaShiftsF0) (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five)
    (h36 : ZInQ.Contrib.TYZGenus.CMBridge.TYZThm36Seven)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves hH
    (tyzThm35ReadingA_of_open h11 h1 h29 hV hI hsh h318 h35 h5 h36)
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Frontier

#print axioms ZInQ.Frontier.tyzThm35ReadingA_of_open
#print axioms ZInQ.Frontier.frozenTarget_of_open
