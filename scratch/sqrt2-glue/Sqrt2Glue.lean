import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.RingClassTwo

/-!
# sqrt2-glue: `√2 ∉ ℍ'_n` (`SqrtTwoNotInHHprime`, TYZ Lemma `torsion2`, Step 3)

Task sqrt2-glue (2026-11-14). Report: `docs/research/sqrt2-glue.md`; log: `scratch/sqrt2-glue/log.md`.

`SqrtTwoNotInHHprime` and `SigmaLift` are copied verbatim from `scratch/tyz-318/Lemma318.lean`, with
tyz-318's proof of `SigmaLift → SqrtTwoNotInHHprime`.

Route A of `docs/research/tyz-318.md` §3.2, in factorization form (no Chebotarev over `L_n(i)`):
`h` is a product of Frobenius elements over `F = L_n(i)` at the prime factors of `α𝓞_F`, where
`α = 1 + 2i∏_{q∣n}(1 + √q*)/2`.

* `FrobNormLaw`: a Frobenius over `F` at a prime `P ∤ 2` acts on `H_{d,4}` as the Artin symbol of the
  relative norm `N_{F/K_d}(P)` (Tau Ceti's ring-class reciprocity at primes, plus the comparison of
  Frobenius exponents `N P = (N 𝔭)^f`).
* `NormSigma`: some `α ∈ 𝓞_F` coprime to `2` has `[N_{F/K_{d₀}}(α𝓞_F)] = σ_{1+2ϖ}` in
  `Pic(ℤ + 4𝓞_{K_{d₀}})` for every `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.TYZGenus.Sqrt2Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

/-! ## §0. The target and tyz-318's reduction (verbatim copies) -/

/-- **GLUE G-√2 (`√2 ∉ ℍ'_n`)**, verbatim from `scratch/tyz-318/Lemma318.lean`: for squarefree
`n ≡ 5 (mod 8)`, `2` is not a square in `ℍ'_n`. TYZ prove this as Step 3 of their proof of Lemma
`torsion2`. -/
def SqrtTwoNotInHHprime : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ s ∈ HHprime n, s ^ 2 ≠ 2

/-- **A common lift of the `σ_{1+2ϖ}`**, verbatim from `scratch/tyz-318/Lemma318.lean`: some
`h ∈ Gal(ℚ̄/ℚ)` fixes `L_n(i)` pointwise and acts on every `H̄_{d₀,4}` as `σ_{1+2ϖ}`. -/
def SigmaLift : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ Lni n, h x = x) ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀, ∀ y : H4 d₀,
      h (embed d₀ (y : SeparableClosure (QNeg d₀))) =
        embed d₀ ((artin4 d₀ (sigmaClass d₀) y : H4 d₀) : SeparableClosure (QNeg d₀))

theorem Hprimebar_eq (d : ℕ) [NeZero d] :
    Hprimebar d = ((Hprime d).restrictScalars ℚ).map (embed d) := by
  rw [Hprimebar, dite_eq_right (NeZero.ne d)]

/-- `σ_{1+2ϖ}` moves `√2` (tyz-318, verbatim). -/
theorem sigma_moves_sqrtTwo {d : ℕ} [NeZero d] (hd : d % 8 = 5) :
    ((artin4 d (sigmaClass d) ⟨sqrtK (QNeg d) 2,
        adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ : H4 d) :
      SeparableClosure (QNeg d)) = -sqrtK (QNeg d) 2 := by
  set σ := artin4 d (sigmaClass d)
  set w : H4 d := ⟨sqrtK (QNeg d) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩
  have hw2 : w * w = 2 := by
    apply Subtype.ext
    show sqrtK (QNeg d) 2 * sqrtK (QNeg d) 2 = 2
    rw [← sq, sqrtK_sq]; norm_num
  have hσw : σ w * σ w = w * w := by rw [← map_mul, hw2, map_ofNat]
  rcases mul_self_eq_mul_self_iff.mp hσw with e | e
  · exfalso
    apply not_adjSqrt_two_le_Hprime hd
    rw [IntermediateField.adjoin_simple_le_iff]
    show ((w : H4 d) : SeparableClosure (QNeg d)) ∈ Hprime d
    rw [Hprime, IntermediateField.mem_lift, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer _ w := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact e
    exact hst hg
  · rw [e]; rfl

/-- **`SqrtTwoNotInHHprime` from `SigmaLift`** (tyz-318, verbatim: Route A, steps 5–7). -/
theorem sqrtTwoNotInHHprime_of_sigmaLift (hL : SigmaLift) : SqrtTwoNotInHHprime := by
  intro n hn hsq s hs hs2
  obtain ⟨h, hLni, hH⟩ := hL n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  -- `h` fixes every `H̄'_{d₀}`
  have hfixH : ∀ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), ∀ x ∈ Hprimebar d₀, h x = x := by
    intro d₀ hd₀ x hx
    rw [Finset.mem_filter] at hd₀
    haveI : NeZero d₀ := ⟨by omega⟩
    rw [Hprimebar_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ Hprime d₀ := hy
    have hyH4 : y ∈ H4 d₀ := Hprime_le_H4 d₀ hy'
    have hz := (IntermediateField.mem_lift (⟨y, hyH4⟩ : H4 d₀)).mp hy'
    rw [IntermediateField.mem_fixedField_iff] at hz
    have hσz := hz (artin4 d₀ (sigmaClass d₀)) (Subgroup.mem_zpowers _)
    have e : ((artin4 d₀ (sigmaClass d₀) ⟨y, hyH4⟩ : H4 d₀) : SeparableClosure (QNeg d₀)) = y :=
      congrArg Subtype.val hσz
    have key := hH d₀ hd₀.1 hd₀.2 ‹NeZero d₀› ⟨y, hyH4⟩
    have k2 := key.trans (congrArg (embed d₀) e)
    exact k2
  -- `h` fixes `ℍ'_n`
  have hmemF : ∀ y, h y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers h) := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers h ≤ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) y := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hy
    exact hst hg
  have hF : HHprime n ≤ IntermediateField.fixedField (Subgroup.zpowers h) := by
    apply sup_le
    · intro x hx; exact hmemF x (hLni x hx)
    · apply iSup₂_le
      intro d₀ hd₀ x hx
      exact hmemF x (hfixH d₀ hd₀ x hx)
  have hhs : h s = s := by
    have := hF hs
    rw [IntermediateField.mem_fixedField_iff] at this
    exact this h (Subgroup.mem_zpowers _)
  -- `h` moves `√2`
  set w : H4 n := ⟨sqrtK (QNeg n) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ with hw
  have hmove : h (embed n (w : SeparableClosure (QNeg n))) = -embed n (w : SeparableClosure (QNeg n)) := by
    rw [hH n (Nat.mem_divisors_self n (by omega)) hn inferInstance w, hw, sigma_moves_sqrtTwo hn,
      map_neg]
  have hw2 : (embed n (w : SeparableClosure (QNeg n))) ^ 2 = 2 := by
    rw [← map_pow, hw]
    show embed n (sqrtK (QNeg n) 2 ^ 2) = 2
    rw [sqrtK_sq]; simp only [Int.cast_ofNat]; exact map_ofNat (embed n) 2
  have hsw : s ^ 2 = (embed n (w : SeparableClosure (QNeg n))) ^ 2 := by rw [hs2, hw2]
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsw with e | e
  · rw [e, hmove] at hhs
    exact hs0 (by rw [e]; linear_combination hhs.symm / 2)
  · rw [e, map_neg, hmove, neg_neg] at hhs
    exact hs0 (by rw [e]; linear_combination -hhs / 2)

/-! ## §1. Definitions: `K_d → F`, relative norms, Picard classes -/

/-- `K_d = ℚ(√−d) → ℚ̄` through `K_dˢ` and `embed d` (the embedding used for `H̄_{d,4}`). -/
def kEmb (d : ℕ) [NeZero d] : QNeg d →ₐ[ℚ] Qbar :=
  (embed d).comp (IsScalarTower.toAlgHom ℚ (QNeg d) (SeparableClosure (QNeg d)))

/-- `K_d → F` when `kEmb d` lands in `F`. -/
def iotaK (F : IntermediateField ℚ Qbar) (d : ℕ) [NeZero d] (h : ∀ k, kEmb d k ∈ F) :
    QNeg d →ₐ[ℚ] F :=
  (kEmb d).codRestrict F.toSubalgebra h

/-- **The relative norm `N_{F/K_d}` of an ideal of `𝓞_F`**, for `F ⊂ ℚ̄` a number field containing
`kEmb d (K_d)`, with `K_d → F` given by `iotaK` (Mathlib's `Ideal.relNorm`); `⊥` otherwise. -/
def relNormK (F : IntermediateField ℚ Qbar) (d : ℕ) [NeZero d] (P : Ideal (𝓞 F)) :
    Ideal (𝓞 (QNeg d)) := by
  classical
  exact if h : (∀ k, kEmb d k ∈ F) ∧ FiniteDimensional ℚ F then
    letI : Algebra (QNeg d) F := (iotaK F d h.1).toRingHom.toAlgebra
    haveI : FiniteDimensional ℚ F := h.2
    haveI : NumberField F := ⟨⟩
    Ideal.relNorm (𝓞 (QNeg d)) P
  else ⊥

open Classical in
/-- The class in `Pic(ℤ + 4𝓞_{K_d})` of an ideal of `𝓞_{K_d}` prime to the conductor (`1` for other
ideals). `sigmaClass d = classOf (span {3 + 2√−d})` by definition. -/
def classOf {d : ℕ} [NeZero d] (J : Ideal (𝓞 (QNeg d))) : Pic (O4 d) :=
  if h : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨J, h⟩ else 1

theorem sigmaClass_eq_classOf (d : ℕ) [NeZero d] :
    sigmaClass d = classOf (Ideal.span {alpha d}) := rfl

/-! ## §2. The two Props -/

/-- **GLUE `FrobNormLaw` (norm compatibility of ring-class reciprocity, at primes)**: let `F ⊂ ℚ̄` be a
number field, normal over `ℚ`, `D` a finite set of indices and `P` a nonzero prime of `𝓞_F` with
`2 ∉ P`. Then some `h ∈ Gal(ℚ̄/F)` (a Frobenius at a prime above `P`) acts on `H̄_{d,4}`, for every
`d ∈ D` with `K_d ⊂ F`, as the Artin symbol of the relative norm `N_{F/K_d}(P) = 𝔭^f` in
`Pic(ℤ + 4𝓞_{K_d})`.

Proof (below, `frobNormLaw`): Mathlib's Frobenius over `𝓞_F` in a finite Galois `M ⊇ F, H̄_{d,4}`;
on `H_{d,4}` it is an arithmetic Frobenius over `𝓞_{K_d}` with exponent `N P = (N 𝔭)^f`, as is
`Art([𝔭])^f` (Tau Ceti `isArithFrobAt_ringClassArtinEquiv_picClass`); both agree since `𝔭 ∤ 4` is
unramified in `H_{d,4}` (Tau Ceti `isUnramifiedAt_ringClassField`). Standard (norm functoriality of
the Artin map, e.g. Neukirch, *Algebraic Number Theory*, VI.5, UNVERIFIED number). -/
def FrobNormLaw : Prop :=
  ∀ F : IntermediateField ℚ Qbar, FiniteDimensional ℚ F → Normal ℚ F →
    ∀ D : Finset ℕ, ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → (2 : 𝓞 F) ∉ P →
      ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ F, h x = x) ∧
        ∀ d ∈ D, ∀ _ : NeZero d, (∀ k, kEmb d k ∈ F) → ∀ y : H4 d,
          h (embed d (y : SeparableClosure (QNeg d))) =
            embed d ((artin4 d (classOf (relNormK F d P)) y : H4 d) : SeparableClosure (QNeg d))

/-- **GLUE `NormSigma` (an element of `L_n(i)` whose norms have class `σ_{1+2ϖ}`)**: for squarefree
`n ≡ 5 (mod 8)` some `α ∈ 𝓞_{L_n(i)}`, `α ≠ 0`, coprime to `2`, has
`[N_{L_n(i)/K_{d₀}}(α𝓞)] = σ_{1+2ϖ}` in `Pic(ℤ + 4𝓞_{K_{d₀}})` for every `d₀ ∣ n`,
`d₀ ≡ 5 (mod 8)`. Route A, step 1: `α = 1 + 2i∏_{q∣n}(1 + √q*)/2`
(`docs/research/tyz-318.md` §3.2; checked numerically by `scratch/tyz-318/trace_check.py`). -/
def NormSigma : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ α : 𝓞 (Lni n), α ≠ 0 ∧ IsCoprime α 2 ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀,
      classOf (relNormK (Lni n) d₀ (Ideal.span {α})) = sigmaClass d₀

/-! ## §3. Ideal-theoretic lemmas -/

section Generic

variable {L : Type*} [Field L] [NumberField L]

/-- An ideal of odd absolute norm is coprime to `2`. -/
theorem isCoprime_two_of_odd_absNorm {J : Ideal (𝓞 L)} (h : Odd (Ideal.absNorm J)) :
    IsCoprime J (Ideal.span {(2 : 𝓞 L)}) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  obtain ⟨k, hk⟩ := h
  have h1 : ((Ideal.absNorm J : ℕ) : 𝓞 L) ∈ J := Ideal.absNorm_mem J
  have e : (1 : 𝓞 L) = ((Ideal.absNorm J : ℕ) : 𝓞 L) - 2 * (k : 𝓞 L) := by
    rw [hk]; push_cast; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left h1)
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

/-- A nonzero ideal coprime to `2` has odd absolute norm (Cauchy's theorem in `𝓞_L / J`). -/
theorem odd_absNorm_of_isCoprime_two {J : Ideal (𝓞 L)} (hJ0 : J ≠ ⊥)
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 L)})) : Odd (Ideal.absNorm J) := by
  rw [Nat.odd_iff]
  by_contra hev
  have h2 : 2 ∣ Nat.card (𝓞 L ⧸ J) := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; omega
  haveI : Finite (𝓞 L ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have h2x : (2 : 𝓞 L ⧸ J) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, nsmul_eq_mul] at this
    exact_mod_cast this
  have hc : Ideal.Quotient.mk J c * 2 = 1 := by
    have : Ideal.Quotient.mk J (a + c * 2) = 1 := by rw [hab, map_one]
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_ofNat] at this
    exact this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk J c * 2) * x := by rw [hc, one_mul]
      _ = Ideal.Quotient.mk J c * (2 * x) := by ring
      _ = 0 := by rw [h2x, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  omega

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

/-- The relative norm of a nonzero ideal coprime to `2` is coprime to `2`. -/
theorem relNorm_isCoprime_two {J : Ideal (𝓞 L)} (hJ0 : J ≠ ⊥)
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 L)})) :
    IsCoprime (Ideal.relNorm (𝓞 K) J) (Ideal.span {(2 : 𝓞 K)}) := by
  apply isCoprime_two_of_odd_absNorm
  rw [Ideal.absNorm_relNorm]
  exact odd_absNorm_of_isCoprime_two hJ0 h

end Generic

section PicClass

variable {d : ℕ} [NeZero d]

theorem absNorm_span_natCast' (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have e : (p : 𝓞 (QNeg d)) = algebraMap ℤ (𝓞 (QNeg d)) (p : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]
  simp

/-- An ideal of `𝓞_{K_d}` coprime to `2` is prime to the conductor of `ℤ + 4𝓞_{K_d}`. -/
theorem mem_primeTo_of_isCoprime_two {J : Ideal (𝓞 (QNeg d))}
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 (QNeg d))})) :
    J ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at h
    have := absNorm_span_natCast' (d := d) 2
    rw [show ((2 : ℕ) : 𝓞 (QNeg d)) = 2 by norm_num, h, Ideal.absNorm_top] at this
    norm_num at this
  · have h4 : IsCoprime J (Ideal.span {(2 : 𝓞 (QNeg d))} ^ 2) := h.pow_right
    rw [Ideal.span_singleton_pow, Ideal.isCoprime_iff_sup_eq] at h4
    rw [eq_top_iff, ← h4]
    apply sup_le_sup_left
    rw [Ideal.span_singleton_le_iff_mem]
    have := natCast_mul_mem_conductor (QNeg d) 4 1
    rw [mul_one] at this
    convert this using 1
    norm_num

theorem classOf_of_mem {J : Ideal (𝓞 (QNeg d))} (h : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus) :
    classOf J = (O4 d).picClass ⟨J, h⟩ := by
  rw [classOf, dif_pos h]

theorem classOf_mul {I J : Ideal (𝓞 (QNeg d))} (hI : I ∈ integralIdealsPrimeTo (O4 d).conductorModulus)
    (hJ : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus) :
    classOf (I * J) = classOf I * classOf J := by
  rw [classOf_of_mem hI, classOf_of_mem hJ, classOf_of_mem (Submonoid.mul_mem _ hI hJ), ← map_mul]
  rfl

theorem classOf_top : classOf (⊤ : Ideal (𝓞 (QNeg d))) = 1 := by
  have h1 : (⊤ : Ideal (𝓞 (QNeg d))) ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
    rw [← Ideal.one_eq_top]; exact (integralIdealsPrimeTo (O4 d).conductorModulus).one_mem
  rw [classOf_of_mem h1]
  have e : (⟨⊤, h1⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) = 1 :=
    Subtype.ext Ideal.one_eq_top.symm
  rw [e, map_one]

end PicClass

section RelNormK

variable (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] (d : ℕ) [NeZero d]
  (hK : ∀ k, kEmb d k ∈ F)
include hK

theorem relNormK_mul (I J : Ideal (𝓞 F)) :
    relNormK F d (I * J) = relNormK F d I * relNormK F d J := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact map_mul _ _ _

theorem relNormK_top : relNormK F d ⊤ = ⊤ := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact Ideal.relNorm_top _

theorem relNormK_ne_bot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : relNormK F d I ≠ ⊥ := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact Ideal.relNorm_eq_bot_iff.not.mpr hI

theorem relNormK_isCoprime {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (h : IsCoprime I (Ideal.span {(2 : 𝓞 F)})) :
    IsCoprime (relNormK F d I) (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact relNorm_isCoprime_two hI h

end RelNormK

/-! ## §4. Assembly: `SigmaLift` from `FrobNormLaw` and `NormSigma` -/

/-- Square roots of `−d₀` lie in `L_n(i)` for `d₀ ∣ n` squarefree. -/
theorem mem_Lni_of_sq_eq_neg {n d₀ : ℕ} (hsq : Squarefree n) (hd : d₀ ∣ n) {x : Qbar}
    (hx : x ^ 2 = -(d₀ : Qbar)) : x ∈ Lni n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hsqd : Squarefree d₀ := hsq.squarefree_of_dvd hd
  have hroot : ∀ p ∈ d₀.primeFactors, ∃ s ∈ Lni n, s ^ 2 = (p : Qbar) := by
    intro p hp
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p : Qbar) (by norm_num : 0 < 2)
    refine ⟨s, IntermediateField.subset_adjoin _ _ (Or.inr ⟨p, ?_, hs⟩), hs⟩
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hd, hn0⟩
  choose! s hsL hs2 using hroot
  set r : Qbar := iQ * ∏ p ∈ d₀.primeFactors, s p with hr
  have hrL : r ∈ Lni n :=
    (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n)
      ((Lni n).prod_mem fun p hp => hsL p hp)
  have hr2 : r ^ 2 = -(d₀ : Qbar) := by
    rw [hr, mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl hs2, iQ_sq]
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqd]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hr2.symm) with e | e
  · rw [e]; exact hrL
  · rw [e]; exact (Lni n).neg_mem hrL

theorem kEmb_mem_Lni {n d₀ : ℕ} [NeZero d₀] (hsq : Squarefree n) (hd : d₀ ∣ n) :
    ∀ k, kEmb d₀ k ∈ Lni n := by
  intro k
  have hk : k = algebraMap ℚ (QNeg d₀) k.re + algebraMap ℚ (QNeg d₀) k.im * QuadraticAlgebra.omega := by
    ext <;> simp
  have hω : kEmb d₀ QuadraticAlgebra.omega ∈ Lni n := by
    apply mem_Lni_of_sq_eq_neg hsq hd
    rw [← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hk, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact (Lni n).add_mem ((Lni n).algebraMap_mem _)
    ((Lni n).mul_mem ((Lni n).algebraMap_mem _) hω)

theorem finiteDimensional_Lni {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    FiniteDimensional ℚ (Lni n) := by
  haveI : NeZero n := ⟨by omega⟩
  have hle := Lni_le_Hprimebar (by omega) hsq
  have : FiniteDimensional ℚ (Hprimebar n) := by
    rw [Hprimebar_eq]
    have : FiniteDimensional ℚ (Hprime n) := Module.Finite.trans (QNeg n) (Hprime n)
    have : FiniteDimensional ℚ ((Hprime n).restrictScalars ℚ) :=
      inferInstanceAs (FiniteDimensional ℚ (Hprime n))
    exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap ((Hprime n).restrictScalars ℚ) (embed n)).toLinearEquiv
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

/-- A product of nonzero ideals coprime to `I` is nonzero and coprime to `I`. -/
theorem prod_ne_bot_isCoprime {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R}
    (t : Multiset (Ideal R)) (ht : ∀ Q ∈ t, Q ≠ ⊥ ∧ IsCoprime Q I) :
    t.prod ≠ ⊥ ∧ IsCoprime t.prod I := by
  induction t using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Ideal.one_eq_top]
    exact ⟨top_ne_bot, Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq I)⟩
  | cons Q u ihu =>
    obtain ⟨h1, h2⟩ := ihu (fun R hR => ht R (Multiset.mem_cons_of_mem hR))
    obtain ⟨h3, h4⟩ := ht Q (Multiset.mem_cons_self _ _)
    rw [Multiset.prod_cons]
    refine ⟨fun h0 => ?_, h4.mul_left h2⟩
    rcases Ideal.mul_eq_bot.mp h0 with e | e
    · exact h3 e
    · exact h1 e

/-- **`SigmaLift` from `FrobNormLaw` and `NormSigma`** (product of Frobenius elements over the prime
factors of `α𝓞_F`). -/
theorem sigmaLift_of (hF : FrobNormLaw) (hN : NormSigma) : SigmaLift := by
  intro n hn hsq
  obtain ⟨α, hα0, hα2, hασ⟩ := hN n hn hsq
  haveI hFD : FiniteDimensional ℚ (Lni n) := finiteDimensional_Lni hn hsq
  haveI : NumberField (Lni n) := ⟨⟩
  haveI : Normal ℚ (Lni n) := ZInQ.Contrib.TYZGenus.Package.normal_Lni n
  set D := n.divisors.filter (fun d => d % 8 = 5)
  -- the claim, by induction on a multiset of primes
  have claim : ∀ s : Multiset (Ideal (𝓞 (Lni n))),
      (∀ P ∈ s, P.IsPrime ∧ P ≠ ⊥ ∧ IsCoprime P (Ideal.span {(2 : 𝓞 (Lni n))})) →
      ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ Lni n, h x = x) ∧
        ∀ d ∈ D, ∀ _ : NeZero d, (∀ k, kEmb d k ∈ Lni n) → ∀ y : H4 d,
          h (embed d (y : SeparableClosure (QNeg d))) =
            embed d ((artin4 d (classOf (relNormK (Lni n) d s.prod)) y : H4 d) :
              SeparableClosure (QNeg d)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      refine ⟨AlgEquiv.refl, fun x _ => rfl, ?_⟩
      intro d _ _ hK y
      rw [Multiset.prod_zero, Ideal.one_eq_top, relNormK_top (Lni n) d hK, classOf_top, map_one]
      rfl
    | cons P t ih =>
      intro hs
      obtain ⟨hP, hP0, hP2⟩ := hs P (Multiset.mem_cons_self _ _)
      obtain ⟨ht, htF, htH⟩ := ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
      have hP2' : (2 : 𝓞 (Lni n)) ∉ P := by
        intro h2
        rw [Ideal.isCoprime_iff_sup_eq] at hP2
        apply hP.ne_top
        rw [eq_top_iff, ← hP2]
        exact sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).mpr h2)
      obtain ⟨hp, hpF, hpH⟩ := hF (Lni n) hFD inferInstance D P hP hP0 hP2'
      refine ⟨hp * ht, fun x hx => by rw [AlgEquiv.mul_apply, htF x hx, hpF x hx], ?_⟩
      intro d hd hd0 hK y
      -- the product `t.prod` is nonzero and coprime to `2`
      have htprod := prod_ne_bot_isCoprime t (fun Q hQ =>
          ⟨(hs Q (Multiset.mem_cons_of_mem hQ)).2.1, (hs Q (Multiset.mem_cons_of_mem hQ)).2.2⟩)
      have hcP := mem_primeTo_of_isCoprime_two (relNormK_isCoprime (Lni n) d hK hP0 hP2)
      have hct := mem_primeTo_of_isCoprime_two (relNormK_isCoprime (Lni n) d hK htprod.1 htprod.2)
      rw [AlgEquiv.mul_apply, htH d hd hd0 hK y, hpH d hd hd0 hK, Multiset.prod_cons,
        relNormK_mul (Lni n) d hK, classOf_mul hcP hct, map_mul]
      rfl
  -- apply the claim to the prime factors of `α𝓞_F`
  have hspan0 : Ideal.span {α} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨h, hfix, hact⟩ := claim (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {α}))
    (by
      intro P hP
      have hPprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      have hPne : P ≠ ⊥ := hPprime.ne_zero
      refine ⟨Ideal.isPrime_of_prime hPprime, hPne, ?_⟩
      have hαP : α ∈ P := by
        have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
        rw [Ideal.dvd_iff_le] at hdvd
        exact hdvd (Ideal.mem_span_singleton_self α)
      obtain ⟨a, b, hab⟩ := hα2
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left a hαP))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ b (Ideal.mem_span_singleton_self _))))
  refine ⟨h, hfix, ?_⟩
  intro d₀ hd₀ hd₀5 hd₀0 y
  have hK := kEmb_mem_Lni (d₀ := d₀) hsq (Nat.dvd_of_mem_divisors hd₀)
  rw [hact d₀ (Finset.mem_filter.mpr ⟨hd₀, hd₀5⟩) hd₀0 hK y,
    Ideal.prod_normalizedFactors_eq_self hspan0, hασ d₀ hd₀ hd₀5 hd₀0]

/-- **`SqrtTwoNotInHHprime` from `FrobNormLaw` and `NormSigma`.** -/
theorem sqrtTwoNotInHHprime_of (hF : FrobNormLaw) (hN : NormSigma) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of_sigmaLift (sigmaLift_of hF hN)

/-! ## §5. Frobenius comparison: an exponent-`(N𝔭)^f` Frobenius is `Art(𝔭)^f` -/

section FrobPow

/-- Iterating a Frobenius-type congruence. -/
theorem iterate_congr {S : Type*} [CommRing S] (Q : Ideal S) (φ : S → S) (m : ℕ)
    (hφ : ∀ x, φ x - x ^ m ∈ Q) (hQ : ∀ x y, x - y ∈ Q → φ x - φ y ∈ Q) :
    ∀ k x, φ^[k] x - x ^ (m ^ k) ∈ Q := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    have h1 := hφ (φ^[k] x)
    have h2 : (φ^[k] x) ^ m - (x ^ (m ^ k)) ^ m ∈ Q :=
      Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ m) (ih x)
    have e : φ (φ^[k] x) - x ^ (m ^ (k + 1)) =
        (φ (φ^[k] x) - (φ^[k] x) ^ m) + ((φ^[k] x) ^ m - (x ^ (m ^ k)) ^ m) := by
      rw [← pow_mul, ← pow_succ]; ring
    rw [e]; exact Q.add_mem h1 h2

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- **An automorphism acting as `x ↦ x^{(N𝔭)^f}` modulo an unramified `Q` is `φ^f`**, `φ` an arithmetic
Frobenius at `Q` (reduction to Tau Ceti's uniqueness `isArithFrobAt_eq_of_isUnramifiedAt`). -/
theorem eq_pow_of_congr {Q : Ideal (𝓞 L)} [hQ : Q.IsPrime] [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {φ τ : L ≃ₐ[K] L} (hφ : IsArithFrobAt (𝓞 K) φ Q) (f : ℕ)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ (Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ f) ∈ Q) : τ = φ ^ f := by
  set N := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hN
  have hNpos : 0 < N := hφ.card_pos
  have hφ' : ∀ x : 𝓞 L, φ • x - x ^ N ∈ Q := fun x => hφ x
  have hφQ : ∀ x y : 𝓞 L, x - y ∈ Q → φ • x - φ • y ∈ Q := by
    intro x y hxy
    have := hφ.le_comap hxy
    rw [Ideal.mem_comap, map_sub] at this
    exact this
  -- `φ^f` has exponent `N^f`
  have hφf : ∀ x : 𝓞 L, φ ^ f • x - x ^ (N ^ f) ∈ Q := by
    intro x
    have := iterate_congr Q (fun x => φ • x) N hφ' hφQ f x
    rwa [smul_iterate_apply] at this
  -- `τ` preserves `Q`
  have hτQ1 : ∀ j : ℕ, ∀ x ∈ Q, τ ^ j • x ∈ Q := by
    intro j
    induction j with
    | zero => intro x hx; rwa [pow_zero, one_smul]
    | succ j ih =>
      intro x hx
      rw [pow_succ', mul_smul]
      have h1 := ih x hx
      have h2 := hτ (τ ^ j • x)
      have h3 : (τ ^ j • x) ^ (N ^ f) ∈ Q := Q.pow_mem_of_mem h1 _ (pow_pos hNpos f)
      have := Q.add_mem h2 h3
      rwa [sub_add_cancel] at this
  have hfin : IsOfFinOrder τ := isOfFinOrder_of_finite τ
  have hτinv : ∀ x ∈ Q, τ⁻¹ • x ∈ Q := by
    intro x hx
    have e : τ⁻¹ = τ ^ (orderOf τ - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hfin.orderOf_pos,
        pow_orderOf_eq_one]
    rw [e]; exact hτQ1 _ x hx
  -- `ρ = τ⁻¹ φ^f` acts trivially modulo `Q`
  set ρ := τ⁻¹ * φ ^ f with hρ
  have hρ1 : ∀ x : 𝓞 L, ρ • x - x ∈ Q := by
    intro x
    have hd : φ ^ f • x - τ • x ∈ Q := by
      have := Q.sub_mem (hφf x) (hτ x)
      rwa [sub_sub_sub_cancel_right] at this
    have := hτinv _ hd
    rw [smul_sub, inv_smul_smul, ← mul_smul] at this
    exact this
  -- `φρ` is an arithmetic Frobenius at `Q`, hence `φρ = φ`
  have hφρ : IsArithFrobAt (𝓞 K) (φ * ρ) Q := by
    intro x
    show (φ * ρ) • x - x ^ N ∈ Q
    have h1 := hφQ _ _ (hρ1 x)
    have h2 := hφ' x
    have e : (φ * ρ) • x - x ^ N = (φ • ρ • x - φ • x) + (φ • x - x ^ N) := by
      rw [mul_smul]; ring
    rw [e]; exact Q.add_mem h1 h2
  have := isArithFrobAt_eq_of_isUnramifiedAt hφρ hφ
  have hρ1' : ρ = 1 := by
    have := congrArg (φ⁻¹ * ·) this
    simpa using this
  rw [hρ, inv_mul_eq_one] at hρ1'
  exact hρ1'

end FrobPow

/-! ## §6. Transport `H_{d,4} ≅ H̄_{d,4}` and the Frobenius over `F` on `H_{d,4}` -/

section Transport

variable {d : ℕ} [NeZero d]

/-- `H_{d,4} ≅ H̄_{d,4} ⊂ ℚ̄` through `embed d`. -/
def psi4 (d : ℕ) [NeZero d] : ((H4 d).restrictScalars ℚ) ≃ₐ[ℚ] H4bar d :=
  (IntermediateField.equivMap ((H4 d).restrictScalars ℚ) (embed d)).trans
    (IntermediateField.equivOfEq (H4bar_eq_map (d := d)).symm)

theorem psi4_apply (y : (H4 d).restrictScalars ℚ) :
    ((psi4 d y : H4bar d) : Qbar) = embed d (y : SeparableClosure (QNeg d)) := rfl

instance instNormalH4bar : Normal ℚ (H4bar d) := normal_H4bar d

/-- `h ∈ Gal(ℚ̄/ℚ)` transported to a `ℚ`-automorphism of `H_{d,4}`. -/
def tauQ4 (h : Qbar ≃ₐ[ℚ] Qbar) : ((H4 d).restrictScalars ℚ) ≃ₐ[ℚ] ((H4 d).restrictScalars ℚ) :=
  ((psi4 d).trans (h.restrictNormal (H4bar d))).trans (psi4 d).symm

theorem psi4_tauQ4 (h : Qbar ≃ₐ[ℚ] Qbar) (y : (H4 d).restrictScalars ℚ) :
    ((psi4 d (tauQ4 (d := d) h y) : H4bar d) : Qbar) = h ((psi4 d y : H4bar d) : Qbar) := by
  simp only [tauQ4, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes h (H4bar d) (psi4 d y)

/-- If `h` fixes `kEmb d (K_d)`, its transport is a `K_d`-automorphism of `H_{d,4}`. -/
def tau4 (h : Qbar ≃ₐ[ℚ] Qbar) (hK : ∀ k, h (kEmb d k) = kEmb d k) : Gal(H4 d / QNeg d) :=
  AlgEquiv.ofRingEquiv (f := (tauQ4 (d := d) h).toRingEquiv) (fun c => by
    apply Subtype.ext
    apply (embed d).injective
    have e := psi4_tauQ4 (d := d) h
      (⟨algebraMap (QNeg d) (SeparableClosure (QNeg d)) c, (H4 d).algebraMap_mem c⟩ :
        (H4 d).restrictScalars ℚ)
    rw [psi4_apply, psi4_apply] at e
    exact e.trans (hK c))

theorem coe_tau4 (h : Qbar ≃ₐ[ℚ] Qbar) (hK : ∀ k, h (kEmb d k) = kEmb d k) (y : H4 d) :
    ((tau4 h hK y : H4 d) : SeparableClosure (QNeg d)) =
      ((tauQ4 (d := d) h y : (H4 d).restrictScalars ℚ) : SeparableClosure (QNeg d)) := rfl

theorem classOf_pow {J : Ideal (𝓞 (QNeg d))} (hJ : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus)
    (k : ℕ) : classOf (J ^ k) = classOf J ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, classOf_top]
  | succ k ih =>
    have hk : J ^ k ∈ integralIdealsPrimeTo (O4 d).conductorModulus := Submonoid.pow_mem _ hJ k
    rw [pow_succ, classOf_mul hk hJ, ih, pow_succ]

end Transport

/-- **The Frobenius over `F` on `H_{d,4}`**: let `F ⊂ M ⊂ ℚ̄` be number fields with `K_d ⊂ F` and
`H̄_{d,4} ⊂ M`, `𝔔` a prime of `𝓞_M` over a nonzero prime `P ∌ 2` of `𝓞_F`, and `h ∈ Gal(ℚ̄/F)`
acting as `x ↦ x^{N P}` modulo `𝔔` on `𝓞_M`. Then `h` acts on `H̄_{d,4}` as the Artin symbol of
`N_{F/K_d}(P) = 𝔭^f`. -/
theorem frob_on_H4 (F M : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [FiniteDimensional ℚ M]
    (hFM : F ≤ M) (d : ℕ) [NeZero d] (hK : ∀ k, kEmb d k ∈ F) (hHM : H4bar d ≤ M)
    (h : Qbar ≃ₐ[ℚ] Qbar) (hfix : ∀ x ∈ F, h x = x) (𝔔 : Ideal (𝓞 M)) [𝔔.IsPrime]
    (P : Ideal (𝓞 F)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hP2 : (2 : 𝓞 F) ∉ P)
    (hPQ : ∀ a : 𝓞 F, a ∈ P ↔
      RingOfIntegers.mapRingHom (IntermediateField.inclusion hFM).toRingHom a ∈ 𝔔)
    (hfrob : ∀ x b : 𝓞 M, ((b : M) : Qbar) =
      h ((x : M) : Qbar) - ((x : M) : Qbar) ^ Nat.card (𝓞 F ⧸ P) → b ∈ 𝔔) :
    ∀ y : H4 d, h (embed d (y : SeparableClosure (QNeg d))) =
      embed d ((artin4 d (classOf (relNormK F d P)) y : H4 d) : SeparableClosure (QNeg d)) := by
  haveI : NumberField F := ⟨⟩
  haveI : NumberField M := ⟨⟩
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  have hKfix : ∀ k, h (kEmb d k) = kEmb d k := fun k => hfix _ (hK k)
  obtain ⟨τ, hτval⟩ : ∃ τ : Gal(H4 d / QNeg d), ∀ y : H4 d,
      embed d ((τ y : H4 d) : SeparableClosure (QNeg d)) =
        h (embed d ((y : H4 d) : SeparableClosure (QNeg d))) :=
    ⟨tau4 h hKfix, fun y => psi4_tauQ4 (d := d) h (y : H4 d)⟩
  let ψ : 𝓞 (H4 d) →+* 𝓞 M := RingOfIntegers.mapRingHom
    ((IntermediateField.inclusion hHM).toRingHom.comp (psi4 d).toRingHom)
  have hψ : ∀ y : 𝓞 (H4 d), (((ψ y : 𝓞 M) : M) : Qbar) =
      embed d ((y : H4 d) : SeparableClosure (QNeg d)) := fun y => rfl
  set Q' := 𝔔.comap ψ with hQ'
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  set q := Nat.card (𝓞 F ⧸ P) with hqdef
  -- the congruence for `τ`
  have hτ : ∀ y : 𝓞 (H4 d), τ • y - y ^ q ∈ Q' := by
    intro y
    rw [hQ', Ideal.mem_comap]
    apply hfrob (ψ y) (ψ (τ • y - y ^ q))
    have e1 : (((ψ (τ • y) : 𝓞 M) : M) : Qbar) = h (((ψ y : 𝓞 M) : M) : Qbar) := by
      rw [hψ, hψ]
      exact hτval (y : H4 d)
    rw [map_sub, map_pow]
    push_cast
    rw [e1]
  -- the prime `𝔭` of `𝓞_{K_d}` below
  set 𝔭 := Q'.under (𝓞 (QNeg d)) with h𝔭def
  have hιeq : ∀ k : 𝓞 (QNeg d),
      RingOfIntegers.mapRingHom (IntermediateField.inclusion hFM).toRingHom
        (algebraMap (𝓞 (QNeg d)) (𝓞 F) k) = ψ (algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) k) := by
    intro k
    apply RingOfIntegers.ext
    apply Subtype.ext
    rfl
  have hP𝔭 : P.under (𝓞 (QNeg d)) = 𝔭 := by
    ext k
    rw [Ideal.under_def, Ideal.mem_comap, hPQ, hιeq, h𝔭def, Ideal.under_def, Ideal.mem_comap,
      hQ', Ideal.mem_comap]
  haveI : P.LiesOver 𝔭 := ⟨hP𝔭.symm⟩
  have h2𝔭 : (2 : 𝓞 (QNeg d)) ∉ 𝔭 := by
    rw [← hP𝔭, Ideal.under_def, Ideal.mem_comap, map_ofNat]; exact hP2
  have h𝔭0 : 𝔭 ≠ ⊥ := by rw [← hP𝔭]; exact Ideal.under_ne_bot _ hP0
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  haveI h𝔭max : 𝔭.IsMaximal := h𝔭prime.isMaximal h𝔭0
  haveI : P.IsMaximal := hP.isMaximal hP0
  -- the relative norm and the exponent
  have hrel : relNormK F d P = 𝔭 ^ P.inertiaDeg (𝓞 (QNeg d)) := by
    simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
    exact Ideal.relNorm_eq_pow_of_isMaximal P 𝔭
  have hq : q = Nat.card (𝓞 (QNeg d) ⧸ 𝔭) ^ P.inertiaDeg (𝓞 (QNeg d)) := by
    have := Ideal.cardQuot_pow_inertiaDeg 𝔭 P
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at this
    exact this.symm
  -- the class of `𝔭`
  have hco : IsCoprime 𝔭 (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have := h𝔭max.eq_of_le hne le_sup_left
    exact h2𝔭 (this ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h𝔭mem := mem_primeTo_of_isCoprime_two hco
  set f := P.inertiaDeg (𝓞 (QNeg d))
  have hclass : classOf (relNormK F d P) = (O4 d).picClass ⟨𝔭, h𝔭mem⟩ ^ f := by
    rw [hrel, classOf_pow h𝔭mem, classOf_of_mem h𝔭mem]
  -- Frobenius at `Q'` and unramifiedness
  haveI : ((⟨𝔭, h𝔭mem⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := h𝔭max
  haveI : Q'.LiesOver ((⟨𝔭, h𝔭mem⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := ⟨rfl⟩
  have hφ := isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨𝔭, h𝔭mem⟩ Q'
  have hndvd : ¬ (⟨𝔭, h𝔭prime, h𝔭0⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 (QNeg d))).asIdeal ∣
      (O4 d).conductor := by
    intro hdvd
    rw [Ideal.dvd_iff_le] at hdvd
    have h1 := ((mem_integralIdealsPrimeTo_conductorModulus_iff (O := O4 d)).mp h𝔭mem).2
    rw [sup_eq_left.mpr hdvd] at h1
    exact h𝔭max.ne_top h1
  haveI : Q'.LiesOver (⟨𝔭, h𝔭prime, h𝔭0⟩ :
    IsDedekindDomain.HeightOneSpectrum (𝓞 (QNeg d))).asIdeal := ⟨rfl⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 (QNeg d)) Q' :=
    isUnramifiedAt_ringClassField (O4 d) hndvd Q'
  have hτ' : ∀ x : 𝓞 (H4 d), τ • x - x ^ (Nat.card (𝓞 (QNeg d) ⧸ Q'.under (𝓞 (QNeg d))) ^ f) ∈ Q' := by
    intro x
    have e : Nat.card (𝓞 (QNeg d) ⧸ Q'.under (𝓞 (QNeg d))) ^ f = q := hq.symm
    rw [e]
    exact hτ x
  have hτφ : τ = ringClassArtinEquiv (O4 d) ((O4 d).picClass ⟨𝔭, h𝔭mem⟩) ^ f :=
    eq_pow_of_congr (K := QNeg d) (L := H4 d) (Q := Q') hφ f hτ'
  intro y
  rw [show artin4 d = ringClassArtinEquiv (O4 d) from rfl, hclass, map_pow, ← hτφ]
  exact (hτval y).symm

/-! ## §7. `FrobNormLaw` holds -/

instance finiteDimensional_H4bar (d : ℕ) : FiniteDimensional ℚ (H4bar d) := by
  by_cases h : d = 0
  · subst h; rw [H4bar, dite_eq_left rfl]; infer_instance
  · haveI : NeZero d := ⟨h⟩
    rw [H4bar_eq_map]
    have : FiniteDimensional ℚ (H4 d) := Module.Finite.trans (QNeg d) (H4 d)
    have : FiniteDimensional ℚ ((H4 d).restrictScalars ℚ) :=
      inferInstanceAs (FiniteDimensional ℚ (H4 d))
    exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap ((H4 d).restrictScalars ℚ) (embed d)).toLinearEquiv

/-- **`FrobNormLaw` holds** (no hypotheses). -/
theorem frobNormLaw : FrobNormLaw := by
  intro F hFD hFN D P hP hP0 hP2
  haveI := hFD
  haveI := hFN
  haveI : NumberField F := ⟨⟩
  set M : IntermediateField ℚ Qbar := F ⊔ ⨆ d : D, H4bar (d : ℕ) with hM
  haveI : FiniteDimensional ℚ M := by rw [hM]; infer_instance
  haveI : Normal ℚ M := by rw [hM]; infer_instance
  haveI : NumberField M := ⟨⟩
  have hFM : F ≤ M := le_sup_left
  have hHM : ∀ d ∈ D, H4bar d ≤ M := fun d hd =>
    le_sup_of_le_right (le_iSup (fun d : D => H4bar (d : ℕ)) ⟨d, hd⟩)
  letI : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsGalois ℚ M := ⟨⟩
  haveI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  haveI : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let _ := IsIntegralClosure.MulSemiringAction (𝓞 F) F M (𝓞 M)
  have := Algebra.isInvariant_of_isGalois (𝓞 F) F M (𝓞 M)
  haveI : SMulCommClass (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) := ⟨fun g r x => by
    change galRestrict (𝓞 F) F M (𝓞 M) g (r • x) = r • galRestrict (𝓞 F) F M (𝓞 M) g x
    exact map_smul _ r x⟩
  -- a prime `𝔔` of `𝓞_M` over `P`
  obtain ⟨𝔔, -, h𝔔, h𝔔P⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 M))
    (by
      intro a ha
      rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot] at ha
      have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 M)) :=
        FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 M)
      rw [hinj (ha.trans (map_zero _).symm)]
      exact P.zero_mem)
  haveI := h𝔔
  have h𝔔0 : 𝔔 ≠ ⊥ := by
    rintro rfl
    apply hP0
    rw [← h𝔔P]
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ha
      exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 M) (ha.trans (map_zero _).symm)
    · rintro rfl; exact map_zero _
  haveI : Finite (𝓞 M ⧸ 𝔔) := Ring.HasFiniteQuotients.finiteQuotient h𝔔0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 F) (M ≃ₐ[F] M) 𝔔
  -- lift `σ` to `h ∈ Gal(ℚ̄/ℚ)`
  obtain ⟨h, hres⟩ : ∃ h : Qbar ≃ₐ[ℚ] Qbar, AlgEquiv.restrictNormal h M = σ.restrictScalars ℚ :=
    ⟨(σ.restrictScalars ℚ).liftNormal Qbar, (σ.restrictScalars ℚ).restrict_liftNormal Qbar⟩
  have hσM : ∀ x : M, ((σ x : M) : Qbar) = h (x : Qbar) := by
    intro x
    have := AlgEquiv.restrictNormal_commutes h M x
    rw [hres] at this
    exact this
  have hσx : ∀ x : 𝓞 M, (((σ • x : 𝓞 M) : M) : Qbar) = h ((x : M) : Qbar) := by
    intro x
    rw [← hσM]
    change ((algebraMap (𝓞 M) M (galRestrict (𝓞 F) F M (𝓞 M) σ x) : M) : Qbar) = _
    rw [algebraMap_galRestrict_apply]
  have hfixF : ∀ x ∈ F, h x = x := by
    intro x hx
    have e1 := hσM (algebraMap F M ⟨x, hx⟩)
    rw [AlgEquiv.commutes] at e1
    exact e1.symm
  refine ⟨h, hfixF, ?_⟩
  intro d hd hd0 hK y
  apply frob_on_H4 F M hFM d hK (hHM d hd) h hfixF 𝔔 P hP0 hP2
  · intro a
    rw [← h𝔔P, Ideal.under_def, Ideal.mem_comap]
    rfl
  · intro x b hb
    have hσ' := hσ x
    have hu : 𝔔.under (𝓞 F) = P := h𝔔P
    have e2 : (((σ • x - x ^ Nat.card (𝓞 F ⧸ P) : 𝓞 M) : M) : Qbar) =
        h ((x : M) : Qbar) - ((x : M) : Qbar) ^ Nat.card (𝓞 F ⧸ P) := by
      rw [← hσx]
      push_cast
      rfl
    have e : b = σ • x - x ^ Nat.card (𝓞 F ⧸ P) :=
      RingOfIntegers.ext (Subtype.ext (hb.trans e2.symm))
    rw [e]
    have : (MulSemiringAction.toAlgHom (𝓞 F) (𝓞 M) σ) x = σ • x := rfl
    rw [← this, ← hu]
    exact hσ'

/-- **`SqrtTwoNotInHHprime` from `NormSigma` alone.** -/
theorem sqrtTwoNotInHHprime_of_normSigma (hN : NormSigma) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of frobNormLaw hN

end ZInQ.Contrib.TYZGenus.Sqrt2Glue

#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sigmaLift_of
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.frobNormLaw
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sqrtTwoNotInHHprime_of_normSigma
