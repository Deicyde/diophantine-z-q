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

/-! ## §8. From the norm congruence `N(α) ≡ 1 ± 2√−d₀ (mod 4)` to `NormSigma` -/

section NormClass

variable {d : ℕ} [NeZero d]

theorem intCast_add_four_mul_mem (a : ℤ) (y : 𝓞 (QNeg d)) :
    ((a : 𝓞 (QNeg d)) + 4 * y) ∈ (O4 d).toRingOfIntegers := by
  rw [mem_toRingOfIntegers]
  refine ⟨a, y, ?_⟩
  push_cast
  rfl

theorem isCoprime_span_two_of_eq {x y : 𝓞 (QNeg d)} (h : x = 1 + 2 * y) :
    IsCoprime (Ideal.span {x}) (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, -y, by rw [h]; ring⟩

theorem classOf_span_mul_eq_one {x y : 𝓞 (QNeg d)}
    (hx : IsCoprime (Ideal.span {x}) (Ideal.span {(2 : 𝓞 (QNeg d))}))
    (hy : IsCoprime (Ideal.span {y}) (Ideal.span {(2 : 𝓞 (QNeg d))}))
    (hxy : x * y ∈ (O4 d).toRingOfIntegers) :
    classOf (Ideal.span {x}) * classOf (Ideal.span {y}) = 1 := by
  have hmx := mem_primeTo_of_isCoprime_two hx
  have hmy := mem_primeTo_of_isCoprime_two hy
  rw [← classOf_mul hmx hmy, Ideal.span_singleton_mul_span_singleton,
    classOf_of_mem (by rw [← Ideal.span_singleton_mul_span_singleton]; exact Submonoid.mul_mem _ hmx hmy),
    picClass_eq_one_iff]
  exact ⟨x * y, hxy, rfl⟩

/-- **The class of `1 + 2ε√−d + 4γ` is `σ_{1+2ϖ}`** (`ε = ±1`, `d ≡ 5 (mod 8)`): its product with
`3 − 2ε√−d` lies in `ℤ + 4𝓞_K`, and `3 ∓ 2√−d` both have class `σ^{±1} = σ`. -/
theorem classOf_span_congr (hd : d % 8 = 5) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (γ : 𝓞 (QNeg d)) :
    classOf (Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d + 4 * γ}) = sigmaClass d := by
  have hε2 : (ε : 𝓞 (QNeg d)) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  set u := 1 + 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d + 4 * γ with hu
  set v := 3 - 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d with hv
  have hcu := isCoprime_span_two_of_eq (x := u) (y := ε * sqrtNeg d + 2 * γ) (by rw [hu]; ring)
  have hcv := isCoprime_span_two_of_eq (x := v) (y := 1 - ε * sqrtNeg d) (by rw [hv]; ring)
  have huv : u * v ∈ (O4 d).toRingOfIntegers := by
    have e : u * v = ((3 + 4 * (d : ℤ) : ℤ) : 𝓞 (QNeg d)) +
        4 * (ε * sqrtNeg d + γ * (3 - 2 * ε * sqrtNeg d)) := by
      rw [hu, hv]
      push_cast
      linear_combination (-4 : 𝓞 (QNeg d)) * (ε : 𝓞 (QNeg d)) * ε * sqrtNeg_mul_self (d := d) +
        (4 * (d : 𝓞 (QNeg d))) * hε2
    rw [e]; exact intCast_add_four_mul_mem _ _
  have h1 := classOf_span_mul_eq_one hcu hcv huv
  have hσ2 : sigmaClass d * sigmaClass d = 1 := by rw [← sq]; exact sigmaClass_sq
  have hσ : sigmaClass d = classOf (Ideal.span {alpha d}) := rfl
  have hca : IsCoprime (Ideal.span {alpha d}) (Ideal.span {(2 : 𝓞 (QNeg d))}) :=
    isCoprime_span_two_of_eq (y := 1 + sqrtNeg d) (by unfold alpha; ring)
  rcases hε with rfl | rfl
  · -- `v = 3 − 2√−d`, `v · α = 9 + 4d`
    have hva : v * alpha d ∈ (O4 d).toRingOfIntegers := by
      have e : v * alpha d = ((9 + 4 * (d : ℤ) : ℤ) : 𝓞 (QNeg d)) + 4 * 0 := by
        rw [hv]; unfold alpha; push_cast
        linear_combination (-4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)
      rw [e]; exact intCast_add_four_mul_mem _ _
    have h2 := classOf_span_mul_eq_one hcv hca hva
    rw [← hσ] at h2
    -- `cu * cv = 1` and `cv * σ = 1`, so `cu = σ`
    calc classOf (Ideal.span {u}) = classOf (Ideal.span {u}) * (classOf (Ideal.span {v}) * sigmaClass d) := by
          rw [h2, mul_one]
      _ = (classOf (Ideal.span {u}) * classOf (Ideal.span {v})) * sigmaClass d := by rw [mul_assoc]
      _ = sigmaClass d := by rw [h1, one_mul]
  · -- `v = 3 + 2√−d = α`
    have hva : v = alpha d := by rw [hv]; unfold alpha; push_cast; ring
    rw [hva, ← hσ] at h1
    calc classOf (Ideal.span {u}) = classOf (Ideal.span {u}) * (sigmaClass d * sigmaClass d) := by
          rw [hσ2, mul_one]
      _ = (classOf (Ideal.span {u}) * sigmaClass d) * sigmaClass d := by rw [mul_assoc]
      _ = sigmaClass d := by rw [h1, one_mul]

end NormClass

/-- **GLUE `NormCongr` (the norm congruence of Route A, step 1)**: for squarefree `n ≡ 5 (mod 8)` some
`α ∈ 𝓞_{L_n(i)}`, `α ≠ 0`, coprime to `2`, has `N_{L_n(i)/K_{d₀}}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_{K_{d₀}}`
with `ε = ±1`, `γ ∈ 𝓞_{K_{d₀}}`, for every `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`. For
`α = 1 + 2i∏_{q∣n}(1 + √q*)/2`: `N(1 + 2β) ≡ 1 + 2 Tr(β) (mod 4)` and `Tr_{L_n(i)/K_{d₀}}(β) = ±√−d₀`
(`docs/research/tyz-318.md` §3.2). -/
def NormCongr : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ α : 𝓞 (Lni n), α ≠ 0 ∧ IsCoprime α 2 ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ γ : 𝓞 (QNeg d₀), relNormK (Lni n) d₀ (Ideal.span {α}) =
        Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ}

theorem normSigma_of (h : NormCongr) : NormSigma := by
  intro n hn hsq
  obtain ⟨α, hα0, hα2, hα⟩ := h n hn hsq
  refine ⟨α, hα0, hα2, ?_⟩
  intro d₀ hd₀ hd₀5 hd₀0
  obtain ⟨ε, hε, γ, hrel⟩ := hα d₀ hd₀ hd₀5 hd₀0
  rw [hrel]
  exact classOf_span_congr hd₀5 hε γ

/-- **`SqrtTwoNotInHHprime` from `NormCongr` alone.** -/
theorem sqrtTwoNotInHHprime_of_normCongr (h : NormCongr) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of_normSigma (normSigma_of h)

/-! ## §9. Rational arithmetic for the multiquadratic field `L_n(i)` -/

section Arith

/-- `p* = ±p ≡ 1 (mod 4)` for an odd prime `p`. -/
def pstar (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

theorem pstar_mod_four {p : ℕ} (hp : p % 2 = 1) : pstar p % 4 = 1 := by
  unfold pstar
  split_ifs with h
  · omega
  · omega

theorem pstar_eq_or (p : ℕ) : pstar p = p ∨ pstar p = -p := by
  unfold pstar; split_ifs <;> simp

/-- `p ∤ ∏_{q ∈ V} q*` for a prime `p ∉ V`, `V` a set of primes. -/
theorem not_dvd_prod_pstar (V : Finset ℕ) (hV : ∀ q ∈ V, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpV : p ∉ V) : ¬ (p : ℤ) ∣ ∏ q ∈ V, pstar q := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨q, hq, hdvd⟩ := (Prime.dvd_finset_prod_iff hpZ _).mp h
  have hpq : (p : ℤ) ∣ (q : ℤ) := by
    rcases pstar_eq_or q with e | e <;> rw [e] at hdvd
    · exact hdvd
    · exact (dvd_neg).mp hdvd
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp (hV q hq)).mp (Int.natCast_dvd_natCast.mp hpq)
  exact hpV (this ▸ hq)

/-- `p · r` with `p ∤ r` is not a rational square. -/
theorem not_sq_of_mul {p : ℕ} (hp : p.Prime) {r : ℤ} (hr : ¬ (p : ℤ) ∣ r) (q : ℚ) :
    (((p : ℤ) * r : ℤ) : ℚ) ≠ q ^ 2 := by
  intro h
  have hsq : IsSquare ((p : ℤ) * r) := Rat.isSquare_intCast_iff.mp ⟨q, by rw [h, sq]⟩
  obtain ⟨k, hk⟩ := hsq
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpk : (p : ℤ) ∣ k := by
    have : (p : ℤ) ∣ k * k := ⟨r, hk.symm⟩
    rcases hpZ.dvd_or_dvd this with h | h <;> exact h
  obtain ⟨j, rfl⟩ := hpk
  apply hr
  refine ⟨j * j, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hp0
  rw [hk]; ring

/-- `∏_{p ∣ d} p* = d` for squarefree `d ≡ 1 (mod 4)`. -/
theorem prod_pstar_primeFactors {d : ℕ} (hsq : Squarefree d) (hd : d % 4 = 1) :
    ∏ p ∈ d.primeFactors, pstar p = d := by
  have hsgn : ∀ p, pstar p = (if p % 4 = 1 then 1 else -1) * (p : ℤ) := by
    intro p; unfold pstar; split_ifs <;> simp
  have hprod : ∏ p ∈ d.primeFactors, pstar p =
      (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) * d := by
    rw [Finset.prod_congr rfl (fun p _ => hsgn p), Finset.prod_mul_distrib]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hS : (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) = 1 ∨
      (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) = -1 := by
    apply Finset.prod_induction _ (fun x => x = 1 ∨ x = -1)
    · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    · simp
    · intro p _; split_ifs <;> simp
  have hmod : (∏ p ∈ d.primeFactors, pstar p) % 4 = 1 := by
    apply Finset.prod_induction _ (fun x : ℤ => x % 4 = 1)
    · intro a b ha hb; rw [Int.mul_emod, ha, hb]; rfl
    · rfl
    · intro p hp
      apply pstar_mod_four
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
      · subst h2; obtain ⟨k, rfl⟩ := hpd; omega
      · exact h2
  rcases hS with h | h
  · rw [hprod, h, one_mul]
  · rw [hprod, h] at hmod ⊢
    exfalso
    have : ((d : ℤ)) % 4 = 1 := by exact_mod_cast hd
    omega

end Arith

/-! ## §10. Traces of square roots and degrees of multiquadratic fields -/

section TraceSq

open Polynomial

/-- `Tr_{L/K}(x) = 0` if `x² ∈ K` and `x ∉ K`. -/
theorem trace_eq_zero_of_sq {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {x : L} {c : K} (hx : x ^ 2 = algebraMap K L c) (hxK : x ∉ (algebraMap K L).range) :
    Algebra.trace K L x = 0 := by
  have hint : IsIntegral K x := .of_finite K x
  have hmin : minpoly K x = X ^ 2 - C c := by
    have hdvd : minpoly K x ∣ X ^ 2 - C c := minpoly.dvd K x (by simp [hx])
    have hmon : (X ^ 2 - C c : K[X]).Monic := monic_X_pow_sub_C c two_ne_zero
    have hdeg : (X ^ 2 - C c : K[X]).natDegree = 2 := natDegree_X_pow_sub_C
    have h2 := (minpoly.two_le_natDegree_iff hint).mpr hxK
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd
      (by rw [hdeg]; exact h2)).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, Polynomial.nextCoeff, natDegree_X_pow_sub_C]
  simp

/-- `[ℚ(T) : ℚ] ≤ 2^{#T}` for a finite set `T` of elements with rational squares. -/
theorem finrank_adjoin_sq_le {E : Type*} [Field E] [Algebra ℚ E] (T : Finset E)
    (hT : ∀ t ∈ T, ∃ c : ℚ, t ^ 2 = algebraMap ℚ E c) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (T : Set E)) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set E)) ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, IntermediateField.adjoin_empty, Finset.card_empty, pow_zero]
    refine ⟨inferInstance, ?_⟩
    rw [IntermediateField.finrank_bot]
  | insert a T haT ih =>
    obtain ⟨hfd, hle⟩ := ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    obtain ⟨c, hc⟩ := hT a (Finset.mem_insert_self a T)
    have hint : IsIntegral ℚ a := by
      refine ⟨X ^ 2 - C c, monic_X_pow_sub_C c two_ne_zero, ?_⟩
      simp [hc]
    have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hdvd : minpoly ℚ a ∣ X ^ 2 - C c := minpoly.dvd ℚ a (by simp [hc])
      have := Polynomial.natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero two_pos c)
      rwa [natDegree_X_pow_sub_C] at this
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI := hfd
    have heq : IntermediateField.adjoin ℚ ((insert a T : Finset E) : Set E) =
        IntermediateField.adjoin ℚ ({a} : Set E) ⊔ IntermediateField.adjoin ℚ (T : Set E) := by
      rw [Finset.coe_insert, Set.insert_eq, IntermediateField.adjoin_union]
    rw [heq, Finset.card_insert_of_notMem haT]
    refine ⟨inferInstance, ?_⟩
    calc Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({a} : Set E) ⊔ IntermediateField.adjoin ℚ (T : Set E))
        ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) *
          Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set E)) :=
          IntermediateField.finrank_sup_le _ _
      _ ≤ 2 * 2 ^ T.card := Nat.mul_le_mul hdeg hle
      _ = 2 ^ (T.card + 1) := by ring

end TraceSq

/-! ## §11. `N(1 + 2β) ≡ 1 + 2 Tr(β) (mod 4)` and traces of sums of square roots -/

section NormTrace

/-- `∏ (1 + 2 f_i) = 1 + 2 Σ f_i + 4 Z` with `Z` integral over `ℤ`. -/
theorem prod_one_add_two {E ι : Type*} [CommRing E] (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, IsIntegral ℤ (f i)) :
    ∃ Z : E, IsIntegral ℤ Z ∧ ∏ i ∈ s, (1 + 2 * f i) = 1 + 2 * ∑ i ∈ s, f i + 4 * Z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s has ih =>
    obtain ⟨Z, hZ, hprod⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha := hf a (Finset.mem_insert_self a s)
    have hS : IsIntegral ℤ (∑ i ∈ s, f i) :=
      IsIntegral.sum _ (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨Z + f a * ∑ i ∈ s, f i + (f a * Z + f a * Z), ?_, ?_⟩
    · exact (hZ.add (ha.mul hS)).add ((ha.mul hZ).add (ha.mul hZ))
    · rw [Finset.prod_insert has, Finset.sum_insert has, hprod]
      ring

/-- **`N_{F/K}(1 + 2β) = 1 + 2 Tr_{F/K}(β) + 4γ`** with `γ ∈ K` integral over `ℤ`, for `β` integral. -/
theorem norm_one_add_two_mul {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] (β : F) (hβ : IsIntegral ℤ β) :
    ∃ γ : K, IsIntegral ℤ γ ∧ Algebra.norm K (1 + 2 * β) = 1 + 2 * Algebra.trace K F β + 4 * γ := by
  let E := AlgebraicClosure K
  have hN := Algebra.norm_eq_prod_embeddings K E (1 + 2 * β)
  have hT := trace_eq_sum_embeddings E (K := K) (L := F) (x := β)
  obtain ⟨Z, hZ, hprod⟩ := prod_one_add_two (Finset.univ : Finset (F →ₐ[K] E))
    (fun σ => σ β) (fun σ _ => hβ.map σ)
  have h4K : (4 : K) ≠ 0 := by norm_num
  set γ : K := (Algebra.norm K (1 + 2 * β) - 1 - 2 * Algebra.trace K F β) / 4 with hγ
  refine ⟨γ, ?_, by rw [hγ, mul_div_cancel₀ _ h4K]; ring⟩
  have hγE : algebraMap K E γ * 4 = Z * 4 := by
    have e1 : ∏ σ : F →ₐ[K] E, σ (1 + 2 * β) = ∏ σ : F →ₐ[K] E, (1 + 2 * σ β) := by
      apply Finset.prod_congr rfl; intro σ _; rw [map_add, map_mul, map_one, map_ofNat]
    have e2 : γ * 4 = Algebra.norm K (1 + 2 * β) - 1 - 2 * Algebra.trace K F β := by
      rw [hγ, div_mul_cancel₀ _ h4K]
    have e3 := congrArg (algebraMap K E) e2
    rw [map_mul, map_ofNat, map_sub, map_sub, map_mul, map_one, map_ofNat, hN, hT, e1, hprod] at e3
    rw [e3]; ring
  have h4E : (4 : E) ≠ 0 := by
    rw [show (4 : E) = algebraMap K E 4 by rw [map_ofNat]]
    exact (map_ne_zero _).mpr h4K
  have hγZ : algebraMap K E γ = Z := mul_right_cancel₀ h4E hγE
  have : IsIntegral ℤ (algebraMap K E γ) := hγZ ▸ hZ
  exact isIntegral_algebraMap_iff.mp this

/-- **Trace of a sum of square roots**: if `x_{i₀} ∈ K` and every other `x_i` has `x_i² ∈ K`,
`x_i ∉ K`, then `Tr(c Σ x_i) = c [F:K] x_{i₀}`. -/
theorem trace_sum_sq {K F ι : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (I : Finset ι) (x : ι → F) (i₀ : ι) (hi₀ : i₀ ∈ I) (k₀ : K) (hx₀ : x i₀ = algebraMap K F k₀)
    (hx : ∀ i ∈ I, i ≠ i₀ → (∃ c : K, x i ^ 2 = algebraMap K F c) ∧ x i ∉ (algebraMap K F).range)
    (c : K) :
    Algebra.trace K F (algebraMap K F c * ∑ i ∈ I, x i) = c * (Module.finrank K F • k₀) := by
  rw [← Algebra.smul_def, map_smul, map_sum, Finset.sum_eq_single i₀]
  · rw [hx₀, Algebra.trace_algebraMap, smul_eq_mul]
  · intro i hi hne
    obtain ⟨⟨c', hc'⟩, hnot⟩ := hx i hi hne
    exact trace_eq_zero_of_sq hc' hnot
  · intro h; exact absurd hi₀ h

end NormTrace

/-! ## §12. The element `α = 1 + 2i∏_{q∣n}(1 + √q*)/2` of `L_n(i)` -/

section Multiquad

open Polynomial

/-- A chosen square root of `p` in `ℚ̄`. -/
def sqrtQ (p : ℕ) : Qbar := (IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos).choose

theorem sqrtQ_sq (p : ℕ) : sqrtQ p ^ 2 = (p : Qbar) :=
  (IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos).choose_spec

/-- `√(p*)`, `p* = ±p ≡ 1 (mod 4)`. -/
def sQ (p : ℕ) : Qbar := if p % 4 = 1 then sqrtQ p else iQ * sqrtQ p

theorem sQ_sq (p : ℕ) : sQ p ^ 2 = ((pstar p : ℤ) : Qbar) := by
  unfold sQ pstar
  split_ifs with h
  · rw [sqrtQ_sq]; push_cast; rfl
  · rw [mul_pow, iQ_sq, sqrtQ_sq]; push_cast; ring

theorem sqrtQ_mem {n p : ℕ} (hp : p ∈ n.primeFactors) : sqrtQ p ∈ Lni n :=
  IntermediateField.subset_adjoin _ _ (Or.inr ⟨p, hp, sqrtQ_sq p⟩)

theorem sQ_mem {n p : ℕ} (hp : p ∈ n.primeFactors) : sQ p ∈ Lni n := by
  unfold sQ
  split_ifs
  · exact sqrtQ_mem hp
  · exact (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n) (sqrtQ_mem hp)

/-- `x_S = i ∏_{p ∈ S} √(p*)`. -/
def xS (S : Finset ℕ) : Qbar := iQ * ∏ p ∈ S, sQ p

theorem xS_sq (S : Finset ℕ) : xS S ^ 2 = -((∏ p ∈ S, pstar p : ℤ) : Qbar) := by
  unfold xS
  rw [mul_pow, iQ_sq, ← Finset.prod_pow, Finset.prod_congr rfl (fun p _ => sQ_sq p)]
  push_cast; ring

theorem xS_mem {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) : xS S ∈ Lni n :=
  (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n)
    ((Lni n).prod_mem fun p hp => sQ_mem (hS hp))

/-- `β = i ∏_{p ∣ n} (1 + √(p*))/2`. -/
def betaQ (n : ℕ) : Qbar := iQ * ∏ p ∈ n.primeFactors, (1 + sQ p) / 2

theorem betaQ_mem (n : ℕ) : betaQ n ∈ Lni n := by
  unfold betaQ
  refine (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n) ((Lni n).prod_mem fun p hp => ?_)
  exact (Lni n).div_mem ((Lni n).add_mem (Lni n).one_mem (sQ_mem hp)) (by
    have := (Lni n).algebraMap_mem (2 : ℚ); simpa using this)

theorem betaQ_eq (n : ℕ) : betaQ n =
    (1 / 2 : Qbar) ^ n.primeFactors.card * ∑ S ∈ n.primeFactors.powerset, xS S := by
  unfold betaQ xS
  have h1 : ∏ p ∈ n.primeFactors, (1 + sQ p) / 2 =
      (1 / 2 : Qbar) ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (sQ p + 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro p _; ring
  rw [h1, Finset.prod_add (fun p => sQ p) (fun _ => (1 : Qbar))]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _; ring

theorem isIntegral_half_one_add_sQ {p : ℕ} (hp : p % 2 = 1) : IsIntegral ℤ ((1 + sQ p) / 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, pstar p = 4 * c + 1 := ⟨pstar p / 4, by have := pstar_mod_four hp; omega⟩
  refine ⟨X ^ 2 - (X + C c), monic_X_pow_sub (by
    calc degree (X + C c : ℤ[X]) = 1 := degree_X_add_C c
      _ < 2 := by norm_num), ?_⟩
  have hs := sQ_sq p
  rw [hc] at hs
  simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X]
  have hcc : eval₂ (algebraMap ℤ Qbar) ((1 + sQ p) / 2) (C c) = (c : Qbar) := by
    rw [eval₂_C]; simp
  push_cast at hs ⊢
  rw [hcc]
  linear_combination hs / 4

theorem isIntegral_iQ : IsIntegral ℤ iQ := by
  refine ⟨X ^ 2 + 1, by monicity!, ?_⟩
  simp [iQ_sq]

theorem isIntegral_betaQ {n : ℕ} (hn : n % 2 = 1) : IsIntegral ℤ (betaQ n) := by
  unfold betaQ
  refine isIntegral_iQ.mul (IsIntegral.prod _ fun p hp => isIntegral_half_one_add_sQ ?_)
  have hpn := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
  · subst h2; obtain ⟨k, rfl⟩ := hpn; omega
  · exact h2

/-- One prime appearing once makes `±∏_U p* · ∏_V p*` a non-square. -/
theorem prod_pstar_not_sq {U V : Finset ℕ} (hU : ∀ q ∈ U, q.Prime) (hV : ∀ q ∈ V, q.Prime) {p : ℕ}
    (hpU : p ∈ U) (hpV : p ∉ V) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (q : ℚ) :
    ((σ * ((∏ x ∈ U, pstar x) * ∏ x ∈ V, pstar x) : ℤ) : ℚ) ≠ q ^ 2 := by
  have hp := hU p hpU
  obtain ⟨τ, hτ, hpτ⟩ : ∃ τ : ℤ, (τ = 1 ∨ τ = -1) ∧ pstar p = τ * p := by
    rcases pstar_eq_or p with e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [e]; ring⟩
  have e : σ * ((∏ x ∈ U, pstar x) * ∏ x ∈ V, pstar x) =
      (p : ℤ) * (σ * τ * ((∏ x ∈ U.erase p, pstar x) * ∏ x ∈ V, pstar x)) := by
    rw [← Finset.mul_prod_erase U _ hpU, hpτ]; ring
  rw [e]
  apply not_sq_of_mul hp
  intro hdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hστ : IsUnit (σ * τ) := by
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp
  rw [hστ.dvd_mul_left] at hdvd
  rcases hpZ.dvd_or_dvd hdvd with h | h
  · exact not_dvd_prod_pstar (U.erase p) (fun q hq => hU q (Finset.mem_of_mem_erase hq)) hp
      (Finset.notMem_erase p U) h
  · exact not_dvd_prod_pstar V hV hp hpV h

/-- `kEmb d₀ (k) ≠ x_S` unless `S` is the set of primes of `d₀`. -/
theorem kEmb_ne_xS {n d₀ : ℕ} [NeZero d₀] (hsq : Squarefree n) (hd : d₀ ∣ n) (hd4 : d₀ % 4 = 1)
    {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (hSD : S ≠ d₀.primeFactors) (k : QNeg d₀) :
    kEmb d₀ k ≠ xS S := by
  intro hk
  have hsqd : Squarefree d₀ := hsq.squarefree_of_dvd hd
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (hS hq)
  have hDp : ∀ q ∈ d₀.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  set w := kEmb d₀ QuadraticAlgebra.omega with hw
  have hw2 : w ^ 2 = -(d₀ : Qbar) := by
    rw [hw, ← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp
  have hkk : k = algebraMap ℚ (QNeg d₀) k.re + algebraMap ℚ (QNeg d₀) k.im * QuadraticAlgebra.omega := by
    ext <;> simp
  set a := k.re; set b := k.im
  have hk' : algebraMap ℚ Qbar a + algebraMap ℚ Qbar b * w = xS S := by
    rw [← hk, hkk, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  set c : ℤ := ∏ p ∈ S, pstar p with hc
  have hsq2 : (algebraMap ℚ Qbar a + algebraMap ℚ Qbar b * w) ^ 2 = -((c : ℤ) : Qbar) := by
    rw [hk', xS_sq]
  -- `(a² − d₀ b² + c) + 2ab w = 0`
  have hlin : algebraMap ℚ Qbar (a ^ 2 - d₀ * b ^ 2 + c) + algebraMap ℚ Qbar (2 * a * b) * w = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_intCast, map_ofNat]
    linear_combination hsq2 - (algebraMap ℚ Qbar b) ^ 2 * hw2
  -- `w ∉ ℚ`
  have hab : 2 * a * b = 0 := by
    by_contra hne
    have h2ab : algebraMap ℚ Qbar (2 * a * b) ≠ 0 := (_root_.map_ne_zero _).mpr hne
    have hwq : w = algebraMap ℚ Qbar (-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) := by
      rw [map_div₀, map_neg, eq_div_iff h2ab]
      linear_combination hlin
    have h2 : algebraMap ℚ Qbar ((-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) ^ 2) =
        algebraMap ℚ Qbar (-(d₀ : ℚ)) := by
      rw [map_pow, ← hwq, hw2, map_neg, map_natCast]
    have h3 := (algebraMap ℚ Qbar).injective h2
    have h4 : (0 : ℚ) ≤ (-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) ^ 2 := sq_nonneg _
    rw [h3] at h4
    have : (0 : ℚ) < d₀ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d₀)
    linarith
  have hrat : a ^ 2 - d₀ * b ^ 2 + c = 0 := by
    rw [hab, map_zero, zero_mul, add_zero] at hlin
    exact (algebraMap ℚ Qbar).injective (hlin.trans (map_zero _).symm)
  rcases mul_eq_zero.mp hab with h | hb
  · rcases mul_eq_zero.mp h with h | ha
    · norm_num at h
    · -- `a = 0`: `∏_S p* = d₀ b²`, so `∏_S p* ∏_{D₀} p* = (d₀ b)²`
      rw [ha] at hrat
      have hd0' : (∏ p ∈ d₀.primeFactors, ((pstar p : ℤ) : ℚ)) = d₀ := by
        have := prod_pstar_primeFactors hsqd hd4
        exact_mod_cast this
      have hc' : (∏ p ∈ S, ((pstar p : ℤ) : ℚ)) = d₀ * b ^ 2 := by
        have : ((c : ℤ) : ℚ) = d₀ * b ^ 2 := by linarith
        rw [hc] at this; exact_mod_cast this
      have key : (((1 : ℤ) * ((∏ x ∈ S, pstar x) * ∏ x ∈ d₀.primeFactors, pstar x) : ℤ) : ℚ) =
          ((d₀ : ℚ) * b) ^ 2 := by
        push_cast
        rw [hd0', hc']; ring
      by_cases h1 : ∃ p ∈ S, p ∉ d₀.primeFactors
      · obtain ⟨p, hpS, hpD⟩ := h1
        exact prod_pstar_not_sq hSp hDp hpS hpD (Or.inl rfl) _ key
      · push_neg at h1
        have h2 : ∃ p ∈ d₀.primeFactors, p ∉ S := by
          by_contra h2; push_neg at h2
          exact hSD (Finset.Subset.antisymm h1 h2)
        obtain ⟨p, hpD, hpS⟩ := h2
        rw [mul_comm (∏ x ∈ S, pstar x)] at key
        exact prod_pstar_not_sq hDp hSp hpD hpS (Or.inl rfl) _ key
  · -- `b = 0`: `a² = −∏_S p*`
    rw [hb] at hrat
    by_cases hS0 : S = ∅
    · rw [hc, hS0, Finset.prod_empty] at hrat
      norm_num at hrat
      nlinarith [sq_nonneg a]
    · obtain ⟨p, hpS⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
      have hc' : (∏ p ∈ S, ((pstar p : ℤ) : ℚ)) = -a ^ 2 := by
        have : ((c : ℤ) : ℚ) = -a ^ 2 := by linarith
        rw [hc] at this; exact_mod_cast this
      have key : (((-1 : ℤ) * ((∏ x ∈ S, pstar x) * ∏ x ∈ (∅ : Finset ℕ), pstar x) : ℤ) : ℚ) =
          a ^ 2 := by
        rw [Finset.prod_empty, mul_one]; push_cast
        rw [hc']; ring
      exact prod_pstar_not_sq hSp (by simp) hpS (Finset.notMem_empty p) (Or.inr rfl) _ key


theorem finrank_Lni_le {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    Module.finrank ℚ (Lni n) ≤ 2 ^ (n.primeFactors.card + 1) := by
  classical
  set T : Finset Qbar := insert iQ (n.primeFactors.image sqrtQ) with hT
  have hTsq : ∀ t ∈ T, ∃ c : ℚ, t ^ 2 = algebraMap ℚ Qbar c := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨-1, by rw [iQ_sq]; simp⟩
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨p, by rw [sqrtQ_sq]; simp⟩
  obtain ⟨hfd, hle⟩ := finrank_adjoin_sq_le T hTsq
  have hsub : Lni n ≤ IntermediateField.adjoin ℚ (T : Set Qbar) := by
    rw [Lni, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨p, hp, hx⟩)
    · have hx' : x ^ 2 = iQ ^ 2 := by rw [iQ_sq]; exact hx
      have hi : iQ ∈ IntermediateField.adjoin ℚ (T : Set Qbar) :=
        IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with e | e
      · rw [e]; exact hi
      · rw [e]; exact (IntermediateField.adjoin ℚ (T : Set Qbar)).neg_mem hi
    · have hx' : x ^ 2 = sqrtQ p ^ 2 := by rw [sqrtQ_sq]; exact hx
      have hi : sqrtQ p ∈ IntermediateField.adjoin ℚ (T : Set Qbar) :=
        IntermediateField.subset_adjoin _ _
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)))
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with e | e
      · rw [e]; exact hi
      · rw [e]; exact (IntermediateField.adjoin ℚ (T : Set Qbar)).neg_mem hi
  haveI := hfd
  calc Module.finrank ℚ (Lni n) ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set Qbar)) :=
        IntermediateField.finrank_le_of_le_right hsub
    _ ≤ 2 ^ T.card := hle
    _ ≤ 2 ^ (n.primeFactors.card + 1) :=
        Nat.pow_le_pow_right two_pos ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ Finset.card_image_le))

/-- **The norm congruence at one `d₀`**: `N_{L_n(i)/K_{d₀}}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_{K_{d₀}}`. -/
theorem normCongr_at {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) {d₀ : ℕ} [NeZero d₀]
    (hd : d₀ ∈ n.divisors) (hd5 : d₀ % 8 = 5) (αO : 𝓞 (Lni n))
    (hα : ((αO : Lni n) : Qbar) = 1 + 2 * betaQ n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ γ : 𝓞 (QNeg d₀), relNormK (Lni n) d₀ (Ideal.span {αO}) =
      Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ} := by
  haveI hFD : FiniteDimensional ℚ (Lni n) := finiteDimensional_Lni hn hsq
  haveI : NumberField (Lni n) := ⟨⟩
  have hdn : d₀ ∣ n := Nat.dvd_of_mem_divisors hd
  have hK := kEmb_mem_Lni (d₀ := d₀) hsq hdn
  letI : Algebra (QNeg d₀) (Lni n) := (iotaK (Lni n) d₀ hK).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (QNeg d₀) (Lni n) :=
    IsScalarTower.of_algebraMap_eq (fun q => ((iotaK (Lni n) d₀ hK).commutes q).symm)
  haveI : FiniteDimensional (QNeg d₀) (Lni n) :=
    Module.Finite.of_restrictScalars_finite ℚ (QNeg d₀) (Lni n)
  have hval : ∀ k : QNeg d₀, ((algebraMap (QNeg d₀) (Lni n) k : Lni n) : Qbar) = kEmb d₀ k :=
    fun k => rfl
  set P := n.primeFactors with hP
  set r := P.card with hr
  have hD₀P : d₀.primeFactors ⊆ P := Nat.primeFactors_mono hdn (by omega)
  have hd4 : d₀ % 4 = 1 := by omega
  -- the elements `x_S` and `β` of `F`
  let xF : Finset ℕ → Lni n := fun S => if h : S ⊆ P then ⟨xS S, xS_mem h⟩ else 0
  have hxF : ∀ S ∈ P.powerset, ((xF S : Lni n) : Qbar) = xS S := fun S hS => by
    simp only [xF, dif_pos (Finset.mem_powerset.mp hS)]
  set βF : Lni n := ⟨betaQ n, betaQ_mem n⟩ with hβFdef
  have hβF : βF = algebraMap (QNeg d₀) (Lni n) (algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r)) *
      ∑ S ∈ P.powerset, xF S := by
    apply Subtype.ext
    show betaQ n = (((algebraMap (QNeg d₀) (Lni n) (algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r)) *
      ∑ S ∈ P.powerset, xF S : Lni n)) : Qbar)
    rw [IntermediateField.coe_mul, hval, AlgHom.commutes]
    have hsum : ((∑ S ∈ P.powerset, xF S : Lni n) : Qbar) = ∑ S ∈ P.powerset, ((xF S : Lni n) : Qbar) :=
      map_sum (Lni n).val xF P.powerset
    rw [hsum, Finset.sum_congr rfl hxF, betaQ_eq]
    simp only [one_div, inv_pow, map_pow, map_inv₀, map_ofNat]
    rfl
  -- `x_{D₀} = ε √−d₀`
  have hw2 : (kEmb d₀ QuadraticAlgebra.omega) ^ 2 = -(d₀ : Qbar) := by
    rw [← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp
  have hxD : xS d₀.primeFactors ^ 2 = (kEmb d₀ QuadraticAlgebra.omega) ^ 2 := by
    rw [xS_sq, hw2, prod_pstar_primeFactors (hsq.squarefree_of_dvd hdn) hd4]; push_cast; ring
  obtain ⟨ε, hε, hxDε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      xS d₀.primeFactors = kEmb d₀ ((ε : QNeg d₀) * QuadraticAlgebra.omega) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxD with e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [e]; simp⟩
  -- the trace of `β`
  set N := Module.finrank (QNeg d₀) (Lni n) with hN
  have htr : Algebra.trace (QNeg d₀) (Lni n) βF = algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r) *
      (N • ((ε : QNeg d₀) * QuadraticAlgebra.omega)) := by
    rw [hβF]
    apply trace_sum_sq P.powerset xF d₀.primeFactors (Finset.mem_powerset.mpr hD₀P)
    · apply Subtype.ext
      rw [hxF _ (Finset.mem_powerset.mpr hD₀P), hval, hxDε]
    · intro S hS hSD
      refine ⟨⟨algebraMap ℚ (QNeg d₀) (-((∏ p ∈ S, pstar p : ℤ) : ℚ)), ?_⟩, ?_⟩
      · apply Subtype.ext
        rw [IntermediateField.coe_pow, hxF S hS, xS_sq, hval, AlgHom.commutes, map_neg, map_intCast]
      · rintro ⟨k, hk⟩
        have h1 : ((algebraMap (QNeg d₀) (Lni n) k : Lni n) : Qbar) = ((xF S : Lni n) : Qbar) :=
          congrArg Subtype.val hk
        rw [hval, hxF S hS] at h1
        exact kEmb_ne_xS hsq hdn hd4 (Finset.mem_powerset.mp hS) hSD k h1
  -- integrality
  have hβint : IsIntegral ℤ βF := by
    have h1 : IsIntegral ℤ (algebraMap (Lni n) Qbar βF) := isIntegral_betaQ (by omega)
    exact isIntegral_algebraMap_iff.mp h1
  have htrint : IsIntegral ℤ (Algebra.trace (QNeg d₀) (Lni n) βF) := Algebra.isIntegral_trace hβint
  -- `[F : K_{d₀}] = 2^r`
  have hNle : N ≤ 2 ^ r := by
    have h1 := finrank_Lni_le hn hsq
    rw [← hP, ← hr] at h1
    have h2 := Module.finrank_mul_finrank ℚ (QNeg d₀) (Lni n)
    rw [QuadraticAlgebra.finrank_eq_two] at h2
    rw [← h2, pow_succ] at h1
    omega
  have hε2 : (ε : ℚ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hNdvd : 2 ^ r ∣ N := by
    set c : ℚ := (1 / 2) ^ r * N * ε with hc
    have hy : Algebra.trace (QNeg d₀) (Lni n) βF = algebraMap ℚ (QNeg d₀) c * QuadraticAlgebra.omega := by
      rw [htr, nsmul_eq_mul, hc, map_mul, map_mul, map_natCast, map_intCast]; ring
    have hy2 : (Algebra.trace (QNeg d₀) (Lni n) βF) ^ 2 =
        algebraMap ℚ (QNeg d₀) (-(d₀ : ℚ) * c ^ 2) := by
      rw [hy, mul_pow, sq QuadraticAlgebra.omega, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp only [map_mul, map_neg, map_pow, map_natCast, map_zero, zero_mul, mul_zero, add_zero,
        zero_smul]
      ring
    have hint2 : IsIntegral ℤ (algebraMap ℚ (QNeg d₀) (-(d₀ : ℚ) * c ^ 2)) := hy2 ▸ htrint.pow 2
    have hint3 : IsIntegral ℤ (-(d₀ : ℚ) * c ^ 2) := isIntegral_algebraMap_iff.mp hint2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint3
    have hm' : (m : ℚ) = -(d₀ : ℚ) * c ^ 2 := by rw [← hm]; simp
    have h2r : ((1 : ℚ) / 2) ^ r * 2 ^ r = 1 := by rw [← mul_pow]; norm_num
    have hq : (m : ℚ) * 4 ^ r = -((d₀ : ℚ) * (N : ℚ) ^ 2) := by
      have h4 : (4 : ℚ) ^ r = (2 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hm', h4, hc]
      calc -(d₀ : ℚ) * ((1 / 2) ^ r * N * ε) ^ 2 * (2 ^ r) ^ 2 =
          -(d₀ : ℚ) * N ^ 2 * ε ^ 2 * ((1 / 2) ^ r * 2 ^ r) ^ 2 := by ring
        _ = -((d₀ : ℚ) * (N : ℚ) ^ 2) := by rw [hε2, h2r]; ring
    have hz : m * 4 ^ r = -((d₀ : ℤ) * (N : ℤ) ^ 2) := by exact_mod_cast hq
    have hdvdZ : ((4 ^ r : ℕ) : ℤ) ∣ ((d₀ * N ^ 2 : ℕ) : ℤ) := ⟨-m, by push_cast; linarith⟩
    have hdvdN : 4 ^ r ∣ d₀ * N ^ 2 := Int.natCast_dvd_natCast.mp hdvdZ
    have hcop : Nat.Coprime (4 ^ r) d₀ := by
      apply Nat.Coprime.pow_left
      have : Nat.Coprime 2 d₀ := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4]; exact Nat.Coprime.pow_left 2 this
    have h1 : 4 ^ r ∣ N ^ 2 := hcop.dvd_of_dvd_mul_left hdvdN
    have h2 : (2 ^ r) ^ 2 ∣ N ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact h1
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp h2
  have hNeq : N = 2 ^ r := le_antisymm hNle (Nat.le_of_dvd Module.finrank_pos hNdvd)
  have htr' : Algebra.trace (QNeg d₀) (Lni n) βF = (ε : QNeg d₀) * QuadraticAlgebra.omega := by
    rw [htr, hNeq, nsmul_eq_mul, ← mul_assoc]
    have : algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r) * ((2 ^ r : ℕ) : QNeg d₀) = 1 := by
      rw [← map_natCast (algebraMap ℚ (QNeg d₀)), ← map_mul]
      push_cast
      rw [← mul_pow]; norm_num
    rw [this, one_mul]
  -- the norm
  obtain ⟨γK, hγint, hnorm⟩ := norm_one_add_two_mul (K := QNeg d₀) βF hβint
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 (QNeg d₀), algebraMap (𝓞 (QNeg d₀)) (QNeg d₀) γ = γK :=
    ⟨⟨γK, hγint⟩, rfl⟩
  refine ⟨ε, hε, γ, ?_⟩
  simp only [relNormK, dif_pos (And.intro hK hFD)]
  rw [Ideal.relNorm_singleton]
  have hαF : algebraMap (𝓞 (Lni n)) (Lni n) αO = 1 + 2 * βF := by
    apply Subtype.ext
    show ((αO : Lni n) : Qbar) = _
    rw [hα]; push_cast; rfl
  have key : Algebra.intNorm (𝓞 (QNeg d₀)) (𝓞 (Lni n)) αO =
      1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (QNeg d₀)) (QNeg d₀)
    rw [Algebra.algebraMap_intNorm (K := QNeg d₀) (L := Lni n), hαF, hnorm, htr']
    have e1 : algebraMap (𝓞 (QNeg d₀)) (QNeg d₀) (sqrtNeg d₀) = QuadraticAlgebra.omega := rfl
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_one, map_ofNat, map_ofNat, map_intCast,
      e1, hγ]
    ring
  rw [key]

end Multiquad

/-! ## §13. `NormCongr`, `NormSigma`, `SigmaLift` and `SqrtTwoNotInHHprime` hold -/

/-- `β ∈ 𝓞_{L_n(i)}` for odd `n`. -/
def betaO (n : ℕ) (hn : n % 2 = 1) : 𝓞 (Lni n) :=
  ⟨⟨betaQ n, betaQ_mem n⟩, (isIntegral_algebraMap_iff (B := Qbar)).mp (isIntegral_betaQ hn)⟩

theorem coe_betaO (n : ℕ) (hn : n % 2 = 1) : (((betaO n hn : 𝓞 (Lni n)) : Lni n) : Qbar) = betaQ n :=
  rfl

/-- **`NormCongr` holds**, with `α = 1 + 2β`, `β = i∏_{q∣n}(1 + √q*)/2`. -/
theorem normCongr : NormCongr := by
  intro n hn hsq
  have hn2 : n % 2 = 1 := by omega
  set βO := betaO n hn2 with hβO
  have h22 : (((2 : 𝓞 (Lni n)) : Lni n) : Qbar) = 2 := by
    have : ((2 : 𝓞 (Lni n)) : Lni n) = 2 := map_ofNat (algebraMap (𝓞 (Lni n)) (Lni n)) 2
    rw [this]; exact map_ofNat (Lni n).val 2
  refine ⟨1 + 2 * βO, ?_, ⟨1, -βO, by ring⟩, ?_⟩
  · intro h0
    have h1 : (((1 + 2 * βO : 𝓞 (Lni n)) : Lni n) : Qbar) = 0 := by rw [h0]; rfl
    push_cast at h1
    rw [h22, hβO, coe_betaO] at h1
    have h2 : betaQ n = algebraMap ℚ Qbar (-1 / 2) := by
      rw [map_div₀, map_neg, map_one, map_ofNat]; linear_combination h1 / 2
    have h3 : IsIntegral ℤ (algebraMap ℚ Qbar (-1 / 2)) := h2 ▸ isIntegral_betaQ hn2
    have h4 : IsIntegral ℤ ((-1 / 2 : ℚ)) := isIntegral_algebraMap_iff.mp h3
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h4
    have hm' : (m : ℚ) * 2 = -1 := by
      have : (m : ℚ) = -1 / 2 := by rw [← hm]; simp
      rw [this]; norm_num
    have : m * 2 = -1 := by exact_mod_cast hm'
    omega
  · intro d₀ hd₀ hd₀5 hd₀0
    apply normCongr_at hn hsq hd₀ hd₀5
    push_cast
    rw [h22, hβO, coe_betaO]

theorem normSigma : NormSigma := normSigma_of normCongr

theorem sigmaLift : SigmaLift := sigmaLift_of frobNormLaw normSigma

/-- **`√2 ∉ ℍ'_n` (`SqrtTwoNotInHHprime`), proved** (no hypotheses). -/
theorem sqrtTwoNotInHHprime : SqrtTwoNotInHHprime := sqrtTwoNotInHHprime_of_sigmaLift sigmaLift

end ZInQ.Contrib.TYZGenus.Sqrt2Glue

#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sigmaLift_of
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.frobNormLaw
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sqrtTwoNotInHHprime_of_normSigma
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sqrtTwoNotInHHprime
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sigmaLift
