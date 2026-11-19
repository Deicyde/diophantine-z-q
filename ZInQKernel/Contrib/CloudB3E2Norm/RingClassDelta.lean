import ZInQKernel.Contrib.CloudB3E1RingClass.GenuineMovingData

/-!
# The connecting map `𝐅_r^× → Gal(H_r/K)` at a split prime and its exactness

Manuscript `diophantine_zq.tex`, tex 3566–3579 ([Cox, Prop. 7.22, proof of Thm 7.24, (7.25),
(7.27)]): for a prime `r` split in the imaginary quadratic field `K`,
`1 → 𝐅_r^× → Pic(ℤ + r𝒪_K) → Cl(K) → 1` is exact, the kernel being the ratio of the two residue
factors modulo diagonal rational residues (no unit quotient since `𝒪_K^× = {±1}`).

Lane E1 (`CloudB3E1RingClass/ClassGroupMap.lean`) supplies the residue map
`galResidue : (𝒪_K/𝔣)^× → Gal(H_f/K)` and the exactness `ker_galToClassGroup` at `Gal(H_f/K)`, for
the conductor `𝔣` of `ℤ + f𝒪_K`. This file identifies the residues with `𝐅_r^×` at a split prime
and proves the interface's `δ`, `δ_inj`, `exact`.

* `SplitPair K f` (structure): two distinct primes `𝔯 ≠ 𝔯̄` of `𝒪_K` with `f𝒪_K = 𝔯 𝔯̄`.
* `intCast_mem_iff` (PROVED): `a ∈ 𝔯 ↔ f ∣ a` for `a ∈ ℤ`, `f` prime.
* **`conductor_eq`** (PROVED): the conductor of `ℤ + f𝒪_K` is `f𝒪_K` (E1 has `f𝒪_K ≤ 𝔣`; the other
  inclusion: an element of the conductor lies in `𝔯` and in `𝔯̄`).
* `absNorm_eq`, `resEquiv` (PROVED / definition): `𝒪_K/𝔯 ≅ 𝐅_f` (residue degree one, for
  `[K : ℚ] = 2`); `crtEquiv` (definition): `𝒪_K/𝔣 ≅ 𝐅_f × 𝐅_f`, `x ↦ (x mod 𝔯, x mod 𝔯̄)`.
* **`delta`** (definition): `δ(y) = galResidue(x)` with `x ≡ y mod 𝔯`, `x ≡ 1 mod 𝔯̄`.
* `idealClass_span`, `residuePic_span` (PROVED): the ray class / Picard class of a principal ideal
  `(β)` prime to the conductor is the class of the residue of `β` (as in Tau Ceti's `RayClass/Rat`).
* `galResidue_intCast`, `galResidue_diag` (PROVED): rational residues die in `Gal(H_f/K)`.
* **`exact`** (PROVED): `ker(Gal(H_f/K) → Cl(K)) = δ(𝐅_f^×)`.
* **`delta_injective`** (PROVED, given `𝒪_K^× = {±1}`): a residue unit with trivial Picard class is
  `±` the residue of an element of the order, i.e. diagonal, and `(y, 1)` is diagonal only for
  `y = 1`.
* **`units_eq_one_or_neg_one`** (PROVED): `𝒪_K^× = {±1}` for imaginary quadratic `K` with no
  `x² = −1` and no `x² + x + 1 = 0`, i.e. `K ≠ ℚ(i), ℚ(√−3)` (tex 2720).
* `unitsCast`, **`deltaR`** (definitions), **`deltaR_injective`**, **`deltaR_exact`**,
  **`deltaR_injective_of_imagQuad`** (PROVED): the interface form over lane E1's `setupGal`
  (`Gal(H_{max r 1}/K)`, source `𝐅_r^×`) at a split pair `(𝔯, 𝔯̄)` over a prime `r`.

The split pair at a place `v` is `𝔯 = v ∩ 𝒪_K` and its conjugate; `δ` uses the unique ring
identification `𝐅_r ≅ 𝒪_K/𝔯`, so it matches any residue map into `𝐅_r` at `𝔯`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.RingClassDelta

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3E1RingClass

variable {K : Type} [Field K] [NumberField K]

/-- **A split prime**: two distinct primes `𝔯 ≠ 𝔯̄` of `𝒪_K` with `f𝒪_K = 𝔯 𝔯̄`.
Kind: definition. -/
structure SplitPair (K : Type) [Field K] [NumberField K] (f : ℕ) where
  /-- the prime `𝔯` -/
  P : HeightOneSpectrum (𝓞 K)
  /-- the conjugate prime `𝔯̄` -/
  Q : HeightOneSpectrum (𝓞 K)
  ne : P ≠ Q
  span_eq : Ideal.span {(f : 𝓞 K)} = P.asIdeal * Q.asIdeal

namespace SplitPair

variable {f : ℕ} (sp : SplitPair K f)

/-- The pair with the primes exchanged. Kind: definition. -/
def swap : SplitPair K f := ⟨sp.Q, sp.P, sp.ne.symm, by rw [sp.span_eq, mul_comm]⟩

/-- `f𝒪_K ⊆ 𝔯`. Kind: PROVED. -/
theorem span_le_P : Ideal.span {(f : 𝓞 K)} ≤ sp.P.asIdeal := by
  rw [sp.span_eq]; exact Ideal.mul_le_left (I := sp.P.asIdeal) (J := sp.Q.asIdeal)

/-- `f𝒪_K ⊆ 𝔯̄`. Kind: PROVED. -/
theorem span_le_Q : Ideal.span {(f : 𝓞 K)} ≤ sp.Q.asIdeal := by
  rw [sp.span_eq]; exact Ideal.mul_le_right (I := sp.P.asIdeal) (J := sp.Q.asIdeal)

/-- `f ∈ 𝔯`. Kind: PROVED. -/
theorem f_mem_P : (f : 𝓞 K) ∈ sp.P.asIdeal := sp.span_le_P (Ideal.subset_span rfl)

/-- `𝔯 + 𝔯̄ = 𝒪_K`. Kind: PROVED. -/
theorem sup_eq_top : sp.P.asIdeal ⊔ sp.Q.asIdeal = ⊤ :=
  Ideal.IsMaximal.coprime_of_ne sp.P.isMaximal sp.Q.isMaximal fun h => sp.ne
    (HeightOneSpectrum.ext h)

/-- `𝔯̄ ⊄ 𝔯`. Kind: PROVED. -/
theorem not_Q_le_P : ¬ sp.Q.asIdeal ≤ sp.P.asIdeal := fun h =>
  sp.ne (HeightOneSpectrum.ext (sp.Q.isMaximal.eq_of_le sp.P.isMaximal.ne_top h).symm)

/-- **`a ∈ 𝔯 ↔ f ∣ a`** for `a ∈ ℤ`, `f` prime. Kind: PROVED. -/
theorem intCast_mem_iff (hf : f.Prime) (a : ℤ) : (a : 𝓞 K) ∈ sp.P.asIdeal ↔ (f : ℤ) ∣ a := by
  constructor
  · intro ha
    by_contra hdvd
    have hcop : IsCoprime a (f : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hf).2 fun h => hdvd (Int.natCast_dvd.2 h)
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : ((u * a + v * f : ℤ) : 𝓞 K) ∈ sp.P.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ sp.f_mem_P)
    rw [huv, Int.cast_one] at h1
    exact sp.P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rintro ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ sp.f_mem_P

/-- An element of the conductor of `ℤ + f𝒪_K` lies in `𝔯`. Kind: PROVED. -/
theorem mem_P_of_mem_conductor (hf : f.Prime) {x : 𝓞 K}
    (hx : x ∈ (ringClassOrder (K := K) f hf.ne_zero).conductor) : x ∈ sp.P.asIdeal := by
  by_contra hxP
  obtain ⟨y, hyQ, hyP⟩ := IsConcreteLE.not_le_iff_exists.1 sp.not_Q_le_P
  have hxy : ((x * y : 𝓞 K) : K) ∈ (ringClassOrder (K := K) f hf.ne_zero).toSubalgebra := by
    have := (mem_conductor_iff _ x).1 hx y
    simpa using this
  obtain ⟨a, ha⟩ := (mem_ringClassOrder_iff f hf.ne_zero (x * y)).1 hxy
  have haQ : (a : 𝓞 K) ∈ sp.Q.asIdeal := by
    have h1 : x * y ∈ sp.Q.asIdeal := Ideal.mul_mem_left _ _ hyQ
    have h2 := sp.span_le_Q ha
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  have haP : (a : 𝓞 K) ∈ sp.P.asIdeal :=
    (sp.intCast_mem_iff hf a).2 ((sp.swap.intCast_mem_iff hf a).1 haQ)
  have hxyP : x * y ∈ sp.P.asIdeal := by
    have := Ideal.add_mem _ (sp.span_le_P ha) haP
    simpa using this
  rcases sp.P.isPrime.mem_or_mem hxyP with h | h
  · exact hxP h
  · exact hyP h

include sp in
/-- **The conductor of `ℤ + f𝒪_K` is `f𝒪_K`** at a split prime `f` (PROVED). -/
theorem conductor_eq (hf : f.Prime) :
    (ringClassOrder (K := K) f hf.ne_zero).conductor = Ideal.span {(f : 𝓞 K)} := by
  refine le_antisymm (fun x hx => ?_) (span_le_conductor_ringClassOrder f hf.ne_zero)
  rw [sp.span_eq, Ideal.mul_eq_inf_of_coprime sp.sup_eq_top]
  exact ⟨sp.mem_P_of_mem_conductor hf hx, sp.swap.mem_P_of_mem_conductor hf hx⟩

end SplitPair

/-! ### Residue fields and the Chinese remainder theorem -/

namespace SplitPair

variable {f : ℕ} (sp : SplitPair K f) (hf : f.Prime)

include hf

/-- `|𝒪_K/𝔯| = f` for `[K : ℚ] = 2` (residue degree one). Kind: PROVED. -/
theorem absNorm_eq (hK : Module.finrank ℚ K = 2) : Ideal.absNorm sp.P.asIdeal = f := by
  have hprod : Ideal.absNorm sp.P.asIdeal * Ideal.absNorm sp.Q.asIdeal = f ^ 2 := by
    rw [← map_mul, ← sp.span_eq, Ideal.absNorm_span_singleton]
    have h : (f : 𝓞 K) = algebraMap ℤ (𝓞 K) (f : ℤ) := by simp
    rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hK, Int.natAbs_pow,
      Int.natAbs_natCast]
  have hP1 : Ideal.absNorm sp.P.asIdeal ≠ 1 := fun h =>
    sp.P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hQ1 : Ideal.absNorm sp.Q.asIdeal ≠ 1 := fun h =>
    sp.Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hf).1 (Dvd.intro _ hprod)
  interval_cases k
  · exact absurd (by simpa using hkeq) hP1
  · simpa using hkeq
  · exfalso
    rw [hkeq] at hprod
    exact hQ1 (by
      have hpos : 0 < f ^ 2 := pow_pos hf.pos 2
      nlinarith [Nat.eq_of_mul_eq_mul_left hpos (hprod.trans (mul_one _).symm)])

/-- `𝒪_K/𝔯` has characteristic `f`. Kind: PROVED. -/
theorem charP_P : CharP (𝓞 K ⧸ sp.P.asIdeal) f := by
  have : sp.P.asIdeal.IsPrime := sp.P.isPrime
  have h0 : ((f : ℕ) : 𝓞 K ⧸ sp.P.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk sp.P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact sp.f_mem_P
  rcases (Nat.dvd_prime hf).1 (ringChar.dvd h0) with h | h
  · exact absurd h CharP.ringChar_ne_one
  · have := ringChar.charP (𝓞 K ⧸ sp.P.asIdeal)
    rwa [h] at this

/-- **`𝐅_f ≅ 𝒪_K/𝔯`** (the unique ring map, bijective by cardinality). Kind: definition. -/
def resEquiv (hK : Module.finrank ℚ K = 2) : ZMod f ≃+* 𝓞 K ⧸ sp.P.asIdeal :=
  haveI := sp.charP_P hf
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : sp.P.asIdeal.IsMaximal := sp.P.isMaximal
  haveI : Finite (𝓞 K ⧸ sp.P.asIdeal) := by
    refine Nat.finite_of_card_ne_zero ?_
    have := sp.absNorm_eq hf hK
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    rw [this]; exact hf.ne_zero
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl f) (𝓞 K ⧸ sp.P.asIdeal))
    ((ZMod.castHom (dvd_refl f) (𝓞 K ⧸ sp.P.asIdeal)).injective.bijective_of_nat_card_le (by
      have := sp.absNorm_eq hf hK
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
      rw [this, Nat.card_zmod]))

/-- **`𝒪_K/𝔣 ≅ 𝐅_f × 𝐅_f`**, `x ↦ (x mod 𝔯, x mod 𝔯̄)`, for the conductor `𝔣 = f𝒪_K`.
Kind: definition. -/
def crtEquiv (hK : Module.finrank ℚ K = 2) :
    𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor ≃+* ZMod f × ZMod f :=
  ((Ideal.quotEquivOfEq ((sp.conductor_eq hf).trans sp.span_eq)).trans
    (Ideal.quotientMulEquivQuotientProd sp.P.asIdeal sp.Q.asIdeal
      (Ideal.isCoprime_iff_sup_eq.2 sp.sup_eq_top))).trans
    (RingEquiv.prodCongr (sp.resEquiv hf hK).symm (sp.swap.resEquiv hf hK).symm)

/-- Rational residues go to the diagonal. Kind: PROVED. -/
theorem crtEquiv_intCast (hK : Module.finrank ℚ K = 2) (n : ℤ) :
    sp.crtEquiv hf hK (n : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) =
      ((n : ZMod f), (n : ZMod f)) := by
  rw [map_intCast]; rfl

/-- The residue units: `(𝒪_K/𝔣)^× ≅ 𝐅_f^× × 𝐅_f^×`. Kind: definition. -/
def unitsCrt (hK : Module.finrank ℚ K = 2) :
    (𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor)ˣ ≃* (ZMod f)ˣ × (ZMod f)ˣ :=
  (Units.mapEquiv (sp.crtEquiv hf hK).toMulEquiv).trans MulEquiv.prodUnits

variable (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- **The connecting map `δ : 𝐅_f^× → Gal(H_f/K)`** at the place `𝔯` (tex 3576–3579):
`δ(y) = galResidue(x)` for the residue unit `x ≡ y mod 𝔯`, `x ≡ 1 mod 𝔯̄`. Kind: definition. -/
def deltaMul (hK : Module.finrank ℚ K = 2) : (ZMod f)ˣ →* ringClassGal f hf.ne_zero S hS :=
  (galResidue f hf.ne_zero S hS).comp
    ((sp.unitsCrt hf hK).symm.toMonoidHom.comp (MonoidHom.inl _ _))

/-- `δ` in the additive form of the interface. Kind: definition. -/
def delta (hK : Module.finrank ℚ K = 2) :
    Additive (ZMod f)ˣ →+ Additive (ringClassGal f hf.ne_zero S hS) :=
  MonoidHom.toAdditive (sp.deltaMul hf S hS hK)

end SplitPair

/-! ### Residues of principal ideals -/

section Principal

variable (O : NumberFieldOrder K)

/-- **The ray class of a principal ideal prime to the conductor** is the class of the residue of its
generator (the conductor modulus has no real places). Kind: PROVED. -/
theorem idealClass_span (β : 𝓞 K) (J : integralIdealsPrimeTo O.conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) = Ideal.span {β}) :
    ∃ u : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ,
      (u : 𝓞 K ⧸ O.conductorModulus.finitePart) = Ideal.Quotient.mk _ β ∧
        idealClass O.conductorModulus J = residueSignRayClass O.conductorModulus (u, 1) := by
  have hβ : (β : K) ≠ 0 := by
    have hJ0 := (Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp J.2)).1
    intro h0
    apply hJ0
    rw [hJ, Ideal.span_singleton_eq_bot]
    exact_mod_cast h0
  let x : Kˣ := Units.mk0 (β : K) hβ
  have hI : toPrincipalIdeal (𝓞 K) K x =
      (NumberFieldArithmetic.integralIdealsAwayHom K O.conductorModulus.support J :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, NumberFieldArithmetic.coe_integralIdealsAwayHom, hJ,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hx : x ∈ primeToSubgroup O.conductorModulus :=
    NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff.mp
      (hI ▸ (NumberFieldArithmetic.integralIdealsAwayHom K O.conductorModulus.support J).2)
  refine ⟨residueHom O.conductorModulus ⟨x, hx⟩, ?_, ?_⟩
  · rw [coe_residueHom, residue_eq (a := β) (b := 1) _ (by simp) (by simp [x])]
  · have hJ' : NumberFieldArithmetic.integralIdealsAwayHom K O.conductorModulus.support J =
        NumberFieldArithmetic.principalIdealAway K O.conductorModulus.support ⟨x, hx⟩ :=
      Subtype.ext (by rw [NumberFieldArithmetic.coe_principalIdealAway]; exact hI.symm)
    rw [idealClass_apply, hJ', ← principalRayClass_apply, ← residueSignRayClass_residueSignHom]
    refine congrArg _ (Prod.ext rfl (funext fun w => absurd w.2 (by simp)))

/-- **`residuePic` of the residue of a generator is the Picard class of the principal ideal.**
Kind: PROVED. -/
theorem residuePic_span (β : 𝓞 K) (J : integralIdealsPrimeTo O.conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) = Ideal.span {β}) :
    ∃ u : (𝓞 K ⧸ O.conductor)ˣ, (u : 𝓞 K ⧸ O.conductor) = Ideal.Quotient.mk _ β ∧
      residuePic O u = O.picClass J := by
  obtain ⟨u, hu, hcl⟩ := idealClass_span O β J hJ
  refine ⟨u, hu, ?_⟩
  change O.rayClassToPic (residueSignRayClass O.conductorModulus (u, 1)) = _
  rw [← hcl, rayClassToPic_idealClass]

end Principal

/-! ### `exact` and `δ_inj` -/

namespace SplitPair

variable {f : ℕ} (sp : SplitPair K f) (hf : f.Prime) (hK : Module.finrank ℚ K = 2)
  (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include sp in
/-- The conductor is a proper ideal. Kind: PROVED. -/
theorem conductor_ne_top : (ringClassOrder (K := K) f hf.ne_zero).conductor ≠ ⊤ := by
  rw [sp.conductor_eq hf]
  intro h
  exact sp.P.isPrime.ne_top (eq_top_iff.2 (h ▸ sp.span_le_P))

include sp in
/-- **Rational residues die**: the residue unit of an integer has trivial image in `Gal(H_f/K)`
(the principal ideal `(n)` is generated by an element of the order). Kind: PROVED. -/
theorem galResidue_intCast (n : ℤ)
    (u : (𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor)ˣ)
    (hu : (u : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) = (n : 𝓞 K ⧸ _)) :
    galResidue f hf.ne_zero S hS u = 1 := by
  have hmk : (u : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) =
      Ideal.Quotient.mk _ (n : 𝓞 K) := by
    rw [hu, map_intCast]
  have hJ : Ideal.span {(n : 𝓞 K)} ∈
      integralIdealsPrimeTo (ringClassOrder (K := K) f hf.ne_zero).conductorModulus := by
    rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [Ideal.span_singleton_eq_bot] at h0
      rw [h0, map_zero] at hmk
      exact sp.conductor_ne_top hf (Ideal.Quotient.subsingleton_iff.1
        (subsingleton_of_zero_eq_one (by
          have := u.mul_inv
          rw [hmk, zero_mul] at this
          exact this)))
    · obtain ⟨w, hw⟩ : ∃ w : 𝓞 K,
          Ideal.Quotient.mk (ringClassOrder (K := K) f hf.ne_zero).conductor (n * w) = 1 := by
        obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
          (↑u⁻¹ : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor)
        refine ⟨w, ?_⟩
        rw [map_mul, ← hmk, hw, Units.mul_inv]
      rw [Ideal.eq_top_iff_one]
      have h1 : n * w - 1 ∈ (ringClassOrder (K := K) f hf.ne_zero).conductor := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hw, map_one, sub_self]
      have := Ideal.add_mem
        (Ideal.span {(n : 𝓞 K)} ⊔ (ringClassOrder (K := K) f hf.ne_zero).conductor)
        (Ideal.mem_sup_left (Ideal.mul_mem_right w _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_right ((Ideal.neg_mem_iff _).2 h1))
      simpa using this
  obtain ⟨u', hu', hpic⟩ :=
    residuePic_span (ringClassOrder (K := K) f hf.ne_zero) (n : 𝓞 K) ⟨_, hJ⟩ rfl
  have huu : u' = u := Units.ext (hu'.trans hmk.symm)
  have hone : (ringClassOrder (K := K) f hf.ne_zero).picClass ⟨_, hJ⟩ = 1 :=
    ((ringClassOrder (K := K) f hf.ne_zero).picClass_eq_one_iff _).2 ⟨(n : 𝓞 K), by
      rw [mem_toRingOfIntegers]
      exact Subalgebra.intCast_mem _ n, rfl⟩
  simp only [galResidue, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← huu, hpic, hone, map_one]

end SplitPair

namespace SplitPair

variable {f : ℕ} (sp : SplitPair K f) (hf : f.Prime) (hK : Module.finrank ℚ K = 2)
  (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- The residue unit with residues `(a, b)`. Kind: PROVED. -/
theorem crtEquiv_unitsCrt_symm (a b : (ZMod f)ˣ) :
    sp.crtEquiv hf hK ((sp.unitsCrt hf hK).symm (a, b) :
      𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) = ((a : ZMod f), (b : ZMod f)) := by
  have h := (sp.unitsCrt hf hK).apply_symm_apply (a, b)
  have h1 : (((sp.unitsCrt hf hK) ((sp.unitsCrt hf hK).symm (a, b))).1 : ZMod f) =
      (sp.crtEquiv hf hK ((sp.unitsCrt hf hK).symm (a, b) : 𝓞 K ⧸ _)).1 := rfl
  have h2 : (((sp.unitsCrt hf hK) ((sp.unitsCrt hf hK).symm (a, b))).2 : ZMod f) =
      (sp.crtEquiv hf hK ((sp.unitsCrt hf hK).symm (a, b) : 𝓞 K ⧸ _)).2 := rfl
  rw [h] at h1 h2
  exact Prod.ext h1.symm h2.symm

/-- The diagonal residue units die in `Gal(H_f/K)`. Kind: PROVED. -/
theorem galResidue_diag (b : (ZMod f)ˣ) :
    galResidue f hf.ne_zero S hS ((sp.unitsCrt hf hK).symm (b, b)) = 1 := by
  have : NeZero f := ⟨hf.ne_zero⟩
  refine sp.galResidue_intCast hf S hS ((b : ZMod f).val : ℤ) _ ?_
  apply (sp.crtEquiv hf hK).injective
  rw [crtEquiv_unitsCrt_symm, crtEquiv_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- `galResidue = δ(a/b)` on the residue unit with residues `(a, b)`. Kind: PROVED. -/
theorem galResidue_eq_deltaMul (u : (𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor)ˣ) :
    galResidue f hf.ne_zero S hS u = sp.deltaMul hf S hS hK
      ((sp.unitsCrt hf hK u).1 * (sp.unitsCrt hf hK u).2⁻¹) := by
  set a := (sp.unitsCrt hf hK u).1
  set b := (sp.unitsCrt hf hK u).2
  have hu : u = (sp.unitsCrt hf hK).symm (a * b⁻¹, 1) * (sp.unitsCrt hf hK).symm (b, b) := by
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel_right, one_mul]
    exact ((sp.unitsCrt hf hK).symm_apply_apply u).symm
  rw [hu, map_mul, galResidue_diag, mul_one]
  rfl

/-- **`exact`** (tex 3566–3575): a class of `Gal(H_f/K)` has trivial image in `Cl(K)` exactly when
it is `δ(y)` for some `y ∈ 𝐅_f^×` (PROVED; `ker_galToClassGroup`, rational residues die). -/
theorem exact (p : Additive (ringClassGal f hf.ne_zero S hS)) :
    (galToClassGroup f hf.ne_zero S hS).toAdditive p = 0 ↔ ∃ y, sp.delta hf S hS hK y = p := by
  constructor
  · intro hp
    have hker : Additive.toMul p ∈ (galToClassGroup f hf.ne_zero S hS).ker :=
      MonoidHom.mem_ker.2 (congrArg Additive.toMul hp)
    rw [ker_galToClassGroup] at hker
    obtain ⟨u, hu⟩ := hker
    refine ⟨Additive.ofMul ((sp.unitsCrt hf hK u).1 * (sp.unitsCrt hf hK u).2⁻¹), ?_⟩
    show Additive.ofMul (sp.deltaMul hf S hS hK
      ((sp.unitsCrt hf hK u).1 * (sp.unitsCrt hf hK u).2⁻¹)) = p
    rw [← galResidue_eq_deltaMul, hu]
    rfl
  · rintro ⟨y, rfl⟩
    have hmem : sp.deltaMul hf S hS hK (Additive.toMul y) ∈
        (galToClassGroup f hf.ne_zero S hS).ker := by
      rw [ker_galToClassGroup]
      exact ⟨_, rfl⟩
    exact congrArg Additive.ofMul (MonoidHom.mem_ker.1 hmem)

/-- **`δ_inj`** (tex 3566–3575): `δ` is injective when `𝒪_K^× = {±1}` (PROVED: a residue unit with
trivial Picard class is `±` the residue of an element of the order, i.e. a rational residue, and
`(y, 1)` is diagonal only for `y = 1`). -/
theorem delta_injective (hunits : ∀ ε : (𝓞 K)ˣ, ε = 1 ∨ ε = -1) :
    Function.Injective (sp.delta hf S hS hK) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hy' : galResidue f hf.ne_zero S hS ((sp.unitsCrt hf hK).symm (Additive.toMul y, 1)) = 1 :=
    congrArg Additive.toMul hy
  set u := (sp.unitsCrt hf hK).symm (Additive.toMul y, 1)
  have hres : residuePic (ringClassOrder (K := K) f hf.ne_zero) u = 1 := by
    simp only [galResidue, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hy'
    exact (MulEquiv.map_eq_one_iff _).1 hy'
  have hc : residueSignRayClass (ringClassOrder (K := K) f hf.ne_zero).conductorModulus (u, 1) ∈
      (ringClassOrder (K := K) f hf.ne_zero).rayClassToPic.ker := hres
  obtain ⟨J, hJc, β, hβO, hJβ⟩ := (ringClassOrder (K := K) f hf.ne_zero).mem_ker_rayClassToPic.1 hc
  obtain ⟨uβ, huβ, hcl⟩ := idealClass_span (ringClassOrder (K := K) f hf.ne_zero) β J hJβ
  let Q' := 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductorModulus.finitePart
  let I' := (ringClassOrder (K := K) f hf.ne_zero).conductorModulus.infinitePart → ℤˣ
  have h1 : residueSignRayClass (ringClassOrder (K := K) f hf.ne_zero).conductorModulus
      (((show Q'ˣ from u), (1 : I')) * (uβ, (1 : I'))⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hcl, hJc, mul_inv_cancel]
  have h2 : (((show Q'ˣ from u), (1 : I')) * (uβ, (1 : I'))⁻¹) ∈
      (unitsResidueSignHom (ringClassOrder (K := K) f hf.ne_zero).conductorModulus).range := by
    rw [← ker_residueSignRayClass]
    exact h1
  obtain ⟨ε, hε⟩ := h2
  obtain ⟨a, ha⟩ := (mem_ringClassOrder_iff f hf.ne_zero β).1 hβO
  have hβa : (Ideal.Quotient.mk (ringClassOrder (K := K) f hf.ne_zero).conductor β) =
      ((a : ℤ) : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) := by
    rw [← map_intCast (Ideal.Quotient.mk (ringClassOrder (K := K) f hf.ne_zero).conductor),
      Ideal.Quotient.eq, sp.conductor_eq hf]
    exact ha
  have hfst : ((show Q'ˣ from u) : Q') =
      (((unitsResidueSignHom (ringClassOrder (K := K) f hf.ne_zero).conductorModulus ε).1 :
        Q'ˣ) : Q') * (uβ : Q') := by
    rw [hε]
    change _ = (((show Q'ˣ from u) * uβ⁻¹ : Q'ˣ) : Q') * _
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hc' : ∃ c : ℤ, ((show Q'ˣ from u) : Q') = (c : Q') := by
    rcases hunits ε with rfl | rfl
    · refine ⟨a, ?_⟩
      rw [hfst, map_one, Prod.fst_one, Units.val_one, one_mul]
      exact huβ.trans hβa
    · refine ⟨-a, ?_⟩
      rw [hfst, unitsResidueSignHom_neg_one, Units.val_neg, Units.val_one, neg_one_mul]
      push_cast
      exact congrArg Neg.neg (huβ.trans hβa)
  obtain ⟨c, hcu⟩ := hc'
  have hcu' : (u : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) =
      (c : 𝓞 K ⧸ (ringClassOrder (K := K) f hf.ne_zero).conductor) := hcu
  have h3 := congrArg (sp.crtEquiv hf hK) hcu'
  rw [crtEquiv_unitsCrt_symm, crtEquiv_intCast, Prod.mk.injEq] at h3
  have hy1 : Additive.toMul y = 1 := Units.ext (by rw [h3.1, ← h3.2])
  exact congrArg Additive.ofMul hy1

end SplitPair

/-! ### The interface form: `𝐅_r^×` for `Gal(H_{max r 1}/K)` -/

section Interface

variable {r : ℕ} (hr : (max r 1).Prime) (sp : SplitPair K (max r 1))
  (hK : Module.finrank ℚ K = 2) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- `r = max r 1` for `max r 1` prime. Kind: PROVED. -/
theorem eq_max (hr : (max r 1).Prime) : r = max r 1 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; exact absurd hr (by simp [Nat.not_prime_one])
  · omega

/-- `𝐅_r^× ≅ 𝐅_{max r 1}^×`. Kind: definition. -/
def unitsCast : (ZMod r)ˣ ≃* (ZMod (max r 1))ˣ :=
  Units.mapEquiv (ZMod.ringEquivCongr (eq_max hr)).toMulEquiv

/-- **The interface's `δ r v`** at the split pair `v = (𝔯, 𝔯̄)` over `r`: `𝐅_r^× → Gal(H_r/K)`,
`H_r` the ring class field of `ℤ + max(r,1)𝒪_K` (lane E1's `setupGal`). Kind: definition. -/
def deltaR : Additive (ZMod r)ˣ →+ Additive (ringClassGal (max r 1) hr.ne_zero S hS) :=
  (sp.delta hr S hS hK).comp (MonoidHom.toAdditive (unitsCast hr).toMonoidHom)

/-- **`δ_inj`** in the interface form (PROVED; `𝒪_K^× = {±1}`). -/
theorem deltaR_injective (hunits : ∀ ε : (𝓞 K)ˣ, ε = 1 ∨ ε = -1) :
    Function.Injective (deltaR hr sp hK S hS) :=
  (sp.delta_injective hr hK S hS hunits).comp (fun _ _ h =>
    Additive.toMul.injective ((unitsCast hr).injective (congrArg Additive.toMul h)))

/-- **`exact`** in the interface form (PROVED). -/
theorem deltaR_exact (p : Additive (ringClassGal (max r 1) hr.ne_zero S hS)) :
    (galToClassGroup (max r 1) hr.ne_zero S hS).toAdditive p = 0 ↔
      ∃ y, deltaR hr sp hK S hS y = p := by
  rw [sp.exact hr hK S hS p]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Additive.ofMul ((unitsCast hr).symm (Additive.toMul y)), ?_⟩
    change sp.delta hr S hS hK (Additive.ofMul ((unitsCast hr) ((unitsCast hr).symm _))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

end Interface

/-! ### `𝒪_K^× = {±1}` for imaginary quadratic `K ≠ ℚ(i), ℚ(√−3)` -/

section UnitsPM

open NumberField.InfinitePlace NumberField.Units

/-- The coercion `𝒪_K^× → K`. Kind: definition. -/
def unitsToK : (𝓞 K)ˣ →* K := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))

/-- The coercion `𝒪_K^× → K` is injective. Kind: PROVED. -/
theorem unitsToK_injective : Function.Injective (unitsToK (K := K)) := fun _ _ h =>
  Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K h)

/-- **`𝒪_K^× = {±1}`** for an imaginary quadratic field without `i` and without a primitive cube
root of unity, i.e. `K ≠ ℚ(i), ℚ(√−3)` (tex 2720: "different from `ℚ(i)` and `ℚ(√−3)`")
(PROVED: the unit rank is `0`, so every unit is a root of unity; a root of unity of prime order `p`
has degree `p − 1 ≤ 2`, and orders `3`, `4` are excluded). -/
theorem units_eq_one_or_neg_one (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K]
    (hi : ∀ x : K, x ^ 2 ≠ -1) (hω : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (u : (𝓞 K)ˣ) :
    u = 1 ∨ u = -1 := by
  have hrank : rank K = 0 := by
    dsimp only [rank]
    have h := card_add_two_mul_card_eq_rank K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hK] at h
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    omega
  have htor : u ∈ torsion K := by
    obtain ⟨⟨x, e⟩, hxu, -⟩ := exist_unique_eq_mul_prod _ u
    replace hxu : u = x := by
      rw [← mul_one x.1, hxu]
      apply congr_arg
      rw [← Finset.prod_empty]
      congr
      rw [Finset.univ_eq_empty_iff, hrank]
      infer_instance
    rw [hxu]
    exact x.2
  have hm0 : orderOf u ≠ 0 := by
    rw [← Subgroup.orderOf_mk u htor]
    exact (orderOf_pos _).ne'
  -- the element of order `n ∣ m`, in `K`
  have hprim : ∀ n, n ∣ orderOf u → IsPrimitiveRoot (unitsToK (u ^ (orderOf u / n))) n :=
    fun n hn => (orderOf_pow_orderOf_div hm0 hn ▸ IsPrimitiveRoot.orderOf _).map_of_injective
      unitsToK_injective
  have key2 : ∀ p, p.Prime → p ∣ orderOf u → p = 2 := by
    intro p hp hpm
    have hζ := hprim p hpm
    have hdeg : p - 1 ≤ 2 := by
      have h1 := minpoly.natDegree_le (A := ℚ) (unitsToK (u ^ (orderOf u / p)))
      rwa [hK, ← Polynomial.cyclotomic_eq_minpoly_rat hζ hp.pos, Polynomial.natDegree_cyclotomic,
        Nat.totient_prime hp] at h1
    have h3 : p ≠ 3 := by
      rintro rfl
      apply hω (unitsToK (u ^ (orderOf u / 3)))
      have h1 := hζ.pow_eq_one
      have h2 := hζ.ne_one (by norm_num)
      have : (unitsToK (u ^ (orderOf u / 3)) - 1) *
          (unitsToK (u ^ (orderOf u / 3)) ^ 2 + unitsToK (u ^ (orderOf u / 3)) + 1) = 0 := by
        rw [show ∀ z : K, (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 from fun z => by ring, h1, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h2)
    have h2 := hp.two_le
    have hp3 : p ≤ 3 := by omega
    interval_cases p
    · rfl
    · exact absurd rfl h3
  have key4 : ¬ 4 ∣ orderOf u := by
    intro h4
    have hζ := hprim 4 h4
    apply hi (unitsToK (u ^ (orderOf u / 4)))
    have h1 : (unitsToK (u ^ (orderOf u / 4)) ^ 2) * (unitsToK (u ^ (orderOf u / 4)) ^ 2) = 1 := by
      rw [← pow_add]; exact hζ.pow_eq_one
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact absurd h (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
    · exact h
  have hm2 : orderOf u ∣ 2 := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdm => key2 d hd hdm)
    set k := (orderOf u).primeFactorsList.length
    have hk : k ≤ 1 := by
      by_contra hk
      exact key4 (hpow ▸ (pow_dvd_pow 2 (by omega : 2 ≤ k)))
    rw [hpow]
    exact (Nat.pow_dvd_pow 2 hk).trans (by norm_num)
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 hm2
  have hK2 : unitsToK u * unitsToK u = 1 := by rw [← map_mul, hu2, map_one]
  rcases mul_self_eq_one_iff.1 hK2 with h | h
  · exact Or.inl (unitsToK_injective (h.trans (map_one _).symm))
  · exact Or.inr (unitsToK_injective (h.trans (by simp [unitsToK])))

end UnitsPM

/-- **`δ_inj` for imaginary quadratic `K ≠ ℚ(i), ℚ(√−3)`** (PROVED; `units_eq_one_or_neg_one`).
The hypotheses are consistent (e.g. `K = ℚ(√−5)`). -/
theorem deltaR_injective_of_imagQuad {r : ℕ} (hr : (max r 1).Prime) (sp : SplitPair K (max r 1))
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hi : ∀ x : K, x ^ 2 ≠ -1)
    (hω : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Function.Injective (deltaR hr sp hK S hS) :=
  deltaR_injective hr sp hK S hS (units_eq_one_or_neg_one hK hi hω)

/-- **`exact` in lane E1's setup form** (PROVED; `deltaR_exact` with `setupPi`). -/
theorem deltaR_exact_setup {s : ℕ} (C : RingClassSetup K s) {r : ℕ} (hr : (max r 1).Prime)
    (sp : SplitPair K (max r 1)) (hK : Module.finrank ℚ K = 2) (p : Additive (setupGal C r)) :
    setupPi C r p = 0 ↔ ∃ y, deltaR hr sp hK (C.Sr r) (C.hSr r) y = p := by
  have h := deltaR_exact hr sp hK (C.Sr r) (C.hSr r) p
  unfold setupPi
  convert h using 0

end ZInQ.Contrib.CloudB3E2.RingClassDelta
