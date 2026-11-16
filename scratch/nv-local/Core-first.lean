import ZInQKernel.Contrib.OneProof.SGRDirectNV

open Polynomial CategoryTheory AlgebraicGeometry
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

set_option linter.style.haveILetI false

noncomputable section

namespace SGRDirect.NVLocal

/-- **An inertia automorphism at an unramified prime is trivial.** -/
theorem eq_one_of_inertia_of_unram {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsPrime] (hun : P.ramificationIdx ℤ = 1) (σ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : 𝓞 K, σ • x - x ∈ P) : σ = 1 := by
  set G := Subgroup.zpowers σ
  haveI : Finite G := inferInstance
  set K₀ := FixedPoints.subfield G K
  haveI : CharZero K₀ := inferInstance
  haveI : FiniteDimensional ℚ K₀ := by
    exact Module.Finite.of_injective ((algebraMap K₀ K).toRatAlgHom.toLinearMap)
      (algebraMap K₀ K).injective
  haveI : NumberField K₀ := ⟨⟩
  haveI : FaithfulSMul G K := ⟨fun {g₁ g₂} h => Subtype.ext (AlgEquiv.ext h)⟩
  haveI : IsGaloisGroup G K₀ K := IsGaloisGroup.fixedPoints G K
  haveI : IsGaloisGroup G (𝓞 K₀) (𝓞 K) := IsGaloisGroup.of_isFractionRing G (𝓞 K₀) (𝓞 K) K₀ K
  set P₀ := P.under (𝓞 K₀)
  haveI : P₀.IsPrime := Ideal.IsPrime.under _ P
  haveI : P.LiesOver P₀ := ⟨rfl⟩
  have hg : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) ∈ P.inertia G := by
    intro x
    exact hσ x
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := G) P₀ P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P₀ P G] at hcard
  have htow := Ideal.ramificationIdx_tower (R := ℤ) P₀ P
  rw [hun] at htow
  have h1 : P.ramificationIdx (𝓞 K₀) = 1 := (Nat.eq_one_of_mul_eq_one_left htow.symm)
  rw [h1] at hcard
  have : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) = 1 := by
    have hb : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
    rw [hb] at hg
    exact hg
  exact congrArg Subtype.val this


/-- The prime of `𝓞 L` cut out by a prime `𝔓` of a ring `C` mapping to `L` whose localization contains `𝓞 L`. -/
def primeOf {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr) [𝔓.IsPrime]
    (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) : Ideal (𝓞 L) where
  carrier := {y | ∃ d₁ d₂ : Cr, d₁ ∈ 𝔓 ∧ d₂ ∉ 𝔓 ∧ (y : L) * ψ d₂ = ψ d₁}
  zero_mem' := ⟨0, 1, 𝔓.zero_mem, fun h => (Ideal.IsPrime.ne_top inferInstance)
    ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, a₂, ha₁, ha₂, hx⟩ ⟨b₁, b₂, hb₁, hb₂, hy⟩
    refine ⟨a₁ * b₂ + b₁ * a₂, a₂ * b₂, 𝔓.add_mem (𝔓.mul_mem_right _ ha₁) (𝔓.mul_mem_right _ hb₁),
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha₂ hb₂, ?_⟩
    simp only [show ((x + y : 𝓞 L) : L) = (x : L) + y from rfl, map_add, map_mul, ← hx, ← hy]
    ring
  smul_mem' := by
    rintro r x ⟨d₁, d₂, hd₁, hd₂, hx⟩
    obtain ⟨c₁, c₂, hc₂, hr⟩ := hN r
    refine ⟨c₁ * d₁, c₂ * d₂, 𝔓.mul_mem_left _ hd₁,
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hd₂, ?_⟩
    simp only [show ((r • x : 𝓞 L) : L) = (r : L) * x from rfl, map_mul, ← hx, ← hr]
    ring

theorem primeOf_isPrime {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) :
    (primeOf 𝔓 ψ hker hN).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨d₁, d₂, hd₁, hd₂, h⟩
    apply hd₂
    have h' : ψ (d₂ - d₁) = 0 := by
      rw [map_sub, ← h]; simp
    have := 𝔓.add_mem (hker _ h') hd₁
    simpa using this
  · rintro x y ⟨d₁, d₂, hd₁, hd₂, hxy⟩
    obtain ⟨a₁, a₂, ha₂, hx⟩ := hN x
    obtain ⟨b₁, b₂, hb₂, hy⟩ := hN y
    have key : ψ (a₁ * b₁ * d₂ - d₁ * a₂ * b₂) = 0 := by
      simp only [map_sub, map_mul]
      rw [← hx, ← hy, ← hxy, show ((x * y : 𝓞 L) : L) = (x : L) * y from rfl]
      ring
    have h1 : a₁ * b₁ * d₂ ∈ 𝔓 := by
      have := 𝔓.add_mem (hker _ key) (𝔓.mul_mem_right b₂ (𝔓.mul_mem_right a₂ hd₁))
      simpa using this
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h1) with h2 | h2
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h2) with h3 | h3
      · exact Or.inl ⟨a₁, a₂, h3, ha₂, hx⟩
      · exact Or.inr ⟨b₁, b₂, h3, hb₂, hy⟩
    · exact absurd h2 hd₂

theorem mem_primeOf_of_mem {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (p : ℕ)
    (hp : (p : Cr) ∈ 𝔓) : ((p : ℤ) : 𝓞 L) ∈ primeOf 𝔓 ψ hker hN := by
  refine ⟨p, 1, hp, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

theorem inertia_primeOf {L : Type*} [Field L] [CharZero L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) :
    ∀ y : 𝓞 L, σ • y - y ∈ primeOf 𝔓 ψ hker hN := by
  intro y
  obtain ⟨c₁, c₂, hc₂, hy⟩ := hN y
  obtain ⟨c₁', hσ₁, h₁⟩ := hσ c₁
  obtain ⟨c₂', hσ₂, h₂⟩ := hσ c₂
  have hc₂' : c₂' ∉ 𝔓 := by
    intro h
    apply hc₂
    have := 𝔓.sub_mem h h₂
    simpa using this
  refine ⟨c₁' * c₂ - c₁ * c₂', c₂ * c₂', ?_,
    fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hc₂', ?_⟩
  · have : c₁' * c₂ - c₁ * c₂' = (c₁' - c₁) * c₂ - c₁ * (c₂' - c₂) := by ring
    rw [this]
    exact 𝔓.sub_mem (𝔓.mul_mem_right _ h₁) (𝔓.mul_mem_left _ h₂)
  · have hσy : σ (y : L) * ψ c₂' = ψ c₁' := by
      rw [← hσ₂, ← hσ₁, ← map_mul, hy]
    have hcoe : ((σ • y : 𝓞 L) : L) = σ (y : L) := rfl
    simp only [show ((σ • y - y : 𝓞 L) : L) = ((σ • y : 𝓞 L) : L) - y from rfl, hcoe, map_sub,
      map_mul, ← hσy, ← hy]
    ring


/-- **An inertia automorphism is trivial** (assembled): the prime `primeOf` is unramified. -/
theorem eq_one_of_primeOf {L : Type*} [Field L] [NumberField L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) (p : ℕ) (hp : (p : Cr) ∈ 𝔓)
    (hun : ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1) :
    σ = 1 := by
  haveI := primeOf_isPrime 𝔓 ψ hker hN
  exact eq_one_of_inertia_of_unram (primeOf 𝔓 ψ hker hN)
    (hun _ inferInstance (mem_primeOf_of_mem 𝔓 ψ hker hN p hp)) σ (inertia_primeOf 𝔓 ψ hker hN σ hσ)

/-! ## The inclusion `ℤ[X]`-closure → `ℚ[X]`-closure and the Galois action -/

/-- The inclusion of the integral closure of `ℤ[X]` in `E` into that of `ℚ[X]`. -/
def zqIncl (E : Type) [Field E] [Algebra ℚ[X] E] :
    letI := intPolyAlg E
    integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
  letI := intPolyAlg E
  { toFun := fun c => ⟨(c : E), by
      obtain ⟨f, hf, hf0⟩ := c.2
      refine ⟨f.map (Polynomial.mapRingHom (Int.castRingHom ℚ)), hf.map _, ?_⟩
      rw [eval₂_map]
      exact hf0⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

/-- A `ℚ(X)`-automorphism of `E` acting on the integral closure of `ℚ[X]`. -/
def galB (g : Gal(E/RatFunc ℚ)) : integralClosure ℚ[X] E ≃+* integralClosure ℚ[X] E where
  toFun x := ⟨g x, x.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  invFun x := ⟨g⁻¹ x, x.2.map (((g⁻¹ : Gal(E/RatFunc ℚ)) : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ (g (x : E)) = x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  right_inv x := Subtype.ext (by
    show g (g⁻¹ (x : E)) = x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
  map_mul' x y := Subtype.ext (map_mul g (x : E) y)
  map_add' x y := Subtype.ext (map_add g (x : E) y)

theorem galB_apply (g : Gal(E/RatFunc ℚ)) (x : integralClosure ℚ[X] E) :
    ((galB g x : integralClosure ℚ[X] E) : E) = g x := rfl

/-- A `ℚ(X)`-automorphism maps the integral closure of `ℤ[X]` to itself. -/
theorem galC_mem (g : Gal(E/RatFunc ℚ)) :
    letI := intPolyAlg E
    ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E, (c' : E) = g c := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  intro c
  exact ⟨⟨g c, c.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℤ[X])⟩, rfl⟩


end SGRDirect.NVLocal

namespace SGRDirect.NVLocal

/-- **GLUE (local geometry of tame covers at a closed point; h-b1 §3 Lemma NV step 3, geometric half).**
Hypotheses as in `NVLocalInertia` minus the residue fields. Let `C` and `B` be the integral closures of `ℤ[X]`
and `ℚ[X]` in `E`, and `𝔓` a maximal ideal of `C` over `m_b = (p, dX − a)` (`b = a/d`). Then the branch of
`X = b` through `𝔓` is unique and normal there: exactly one prime `Q` of `B` over `X − b` has `Q ∩ C ⊆ 𝔓`,
and every element of `B/Q` integral over `ℤ` is a quotient `c₁/c₂` of images of `c₁, c₂ ∈ C` with `c₂ ∉ 𝔓`
(the localization of `C/(Q ∩ C)` at `𝔓` contains the ring of integers of the number field `B/Q`).
*Proof route* (not compiled): Abhyankar's lemma (SGA 1 XIII 5.2–5.3, UNVERIFIED numbers) at the closed point:
after the Kummer base change `A' = ℤ_(p)[ζ_N, p^{1/N}][r]_{(p^{1/N}, r)}`, `r^N = X − b`, `N = |G|`, the
normalization is unramified in codimension one (the kernel's T2 at both divisors; base change of the
unramified horizontal primes, by `BranchData` and distinctness mod `p`), hence étale by purity
(`PropTSGlue.purityGlobalDim2`, proved); its specialization along `r = 0` is étale over the DVR
`ℤ_(p)[ζ_N, p^{1/N}]`, hence normal, which gives a unique and normal branch upstairs; going down and
invariants under the tame group `Gal(E(ζ_N, r, p^{1/N})/E)` descend both to `E`. -/
def BranchRegular : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf → Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    ∀ b ∈ S,
    letI := intPolyAlg E
    ∀ 𝔓 : Ideal (integralClosure ℤ[X] E), 𝔓.IsMaximal →
      C (p : ℤ) ∈ 𝔓.under ℤ[X] → C (b.den : ℤ) * X - C b.num ∈ 𝔓.under ℤ[X] →
      ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧ Q.under ℚ[X] = Ideal.span {X - C b} ∧
        Q.comap (zqIncl E) ≤ 𝔓 ∧
        (∀ Q' : Ideal (integralClosure ℚ[X] E), Q'.IsPrime →
          Q'.under ℚ[X] = Ideal.span {X - C b} → Q'.comap (zqIncl E) ≤ 𝔓 → Q' = Q) ∧
        (∀ z : integralClosure ℚ[X] E ⧸ Q, IsIntegral ℤ z →
          ∃ c₁ c₂ : integralClosure ℤ[X] E, c₂ ∉ 𝔓 ∧
            Ideal.Quotient.mk Q (zqIncl E c₂) * z = Ideal.Quotient.mk Q (zqIncl E c₁))

set_option maxHeartbeats 1600000 in
/-- **`NVLocalInertia` from `BranchRegular`** (compiled). `τ` in the inertia of a vertical prime `q` fixes a
maximal ideal `𝔓 ⊇ q` over `m_b`, hence the unique branch `Q` through `𝔓`; it acts on the number field `B/Q`
inside the inertia group of the prime `{c₁/c₂ : c₁ ∈ 𝔓}` of its ring of integers, which is unramified; so it acts
trivially on `B/Q`, i.e. `τ ∈ I_Q` (`g = 1`). -/
theorem nvLocalInertia_of_branchRegular (h : BranchRegular) : NVLocalInertia := by
  intro E _ _ _ _ _ _ S n nInf p hp hB hdeg hint hdist b hb hres
  letI := intPolyAlg E
  intro q hq hqu τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  -- the maximal ideal `𝔓 ⊇ q` over `m_b`
  obtain ⟨m, hm, hpm, hbm⟩ := exists_secIdeal p b (hint b hb)
  have hqm : q.under ℤ[X] ≤ m := by
    rw [hqu, vertPrime, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    exact hpm
  obtain ⟨𝔓, hq𝔓, h𝔓p, h𝔓u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m q hqm
  haveI := h𝔓p
  haveI : 𝔓.LiesOver m := ⟨h𝔓u.symm⟩
  have h𝔓max : 𝔓.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal 𝔓 m
  obtain ⟨Q, hQ, hQu, hQ𝔓, hUB, hN⟩ :=
    h E S n nInf p hp hB hdeg hint hdist b hb 𝔓 h𝔓max (h𝔓u ▸ hpm) (h𝔓u ▸ hbm)
  haveI := hQ
  have hq𝔓' : ∀ x, x ∈ q → x ∈ 𝔓 := fun x hx => hq𝔓 hx
  -- `τ` maps `Q` to itself (unibranch)
  have hτC : ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E,
      (c' : E) = τ c ∧ c' - c ∈ 𝔓 := by
    intro c
    obtain ⟨c', hc', hcq⟩ := hτ c
    exact ⟨c', hc', hq𝔓' _ hcq⟩
  have hQτ : Q = Q.map (galB τ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E) := by
    symm
    haveI : (Q.map (galB τ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E)).IsPrime :=
      Ideal.map_isPrime_of_equiv (galB τ)
    refine hUB _ inferInstance ?_ ?_
    · ext f
      have : (galB τ).symm (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
          algebraMap ℚ[X] (integralClosure ℚ[X] E) f := by
        apply Subtype.ext
        show τ⁻¹ (algebraMap ℚ[X] E f) = algebraMap ℚ[X] E f
        exact gal_fix τ⁻¹ f
      rw [Ideal.under_def, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap, this, ← hQu,
        Ideal.under_def, Ideal.mem_comap]
    · intro c hc
      rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hc
      obtain ⟨c'', hc''⟩ := galC_mem τ⁻¹ c
      have h1 : (galB τ).symm (zqIncl E c) = zqIncl E c'' := by
        apply Subtype.ext
        show τ⁻¹ (c : E) = c''
        rw [hc'']
      rw [h1] at hc
      have h2 : c'' ∈ 𝔓 := hQ𝔓 hc
      obtain ⟨c₃, hc₃, hc₃𝔓⟩ := hτC c''
      have h3 : c₃ = c := by
        apply Subtype.ext
        rw [hc₃, hc'']
        show τ (τ⁻¹ (c : E)) = c
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [h3] at hc₃𝔓
      have := 𝔓.add_mem hc₃𝔓 h2
      simpa using this
  -- `Q` is maximal, `κ = B/Q` is a field
  have hspan : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
  haveI : Q.LiesOver (Ideal.span {X - C b}) := ⟨hQu.symm⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {X - C b})
  letI : Field (integralClosure ℚ[X] E ⧸ Q) := Ideal.Quotient.field Q
  -- an embedding `φ : κ → ℚ̄`
  have key : ∀ f : ℚ[X], Ideal.Quotient.mk Q (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
      Ideal.Quotient.mk Q (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (f.eval b))) := by
    intro f
    rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap, ← Ideal.under_def, hQu,
      Ideal.mem_span_singleton]
    exact X_sub_C_dvd_sub_C_eval
  obtain ⟨φ⟩ : Nonempty (integralClosure ℚ[X] E ⧸ Q →+* Qbar) := by
    letI alg : Algebra ℚ (integralClosure ℚ[X] E ⧸ Q) :=
      ((Ideal.Quotient.mk Q).comp ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp C)).toAlgebra
    haveI : Algebra.IsAlgebraic ℚ (integralClosure ℚ[X] E ⧸ Q) := by
      refine ⟨fun z => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨f, hf, hy0⟩ := Algebra.IsIntegral.isIntegral (R := ℚ[X]) y
      have hcomp : (Ideal.Quotient.mk Q).comp (algebraMap ℚ[X] (integralClosure ℚ[X] E)) =
          (algebraMap ℚ (integralClosure ℚ[X] E ⧸ Q)).comp (Polynomial.evalRingHom b) := by
        ext f
        · simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, coe_evalRingHom, eval_C]
        · simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, coe_evalRingHom, eval_X]
          rw [key X, eval_X]
      refine (IsIntegral.isAlgebraic ⟨f.map (Polynomial.evalRingHom b), hf.map _, ?_⟩)
      rw [eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hy0, map_zero]
    haveI : Module.IsTorsionFree ℚ (integralClosure ℚ[X] E ⧸ Q) :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.injective _)
    haveI : Module.IsTorsionFree ℚ Qbar :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.injective _)
    exact ⟨(IsAlgClosed.lift (R := ℚ) (M := Qbar) (S := integralClosure ℚ[X] E ⧸ Q)).toRingHom⟩
  -- the number field `L = φ(κ)` and `e : κ ≃ L`
  set L := IntermediateField.adjoin ℚ (Set.range φ) with hLdef
  haveI : FiniteDimensional ℚ L := finiteDimensional_residue E b Q hQu φ
  haveI : NumberField L := ⟨⟩
  have hunL : UnramifiedAt L p := hres Q hQ hQu φ
  let f : integralClosure ℚ[X] E ⧸ Q →+* L :=
    { toFun := fun z => ⟨φ z, IntermediateField.subset_adjoin _ _ ⟨z, rfl⟩⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (φ.map_add x y) }
  have hfsurj : Function.Surjective f := by
    have hle : L ≤ (φ.fieldRange).toIntermediateField (fun q : ℚ =>
        ⟨(q : integralClosure ℚ[X] E ⧸ Q), (map_ratCast φ q).trans (eq_ratCast _ q).symm⟩) := by
      rw [hLdef, IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hle hy
    exact ⟨z, Subtype.ext hz⟩
  let e : integralClosure ℚ[X] E ⧸ Q ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hfsurj⟩
  have he : ∀ z, (e z : Qbar) = φ z := fun z => rfl
  -- `σ`: the action of `τ` on `κ`, transported to `L`
  let σκ : integralClosure ℚ[X] E ⧸ Q ≃+* integralClosure ℚ[X] E ⧸ Q :=
    Ideal.quotientEquiv Q Q (galB τ) hQτ
  have hσκ : ∀ y, σκ (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (galB τ y) := fun y => rfl
  let σL : L ≃+* L := (e.symm.trans σκ).trans e
  let σ : L ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := σL) (fun x => by
    rw [eq_ratCast (algebraMap ℚ L), map_ratCast])
  -- `ψ : C → L`
  let ψ : integralClosure ℤ[X] E →+* L :=
    e.toRingHom.comp ((Ideal.Quotient.mk Q).comp (zqIncl E))
  have hψ : ∀ c, ψ c = e (Ideal.Quotient.mk Q (zqIncl E c)) := fun c => rfl
  have hker : ∀ c, ψ c = 0 → c ∈ 𝔓 := by
    intro c hc
    rw [hψ, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact hQ𝔓 hc
  have hNL : ∀ y : 𝓞 L, ∃ c₁ c₂ : integralClosure ℤ[X] E, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁ := by
    intro y
    have hy : IsIntegral ℤ (e.symm (y : L)) :=
      (y.2 : IsIntegral ℤ (y : L)).map (e.symm.toRingHom.toIntAlgHom)
    obtain ⟨c₁, c₂, hc₂, hc⟩ := hN _ hy
    refine ⟨c₁, c₂, hc₂, ?_⟩
    rw [hψ, hψ, ← hc, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  have hσψ : ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E,
      σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓 := by
    intro c
    obtain ⟨c', hc', hc'𝔓⟩ := hτC c
    refine ⟨c', ?_, hc'𝔓⟩
    show e (σκ (e.symm (e (Ideal.Quotient.mk Q (zqIncl E c))))) = ψ c'
    rw [RingEquiv.symm_apply_apply, hσκ, hψ]
    congr 2
    apply Subtype.ext
    rw [galB_apply]
    exact hc'.symm
  have hp𝔓 : (p : integralClosure ℤ[X] E) ∈ 𝔓 := by
    have h1 : algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ)) ∈ 𝔓 := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, h𝔓u]; exact hpm
    simpa using h1
  have hσ1 : σ = 1 := eq_one_of_primeOf 𝔓 ψ hker hNL σ hσψ p hp𝔓 hunL
  -- conclusion: `τ ∈ I_Q`
  refine ⟨Q, hQ, hQu, 1, ?_⟩
  rw [one_mul, inv_one, mul_one]
  intro y
  refine ⟨galB τ y, galB_apply τ y, ?_⟩
  rw [← Ideal.Quotient.eq, ← hσκ]
  have h2 : σL (e (Ideal.Quotient.mk Q y)) = e (Ideal.Quotient.mk Q y) := by
    have := congrArg (fun g : L ≃ₐ[ℚ] L => g (e (Ideal.Quotient.mk Q y))) hσ1
    rw [AlgEquiv.one_apply] at this
    exact this
  have h3 : e (σκ (Ideal.Quotient.mk Q y)) = e (Ideal.Quotient.mk Q y) := by
    rw [← h2]
    show e (σκ (Ideal.Quotient.mk Q y)) = e (σκ (e.symm (e (Ideal.Quotient.mk Q y))))
    rw [RingEquiv.symm_apply_apply]
  exact e.injective h3

end SGRDirect.NVLocal

#print axioms SGRDirect.NVLocal.nvLocalInertia_of_branchRegular
