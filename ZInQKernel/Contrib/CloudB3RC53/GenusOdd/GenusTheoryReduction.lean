import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.HeightDischarge

/-!
# GenusOdd: reducing the GLUE `GenusTheory` to two smaller GLUE statements

`GenusTheory` (`Glue.lean`) bundles three claims about the ring class field `H_c` of
`O_c = ℤ + c𝓞_K` (`K` imaginary quadratic) and `χ = χ_{d₁} ∘ N` on `Pic(O_c)`:
1. `H_c/ℚ` is Galois;
2. there are `s₁, s₂ ∈ H_c`, `s₁² = d₁`, `s₂² = d₂`, on which `Gal(H_c/K)` acts by `χ`;
3. some `ρ ∈ Gal(H_c/ℚ)` fixes one of `s₁, s₂` and negates the other.

Claim 3 is PROVED here from 1 and 2 (`genusTheory_of`): `s₁ s₂` is fixed by `Gal(H_c/K)`, hence
lies in `K`; its square `d₁ d₂ = disc(K) c²` is negative (`disc K < 0`, Mathlib's `sign_discr`), so
`s₁ s₂ ∉ ℚ` and the nontrivial automorphism of `K`, lifted to `H_c` (`restrictNormalHom_surjective`),
negates it. What remained GLUE at this stage (`GenusRoots` has since been PROVED,
`genusRoots_proof` in `GenusRootsProof.lean`, and `RingClassGalois` is no longer needed on the route
of `Artin34.lean`):

* `RingClassGalois` (claim 1): standard (Cox, Lemma 9.3: `Gal(H_c/ℚ)` is generalized dihedral).
  Missing in Tau Ceti: functoriality of the global class field correspondence under
  `Aut(K/ℚ)` (the norm group of `τ(H_c)` is `τ` of that of `H_c`, and the ring-class norm group is
  `τ`-stable because `O_c` is).
* `GenusRoots` (claim 2): standard genus theory. Provable from Tau Ceti's splitting law
  (`isArithFrobAt_ringClassArtinEquiv_picClass`), Frobenius generation
  (`closure_isArithFrobAt_eq_top`, `finrank_eq_one_of_stabilizer_eq_bot`) and Euler's criterion in
  residue fields, applied to `H_c(√d₁)/H_c`; this is a substantial formalization (residue fields
  of primes of `H_c`, decomposition groups, Frobenius on `√d₁`), not done here (done in
  `GenusAction.lean`, `GenusSqrtMem.lean`, `GenusRootsProof.lean`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **The ring class field of an imaginary quadratic order is Galois over `ℚ`** (GLUE; Cox,
*Primes of the form x² + ny²*, Lemma 9.3). Not needed on the route of `Artin34.lean`. -/
def RingClassGalois : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (c : ℕ) [NeZero c], IsGalois ℚ (ringClassField (conductorOrder K c))

/-- **Genus square roots** (introduced as GLUE; **PROVED**: `genusRoots_proof`, `GenusRootsProof.lean`; genus theory): under the hypotheses of `GenusTheory`, `√d₁` and
`√d₂` lie in `H_c` and `Gal(H_c/K)` acts on them through `χ = χ_{d₁} ∘ N`. -/
def GenusRoots : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    Odd (discr K) →
    ∀ (c : ℕ) [NeZero c] (d₁ d₂ : ℤ), d₁ * d₂ = discr K * c ^ 2 → d₁ % 4 = 1 → Squarefree d₁ →
      (c : ℤ) ∣ d₁ → Nat.Coprime c (discr K).natAbs →
    ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsQuadRingClassChar K c d₁ χ →
      ∃ s₁ s₂ : ringClassField (conductorOrder K c),
        s₁ ^ 2 = (d₁ : ringClassField (conductorOrder K c)) ∧
        s₂ ^ 2 = (d₂ : ringClassField (conductorOrder K c)) ∧
        (∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
          σ s₁ = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * s₁ ∧
          σ s₂ = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * s₂)

theorem discr_neg_of_totallyComplex {K : Type} [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) [IsTotallyComplex K] : discr K < 0 := by
  have h1 : InfinitePlace.nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have := sign_discr (K := K)
  rw [h1, pow_one] at this
  exact Int.sign_eq_neg_one_iff_neg.mp this

/-- **`GenusTheory` from `RingClassGalois` and `GenusRoots`** (PROVED). -/
theorem genusTheory_of (hG : RingClassGalois) (hR : GenusRoots) : GenusTheory := by
  intro K _ _ hK2 hTC hDodd c _ d₁ d₂ hprod hd₁ hsq hcd hcD χ hχ
  have hgal := hG K hK2 hTC c
  obtain ⟨s₁, s₂, hs₁, hs₂, hσ⟩ := hR K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq hcd hcD χ hχ
  refine ⟨hgal, s₁, s₂, hs₁, hs₂, hσ, ?_⟩
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have hD0 : discr K < 0 := discr_neg_of_totallyComplex hK2
  have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; norm_num at hd₁
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl; rw [mul_zero] at hprod
    exact (mul_ne_zero hD0.ne (pow_ne_zero 2 hc0)) hprod.symm
  have hs0 : ∀ {d : ℤ} {s : ringClassField (conductorOrder K c)},
      s ^ 2 = (d : ringClassField (conductorOrder K c)) → d ≠ 0 → s ≠ 0 := by
    intro d s hs hd h0
    rw [h0] at hs
    have : ((d : ringClassField (conductorOrder K c))) = 0 := by rw [← hs]; ring
    exact hd (by exact_mod_cast this)
  have hs₁0 := hs0 hs₁ hd₁0
  have hs₂0 := hs0 hs₂ hd₂0
  -- `s₁ s₂ ∈ K`
  obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (s₁ * s₂)).mpr fun σ => by
    rw [map_mul, (hσ σ).1, (hσ σ).2]
    have := chiSign_sq (χ := χ) ((ringClassArtinEquiv (conductorOrder K c)).symm σ)
    calc _ = ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) *
          chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) :
            ringClassField (conductorOrder K c)) * (s₁ * s₂) := by push_cast; ring
      _ = s₁ * s₂ := by rw [this]; simp
  -- `r² = d₁ d₂`
  have hr2 : r ^ 2 = ((d₁ * d₂ : ℤ) : K) := by
    apply (algebraMap K (ringClassField (conductorOrder K c))).injective
    rw [map_pow, hr, mul_pow, hs₁, hs₂, map_intCast]; push_cast; ring
  -- `r ∉ ℚ`
  have hrQ : r ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, rfl⟩
    have h1 : (algebraMap ℚ K) (q ^ 2) = (algebraMap ℚ K) ((d₁ * d₂ : ℤ) : ℚ) := by
      rw [map_pow, hr2, map_intCast]
    have h2 : q ^ 2 = ((d₁ * d₂ : ℤ) : ℚ) := (algebraMap ℚ K).injective h1
    have h3 : (0 : ℚ) ≤ ((d₁ * d₂ : ℤ) : ℚ) := h2 ▸ sq_nonneg q
    have h4 : d₁ * d₂ < 0 := by rw [hprod]; exact mul_neg_of_neg_of_pos hD0 (by positivity)
    have : (0 : ℤ) ≤ d₁ * d₂ := by exact_mod_cast h3
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ : K ≃ₐ[ℚ] K, τ r ≠ r := by
    by_contra hcon
    push Not at hcon
    exact hrQ ((IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) r).mpr hcon)
  have hτr : τ r = -r := by
    have : (τ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr2, map_intCast]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_left hτ
  obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K)
    (E := ringClassField (conductorOrder K c)) τ
  refine ⟨ρ, ?_⟩
  have hρr : ρ (s₁ * s₂) = -(s₁ * s₂) := by
    rw [← hr]
    have := AlgEquiv.restrictNormal_commutes ρ K r
    rw [← this]
    have h' : ρ.restrictNormal K = τ := hρ
    rw [h', hτr, map_neg]
  have hcast : ∀ d : ℤ, ((d : ringClassField (conductorOrder K c))) =
      algebraMap ℚ (ringClassField (conductorOrder K c)) (d : ℚ) := fun d => by rw [map_intCast]
  rcases apply_eq_or_neg (by rw [hs₁, hcast]) ρ with h1 | h1 <;>
    rcases apply_eq_or_neg (by rw [hs₂, hcast]) ρ with h2 | h2
  · exfalso
    rw [map_mul, h1, h2] at hρr
    have : (2 : ringClassField (conductorOrder K c)) * (s₁ * s₂) = 0 := by linear_combination hρr
    have hchar : CharZero (ringClassField (conductorOrder K c)) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    simp [hs₁0, hs₂0] at this
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exfalso
    rw [map_mul, h1, h2] at hρr
    have : (2 : ringClassField (conductorOrder K c)) * (s₁ * s₂) = 0 := by linear_combination hρr
    have hchar : CharZero (ringClassField (conductorOrder K c)) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    simp [hs₁0, hs₂0] at this

/-- The GLUE of (3.4) after RC19 and this reduction: `ArtinFactorization`, `RingClassGalois`,
`GenusRoots`, `SplittingCriterion`. -/
structure GlueFinal : Prop where
  artin : ArtinFactorization
  galois : RingClassGalois
  roots : GenusRoots
  split : SplittingCriterion

theorem glueAfterRC19_of_final (G : GlueFinal) : GlueAfterRC19 :=
  ⟨G.artin, genusTheory_of G.galois G.roots, G.split⟩

/-- **(3.4)** from the printed leaves and `GlueFinal`. -/
theorem genusLower34_of_final (P : Prints) (G : GlueFinal) : GenusLower34 :=
  genusLower34_of_RC19 P (glueAfterRC19_of_final G)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
