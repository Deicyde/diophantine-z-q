import ZInQKernel.Contrib.CloudB3E2Norm.RingClassKS

/-!
# Stage 0 of the ring-class realization: the order `ℤ + f𝒪_K`, its ring class field in `K_S`,
# and the restriction `G_{K,S} → Gal(H_f/K)`

Manuscript `diophantine_zq.tex`, tex 3565–3595 (the ring class fields `H_r` of conductor `r`,
`Gal(H_r/K) ≅ Pic(ℤ + r𝒪_K)`) and tex 2779–2796.

* `ringClassOrder f`: the order `ℤ + f𝒪_K` of a number field `K`, as Tau Ceti's
  `NumberFieldOrder` (`mem_ringClassOrder_iff`: `x ∈ ℤ + f𝒪_K` iff `x ≡ a (mod f𝒪_K)` for an
  integer `a`). Its conductor contains `f𝒪_K` (`span_le_conductor_ringClassOrder`), so every prime
  dividing the conductor lies over `f` (`mem_of_dvd_conductor_ringClassOrder`).
* `ringClassFieldOf f S hS`: the ring class field of `ℤ + f𝒪_K`, as an intermediate field of
  `K_S/K`, for `S` containing the primes over `f` (E2's `ringClassFieldS`). It is finite and normal
  over `K` (`normal_ringClassFieldOf`).
* `ringClassGal f S hS`: `Gal(H_f/K)`. `ringClassPicEquiv`: Tau Ceti's Artin isomorphism
  `Pic(ℤ + f𝒪_K) ≃* Gal(H_f/K)` (`ringClassArtinEquiv`), transported to the copy of `H_f` in `K_S`.
* `ringClassRes f S hS : G_{K,S} →* Gal(H_f/K)`: restriction, onto (`ringClassRes_surjective`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open ZInQ.Manuscript.RC.CoefModules (KS)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3E2.NormCochain (toAlgClosure ringClassField_le_KS ringClassFieldS)

variable {K : Type} [Field K] [NumberField K]

/-! ### The order `ℤ + f𝒪_K` -/

/-- `ℤ + f𝒪_K` inside `𝒪_K`: the preimage of the image of `ℤ` in `𝒪_K/f𝒪_K`.
Kind: definition. -/
def ringClassSubalgebra (f : ℕ) : Subalgebra ℤ (𝓞 K) :=
  (⊥ : Subalgebra ℤ (𝓞 K ⧸ Ideal.span {(f : 𝓞 K)})).comap
    (Ideal.Quotient.mkₐ ℤ (Ideal.span {(f : 𝓞 K)}))

omit [NumberField K] in
theorem mem_ringClassSubalgebra_iff (f : ℕ) (x : 𝓞 K) :
    x ∈ ringClassSubalgebra (K := K) f ↔
      ∃ a : ℤ, x - (a : 𝓞 K) ∈ Ideal.span {(f : 𝓞 K)} := by
  rw [ringClassSubalgebra, Subalgebra.mem_comap, Algebra.mem_bot]
  constructor
  · rintro ⟨a, ha⟩
    rw [Ideal.Quotient.mkₐ_eq_mk] at ha
    refine ⟨a, Ideal.Quotient.eq.mp ?_⟩
    rw [← ha, map_intCast, eq_intCast]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq.mpr ha, map_intCast, eq_intCast]

omit [NumberField K] in
theorem span_le_ringClassSubalgebra (f : ℕ) {x : 𝓞 K} (hx : x ∈ Ideal.span {(f : 𝓞 K)}) :
    x ∈ ringClassSubalgebra (K := K) f :=
  (mem_ringClassSubalgebra_iff f x).mpr ⟨0, by simpa using hx⟩

/-- **The order `ℤ + f𝒪_K`** (`f ≠ 0`), as a `NumberFieldOrder`. Kind: definition. -/
def ringClassOrder (f : ℕ) (hf : f ≠ 0) : NumberFieldOrder K where
  toSubalgebra := (ringClassSubalgebra (K := K) f).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  finite := by
    have : Module.Finite ℤ (ringClassSubalgebra (K := K) f) :=
      Module.Finite.of_injective (Subalgebra.toSubmodule (ringClassSubalgebra f)).subtype
        Subtype.val_injective
    exact Module.Finite.equiv (Subalgebra.equivMapOfInjective _ _
      (FaithfulSMul.algebraMap_injective (𝓞 K) K)).toLinearEquiv
  spans := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy0, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    let w' : 𝓞 K := ⟨y • x, hint⟩
    have hmem : ((f : 𝓞 K) * w' : 𝓞 K) ∈ ringClassSubalgebra (K := K) f :=
      span_le_ringClassSubalgebra f (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have hmemK : ((((f : 𝓞 K) * w' : 𝓞 K)) : K) ∈
        ((ringClassSubalgebra (K := K) f).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K) : Set K) :=
      ⟨_, hmem, rfl⟩
    have hx : x = ((f : ℚ) * (y : ℚ))⁻¹ • ((((f : 𝓞 K) * w' : 𝓞 K)) : K) := by
      rw [Algebra.smul_def, map_inv₀, map_mul, map_natCast, map_intCast]
      push_cast
      change x = ((f : K) * (y : K))⁻¹ * ((f : K) * (y • x))
      rw [zsmul_eq_mul]
      have hy : (y : K) ≠ 0 := by exact_mod_cast hy0
      have hfK : (f : K) ≠ 0 := by exact_mod_cast hf
      field_simp
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmemK)

theorem mem_ringClassOrder_iff (f : ℕ) (hf : f ≠ 0) (x : 𝓞 K) :
    (x : K) ∈ (ringClassOrder (K := K) f hf).toSubalgebra ↔
      ∃ a : ℤ, x - (a : 𝓞 K) ∈ Ideal.span {(f : 𝓞 K)} := by
  rw [← mem_ringClassSubalgebra_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 K) K hyx
    exact this ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

/-- `f𝒪_K` lies in the conductor of `ℤ + f𝒪_K`. Kind: PROVED. -/
theorem span_le_conductor_ringClassOrder (f : ℕ) (hf : f ≠ 0) :
    Ideal.span {(f : 𝓞 K)} ≤ (ringClassOrder (K := K) f hf).conductor := by
  rw [le_conductor_iff]
  intro x hx
  exact (mem_ringClassOrder_iff f hf x).mpr ⟨0, by simpa using hx⟩

/-- Every prime dividing the conductor of `ℤ + f𝒪_K` lies over `f`. Kind: PROVED. -/
theorem mem_of_dvd_conductor_ringClassOrder (f : ℕ) (hf : f ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∣ (ringClassOrder (K := K) f hf).conductor) : (f : 𝓞 K) ∈ v.asIdeal := by
  rw [Ideal.dvd_iff_le] at hv
  exact hv (span_le_conductor_ringClassOrder f hf (Ideal.subset_span rfl))

/-! ### The ring class field of conductor `f` inside `K_S`, and the restriction -/

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hS in
theorem conductor_primes_mem (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∣ (ringClassOrder (K := K) f hf).conductor) : v ∈ S :=
  hS v (mem_of_dvd_conductor_ringClassOrder f hf v hv)

/-- **The ring class field `H_f` of `ℤ + f𝒪_K` inside `K_S`** (tex 3565–3570). Kind: definition. -/
def ringClassFieldOf : IntermediateField K (KS K S) :=
  ringClassFieldS (ringClassOrder (K := K) f hf) S (conductor_primes_mem f hf S hS)

instance finiteDimensional_ringClassFieldOf : FiniteDimensional K (ringClassFieldOf f hf S hS) :=
  ZInQ.Contrib.CloudB3E2.NormCochain.finiteDimensional_ringClassFieldS _ _ _

/-- `H_f` inside `K_S` is `K`-isomorphic to Tau Ceti's ring class field. Kind: definition. -/
def ringClassFieldOfEquiv :
    ringClassFieldOf f hf S hS ≃ₐ[K] ringClassField (ringClassOrder (K := K) f hf) :=
  (IntermediateField.restrictAlgEquiv (ringClassField_le_KS _ S
      (conductor_primes_mem f hf S hS))).symm.trans
    (IntermediateField.equivMap (ringClassField (ringClassOrder (K := K) f hf))
      (separableClosure K (AlgebraicClosure K)).val).symm

/-- `H_f/K` is normal. Kind: PROVED. -/
instance normal_ringClassFieldOf : Normal K (ringClassFieldOf f hf S hS) :=
  Normal.of_algEquiv (ringClassFieldOfEquiv f hf S hS).symm

/-- **`Gal(H_f/K)`**. Kind: definition. -/
abbrev ringClassGal : Type := ringClassFieldOf f hf S hS ≃ₐ[K] ringClassFieldOf f hf S hS

/-- **`Pic(ℤ + f𝒪_K) ≃* Gal(H_f/K)`** (tex 3565–3567; [Cox, Thm 9.18]): Tau Ceti's Artin
isomorphism `ringClassArtinEquiv`, transported to the copy of `H_f` in `K_S`.
Kind: definition. -/
def ringClassPicEquiv : Pic (ringClassOrder (K := K) f hf) ≃* ringClassGal f hf S hS :=
  (ringClassArtinEquiv (ringClassOrder (K := K) f hf)).trans
    (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)).symm

/-- `Gal(H_f/K)` is commutative. Kind: PROVED. -/
instance : CommGroup (ringClassGal f hf S hS) :=
  { (inferInstance : Group (ringClassGal f hf S hS)) with
    mul_comm := fun a b => by
      apply (ringClassPicEquiv f hf S hS).symm.injective
      rw [map_mul, map_mul, mul_comm] }

/-- **The restriction `G_{K,S} → Gal(H_f/K)`**. Kind: definition. -/
def ringClassRes : GKS K S →* ringClassGal f hf S hS :=
  AlgEquiv.restrictNormalHom (ringClassFieldOf f hf S hS)

/-- The restriction is onto. Kind: PROVED. -/
theorem ringClassRes_surjective : Function.Surjective (ringClassRes f hf S hS) :=
  AlgEquiv.restrictNormalHom_surjective (KS K S)

end ZInQ.Contrib.CloudB3E1RingClass
