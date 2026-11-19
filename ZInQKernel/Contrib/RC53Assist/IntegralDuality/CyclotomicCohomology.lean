import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCoefficientLimit
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
# Finiteness and support of the actual integral cyclotomic cochains

The coefficient line has the two-adic topology and the genuine cyclotomic
Galois action. Its already constructed residue system supplies the completion
and equivariance hypotheses of the cochain limit theorems. Finite-level
finiteness and dimension bounds are the stated Milne inputs, with the support
and no-real-place conditions retained. No global trace or duality is assumed.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Contrib.RC53Assist.Finiteness
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.CalibrationShape

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} [HasTwoPowerRoots K S]

/-- The genuine finite cyclotomic line has exactly its prescribed two-power order. -/
theorem finiteCyclotomicLine_card (k : ℕ) :
    Nat.card (FiniteCyclotomicLine K S k) = 2 ^ k := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  change Nat.card (ZMod (2 ^ k)) = 2 ^ k
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The primes dividing the finite coefficient order are within the stated dyadic support. -/
theorem finiteCyclotomicLine_support
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (k : ℕ) :
    ∀ v : HeightOneSpectrum (𝓞 K),
      ((Nat.card (FiniteCyclotomicLine K S k) : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  natCard_mem_of_two_pow h2 (finiteCyclotomicLine_card k)

/-- Global finite-level finiteness applies to the actual cyclotomic coefficient lines. -/
theorem finite_globalCyclotomicLevel_homology
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (k : ℕ) (n : ℤ) :
    Finite ((natCx (contCochains ℤ (GKS K S) (FiniteCyclotomicLine K S k))).toCC.homology n) :=
  hglob K S hS ℤ (FiniteCyclotomicLine K S k) inferInstance
    (finiteCyclotomicLine_support h2 k) n

/-- The actual integral global cyclotomic cohomology is finitely generated. -/
theorem moduleFinite_globalIntegralCyclotomic_homology
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (n : ℤ) :
    Module.Finite ℤ_[2]
      ((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).toCC.homology n) :=
  moduleFinite_homology_of_twoAdicLimit (integralCoefficient_isTwoAdicLimit K S)
    (integralCoefficient_isEquivariantLevels K S)
    (finite_globalCyclotomicLevel_homology hglob hS h2) n

/-- The global integral cyclotomic cohomology vanishes above degree two under the real-place guard. -/
theorem globalIntegralCyclotomic_homology_high
    (hglob : MilneGlobalFiniteness) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (n : ℤ) (hn : 2 < n) :
    Subsingleton ((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).toCC.homology n) :=
  twoAdic_homology_subsingleton (integralCoefficient_isTwoAdicLimit K S)
    (integralCoefficient_isEquivariantLevels K S)
    (finite_globalCyclotomicLevel_homology hglob hS h2) n
    (fun k => hglobal K hK S hS (FiniteCyclotomicLine K S k) inferInstance
      (finiteCyclotomicLine_support h2 k) n hn)

/-- Restriction of the specified integral residue map to an actual decomposition group. -/
def localIntegralCoefficientProj (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    ResMod (locMap K S v) (IntegralTate1 K S) →+
      ResMod (locMap K S v) (FiniteCyclotomicLine K S k) :=
  integralCoefficientProj K S k

/-- Restriction changes only the group action, not the coefficient limit or topology. -/
theorem localIntegralCoefficient_isTwoAdicLimit (v : HeightOneSpectrum (𝓞 K)) :
    IsTwoAdicLimit (localIntegralCoefficientProj (K := K) (S := S) v) :=
  integralCoefficient_isTwoAdicLimit K S

/-- The same coefficient maps are equivariant through the genuine localization homomorphism. -/
theorem localIntegralCoefficient_isEquivariantLevels (v : HeightOneSpectrum (𝓞 K)) :
    IsEquivariantLevels (Gloc K v) (localIntegralCoefficientProj (K := K) (S := S) v) := by
  intro k g t
  exact integralCoefficient_isEquivariantLevels K S k (locMap K S v g) t

/-- Local finite-level finiteness applies at every finite place, including those above two. -/
theorem finite_localCyclotomicLevel_homology
    (hloc : MilneLocalFiniteness) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) (n : ℤ) :
    Finite ((natCx (contCochains ℤ (Gloc K v)
      (ResMod (locMap K S v) (FiniteCyclotomicLine K S k)))).toCC.homology n) :=
  hloc K v ℤ (ResMod (locMap K S v) (FiniteCyclotomicLine K S k))
    (inferInstanceAs (Finite (FiniteCyclotomicLine K S k))) n

/-- Local integral cyclotomic cohomology is finitely generated in every degree. -/
theorem moduleFinite_localIntegralCyclotomic_homology
    (hloc : MilneLocalFiniteness) (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Module.Finite ℤ_[2] ((natCx (contCochains ℤ_[2] (Gloc K v)
      (ResMod (locMap K S v) (IntegralTate1 K S)))).toCC.homology n) :=
  moduleFinite_homology_of_twoAdicLimit (localIntegralCoefficient_isTwoAdicLimit v)
    (localIntegralCoefficient_isEquivariantLevels v)
    (finite_localCyclotomicLevel_homology hloc v) n

/-- Local integral cyclotomic cohomology vanishes above degree two. -/
theorem localIntegralCyclotomic_homology_high
    (hloc : MilneLocalFiniteness) (hlocal : MilneLocalDimensionTwo)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) (hn : 2 < n) :
    Subsingleton ((natCx (contCochains ℤ_[2] (Gloc K v)
      (ResMod (locMap K S v) (IntegralTate1 K S)))).toCC.homology n) :=
  twoAdic_homology_subsingleton (localIntegralCoefficient_isTwoAdicLimit v)
    (localIntegralCoefficient_isEquivariantLevels v)
    (finite_localCyclotomicLevel_homology hloc v) n
    (fun k => hlocal K v (ResMod (locMap K S v) (FiniteCyclotomicLine K S k))
      (inferInstanceAs (Finite (FiniteCyclotomicLine K S k))) n hn)

end ZInQ.Contrib.RC53Assist.IntegralDuality
