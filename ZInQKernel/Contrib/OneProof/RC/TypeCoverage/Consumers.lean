import ZInQKernel.Contrib.OneProof.RC.TypeCoverage.Coverage
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Assemble
import ZInQKernel.Contrib.OneProof.RC.O12Formwise.Window
import ZInQKernel.Contrib.OneProof.RC.O12Realize.Window
import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Model

/-! Arithmetic input for the unmodified stage and formwise consumers.
The old-level prime support is the bound from tex 8421–8428, 8938–8981.
The level, transformations, constituents and attachments are for the same lift. -/

noncomputable section

namespace ZInQ.Manuscript.RC.TypeCoverage

open AddressGenuine ThetaCoeff TraceLimits PrintsArith O12Formwise
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators

variable {O : Type} [CommRing O] {M : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}
variable {N m₁ : ℕ} {late : Finset ℕ}
variable (hm : 0 < m₁) (h8 : 8 ∣ m₁) (hℓ : S.ℓ₀.Prime)
  (hcop : S.ℓ₀.Coprime m₁) (hlate : ∀ p ∈ late, Nat.Prime p)

/-- Tex 9670–9674, with the coefficient exclusion supplied by the type. -/
theorem fresh_outside_support {U : Finset ℕ} {q : ℕ}
    (hq : (coveredType (N := N) hm h8 hℓ hcop hlate).Good q) (hqU : q ∉ U) :
    q ∉ coefficientSupport S N late ∪ U := by
  simpa only [Finset.mem_union, not_or] using
    And.intro (good_not_mem_support hm h8 hℓ hcop hlate hq) hqU

/-- The old level is coprime to every good prime of the refined type. -/
theorem old_good {old : ℕ} (hold : old ≠ 0)
    (hlevel : old.primeFactors ⊆ coefficientSupport S N late) :
    ∀ q, (coveredType (N := N) hm h8 hℓ hcop hlate).Good q → q.Coprime old := by
  intro q hq
  apply (Nat.Prime.coprime_iff_not_dvd hq.1).2
  intro hd
  exact good_not_mem_support hm h8 hℓ hcop hlate hq (hlevel (hq.1.mem_primeFactors hd hold))

theorem test_coprime_old {avoid : Finset ℕ} {old : ℕ} (hold : old ≠ 0)
    (hlevel : old.primeFactors ⊆ coefficientSupport S N late) :
    ∀ q, Test (coveredType (N := N) hm h8 hℓ hcop hlate) avoid q → q.Coprime old :=
  fun q hq => old_good hm h8 hℓ hcop hlate hold hlevel q hq.1

/-- A `LevelSetup` for the actual old level, directly usable by
`BlocksPerU.realize_of_stage`. The latter supplies `BlockLevels.old_good`
by copying this field. The fixed Eichler level `N` is distinct from `common`. -/
def levelSetup {W common : ℕ} [NeZero common]
    {P : Window (coveredType (N := N) hm h8 hℓ hcop hlate).Good S W} {avoid : Finset ℕ}
    (old : ℕ) (hfour : 4 ∣ old) (hlevel : old.primeFactors ⊆ coefficientSupport S N late)
    (hcommon : common = old * ∏ p ∈ P.pool, p) (havoid : P.pool ⊆ avoid) :
    BlocksPerU.LevelSetup P avoid common where
  old := old
  four_dvd := hfour
  common := hcommon
  old_good := old_good hm h8 hℓ hcop hlate (by
    intro hz
    exact NeZero.ne common (by simp [hcommon, hz])) hlevel
  pool_avoided := havoid

theorem test_coprime_common {W common : ℕ} [NeZero common]
    {P : Window (coveredType (N := N) hm h8 hℓ hcop hlate).Good S W} {avoid : Finset ℕ}
    {old : ℕ} (hfour : 4 ∣ old) (hlevel : old.primeFactors ⊆ coefficientSupport S N late)
    (hcommon : common = old * ∏ p ∈ P.pool, p) (havoid : P.pool ⊆ avoid) :
    ∀ q, Test (coveredType (N := N) hm h8 hℓ hcop hlate) avoid q → q.Coprime common :=
  (levelSetup hm h8 hℓ hcop hlate old hfour hlevel hcommon havoid).test_coprime

section ExistingFormwise

variable {I K G L : Type} [Fintype I] [Field K] [TopologicalSpace K]
  [IsDomain O] [CharZero O] [Algebra O K] [Group G] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {W R : ℕ} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable {V : Blocks (P := P) A E D C} {levels : BlockLevels V}
variable {ρ₀ : Attachment A frob}

theorem inertiaOn_of_atLevel (H : AtLevel levels ρ₀) (support : Finset ℕ) (B : ℕ) :
    O12Realize.InertiaOn (B := B) V ρ₀ support := by
  intro U _ _ q hq _ hqU Q hQ hqQ σ hσ i hi
  exact seed_unramified H hq hqU hQ hqQ hσ (Finset.Subset.refl U) hi

/-- This is the `hseed` input of `windowModel` and the input used by
`buildWithFormwiseInertia` after trace multiplication. -/
theorem window_hseed (H : AtLevel levels ρ₀) (support : Finset ℕ) (B : ℕ) :
    ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∀ q, T.Good q → q ∉ support → q ∉ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ U₀ ⊆ U, ∀ i, V.seed U₀ i ≠ 0 → ρ₀.ρ i σ = 1 := by
  intro U _ _ q hq _ hqU Q hQ hqQ σ hσ U₀ hU₀ i hi
  exact seed_unramified H hq hqU hQ hqQ hσ hU₀ hi

variable [IsLocalRing O] {m : Ideal O}

/-- The excluded formwise formula on the original lattice. This is the
`hexcl` input after identifying the model's trace and coefficients with
the window construction. -/
theorem window_hexcl (H : AtLevel levels ρ₀)
    (hinj : Function.Injective (algebraMap O K)) (hm : m.IsMaximal) (h2 : (2 : O) ∈ m)
    (hst : ∀ g, ∀ v ∈ A.Λ (O := O) V.seed, tV ρ₀.ρ g v ∈ A.Λ (O := O) V.seed)
    (hsd : ∀ g, ∀ v ∈ A.Λ (O := O) V.seed, dV ρ₀.ρ g v ∈ A.Λ (O := O) V.seed)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (B : ℕ) :
    ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      U.card + 1 ≤ B → q ∈ avoid →
      ∃ diamondF : A.Λ (O := O) V.seed, ∀ n,
        V.coeff hinj n (latT ρ₀.ρ _ hst (frob q) (V.F U)) =
          V.coeff hinj (q * n) (V.F U) +
            if q ∣ n then (q : O) * V.coeff hinj (n / q) diamondF else 0 := by
  intro U q _ hq hqU _ _
  obtain ⟨d, _, _, h⟩ := seed_fourier H hinj hm h2 hst hsd hq hqU (hfrob q hq)
  exact ⟨d, h⟩

end ExistingFormwise

/-- A new support prime requires a new type coordinate. Changing only the
`TypeData.m` field cannot make the original character detect this radical. -/
theorem unchanged_char_cannot_detect {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
    {T : TypeData L ε} {χ : GalQ →* Multiplicative L} (htyp : IsTypeChar T χ)
    {support : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqS : q ∈ support) :
    ¬ TypeDetectsRadicals χ support :=
  fun hs => no_good_mem_stationary htyp
    (fun _ h => chooseFrob_spec frobeniusExists h.1) hs hq hqS

#print axioms fresh_outside_support
#print axioms old_good
#print axioms test_coprime_old
#print axioms levelSetup
#print axioms test_coprime_common
#print axioms inertiaOn_of_atLevel
#print axioms window_hseed
#print axioms window_hexcl
#print axioms unchanged_char_cannot_detect

end ZInQ.Manuscript.RC.TypeCoverage
