import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageDataNonVacuity

/-!
# Theorem 5.3, Lane RC0 round 2: non-vacuity checks for the leaves

* The choices are substituted as stated: `withChoices_hstar`, `withChoices_δo`, and every other
  field is unchanged (`withChoices_toRCData_stages`, …; `rfl`).
* The premise of `RCLeaves.post` (an attained odd minimum) is satisfiable: in a toy model with the
  hyperfilter on stages, `M_θ = θ + 3`, one admissible parameter `D = 1` of valuation `0`, the depth
  set has least element `0` (`toyW_depthSet_isLeast`).
* The quantifier of `RCLeaves.pre` and `RCLeaves.post` over genus partners is not empty under the
  printed leaves: `exists_genusPartner` (lane RC13) produces one.
* The two stage leaves are satisfiable (`toyW_stages`).
* The stage clauses of `PreLeaves` (`StageSupport`, and the stage link `StagesFrom` of
  `OddStagedInstance`) hold for the data built with separated intrinsic unit support and later
  prime exclusions. The intrinsic unit support is disjoint from the primes of the chosen `k`.
  Actual sequences exist unconditionally; the detector value requires a nontorsion rational point (`StageDataNonVacuity.lean`: `stageClauses_concrete`,
  `stageClauses_of_detector`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

theorem withChoices_hstar {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) : (W.withChoices h δ).hstar = h := rfl

theorem withChoices_δo {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) : (W.withChoices h δ).δo = δ := rfl

theorem withChoices_toRCData_stages {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) :
    (W.withChoices h δ).stages = W.stages := rfl

theorem withChoices_toRCData_aθ {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) :
    (W.withChoices h δ).aθ = W.aθ := rfl

theorem withChoices_depthSet {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) :
    (W.withChoices h δ).depthSet = W.depthSet := rfl

/-- Toy interface data: hyperfilter stages, `M_θ = θ + 3`, constant coefficient `1`, the single
admissible parameter `D = 1`. -/
def toyW (ℓ : ℕ) : WData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 1
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := -7
  stages := hyperfilter ℕ
  Mθ := fun θ => θ + 3
  aθ := fun _ _ => 1
  admissible := fun _ D => D = 1
  δo := 0
  kfin := -7
  uPrim := fun _ _ => 1
  uTilde := fun _ _ => 1
  Partitionable := fun _ => False

instance (ℓ : ℕ) : Inhabited (WData ℓ) := ⟨toyW ℓ⟩

/-- **The premise of `RCLeaves.post` is satisfiable** (PROVED): the toy depth set has least
element `0`. -/
theorem toyW_depthSet_isLeast (ℓ : ℕ) : IsLeast (toyW ℓ).depthSet 0 := by
  have hv : (fun θ Dd => vZ ((toyW ℓ).aθ θ Dd)) = fun (_ : ℕ) (_ : ℤ) => (0 : WithTop ℤ) := by
    funext θ Dd
    simp [toyW, vZ, v2]
  refine ⟨⟨0, fun _ => 1, Filter.Eventually.of_forall fun θ => ?_⟩, fun r hr => ?_⟩
  · have hlt : (0 : WithTop ℤ) < ((θ + 3 : ℕ) : WithTop ℤ) := by
      have : (((θ + 3 : ℕ)) : WithTop ℤ) = (((θ + 3 : ℕ) : ℤ) : WithTop ℤ) := rfl
      rw [this]
      exact WithTop.coe_lt_coe.mpr (by omega)
    have hv1 : vZ ((toyW ℓ).aθ θ 1) = 0 := by simp [toyW, vZ, v2]
    refine ⟨rfl, by simp [AppGEndpoints.omega], ?_, ?_⟩
    · show vZ ((toyW ℓ).aθ θ 1) < (((toyW ℓ).Mθ θ : ℕ) : WithTop ℤ)
      rw [hv1]; exact hlt
    · show vZ ((toyW ℓ).aθ θ 1) = (((AppGEndpoints.omega 1 : ℤ) + 0 : ℤ) : WithTop ℤ)
      rw [hv1]; simp [AppGEndpoints.omega]
  · have hr' : r ∈ AppGEndpoints.DepthSet (hyperfilter ℕ) (fun θ => θ + 3)
        (fun _ _ => (0 : WithTop ℤ)) (fun _ D => D = 1) := by
      have : (toyW ℓ).depthSet = AppGEndpoints.DepthSet (hyperfilter ℕ) (fun θ => θ + 3)
          (fun _ _ => (0 : WithTop ℤ)) (fun _ D => D = 1) := by
        simp only [WData.depthSet, hv]
        rfl
      rwa [this] at hr
    exact (AppGEndpoints.depthSet_toy r hr').ge

/-- The toy stages satisfy the two stage leaves (PROVED): the hyperfilter is nonprincipal and
`M_θ = θ + 3 ≥ θ`. -/
theorem toyW_stages (ℓ : ℕ) :
    ((toyW ℓ).stages : Filter ℕ) ≤ cofinite ∧ ∀ θ : ℕ, θ ≤ (toyW ℓ).Mθ θ :=
  ⟨hyperfilter_le_cofinite, fun θ => by simp [toyW]⟩

end ZInQ.Manuscript.RC.Wiring
