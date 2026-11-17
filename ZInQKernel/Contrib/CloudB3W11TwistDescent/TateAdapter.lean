import ZInQKernel.Contrib.CloudB3W11TwistDescent.FiniteIndex
import ZInQKernel.Contrib.CloudB3W11TateTrace.TwistWholeGroup
import ZInQKernel.OneProof.H.TailS

/-!
# Exact finite-field Tate twist adapter

The whole-group local-character theorem is the ported Anthropic Tate proof.
The finite-index extension is the twisted norm-product argument in `FiniteIndex`.
The action is the canonical completion action, proved equal to the repository's
`cpAct`; the scalar is exactly the repository's `cycPow`, with exponent `-i` after
rearranging the invariant equation. No arithmetic hypotheses remain.
-/

namespace ZInQ.Contrib.CloudB3W11TwistDescent

open ZInQ.Contrib.G9.PkgI4
open ZInQ.Contrib.CloudB3W11AxCompletion

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The genuine local cyclotomic character with values embedded in `ℂ_p` units. -/
def cyclotomicCp : GQp p →* ℂ_[p]ˣ :=
  (Units.map ((algebraMap ℚ_[p] ℂ_[p]).comp
    (PadicInt.Coe.ringHom (p := p)) : ℤ_[p] →* ℂ_[p])).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp (toRingEquivHom p))

@[simp]
theorem cyclotomicCp_val (σ : GQp p) :
    ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (((cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := rfl

/-- The integer-power scalar is exactly `cycPow`, not a restated character. -/
theorem cyclotomicCp_zpow_val (σ : GQp p) (i : ℤ) :
    ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ i =
      algebraMap ℚ_[p] ℂ_[p] (cycPow p σ i) := by
  let ι : ℤ_[p]ˣ →* ℂ_[p]ˣ := Units.map
    ((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p)) : ℤ_[p] →* ℂ_[p])
  change ((ι (cyc p σ) : ℂ_[p]ˣ) : ℂ_[p]) ^ i = _
  rw [← Units.val_zpow_eq_zpow_val, ← map_zpow ι]
  rfl

/-- Rearrange the exact invariant equation to the character-eigenvector form. -/
theorem eigenvector_of_twisted_fixed (σ : GQp p) (i : ℤ) (x : ℂ_[p])
    (hx : cycPow p σ i • cpAct p σ x = x) :
    σ • x = ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-i) * x := by
  rw [galois_smul_eq_cpAct]
  have h1 : ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ i * cpAct p σ x = x := by
    rw [cyclotomicCp_zpow_val, ← Algebra.smul_def]
    exact hx
  have h2 := congrArg
    (fun y : ℂ_[p] => ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-i) * y) h1
  rw [← mul_assoc, ← zpow_add₀ (cyclotomicCp p σ).ne_zero,
    neg_add_cancel, zpow_zero, one_mul] at h2
  exact h2

/-- Unconditional nonzero-twist vanishing for every finite intermediate field,
with exactly the existing `HodgeSplit.TateTwistInvariants` type. -/
theorem all_twist_invariants_vanish : ZInQ.Contrib.HodgeSplit.TateTwistInvariants := by
  intro p hp K hK i hi x hx
  let χ := cyclotomicCp p
  have hχ : ∀ (σ τ : GQp p), σ • ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) =
      ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) := by
    intro σ τ
    rw [cyclotomicCp_val]
    exact PadicComplex.smul_algebraMap p σ _
  have hvan : ∀ m : ℤ, m ≠ 0 → ∀ c : ℂ_[p],
      (∀ σ : GQp p, σ • c = ((χ σ : ℂ_[p]ˣ) : ℂ_[p]) ^ m * c) → c = 0 := by
    intro m hm c hc
    refine ZInQ.Contrib.CloudB3W11TateTrace.TwistWholeGroup.solution p m hm c ?_
    intro σ
    have h := hc σ
    change σ • c = ((cyclotomicCp p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ m * c at h
    rw [cyclotomicCp_val] at h
    exact h
  haveI : K.fixingSubgroup.FiniteIndex :=
    ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
        exact Module.finrank_pos.ne'⟩
  refine zero_of_finiteIndex_twistedInvariants χ hχ hvan K.fixingSubgroup
    (-i) (neg_ne_zero.mpr hi) x ?_
  intro σ hσ
  exact eigenvector_of_twisted_fixed p σ i x (hx σ hσ)

end

end ZInQ.Contrib.CloudB3W11TwistDescent
