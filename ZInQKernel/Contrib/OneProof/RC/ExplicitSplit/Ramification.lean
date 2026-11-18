import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Scalars
import ZInQKernel.Contrib.OneProof.RC.Eichler.Explicit
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Algebra

/-!
# Ramification of the explicit quaternion algebra

On-the-spot (c), for tex 8462–8463. The general existence print remains
available independently of this explicit construction.
-/

namespace ZInQ.Manuscript.RC.ExplicitSplit

theorem anisotropic_at_ell {ell : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) :
    AppF.NormFormAnisotropic ℚ_[ell] ((-1 : ℚ) : ℚ_[ell]) ((-(ell : ℚ)) : ℚ_[ell]) := by
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  intro x y z t hn
  let q : LocalDivision.D ell := ⟨x, y, z, t⟩
  have hz : LocalDivision.nrd q = 0 := by
    rw [LocalDivision.nrd_formula]
    push_cast at hn
    change x ^ 2 + y ^ 2 + (ell : ℚ_[ell]) * (z ^ 2 + t ^ 2) = 0
    linear_combination hn
  have hq := (LocalDivision.nrd_eq_zero q).mp hz
  exact ⟨congrArg QuaternionAlgebra.re hq, congrArg QuaternionAlgebra.imI hq,
    congrArg QuaternionAlgebra.imJ hq, congrArg QuaternionAlgebra.imK hq⟩

theorem isotropic_away {ell p : ℕ} [Fact p.Prime] (hell : ell.Prime) (h : ell % 4 = 3)
    (hp : p ≠ ell) :
    ¬ AppF.NormFormAnisotropic ℚ_[p] ((-1 : ℚ) : ℚ_[p]) ((-(ell : ℚ)) : ℚ_[p]) := by
  obtain ⟨a, b, hab⟩ := integral_parameters hell h hp
  have hab' := congrArg (algebraMap ℤ_[p] ℚ_[p]) hab
  push_cast at hab'
  change (2 * (a : ℚ_[p]) - 1) ^ 2 + (2 * (b : ℚ_[p])) ^ 2 = -(ell : ℚ_[p]) at hab'
  intro hn
  exact one_ne_zero (hn (2 * (a : ℚ_[p]) - 1) (2 * (b : ℚ_[p])) 1 0 (by
    push_cast
    linear_combination hab')).2.2.1

/-- The explicit algebra supplies the ramification predicate of Appendix F. -/
theorem explicit_ramifiedExactlyAtEll0Infty {ell : ℕ} (hell : ell.Prime) (h : ell % 4 = 3) :
    AppF.RamifiedExactlyAtEll0Infty ell (-1) (-(ell : ℚ)) := by
  refine ⟨by norm_num, neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hell.ne_zero), ?_, ?_⟩
  · simpa using Eichler.explicit_anisotropic_real hell.pos
  · intro p _hp
    constructor
    · intro hA
      by_contra he
      exact isotropic_away hell h he hA
    · rintro rfl
      exact anisotropic_at_ell h

#print axioms anisotropic_at_ell
#print axioms isotropic_away
#print axioms explicit_ramifiedExactlyAtEll0Infty

end ZInQ.Manuscript.RC.ExplicitSplit
