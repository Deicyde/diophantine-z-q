import ZInQKernel.Contrib.OneProof.RC.Eichler.Explicit
import ZInQKernel.Contrib.OneProof.RC.Eichler.Local

/-!
# Coordinates on the completed explicit order

On-the-spot (c), for tex 8464–8465. Completion preserves the lattice
coordinates on the original four generators, including at two.
-/

namespace ZInQ.Manuscript.RC.ExplicitSplit

open Eichler

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Local coordinates on `1, i, (1+j)/2, (i+k)/2`. -/
def localCoords (b : ℚ) : Bp p (-1) b ≃ₗ[ℚ_[p]] (Fin 4 → ℚ_[p]) where
  toFun x := ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]
  invFun z := ⟨z 0 + z 2 / 2, z 1 + z 3 / 2, z 2 / 2, z 3 / 2⟩
  left_inv x := by ext <;> simp
  right_inv z := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' t x := by ext i; fin_cases i <;> simp <;> ring

private def toLocalInt (b : ℚ) : B (-1) b →ₗ[ℤ] Bp p (-1) b where
  toFun := toLocal p
  map_add' := map_add _
  map_smul' n x := map_zsmul (toLocal p) n x

private theorem completion_span (m : ℤ) :
    ((explicitOrder m).completion p).toSubmodule =
      Submodule.span ℤ_[p] (Set.range (Module.Basis.ofEquivFun
        (localCoords p (1 - 4 * (m : ℚ))))) := by
  let b : ℚ := 1 - 4 * (m : ℚ)
  let e := Module.Basis.ofEquivFun (explicitCoords m)
  let d := Module.Basis.ofEquivFun (localCoords p b)
  have he : (explicitOrder m).lattice = Submodule.span ℤ (Set.range e) := rfl
  have hd (i : Fin 4) : toLocalInt p b (e i) = d i := by
    simp only [e, d, Module.Basis.coe_ofEquivFun]
    ext <;> simp [explicitCoords, localCoords, toLocalInt, toLocal, Pi.single_apply, apply_ite]
  rw [Order.completion_toSubmodule, localLattice, he]
  change Submodule.span ℤ_[p]
    (toLocalInt p b '' (Submodule.span ℤ (Set.range e) : Set _)) = _
  rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower,
    ← Set.range_comp]
  have heq : toLocalInt p b ∘ (e : Fin 4 → _) = d := funext hd
  rw [heq]

/-- The completed order consists of exactly the quaternions whose four coordinates
on the explicit basis belong to the local integers. -/
theorem completion_coeffs (ell : ℕ) (h : ell % 4 = 3) (x : Bp p (-1) (-(ell : ℚ))) :
    x ∈ (explicitOrderAt ell h).completion p ↔
      ∃ v : Fin 4 → ℤ_[p], x = (localCoords p (-(ell : ℚ))).symm (fun i => (v i : ℚ_[p])) := by
  let m : ℤ := (ell / 4 : ℕ) + 1
  have he : (ell : ℤ) = 4 * m - 1 := by dsimp [m]; omega
  have he' : (ell : ℚ) = 4 * (m : ℚ) - 1 := by exact_mod_cast he
  have hb : 1 - 4 * (m : ℚ) = -(ell : ℚ) := by linarith
  have hR : explicitOrderAt ell h =
      (congrArg (Order (-1)) hb.symm).mpr (explicitOrder m) := by
    unfold explicitOrderAt
    rfl
  rw [hR]
  have aux (b : ℚ) (hb : 1 - 4 * (m : ℚ) = b) (x : Bp p (-1) b) :
      x ∈ ((congrArg (Order (-1)) hb.symm).mpr (explicitOrder m)).completion p ↔
        ∃ v : Fin 4 → ℤ_[p], x = (localCoords p b).symm (fun i => (v i : ℚ_[p])) := by
    subst b
    change x ∈ ((explicitOrder m).completion p).toSubmodule ↔ _
    rw [completion_span]
    let e := localCoords p (1 - 4 * (m : ℚ))
    refine ((Module.Basis.ofEquivFun e).mem_span_iff_repr_mem ℤ_[p] x).trans ?_
    simp only [Module.Basis.ofEquivFun_repr_apply]
    constructor
    · intro hx
      choose v hv using hx
      refine ⟨v, (localCoords p _).injective ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact (funext hv).symm
    · rintro ⟨v, rfl⟩ i
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨v i, rfl⟩
  exact aux _ hb x

#print axioms completion_span
#print axioms completion_coeffs

end

end ZInQ.Manuscript.RC.ExplicitSplit
