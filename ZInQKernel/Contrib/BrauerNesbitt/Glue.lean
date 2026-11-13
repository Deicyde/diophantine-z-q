/-
GLUE-03 bridge (`docs/h-targets/TASKS.md` §5 of the reference packet): the matrix form T19
implies the representation form `BrauerNesbittChar0` that the C10 glue consumes.

`brauerNesbittChar0_of_t19` takes the closed T19 body as a hypothesis and derives the closed
`PkgI6.BrauerNesbittChar0` body from it alone, by choosing bases. It does not use the project
proof of either statement, so it remains valid for any provider of T19. (Both statements are also
proved outright in `Representation.lean` and `Matrix.lean`; with those proofs this implication is
not needed, it records that the two encodings agree.)

Project proof for the pinned Lean 4.35.0 / Mathlib `v4.35.0` (2026-11-13).
-/
import ZInQKernel.Contrib.BrauerNesbitt.Matrix
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Dimension.Free

namespace ZInQ.Contrib.BrauerNesbitt

open Module

section Coordinates

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An intertwining `k`-linear equivalence is a `MonoidAlgebra k G`-linear equivalence of the
associated modules. -/
noncomputable def asModuleEquivOfIntertwining (ρ : Representation k G V)
    (σ : Representation k G W) (f : V ≃ₗ[k] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) :
    ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule :=
  LinearEquiv.ofLinearMap
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
      (f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ hf))
    (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
      (f.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap σ ρ fun g w =>
        f.injective (by simp [hf])))
    (LinearMap.ext fun w => f.apply_symm_apply w)
    (LinearMap.ext fun v => f.symm_apply_apply v)

/-- Matrices of endomorphisms in the coordinates `e`, as a monoid homomorphism. -/
noncomputable def coordHom {n : ℕ} (e : V ≃ₗ[k] (Fin n → k)) :
    Module.End k V →* Matrix (Fin n) (Fin n) k where
  toFun f := LinearMap.toMatrix' (e.conj f)
  map_one' := by rw [Module.End.one_eq_id, LinearEquiv.conj_id, LinearMap.toMatrix'_id]
  map_mul' f g := by rw [Module.End.mul_eq_comp, LinearEquiv.conj_comp, LinearMap.toMatrix'_comp]

/-- The matrix representation of `ρ` in the coordinates `e`. -/
noncomputable def toMatrixRep {n : ℕ} (e : V ≃ₗ[k] (Fin n → k)) (ρ : Representation k G V) :
    G →* GL (Fin n) k :=
  (Units.map (coordHom e)).comp ρ.asGroupHom

theorem toLin'_toMatrixRep {n : ℕ} (e : V ≃ₗ[k] (Fin n → k)) (ρ : Representation k G V)
    (g : G) : Matrix.toLin' (toMatrixRep e ρ g : Matrix (Fin n) (Fin n) k) = e.conj (ρ g) :=
  Matrix.toLin'_toMatrix' _

theorem trace_toMatrixRep {n : ℕ} (e : V ≃ₗ[k] (Fin n → k)) (ρ : Representation k G V)
    (g : G) : Matrix.trace (toMatrixRep e ρ g : Matrix (Fin n) (Fin n) k) =
      LinearMap.trace k V (ρ g) := by
  rw [← Matrix.trace_toLin'_eq, toLin'_toMatrixRep, LinearMap.trace_conj']

/-- `e` intertwines `ρ` with the linear representation of its matrix representation. -/
theorem symm_matrixRep_toMatrixRep {n : ℕ} (e : V ≃ₗ[k] (Fin n → k))
    (ρ : Representation k G V) (g : G) (x : Fin n → k) :
    e.symm (matrixRep (toMatrixRep e ρ) g x) = ρ g (e.symm x) := by
  rw [matrixRep_apply, toLin'_toMatrixRep, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply]

end Coordinates

section Semisimple

variable {G : Type*} [Group G] {E : Type*} [Field E] {n : ℕ}

/-- Converse of `isSemisimpleModule_matrixRep`: semisimplicity of the module gives invariant
complements of invariant subspaces, in exactly the T19 form. -/
theorem invariant_compl_of_isSemisimpleModule (ρ : G →* GL (Fin n) E)
    (h : IsSemisimpleModule (MonoidAlgebra E G) (matrixRep ρ).asModule) :
    ∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W' := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at h
  intro W hW
  let σ : Subrepresentation (matrixRep ρ) := ⟨W, fun g v hv => hW g ⟨v, hv, rfl⟩⟩
  obtain ⟨τ, hτ⟩ := exists_isCompl σ
  refine ⟨τ.toSubmodule, ⟨?_, ?_⟩, fun g =>
    Submodule.map_le_iff_le_comap.mpr fun v hv => τ.apply_mem_toSubmodule g hv⟩
  · rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule (disjoint_iff.mp hτ.disjoint)
  · rw [codisjoint_iff]
    exact congrArg Subrepresentation.toSubmodule (codisjoint_iff.mp hτ.codisjoint)

end Semisimple

/-- **GLUE-03.** The closed T19 body (as a hypothesis) implies the closed
`PkgI6.BrauerNesbittChar0` body. Equal traces at `1` give equal dimensions in characteristic
zero; bases turn both representations into matrix representations with the same traces and the
invariant-complement property; the conjugating matrix supplied by T19 becomes an intertwining
equivalence. -/
theorem brauerNesbittChar0_of_t19
    (h19 : ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
      (ρ₁ ρ₂ : G →* GL (Fin n) E),
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
        Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
      ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹) :
    ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W),
      IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
      IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
      (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) := by
  intro k G V W _ _ _ _ _ _ _ _ _ ρ σ hρ hσ htr
  have hdim : finrank k V = finrank k W := by
    have h1 := htr 1
    rw [ρ.map_one, σ.map_one, LinearMap.trace_one, LinearMap.trace_one] at h1
    exact_mod_cast h1
  obtain ⟨n, hn⟩ : ∃ n, finrank k V = n := ⟨_, rfl⟩
  let eV : V ≃ₗ[k] (Fin n → k) := (Module.finBasisOfFinrankEq k V hn).equivFun
  let eW : W ≃ₗ[k] (Fin n → k) := (Module.finBasisOfFinrankEq k W (hdim.symm.trans hn)).equivFun
  let ρ₁ := toMatrixRep eV ρ
  let ρ₂ := toMatrixRep eW σ
  have hss₁ : IsSemisimpleModule (MonoidAlgebra k G) (matrixRep ρ₁).asModule :=
    IsSemisimpleModule.congr (asModuleEquivOfIntertwining (matrixRep ρ₁) ρ eV.symm
      (symm_matrixRep_toMatrixRep eV ρ))
  have hss₂ : IsSemisimpleModule (MonoidAlgebra k G) (matrixRep ρ₂).asModule :=
    IsSemisimpleModule.congr (asModuleEquivOfIntertwining (matrixRep ρ₂) σ eW.symm
      (symm_matrixRep_toMatrixRep eW σ))
  obtain ⟨P, hP⟩ := h19 G k n ρ₁ ρ₂
    (invariant_compl_of_isSemisimpleModule ρ₁ hss₁)
    (invariant_compl_of_isSemisimpleModule ρ₂ hss₂)
    fun g => by rw [trace_toMatrixRep, trace_toMatrixRep, htr g]
  -- `P` intertwines the two matrix representations.
  have hconj : ∀ g, (ρ₂ g : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * (ρ₁ g : Matrix (Fin n) (Fin n) k) := by
    intro g
    rw [hP g, Units.val_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  let M : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (P : Matrix (Fin n) (Fin n) k))
      (Matrix.toLin' (↑P⁻¹ : Matrix (Fin n) (Fin n) k))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
  let f : V ≃ₗ[k] W := (eV.trans M).trans eW.symm
  have hf : ∀ g v, f (ρ g v) = σ g (f v) := by
    intro g v
    have h1 : eV (ρ g v) = Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) k) (eV v) := by
      rw [toLin'_toMatrixRep, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    have h2 : σ g (eW.symm (M (eV v))) =
        eW.symm (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) k) (M (eV v))) := by
      rw [toLin'_toMatrixRep, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    have h3 : M (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) k) (eV v)) =
        Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) k) (M (eV v)) := by
      change Matrix.toLin' (P : Matrix (Fin n) (Fin n) k)
          (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) k) (eV v)) =
        Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) k)
          (Matrix.toLin' (P : Matrix (Fin n) (Fin n) k) (eV v))
      rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hconj g]
    change eW.symm (M (eV (ρ g v))) = σ g (eW.symm (M (eV v)))
    rw [h1, h3, h2]
  exact ⟨asModuleEquivOfIntertwining ρ σ f hf⟩

end ZInQ.Contrib.BrauerNesbitt
