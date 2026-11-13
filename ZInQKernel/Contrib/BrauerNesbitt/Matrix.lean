/-
Brauer–Nesbitt in characteristic zero, matrix form: the exact closed statement of the proposed H
target T19 (reference packet of draft PR 41, head `2757349fbd8ca613340b679bbd149f78c2baba6b`,
`ZInQKernel/Targets/H/T19.lean`, file SHA-256
`e35ffa3140f8386d15ed0ba019553e0466df99b534db7cfe3a8a5b2ed797fb71`). That unregistered target
file is **not** imported; `t19` restates its body verbatim, so that a provider can later be
`T19_holds : T19 := t19` once the target is registered and reviewed.

Project proof for the pinned Lean 4.35.0 / Mathlib `v4.35.0` (2026-11-13). A matrix
representation `G →* GL (Fin n) E` is turned into a `Representation E G (Fin n → E)` through
`Matrix.toLin'`; the invariant-complement hypothesis is exactly complementedness of the lattice of
subrepresentations; the module form gives a `MonoidAlgebra E G`-linear equivalence, whose matrix
is the conjugating element of `GL (Fin n) E`. Nothing is assumed about `G`, `E` (beyond
characteristic zero) or `n`; `n = 0` is not a special case.
-/
import ZInQKernel.Contrib.BrauerNesbitt.Representation
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace ZInQ.Contrib.BrauerNesbitt

section MatrixRep

variable {G : Type*} [Group G] {E : Type*} [Field E] {n : ℕ}

/-- The linear representation on `Fin n → E` of a matrix representation. -/
noncomputable def matrixRep (ρ : G →* GL (Fin n) E) : Representation E G (Fin n → E) where
  toFun g := Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)
  map_one' := by rw [map_one, Units.val_one, Matrix.toLin'_one, Module.End.one_eq_id]
  map_mul' g h := by rw [map_mul, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem matrixRep_apply (ρ : G →* GL (Fin n) E) (g : G) :
    matrixRep ρ g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E) :=
  rfl

theorem trace_matrixRep (ρ : G →* GL (Fin n) E) (g : G) :
    LinearMap.trace E (Fin n → E) (matrixRep ρ g) = Matrix.trace (ρ g : Matrix (Fin n) (Fin n) E) :=
  Matrix.trace_toLin'_eq _

/-- The T19 semisimplicity hypothesis (every invariant subspace has an invariant complement)
makes the `MonoidAlgebra` module of `matrixRep ρ` semisimple. -/
theorem isSemisimpleModule_matrixRep (ρ : G →* GL (Fin n) E)
    (hρ : ∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) E)) ≤ W') :
    IsSemisimpleModule (MonoidAlgebra E G) (matrixRep ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun σ => ?_⟩
  obtain ⟨W', hcompl, hW'⟩ := hρ σ.toSubmodule fun g =>
    Submodule.map_le_iff_le_comap.mpr fun v hv => σ.apply_mem_toSubmodule g hv
  let τ : Subrepresentation (matrixRep ρ) := ⟨W', fun g v hv => hW' g ⟨v, hv, rfl⟩⟩
  refine ⟨τ, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hcompl.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hcompl.sup_eq_top

/-- A `MonoidAlgebra`-linear equivalence between the modules of two matrix representations
yields one invertible matrix conjugating the first representation into the second. -/
theorem exists_conj_of_linearEquiv (ρ₁ ρ₂ : G →* GL (Fin n) E)
    (e : (matrixRep ρ₁).asModule ≃ₗ[MonoidAlgebra E G] (matrixRep ρ₂).asModule) :
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹ := by
  let f : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    ((matrixRep ρ₁).asModuleEquiv.symm.trans (e.restrictScalars E)).trans
      (matrixRep ρ₂).asModuleEquiv
  have hf : ∀ (g : G) (v : Fin n → E), f (matrixRep ρ₁ g v) = matrixRep ρ₂ g (f v) := by
    intro g v
    have h1 := e.map_smul (MonoidAlgebra.single g (1 : E)) ((matrixRep ρ₁).asModuleEquiv.symm v)
    rw [Representation.single_smul, Representation.single_smul, one_smul, one_smul] at h1
    exact h1
  have hinv₁ : LinearMap.toMatrix' (f : (Fin n → E) →ₗ[E] (Fin n → E)) *
      LinearMap.toMatrix' (f.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => f.apply_symm_apply v
  have hinv₂ : LinearMap.toMatrix' (f.symm : (Fin n → E) →ₗ[E] (Fin n → E)) *
      LinearMap.toMatrix' (f : (Fin n → E) →ₗ[E] (Fin n → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => f.symm_apply_apply v
  refine ⟨⟨_, _, hinv₁, hinv₂⟩, fun g => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Units.inv_mk, Units.val_mk, Units.val_mk]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    ← matrixRep_apply, ← matrixRep_apply, hf, f.apply_symm_apply]

end MatrixRep

/-- The matrix form follows from the representation form: the closed `PkgI6.BrauerNesbittChar0`
body (restated verbatim, as a hypothesis) implies the closed T19 body. Only its instance at
`V = W = Fin n → E` is used. -/
theorem t19_of_brauerNesbittChar0
    (hBN : ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W),
      IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
      IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
      (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)) :
    ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
      (ρ₁ ρ₂ : G →* GL (Fin n) E),
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
        Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
      ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹ := by
  intro G _ E _ _ n ρ₁ ρ₂ h₁ h₂ htr
  obtain ⟨e⟩ := hBN E G (Fin n → E) (Fin n → E) (matrixRep ρ₁) (matrixRep ρ₂)
    (isSemisimpleModule_matrixRep ρ₁ h₁) (isSemisimpleModule_matrixRep ρ₂ h₂)
    fun g => by rw [trace_matrixRep, trace_matrixRep, htr g]
  exact exists_conj_of_linearEquiv ρ₁ ρ₂ e

/-- **The exact closed body of the proposed target `ZInQ.Targets.H.T19`** (Brauer–Nesbitt,
characteristic zero, trace form), copied verbatim from the reference packet. -/
theorem t19 :
    ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
      (ρ₁ ρ₂ : G →* GL (Fin n) E),
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ W : Submodule E (Fin n → E),
        (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
        ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
      (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
        Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
      ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹ :=
  t19_of_brauerNesbittChar0 brauerNesbittChar0

end ZInQ.Contrib.BrauerNesbitt
