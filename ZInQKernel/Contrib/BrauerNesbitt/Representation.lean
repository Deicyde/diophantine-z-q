/-
Brauer–Nesbitt in characteristic zero for representations of an arbitrary group, in the exact
form of the baseline leaf `PkgI6.BrauerNesbittChar0`
(`ZInQKernel/HDecomp/Conductor/I6Base.lean`). That module is not imported here; the bridge to the
baseline names is `ZInQKernel.Contrib.BrauerNesbitt.Bridge`.

Project proof for the pinned Lean 4.35.0 / Mathlib `v4.35.0` (2026-11-13). It applies the module
form `nonempty_linearEquiv_of_character_eq` with `A = MonoidAlgebra k G`; equality of traces on
group elements extends `k`-linearly to every element of the monoid algebra.
-/
import ZInQKernel.Contrib.BrauerNesbitt.Basic
import Mathlib.RepresentationTheory.Basic

namespace ZInQ.Contrib.BrauerNesbitt

section Representation

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The character of `ρ.asModule` at `a` is the trace of `ρ.asAlgebraHom a`. -/
theorem character_asModule (ρ : Representation k G V) (a : MonoidAlgebra k G) :
    character k ρ.asModule a = LinearMap.trace k V (ρ.asAlgebraHom a) := by
  rw [character_def, ← LinearMap.trace_conj' _ ρ.asModuleEquiv]
  congr 1

/-- Equal traces on group elements give equal characters on the whole monoid algebra. -/
theorem character_asModule_eq (ρ : Representation k G V) (σ : Representation k G W)
    (h : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g))
    (a : MonoidAlgebra k G) : character k ρ.asModule a = character k σ.asModule a := by
  rw [character_asModule, character_asModule]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | single g c => rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single,
      map_smul, map_smul, h g]

/-- **Brauer–Nesbitt, characteristic zero, representation form**, universe-polymorphic and for
any monoid `G`: two finite-dimensional representations over a field of characteristic zero whose
`MonoidAlgebra` modules are semisimple and whose traces agree at every element of `G` are
isomorphic. -/
theorem nonempty_asModule_linearEquiv_of_trace_eq [CharZero k] [FiniteDimensional k V]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k G) σ.asModule)
    (h : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :=
  nonempty_linearEquiv_of_character_eq ρ.asModule σ.asModule (character_asModule_eq ρ σ h)

end Representation

/-- **The exact closed `PkgI6.BrauerNesbittChar0` body**, copied verbatim from
`ZInQKernel/HDecomp/Conductor/I6Base.lean` (main `a5937595cde3e3db00975b81e5171cdef92c801a`).
The group is arbitrary (not assumed finite), and the field need not be algebraically closed. -/
theorem brauerNesbittChar0 :
    ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W),
      IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
      IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
      (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) := by
  intro k G V W _ _ _ _ _ _ _ _ _ ρ σ hρ hσ h
  exact nonempty_asModule_linearEquiv_of_trace_eq ρ σ hρ hσ h

end ZInQ.Contrib.BrauerNesbitt
