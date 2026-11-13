/-
# Abelian Galois transport on the actual completed-field model

Commutativity is transported by the proved canonical decomposition-field group
surjection. Completed Galoisness is the separately proved global splitting-field
argument. The native Mathlib IsAbelianGalois class is constructed from those
actual results; no new local-model default or Kronecker-Weber premise is added.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.CompletedDecomposition
public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Native completed abelian-Galois field interfaces

All outputs use the existing canonical completionAlgebra and scalar towers on
`v.adicCompletion Q` and `w.adicCompletion L`. The scoped exports are additive;
no nongalois source or existing contributor/provider is changed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField GlobalDifferentTransportCompletion IsMulCommutative

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The actual completed-field Galois group is commutative if the original global group is
commutative. This consumes the genuine action and its surjectivity, not an order comparison. -/
theorem isMulCommutative_numberFieldCompletion [Normal ℚ L] [IsMulCommutative Gal(L/ℚ)] :
    IsMulCommutative (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) := by
  apply IsMulCommutative.of_comm
  intro σ τ
  obtain ⟨σ, rfl⟩ := decompositionFieldHom_surjective L v w σ
  obtain ⟨τ, rfl⟩ := decompositionFieldHom_surjective L v w τ
  rw [← map_mul, ← map_mul, mul_comm]

/-- Native IsAbelianGalois on the actual completed extension, derived from global abelian
Galoisness and the proved canonical completed field interfaces. -/
theorem isAbelianGalois_numberFieldCompletion [IsAbelianGalois ℚ L] :
    IsAbelianGalois (v.adicCompletion ℚ) (w.adicCompletion L) := by
  let := isGalois_numberFieldCompletion L v w
  let := isMulCommutative_numberFieldCompletion L v w
  exact { }

scoped[GlobalDifferentTransportCompletedGalois] attribute [instance]
  GlobalDifferentTransport.isGalois_numberFieldCompletion
  GlobalDifferentTransport.isMulCommutative_numberFieldCompletion
  GlobalDifferentTransport.isAbelianGalois_numberFieldCompletion

end GlobalDifferentTransport
