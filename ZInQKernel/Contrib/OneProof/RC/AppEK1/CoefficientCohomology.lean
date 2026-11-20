import ZInQKernel.Contrib.OneProof.RC.AppEK1.Coefficients
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CoefModule

/-!
# The coefficient map on continuous cohomology

This map concerns the tensor representation at one level, on the ambient Galois
group or on any group with the displayed action. It can be applied after inverse
Shapiro once the induced module is identified with this tensor representation.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppEK1

open CoefModules SelmerComplex
open scoped TensorProduct

section Change

variable {G A B T : Type} [Group G] [CommRing A] [CommRing B]
  [AddCommGroup T] [DistribMulAction G T]

/-- Transport a unit-valued action along the coefficient ring map. -/
def mapAction (f : A →+* B) (α : G →* Aˣ) : G →* Bˣ :=
  (Units.map f.toMonoidHom).comp α

/-- Tensor change of coefficients on the same underlying representation. -/
def tensorCoeffMap (f : A →+* B) (α : G →* Aˣ) :
    CoefMod A α T →ₗ[ℤ] CoefMod B (mapAction f α) T :=
  TensorProduct.map f.toAddMonoidHom.toIntLinearMap LinearMap.id

omit [DistribMulAction G T] in
/-- The underlying action on pure tensors. -/
theorem tensorCoeffMap_tmul (f : A →+* B) (α : G →* Aˣ) (a : A) (t : T) :
    tensorCoeffMap f α (CoefMod.equiv A α T (a ⊗ₜ t)) =
      CoefMod.equiv B (mapAction f α) T (f a ⊗ₜ t) := by
  exact TensorProduct.map_tmul _ _ _ _

/-- Change of coefficients is equivariant for the transported action. -/
theorem tensorCoeffMap_smul (f : A →+* B) (α : G →* Aˣ) (g : G) (z : CoefMod A α T) :
    tensorCoeffMap f α (g • z) = g • tensorCoeffMap f α z := by
  refine TensorProduct.inductionOn (motive := fun v : A ⊗[ℤ] T =>
    tensorCoeffMap f α (g • (show CoefMod A α T from v)) =
      g • tensorCoeffMap f α (show CoefMod A α T from v)) (show A ⊗[ℤ] T from z) ?_ ?_
  · intro a t
    change tensorCoeffMap f α (g • CoefMod.equiv A α T (a ⊗ₜ t)) =
      g • tensorCoeffMap f α (CoefMod.equiv A α T (a ⊗ₜ t))
    rw [CoefMod.smul_tmul, tensorCoeffMap_tmul, tensorCoeffMap_tmul, CoefMod.smul_tmul, map_mul]
    rfl
  · intro a b ha hb
    let a' : CoefMod A α T := a
    let b' : CoefMod A α T := b
    change tensorCoeffMap f α (g • (a' + b')) = g • tensorCoeffMap f α (a' + b')
    rw [smul_add, map_add, map_add, smul_add, ha, hb]

variable [TopologicalSpace G] [IsTopologicalGroup G] [HasOpenStabilizers G T]

instance mapAction_isOpenKer (f : A →+* B) (α : G →* Aˣ) [IsOpenKer α] :
    IsOpenKer (mapAction f α) :=
  ⟨Subgroup.isOpen_mono (H₁ := α.ker) (fun g hg => by
      have := MonoidHom.mem_ker.mp hg
      exact MonoidHom.mem_ker.mpr (by simp [mapAction, this]))
    (IsOpenKer.isOpen_ker (α := α))⟩

/-- The actual map on continuous cohomology given by changing tensor coefficients.
For (K10) the ring homomorphism is `familyMap`, and the action formula is
`weightedMap_invDeck`. -/
abbrev tensorCoeffH1 (f : A →+* B) (α : G →* Aˣ) [IsOpenKer α] :=
  contCohomologyMap (ContinuousMonoidHom.id G) (tensorCoeffMap (T := T) f α)
    continuous_of_discreteTopology (tensorCoeffMap_smul f α) 1

end Change

section Deck

variable {R A B G : Type} [CommRing R] [CommGroup A] [CommGroup B] [Group G]

/-- The action on group coefficients before applying the character and deck quotient. -/
def inverseDeck (q : G →* A) : G →* (MonoidAlgebra R A)ˣ :=
  ((MonoidAlgebra.of R A).comp q⁻¹).toHomUnits

/-- The action obtained by pushing inverse deck action through the quadratic
coefficient map is exactly multiplication by the quadratic weight and the
inverse image of the deck element. -/
theorem mapAction_weightedMap_invDeck (q : G →* A) (b : A →* B) (χ : A →* Rˣ)
    (hχ : ∀ a, χ a * χ a = 1) (g : G) :
    ((mapAction (weightedMap b χ).toRingHom (inverseDeck q) g : (MonoidAlgebra R B)ˣ) :
        MonoidAlgebra R B) =
      MonoidAlgebra.single (b (q g))⁻¹ (χ (q g) : R) := by
  change weightedMap b χ (MonoidAlgebra.single (q g)⁻¹ 1) = _
  simpa only [mul_one, map_one] using
    (weightedMap_invDeck b χ hχ (q g) (1 : MonoidAlgebra R A))

end Deck

end ZInQ.Manuscript.RC.AppEK1
