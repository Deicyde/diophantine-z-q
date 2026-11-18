import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Leaf
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents

/-!
# Theorem 5.3, Lane RC24: the address leaf from constituent models over `G_ℚ`

The finest form of the genuine address leaf: the Galois trace models of `Leaf.lean` are built
from constituent models (`Constituents.lean`: the two-dimensional Galois representations of the
constituents of `F_U = θ H_U` on the characteristic-zero space, the integral trace module `Λ` and
its reduction modulo `𝔪`; App F, tex 9638–9797), one at every valid odd stage for every budget
and one for the transported even source at every budget.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter

section Constituents

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Constituent models of the odd stage source** (App F, tex 9638–9797, 9905–9918; the fields'
kinds as in `GaloisConstituentModel`): for every cutoff, on a set of stages of the ultrafilter, a
constituent model over `G_ℚ` of the genuine odd reading with its ELLIOT inputs. -/
def OddConstituentModels : Prop :=
  ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
    ∃ X : GaloisConstituentModel (D.T₁ θ) (Rodd W θ) (apo ℓ) (Wc + 1) (stageChar D.m₁ (D.ℓ₀ θ)),
      X.Inputs

/-- **Constituent models of the transported even source at every budget** (as
`OddConstituentModels`; tex 10288–10318). -/
def EvenConstituentModels : Prop :=
  ∀ B : ℕ, ∃ X : GaloisConstituentModel D.T₂ Rev (apk W) B (typChar D.m₂), X.Inputs

/-- **Galois trace models from constituent models** (PROVED:
`GaloisConstituentModel.toGaloisTraceModel`). -/
theorem oddGaloisModels_of_constituents (h : OddConstituentModels W D) : OddGaloisModels W D :=
  fun Wc => (h Wc).mono fun _ ⟨X, hX⟩ => ⟨X.toGaloisTraceModel hX⟩

/-- **Galois trace models of the even source from constituent models** (PROVED). -/
theorem evenGaloisModels_of_constituents (h : EvenConstituentModels W D Rev) :
    EvenGaloisModels W D Rev :=
  fun B => match h B with | ⟨X, hX⟩ => ⟨X.toGaloisTraceModel hX⟩

end Constituents

/-- **The genuine address leaf with constituent models** (as `AddressGenuineLeaf`, with the
Galois trace models built from constituent models). -/
def AddressConstituentLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (D : LabelData W) (Rev : Finset ℕ → ZMod 2), FreshPrime W D ∧ OddConstituentModels W D ∧
    OddWitness W D ∧ OddFilter W D ∧ PreparedFilter W D ∧ EvenConstituentModels W D Rev ∧
    EvenFilter W D Rev ∧ KSplitSeed W D Rev ∧ EvenReading W D Rev

/-- **The genuine address leaf from the constituent form** (PROVED). -/
theorem addressGenuineLeaf_of_constituentLeaf {ℓ : ℕ} {W : WData ℓ}
    (h : AddressConstituentLeaf W) : AddressGenuineLeaf W := by
  obtain ⟨D, Rev, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨D, Rev, h1, oddGaloisModels_of_constituents W D h2, h3, h4, h5,
    evenGaloisModels_of_constituents W D Rev h6, h7, h8, h9⟩

/-- **`AddressLeaf` from the constituent form** (PROVED). -/
theorem addressLeaf_of_constituentLeaf {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ)
    (hcomp : CompanionLeaf W) (h : AddressConstituentLeaf W) : AddressLeaf W :=
  addressLeaf_of_genuineLeaf hℓ hcomp (addressGenuineLeaf_of_constituentLeaf h)

end ZInQ.Manuscript.RC.AddressGenuine
