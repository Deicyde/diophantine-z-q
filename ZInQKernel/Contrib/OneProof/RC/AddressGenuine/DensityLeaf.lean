import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Leaf
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev

/-!
# Theorem 5.3, Lane RC24: the address leaf with Chebotarev from the density theorem

The genuine address leaf of `Leaf.lean` with the Galois trace models replaced by the density models
of `Chebotarev.lean`: the PRINT field `chebotarev` and the GLUE field `finiteIndex` of
`GaloisTraceModel` are replaced by the openness (a) and the unramifiedness (b) of `N_U` (GLUE,
tex 9524–9548, 9663–9669), and Chebotarev's theorem is the repository's PROVED density theorem
(`ZInQ.Contrib.ChebFD.C10.frobDense`, `ZInQ.Contrib.chebotarevExists`; tex 9666–9668, 9749–9750).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter

section Density

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Density models of the odd stage source** (the fields of `GaloisDensityModel`: ELLIOT trace
identities and readings, tex 9671–9745, 9905–9918; GLUE Kummer, openness, unramifiedness,
tex 9524–9548, 9663–9669, 9745–9750): for every cutoff, on a set of stages of the ultrafilter. -/
def OddDensityModels : Prop :=
  ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
    Nonempty (GaloisDensityModel (D.T₁ θ) (Rodd W θ) (apo ℓ) (Wc + 1) (stageChar D.m₁ (D.ℓ₀ θ)))

/-- **Density models of the transported even source at every budget** (tex 10288–10318). -/
def EvenDensityModels : Prop :=
  ∀ B : ℕ, Nonempty (GaloisDensityModel D.T₂ Rev (apk W) B (typChar D.m₂))

/-- **Galois trace models from density models** (PROVED: `GaloisDensityModel.toGaloisTraceModel`,
with `chebotarev` from the density theorem). -/
theorem oddGaloisModels_of_density (h : OddDensityModels W D) : OddGaloisModels W D :=
  fun Wc => (h Wc).mono fun _ ⟨X⟩ => ⟨X.toGaloisTraceModel⟩

/-- **Galois trace models of the even source from density models** (PROVED). -/
theorem evenGaloisModels_of_density (h : EvenDensityModels W D Rev) : EvenGaloisModels W D Rev :=
  fun B => match h B with | ⟨X⟩ => ⟨X.toGaloisTraceModel⟩

end Density

/-- **The genuine address leaf with Chebotarev from the density theorem** (as `AddressGenuineLeaf`,
with density models). -/
def AddressDensityLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (D : LabelData W) (Rev : Finset ℕ → ZMod 2), FreshPrime W D ∧ OddDensityModels W D ∧
    OddWitness W D ∧ OddFilter W D ∧ PreparedFilter W D ∧ EvenDensityModels W D Rev ∧
    EvenFilter W D Rev ∧ KSplitSeed W D Rev ∧ EvenReading W D Rev

/-- **The genuine address leaf from the density form** (PROVED). -/
theorem addressGenuineLeaf_of_densityLeaf {ℓ : ℕ} {W : WData ℓ} (h : AddressDensityLeaf W) :
    AddressGenuineLeaf W := by
  obtain ⟨D, Rev, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨D, Rev, h1, oddGaloisModels_of_density W D h2, h3, h4, h5,
    evenGaloisModels_of_density W D Rev h6, h7, h8, h9⟩

/-- **`AddressLeaf` from the density form** (PROVED). -/
theorem addressLeaf_of_densityLeaf {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ) (hcomp : CompanionLeaf W)
    (h : AddressDensityLeaf W) : AddressLeaf W :=
  addressLeaf_of_genuineLeaf hℓ hcomp (addressGenuineLeaf_of_densityLeaf h)

end ZInQ.Manuscript.RC.AddressGenuine
