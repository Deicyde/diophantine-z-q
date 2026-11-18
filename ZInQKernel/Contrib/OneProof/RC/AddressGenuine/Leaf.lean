import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Assembly
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.OneProof.RC.Wiring.CompanionLeaf

/-!
# Theorem 5.3, Lane RC24: the address leaf over the genuine objects

The leaves `AddressPackageStagedLeaf W` and `AddressLeaf W` (lane RC0's `RC/Wiring/Address.lean`,
`RC/Wiring/FinalFamily.lean`) from the genuine label alphabets, prime realizations and readings of
`Assembly.lean`, in two forms:

* `addressLeaf_of_genuine`: the odd and even readings of App F (fixed-`U` factorization, (O.12)
  reading, primary isolation) as inputs over the genuine type data and readings;
* `addressLeaf_of_galois`: those readings PROVED from genuine Galois trace models
  (`GaloisModel.lean`: the group `G_ℚ = Aut(ℚ̄/ℚ)`, genuine Frobenius elements, the genuine type and
  bit characters, the subgroup `N_U` defined), one at every valid odd stage for every budget and
  one for the even source at every budget.

The companion leaf `CompanionLeaf W` (an existing leaf of lane RC0's `PostLeaves`) supplies that
`k` is odd and squarefree in Branch 2.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter Finset

/-! ## The leaf -/

/-- **Lane RC0's staged address leaf over the genuine objects** (PROVED): in Branch 2 the
companion leaf gives `k` odd and squarefree, and `addressPackageStaged_of_genuine` gives the
package at every coarse constant. -/
theorem addressPackageStagedLeaf_of_genuine {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hcomp : CompanionLeaf W) (hfresh : FreshPrime W D)
    (hodd : OddReadings W D) (hwit : OddWitness W D) (hofilt : OddFilter W D)
    (hprep : PreparedFilter W D) (hev : EvenReadings W D Rev) (hefilt : EvenFilter W D Rev)
    (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev) : AddressPackageStagedLeaf W := by
  intro A CE CR Cper Cdet _ _ _ _ hU
  obtain ⟨_, hsf, _, _, _, h4, _⟩ := hcomp hU
  have hk : Odd W.kfin := Int.odd_iff.mpr (by omega)
  exact addressPackageStaged_of_genuine W D Rev hℓ hk hsf hfresh hodd hwit hofilt hprep hev hefilt
    hseed hread _

/-- **The address leaf of the final family over the genuine objects** (PROVED, through lane RC0's
`addressLeaf_of_stagedPackage`). -/
theorem addressLeaf_of_genuine {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hcomp : CompanionLeaf W) (hfresh : FreshPrime W D)
    (hodd : OddReadings W D) (hwit : OddWitness W D) (hofilt : OddFilter W D)
    (hprep : PreparedFilter W D) (hev : EvenReadings W D Rev) (hefilt : EvenFilter W D Rev)
    (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev) : AddressLeaf W :=
  addressLeaf_of_stagedPackage W (addressPackageStagedLeaf_of_genuine W D Rev hℓ hcomp hfresh
    hodd hwit hofilt hprep hev hefilt hseed hread)


/-! ## The readings from genuine Galois trace models -/

section Galois

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Genuine Galois trace models of the odd stage source** (the model's ELLIOT/GLUE/PRINT fields:
lane RC12's trace identities on the reduced module, tex 9705–9745; Kummer, tex 9745–9750;
continuity, tex 9663–9669; Chebotarev for `G_ℚ/N_U`, tex 9666–9668, 9749–9750; the
coefficient-one reading, tex 9671–9704; (O.12), tex 9905–9918): for every cutoff, on a set of
stages of the ultrafilter (tex 10533–10540), a `GaloisTraceModel` of the genuine odd reading over
the genuine stage types and the genuine stage character. -/
def OddGaloisModels : Prop :=
  ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
    Nonempty (GaloisTraceModel (D.T₁ θ) (Rodd W θ) (apo ℓ) (Wc + 1) (stageChar D.m₁ (D.ℓ₀ θ)))

/-- **Genuine Galois trace models of the transported even source at every budget** (fields as in
`OddGaloisModels`; tex 9447–9976, 10288–10318). -/
def EvenGaloisModels : Prop :=
  ∀ B : ℕ, Nonempty (GaloisTraceModel D.T₂ Rev (apk W) B (typChar D.m₂))

/-- **The odd readings from the Galois models** (PROVED: `GaloisTraceModel.fixedU_of_model`,
`o12_of_model`, `primary_of_model`, with the stage character a type character,
`isTypeChar_stage`). -/
theorem oddReadings_of_galois (h : OddGaloisModels W D) : OddReadings W D := by
  intro Wc
  filter_upwards [h Wc] with θ hθ
  obtain ⟨X⟩ := hθ
  have hℓ₀2 : D.ℓ₀ θ ≠ 2 := ne_two_of_coprime_even (dvd_trans (by norm_num) D.four) (D.ℓ₀_cop θ)
  have htyp : IsTypeChar (D.T₁ θ) (stageChar D.m₁ (D.ℓ₀ θ)) :=
    isTypeChar_stage (D.T₁ θ) (D.T₁_m θ) (D.T₁_typ θ) (D.ℓ₀_prime θ) hℓ₀2
  exact ⟨X.fixedU_of_model htyp, X.o12_of_model htyp, X.primary_of_model htyp⟩

/-- **The even readings from the Galois models** (PROVED, as `oddReadings_of_galois`, with
`isTypeChar_typeData`). -/
theorem evenReadings_of_galois (h : EvenGaloisModels W D Rev) : EvenReadings W D Rev := by
  have htyp : IsTypeChar D.T₂ (typChar D.m₂) := isTypeChar_typeData D.m₂ D.m₂_pos D.four₂
  exact ⟨fun B => (h B).some.fixedU_of_model htyp, fun B => (h B).some.o12_of_model htyp,
    fun B => (h B).some.primary_of_model htyp⟩

/-- **The Galois-model inputs are satisfiable** (non-vacuity, PROVED from lane RC24's zero models
`galoisTraceModel_stage_nonempty'`, `galoisTraceModel_typeData_nonempty'`): for the zero readings,
genuine Galois trace models exist at every stage and budget. -/
theorem galoisModels_zero_nonempty (θ B : ℕ) :
    Nonempty (GaloisTraceModel (D.T₁ θ) (fun _ => 0) (apo ℓ) B (stageChar D.m₁ (D.ℓ₀ θ))) ∧
      Nonempty (GaloisTraceModel D.T₂ (fun _ => 0) (apk W) B (typChar D.m₂)) := by
  have hℓ₀2 : D.ℓ₀ θ ≠ 2 := ne_two_of_coprime_even (dvd_trans (by norm_num) D.four) (D.ℓ₀_cop θ)
  exact ⟨galoisTraceModel_nonempty (D.T₁ θ) (apo ℓ) B
      (isTypeChar_stage (D.T₁ θ) (D.T₁_m θ) (D.T₁_typ θ) (D.ℓ₀_prime θ) hℓ₀2),
    galoisTraceModel_nonempty D.T₂ (apk W) B
      (isTypeChar_typeData D.m₂ D.m₂_pos D.four₂)⟩

end Galois

/-- **The staged address leaf from genuine Galois trace models** (PROVED). -/
theorem addressPackageStagedLeaf_of_galois {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hcomp : CompanionLeaf W) (hfresh : FreshPrime W D)
    (hodd : OddGaloisModels W D) (hwit : OddWitness W D) (hofilt : OddFilter W D)
    (hprep : PreparedFilter W D) (hev : EvenGaloisModels W D Rev) (hefilt : EvenFilter W D Rev)
    (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev) : AddressPackageStagedLeaf W :=
  addressPackageStagedLeaf_of_genuine W D Rev hℓ hcomp hfresh (oddReadings_of_galois W D hodd)
    hwit hofilt hprep (evenReadings_of_galois W D Rev hev) hefilt hseed hread

/-- **The address leaf of the final family from genuine Galois trace models** (PROVED). -/
theorem addressLeaf_of_galois {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hcomp : CompanionLeaf W) (hfresh : FreshPrime W D)
    (hodd : OddGaloisModels W D) (hwit : OddWitness W D) (hofilt : OddFilter W D)
    (hprep : PreparedFilter W D) (hev : EvenGaloisModels W D Rev) (hefilt : EvenFilter W D Rev)
    (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev) : AddressLeaf W :=
  addressLeaf_of_stagedPackage W (addressPackageStagedLeaf_of_galois W D Rev hℓ hcomp hfresh hodd
    hwit hofilt hprep hev hefilt hseed hread)

/-! ## The leaf in one proposition, for `PostLeaves` -/

/-- **The genuine address leaf** (each conjunct with its tex lines and kind in its own docstring):
label data `D` (definition) and the even reading `Rev` of the transported source, with the fresh
ramification of `K` (ELLIOT), genuine Galois trace models of the odd stage source and of the even
source (App F; ELLIOT/GLUE/PRINT fields), the bounded-weight witness (ELLIOT), the odd, prepared
and even filters (definition), the `K`-split seed (ELLIOT, App G) and the even reading (ELLIOT/PRINT,
Waldspurger). It replaces `AddressPackageDictLeaf W` in `PostLeaves` (`addressLeaf_of_genuineLeaf`). -/
def AddressGenuineLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (D : LabelData W) (Rev : Finset ℕ → ZMod 2), FreshPrime W D ∧ OddGaloisModels W D ∧
    OddWitness W D ∧ OddFilter W D ∧ PreparedFilter W D ∧ EvenGaloisModels W D Rev ∧
    EvenFilter W D Rev ∧ KSplitSeed W D Rev ∧ EvenReading W D Rev

/-- **`AddressLeaf` from the genuine address leaf** (PROVED). -/
theorem addressLeaf_of_genuineLeaf {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ) (hcomp : CompanionLeaf W)
    (h : AddressGenuineLeaf W) : AddressLeaf W := by
  obtain ⟨D, Rev, hfresh, hodd, hwit, hofilt, hprep, hev, hefilt, hseed, hread⟩ := h
  exact addressLeaf_of_galois W D Rev hℓ hcomp hfresh hodd hwit hofilt hprep hev hefilt hseed hread

/-- **The staged leaf from the genuine address leaf** (PROVED). -/
theorem addressPackageStagedLeaf_of_genuineLeaf {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ)
    (hcomp : CompanionLeaf W) (h : AddressGenuineLeaf W) : AddressPackageStagedLeaf W := by
  obtain ⟨D, Rev, hfresh, hodd, hwit, hofilt, hprep, hev, hefilt, hseed, hread⟩ := h
  exact addressPackageStagedLeaf_of_galois W D Rev hℓ hcomp hfresh hodd hwit hofilt hprep hev
    hefilt hseed hread

end ZInQ.Manuscript.RC.AddressGenuine
