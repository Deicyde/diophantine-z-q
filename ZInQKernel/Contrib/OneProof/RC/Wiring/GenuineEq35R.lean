import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35H
import ZInQKernel.Contrib.RC53Assist.OuterRealization.RetainedClass

/-!
**Theorem 5.3: the (3.5) leaf with outer model classes required only to be nonzero**

Proposition `ex:limits-uniform-lower-bound` (tex 4909–5202) at the ring instances of Proposition
`ex:sec7-genus-lower` (tex 2418–2446), in the text's quantifier order, with the size bound (5.1),
homology-level regularity data (`Eq35InputsGenuineABoundedH`, `GenuineEq35H.lean`) and outer
switching models in the text's form (model classes only nonzero).

**The departure of form removed (strength unchanged).** The outer conjunct of
`Eq35InputsGenuineABoundedH` asks for batch 3's
`GenuineOuterModels`, whose instance models (`SwitchInputs.InstanceModel`) carry `hprim`: the
selected outer model's class must be primitive. The text keeps the primitive kernel vector apart
from the actual class (tex 4939–4950): "In each generic one-dimensional kernel choose a primitive
vector `v_j`. Its outer image is nonzero, so the outer kernel dimension `s` is at least one. [...]
The actual inner class is a nonzero scalar multiple of `v_j`. Even if this scalar tends to zero,
its generic localization is nonzero on an outer-large set." `Eq35InputsGenuineABoundedR W` asks
instead for the outer models of the RC53 group's `RetainedOuterModels`
(`RC53Assist/OuterRealization/RetainedClass.lean`): every model carries a class required only to
be nonzero (tex 4928–4934), so the text's possibly divisible actual class is admitted, a closed
integral functional and the coordinate computed from them; the switch input is stated on these
data (`RetainedOuterSwitchData`). The data are existential: nothing ties them to the instance's
actual retained class, paired functional or complexes, and by `eq35InputsGenuineABoundedR_iff`
the leaf has the strength of the earlier form. The scalar
relating the actual class to the primitive vector is carried by the functional when the family is
realized (`RetainedInstanceModel.ofPrimitiveVector`: class `v`, functional `c₀ • lam`, the same
class-functional tensor and coordinate); the primitive vector itself is PROVED to exist (the RC53
group's `exists_primitiveKernelVector`, the saturation of `ker d`, tex 4987–4990).

**Scope of the data.** The structures record supplied matrices, classes, functionals and
complements. Their identification with the actual arithmetic instance and its retained class and
paired functional is OPEN (ELLIOT + GLUE). References below to actual data are conditional on that
identification. `IsGenuineTwoTermModel` concerns the matrix alone and supplies no class or
functional identification. Examples with `Gen := True` establish structural satisfiability only.

PROVED:
* **`eq35InputsGenuineABoundedR_iff`: `Eq35InputsGenuineABoundedR W ↔
  Eq35InputsGenuineABoundedH W`** — the two forms have the same strength (the RC53 group's
  `eq35OuterPart_iff` at `cap = eq51Cap ℓ A` for every `A`; realization `toGenuine` one way, the
  reading `ofGenuine` of an old family the other);
* `eq35Target_of_inputsAR` ((3.5) for each `A`), `eq55_of_inputsAR` ((5.5) for the coordinates
  `u_prim` chosen before `A`, directly from the retained model data through `eq55_of_retained`);
* the comparisons `Eq35InputsGenuineABoundedH.toR`, `Eq35InputsGenuineABoundedR.toH`,
  `Eq35InputsGenuineABounded.toR` (from the cochain-level leaf) and the degenerate satisfiability
  `eq35InputsGenuineABoundedR_of_not_prepared`.

Non-vacuity at the level of the structures (over `ℤ₂ ⊂ ℚ₂`): `eq35R_outerPart_divisible` (the
retained outer conjunct holds for a family whose model class `2` is divisible, which is the class
of no old instance model, `eq35R_divisible_not_instanceClass`) and `eq35R_outerPart_scaled` (it
holds for the family of model classes `2^j`, the scalar tending to zero as in tex 4949).

**What remains.** The retained family itself (the actual minimal models, the actual classes with
`z ≠ 0`, the actual paired functionals and complements; ELLIOT + GLUE, tex 4927–4953, 3864–3869),
the genuineness of the matrices (`IsGenuineTwoTermModel`: existential genuine Galois Selmer data,
not tied to the instance), the coordinate clause, and the switch input `RetainedOuterSwitchData`
(GLUE, tex 4940–4950), whose steps still carry an existential Selmer-level datum
`SelmerNonquadStep` with finite-dimensional cochain modules (`fG`, `fL`, `fF`, `fS`), not tied to
the genuine complexes. The regularity conjunct is that of `Eq35InputsGenuineABoundedH`
(homology-level switching data; existential configuration families and stage models).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)
open ZInQ.Contrib.RC53Assist.OuterRealization (RetainedOuterModels RetainedOuterSwitchData
  IsGenuineTwoTermModel eq35OuterPart_iff eq55_of_retained)

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with outer model classes required only to be nonzero** (Proposition
`ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of Proposition
`ex:sec7-genus-lower`, tex 2418–2446): `Eq35InputsGenuineABoundedH W` with its outer conjunct at
every `A` replaced by the outer conjunct on retained families — a label type `Pl` and a family
`T` of `RetainedOuterModels` over `𝒪` for the companion pairs with `ω(k') ≤ A` (model classes
only nonzero, not primitive, and closed integral functionals, existential and not tied to the
instance; tex 4927–4953, 4948–4950), of size at most the cap of (5.1) (tex 4453–4460,
4936–4938, 4954–4956), every model matrix a two-term model of genuine Galois Selmer data
(`IsGenuineTwoTermModel`; GLUE), the coordinates of the starting models with the valuations of
`ι_𝒪 u_prim` (tex 3877–3892), and the switch input `RetainedOuterSwitchData` on these data for
every sequence of instances (tex
4940–4950; GLUE). The data `u_prim`, `C₀`, the regularity (`RegularityInputsHPK`) and (4.6) are
chosen before `A`, as in `Eq35InputsGenuineABoundedH`. Kind: definition. -/
def Eq35InputsGenuineABoundedR : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsHPK (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst

/-- **The outer conjunct at `A` of the two forms** (the RC53 group's `eq35OuterPart_iff` at the cap
of (5.1), `cap = eq51Cap ℓ A`): the retained outer conjunct of `Eq35InputsGenuineABoundedR` is
equivalent to the outer conjunct of `Eq35InputsGenuineABoundedH` (and of
`Eq35InputsGenuineABounded`). Kind: PROVED. -/
theorem eq35R_outerPart_iff (A : ℕ) (uprim : ℤ → ℤ → FractionRing Lambda) :
    (∃ (Pl : Type) (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst) ↔
    ∃ (Pl : Type)
      (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, G.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : CompanionPair W A, vO (G.model i []).coordOf = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst :=
  eq35OuterPart_iff W A (eq51Cap ℓ A) uprim

/-- **The retained form gives the homology-level form** (realization of the retained outer models
at the primitive kernel vectors, the scalar moved into the functional). Kind: PROVED. -/
theorem Eq35InputsGenuineABoundedR.toH (hin : Eq35InputsGenuineABoundedR W) :
    Eq35InputsGenuineABoundedH W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, hreg, h46, fun A => (eq35R_outerPart_iff W A uprim).mp (hout A)⟩

/-- **The homology-level form gives the retained form** (every old outer family read as a retained
one: a primitive class is nonzero, the coordinate unchanged). Kind: PROVED. -/
theorem Eq35InputsGenuineABoundedH.toR (hin : Eq35InputsGenuineABoundedH W) :
    Eq35InputsGenuineABoundedR W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, hreg, h46, fun A => (eq35R_outerPart_iff W A uprim).mpr (hout A)⟩

/-- **The two forms have the same strength**: `Eq35InputsGenuineABoundedR W ↔
Eq35InputsGenuineABoundedH W`. Kind: PROVED. -/
theorem eq35InputsGenuineABoundedR_iff :
    Eq35InputsGenuineABoundedR W ↔ Eq35InputsGenuineABoundedH W :=
  ⟨Eq35InputsGenuineABoundedR.toH W, Eq35InputsGenuineABoundedH.toR W⟩

/-- **(3.5) for each fixed `A` from the retained form** (tex 2441–2446, 5200–5202), through the
homology-level form (`eq35Target_of_inputsAH`). Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsAR (hin : Eq35InputsGenuineABoundedR W) : Eq35Target W :=
  eq35Target_of_inputsAH W (Eq35InputsGenuineABoundedR.toH W hin)

/-- **(5.5) for the coordinates `u_prim`, directly from the retained form** (tex 4927–4972): for
each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion pair with `ω(k') ≤ A`, from the
retained model family and the switch input on these model data (the RC53 group's
`eq55_of_retained`). Kind: PROVED
from the inputs. -/
theorem eq55_of_inputsAR (hin : Eq35InputsGenuineABoundedR W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ, ∀ i : CompanionPair W A,
      (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, hout⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨Pl, T, -, -, hcoord, hsw⟩ := hout A
  exact eq55_of_retained uprim T hcoord hsw

/-- **The cochain-level leaf gives the retained form** (through `Eq35InputsGenuineABounded.toH`).
Kind: PROVED. -/
theorem Eq35InputsGenuineABounded.toR (hin : Eq35InputsGenuineABounded W) :
    Eq35InputsGenuineABoundedR W :=
  Eq35InputsGenuineABoundedH.toR W (Eq35InputsGenuineABounded.toH W hin)

/-- **`Eq35InputsGenuineABoundedR W` is satisfiable** in the degenerate case (no ring instances).
Kind: PROVED. -/
theorem eq35InputsGenuineABoundedR_of_not_prepared (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineABoundedR W :=
  Eq35InputsGenuineABoundedH.toR W (eq35InputsGenuineABoundedH_of_not_prepared W hW)

/-! ### Non-vacuity at the level of the structures -/

section NonVacuity

open Matrix
open ZInQ.Contrib.RC53Assist.OuterRealization (RetainedOuterPart GenuineOuterPart exRetained
  exRetainedModels exRetainedOuterPart exRetained_not_primitive exScaled outerKerDim
  padicInt_algebraMap_injective retainedOuterPart_iff)
open ZInQ.Manuscript.RC.Limits (OInf outerMatrix)

/-- PROVED. **The divisible actual class of the RC53 group's example is the class of no old
instance model** (tex 4948: "The actual inner class is a nonzero scalar multiple of `v_j`"): every
`SwitchInputs.InstanceModel` has a primitive class (`hprim`), while the actual class `2` of
`exRetained` is divisible by `2`. -/
theorem eq35R_divisible_not_instanceClass :
    ¬ ∃ X : SwitchInputs.InstanceModel (2 : ℤ_[2]) ℚ_[2] 0, X.zR = exRetained.z := by
  rintro ⟨X, hX⟩
  obtain ⟨i, hi⟩ := X.hprim
  rw [hX] at hi
  exact hi (dvd_refl _)

/-- PROVED. **The retained outer conjunct holds for a family whose actual classes are divisible**
(tex 4927–4953, 4948–4950; over `ℤ₂ ⊂ ℚ₂`, the RC53 group's constant family `exRetainedModels`
with actual class `2`, functional `1` and coordinate `2`): the retained form accepts the actual
class, which the old instance models cannot carry (`eq35R_divisible_not_instanceClass`); the
realization moves the scalar `2` into the functional (`exRealized_spec`); the old outer conjunct
holds for the realized data, so the example separates the model types, not the conjuncts
(`eq35R_outerPart_iff`). -/
theorem eq35R_outerPart_divisible :
    RetainedOuterPart (2 : ℤ_[2]) ℚ_[2] Unit (fun _ => 0) (fun _ => True)
        (Padic.addValuation (p := 2)) (fun _ => 2) ∧
      ∀ i l, ¬ ∃ i', ¬ (2 : ℤ_[2]) ∣ (exRetainedModels.model i l).z i' :=
  ⟨exRetainedOuterPart.1, fun _ _ => exRetained_not_primitive⟩

/-- Definition. **The family of actual classes `2^j`** (tex 4949: "Even if this scalar tends to
zero"): instances `j : ℕ`, no derivative-prime labels used, every configuration the RC53 group's
`exScaled j` (the model `[ℤ₂ --0--> ℤ₂]` with actual class `2^j` and functional `1`). -/
def eq35RScaledModels : RetainedOuterModels ℤ_[2] ℚ_[2] ℕ Unit where
  nOf _ := 0
  model j _ := exScaled j

/-- PROVED. The outer kernel dimension of the actual matrices of `eq35RScaledModels` is one (the
matrices are zero; tex 4940–4941). -/
theorem eq35RScaled_outerKerDim (𝒰 : Ultrafilter ℕ) (inst : ℕ → ℕ) (l : List Unit) :
    outerKerDim 𝒰 (2 : ℤ_[2]) (fun j => (eq35RScaledModels.model (inst j) l).M) = 1 := by
  have h0 : (outerMatrix 𝒰 (2 : ℤ_[2]) (fun j => (eq35RScaledModels.model (inst j) l).M)).map
      (algebraMap (OInf 𝒰 (2 : ℤ_[2])) (FractionRing (OInf 𝒰 (2 : ℤ_[2])))) = 0 := by
    ext a b
    simp only [eq35RScaledModels, exScaled, outerMatrix, Matrix.zero_apply]
    exact (algebraMap (OInf 𝒰 (2 : ℤ_[2])) (FractionRing (OInf 𝒰 (2 : ℤ_[2])))).map_zero
  unfold outerKerDim
  rw [h0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  rfl

/-- PROVED. **The retained outer conjunct holds for the family of actual classes `2^j`** (tex
4949–4950: the scalar relating the actual class to the primitive vector tends to zero along the
instances; outer kernel dimension one, so no switch is required), with the actual coordinates as
targets; hence so does the outer conjunct on old families (through `retainedOuterPart_iff`, which
realizes the family at the primitive vectors `1` with the functionals `2^j`). -/
theorem eq35R_outerPart_scaled :
    RetainedOuterPart (2 : ℤ_[2]) ℚ_[2] ℕ (fun _ => 0) (fun _ => True)
        (Padic.addValuation (p := 2)) (fun j => (exScaled j).coord) ∧
      GenuineOuterPart (2 : ℤ_[2]) ℚ_[2] ℕ (fun _ => 0) (fun _ => True)
        (Padic.addValuation (p := 2)) (fun j => (exScaled j).coord) := by
  have h : RetainedOuterPart (2 : ℤ_[2]) ℚ_[2] ℕ (fun _ => 0) (fun _ => True)
      (Padic.addValuation (p := 2)) (fun j => (exScaled j).coord) :=
    ⟨Unit, eq35RScaledModels, fun _ => le_rfl, fun _ _ => trivial, fun _ => rfl,
      fun inst => ⟨fun l hl => by
        rw [eq35RScaled_outerKerDim] at hl
        exact absurd hl (lt_irrefl 1)⟩⟩
  exact ⟨h, (retainedOuterPart_iff (2 : ℤ_[2]) ℚ_[2] padicInt_algebraMap_injective ℕ
    (fun _ => 0) (fun _ => True) (Padic.addValuation (p := 2)) (fun j => (exScaled j).coord)).mp h⟩

end NonVacuity

end ZInQ.Manuscript.RC.Wiring
