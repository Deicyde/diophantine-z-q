import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPad
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHExample

/-!
**Theorem 5.3: non-vacuity of the homology-level switching data over infinite-dimensional fibres**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195 (the nonquadratic switch, tex 4997–5003; the exact sequences
(5.5a), tex 5055–5086; the localization duality, tex 5068–5075).

The previous leaves' switching data `GenuineSwitchDataPK` demand, at the source of every switch,
finite-dimensional global 1-cochains of the configuration's fibre (`fG`); over the genuine
continuous-cochain fibres no switch can be formed. This file exhibits a configuration family over
which:

* every fibre has INFINITE-dimensional global 1-cochains (`hnvFamily_fibre_infinite`), so the
  configuration's Selmer complex is infinite-dimensional in degree one
  (`hnv_model_source_infinite`), and the switch model at the actual configuration is a genuine
  homotopy equivalence from it to the finite two-term fibre, not an isomorphism of complexes
  (`hnv_model_not_iso`);
* a `HomologySwitchDataPK` exists (`hnvData`), whose actual configuration (fibre dimension three)
  DEMANDS a switch and has one, through a homology-level step whose sides are the fibres
  (`hnvData_fiberDim_actual`);
* NO `GenuineSwitchDataPK` exists, for any coordinate (`hnv_old_empty`).

Construction: lane RC29's finite example `swxFamily`, `swxData` (`GenuineSwitchHExample.lean`: a
nonquadratic family over `ℚ` with a demanded switch `3 → 1`) padded by the contractible complex with
terms `V × V`, `V = ℕ →₀ ℚ` (`hpadFamily`, `HomologySwitchDataPK.hpad`,
`GenuineSwitchHPad.lean`). Padding by a contractible summand changes no cohomology, so the
homology-level structure cannot tell a fibre from its padding, while the old structure's `fG`
can: this is the evidence, in the sense of the non-vacuity requirement for new structures, that
the homology-level structure removes the cochain-finiteness obstruction.

Scope: a structure-level example over `A = F = k = ℚ` (`ℚ` is not a DVR, the fibres are not genuine
Galois fibres). A leaf-level witness of `RegularityInputsHPK u` with `u ≠ 0` needs a genuine Galois
Selmer complex over a residue field `k(𝔭)` with nonzero `H¹`, which is not in the tree (as for the
previous leaves, `GenuineSwitchPKNonVacuity.lean`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- Definition. **The padded example family**: `swxFamily` with every fibre padded by the
contractible complex with terms `(ℕ →₀ ℚ)²`. -/
abbrev hnvFamily : SwitchFamily ℚ ℚ := hpadFamily swxFamily (ℕ →₀ ℚ)

/-- Definition. **The homology-level switching datum over the padded family** (`swxData` padded;
stages, signs and the switch transported, models composed with the padding homotopy
equivalence). -/
def hnvData : HomologySwitchDataPK hnvFamily (RingHom.id ℚ) (RingHom.id ℚ) swxUF :=
  swxData.hpad swxFamily_not_quadratic (ℕ →₀ ℚ)

/-- PROVED. The actual configuration of the padded datum has fibre dimension three, so its switch
field is exercised (`1 < 3`). -/
theorem hnvData_fiberDim_actual :
    (hnvData.stage hnvFamily.actual).fiberDim (RingHom.id ℚ) = 3 :=
  swxData_fiberDim_actual

/-- PROVED. Every fibre of the padded family has infinite-dimensional global 1-cochains. -/
theorem hnvFamily_fibre_infinite (c : hnvFamily.Config) :
    ¬ FiniteDimensional ℚ ((hnvFamily.fibre c).G.X 1) :=
  hpadFamily_not_finiteDimensional swxFamily (ℕ →₀ ℚ) (hpadInf ℚ) c

/-- PROVED. **No datum of the previous form exists over the padded family**, for any coordinate:
its switch at the actual configuration (fibre dimension three) would force finite-dimensional
global 1-cochains. -/
theorem hnv_old_empty (u' : ℚ) :
    IsEmpty (GenuineSwitchDataPK hnvFamily (RingHom.id ℚ) (RingHom.id ℚ) u') :=
  hpad_isEmpty_genuinePK swxData (by rw [swxData_fiberDim_actual]; norm_num) (ℕ →₀ ℚ)
    (hpadInf ℚ) u'

/-- PROVED. **The separation**: over the padded family the homology-level data exist, the data of
the previous form do not, and every fibre has infinite-dimensional global 1-cochains. -/
theorem hnv_separates :
    Nonempty (HomologySwitchDataPK hnvFamily (RingHom.id ℚ) (RingHom.id ℚ) swxUF) ∧
      IsEmpty (GenuineSwitchDataPK hnvFamily (RingHom.id ℚ) (RingHom.id ℚ) swxUF) ∧
      ∀ c, ¬ FiniteDimensional ℚ ((hnvFamily.fibre c).G.X 1) :=
  ⟨⟨hnvData⟩, hnv_old_empty swxUF, hnvFamily_fibre_infinite⟩

/-- PROVED. The Selmer complex of the actual configuration of the padded family is
infinite-dimensional in degree one (its global part is a direct factor). -/
theorem hnv_model_source_infinite :
    ¬ FiniteDimensional ℚ ((selCx (hnvFamily.fibre hnvFamily.actual)).toCC.X 1) := by
  intro h
  have h' : FiniteDimensional ℚ ((hnvFamily.fibre hnvFamily.actual).G.X 1 ×
      (hnvFamily.fibre hnvFamily.actual).U.X 1 × (hnvFamily.fibre hnvFamily.actual).L.X (1 - 1)) :=
    h
  exact hnvFamily_fibre_infinite hnvFamily.actual
    (Module.Finite.of_surjective (LinearMap.fst ℚ ((hnvFamily.fibre hnvFamily.actual).G.X 1)
      ((hnvFamily.fibre hnvFamily.actual).U.X 1 × (hnvFamily.fibre hnvFamily.actual).L.X (1 - 1)))
      LinearMap.fst_surjective)

/-- PROVED. **The switch model at the actual configuration is a genuine homotopy equivalence**: the
Selmer complex of the actual fibre and the finite two-term fibre of its stage are homotopy
equivalent (`hnvData.model`) but not isomorphic as complexes (the source is infinite-dimensional in
degree one, the target finite). -/
theorem hnv_model_not_iso :
    IsEmpty ((selCx (hnvFamily.fibre hnvFamily.actual)).toCC ≅
      twoTermFiberComplex (RingHom.id ℚ) (hnvData.stage hnvFamily.actual)) := by
  refine ⟨fun e => hnv_model_source_infinite ?_⟩
  have e1 : ((selCx (hnvFamily.fibre hnvFamily.actual)).toCC.X 1) ≃ₗ[ℚ]
      ((twoTermFiberComplex (RingHom.id ℚ) (hnvData.stage hnvFamily.actual)).X 1) :=
    ((HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.up ℤ) 1).mapIso e).toLinearEquiv
  have : FiniteDimensional ℚ ((twoTermFiberComplex (RingHom.id ℚ)
      (hnvData.stage hnvFamily.actual)).X 1) :=
    inferInstanceAs (FiniteDimensional ℚ (Fin ((hnvData.stage hnvFamily.actual).n + 1) → ℚ))
  exact LinearEquiv.finiteDimensional e1.symm

end ZInQ.Manuscript.RC.Wiring
