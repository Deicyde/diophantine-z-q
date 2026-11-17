import Mathlib

/-!
# Lane RC6 (limits): the homological perturbation step of Lemma `ex:limits-inner-limit`

This file formalizes manuscript lines 4408-4442 (proof of Lemma `ex:limits-inner-limit`):
the normalized contraction of the split residual complex (tex 4416-4427), the perturbation
formulas (tex 4428-4436), the identities `p i = 1` and `1 - i p = d h + h d` (tex 4437), and the
transport `f ↦ p' f i` of maps, homotopies and second homotopies (tex 4438-4442).
Everything in this file is `PROVED`.

## Conventions and departures

* DEPARTURE (total module). Elliot works with a bounded complex of free `A`-modules. Here `M` is
  the total module (all degrees summed) and `d₀, ε, h₀` are `A`-linear endomorphisms of `M`; the
  perturbation identities do not involve degrees. Degrees are tracked separately, in the
  optional section `Graded` (perturbed maps of degrees `1, 0, 0, -1`).
* DEPARTURE (split residual complex). The decomposition of the residual complex into cohomology,
  disk sources and disk targets, and the lifting of graded bases (tex 4416-4423), are not
  constructed here. Their consequences are hypotheses: `NormalizedContraction` (tex 4425-4426)
  and `SplitResidualComplex` (`d₀² = 0`, `d₀ i₀ = 0`, `p₀ d₀ = 0`). The example section builds
  them for one disk.
* DEPARTURE (invertibility, two layers). The core theorems assume that `1 + h₀ ε` and `1 + ε h₀`
  are units. Elliot's setting ("the finite geometric series", tex 4428) is the corollary layer:
  `𝔪` is a nilpotent ideal and `ε` has entries in `𝔪`, formalized basis-free as
  `∀ x, ε x ∈ 𝔪 • ⊤`. Locality of `A` is not used. Inverses are `Ring.inverse`, which in the
  Artin layer is proved to be the finite geometric series `∑_{k<n} (-h₀ ε)^k`.
* Additions (implicit in "bounded finite free model with actual inclusion, projection and
  contraction homotopy", tex 4395-4396 and 4438): besides `p i = 1` and `1 - i p = d h + h d`, the
  file proves `d i = i d_C`, `p d = d_C p`, `d_C² = 0`, and `h² = h i = p h = 0`.
* Transport (tex 4439-4442) is stated for abstract deformation retract data
  (`IsDeformationRetract`), not tied to the construction; `perturbation_isDeformationRetract`
  shows that the construction produces such data.
-/

namespace ZInQ.Manuscript.RC.Limits

/-! ### Ring-level identities

The perturbation identities are first proved in an arbitrary ring `R` (later `R = End_A M`),
with `π` standing for the idempotent `i₀ p₀`, `X` for `(1 + ε h₀)⁻¹` and `Y` for `(1 + h₀ ε)⁻¹`.
-/

namespace PerturbationRing

variable {R : Type*} [Ring R] {d₀ ε h₀ π X Y : R}

/-- Two-sided cancellation of units. Auxiliary, `PROVED`. -/
theorem cancel_left_right {u v a b : R} (hY : Y * u = 1) (hX : v * X = 1)
    (h : u * a * v = u * b * v) : a = b := by
  linear_combination (norm := noncomm_ring) Y * h * X - hY * ((a - b) * v * X) - (a - b) * hX

/-- Left cancellation of a unit. Auxiliary, `PROVED`. -/
theorem cancel_left {u a b : R} (hY : Y * u = 1) (h : u * a = u * b) : a = b := by
  linear_combination (norm := noncomm_ring) Y * h - hY * (a - b)

/-- Right cancellation of a unit. Auxiliary, `PROVED`. -/
theorem cancel_right {v a b : R} (hX : v * X = 1) (h : a * v = b * v) : a = b := by
  linear_combination (norm := noncomm_ring) h * X - (a - b) * hX

/-- `h₀ Y = h₀` (uses `h₀² = 0`). Auxiliary, `PROVED`. -/
theorem homotopy_mul_inv (hhh : h₀ * h₀ = 0) (hYr : (1 + h₀ * ε) * Y = 1) : h₀ * Y = h₀ := by
  linear_combination (norm := noncomm_ring) h₀ * hYr - hhh * (ε * Y)

/-- `X h₀ = h₀` (uses `h₀² = 0`). Auxiliary, `PROVED`. -/
theorem inv_mul_homotopy (hhh : h₀ * h₀ = 0) (hXl : X * (1 + ε * h₀) = 1) : X * h₀ = h₀ := by
  linear_combination (norm := noncomm_ring) hXl * h₀ - (X * ε) * hhh

/-- `Y h₀ = h₀ X`. Auxiliary, `PROVED`. -/
theorem inv_mul_homotopy_comm (hXr : (1 + ε * h₀) * X = 1) (hYl : Y * (1 + h₀ * ε) = 1) :
    Y * h₀ = h₀ * X := by
  linear_combination (norm := noncomm_ring) -(Y * h₀) * hXr + hYl * (h₀ * X)

/-- `X ε = ε Y`. Auxiliary, `PROVED`. -/
theorem inv_mul_pert_comm (hXl : X * (1 + ε * h₀) = 1) (hYr : (1 + h₀ * ε) * Y = 1) :
    X * ε = ε * Y := by
  linear_combination (norm := noncomm_ring) -(X * ε) * hYr + hXl * (ε * Y)

/-- `X π = π` (uses `h₀ i₀ = 0`). Auxiliary, `PROVED`. -/
theorem inv_mul_idem (hhπ : h₀ * π = 0) (hXl : X * (1 + ε * h₀) = 1) : X * π = π := by
  linear_combination (norm := noncomm_ring) hXl * π - (X * ε) * hhπ

/-- `π Y = π` (uses `p₀ h₀ = 0`). Auxiliary, `PROVED`. -/
theorem idem_mul_inv (hπh : π * h₀ = 0) (hYr : (1 + h₀ * ε) * Y = 1) : π * Y = π := by
  linear_combination (norm := noncomm_ring) π * hYr - hπh * (ε * Y)

/-- Ring form of `p i = 1` (tex 4437): `π X Y π = π`. Uses only the side conditions.
Auxiliary, `PROVED`. -/
theorem pi_eq (hhh : h₀ * h₀ = 0) (hhπ : h₀ * π = 0) (hπh : π * h₀ = 0) (hππ : π * π = π)
    (hXl : X * (1 + ε * h₀) = 1) (hYr : (1 + h₀ * ε) * Y = 1) :
    π * X * Y * π = π := by
  have F4 := inv_mul_homotopy hhh hXl
  have F7 := inv_mul_idem hhπ hXl
  linear_combination (norm := noncomm_ring) π * F7 + hππ + (π * X) * hYr * π
    - π * F4 * (ε * Y * π) - hπh * (ε * Y * π)

/-- Ring form of `h h = 0`. Auxiliary, `PROVED`. -/
theorem hh_eq (hhh : h₀ * h₀ = 0) (hXl : X * (1 + ε * h₀) = 1) :
    h₀ * X * (h₀ * X) = 0 := by
  have F4 := inv_mul_homotopy hhh hXl
  linear_combination (norm := noncomm_ring) h₀ * F4 * X + hhh * X

/-- Ring form of `h i = 0`. Auxiliary, `PROVED`. -/
theorem hi_eq (hhh : h₀ * h₀ = 0) (hhπ : h₀ * π = 0)
    (hXl : X * (1 + ε * h₀) = 1) (hYr : (1 + h₀ * ε) * Y = 1) :
    h₀ * X * Y * π = 0 := by
  have F4 := inv_mul_homotopy hhh hXl
  have F7 := inv_mul_idem hhπ hXl
  linear_combination (norm := noncomm_ring) hhπ + h₀ * F7 + (h₀ * X) * hYr * π
    - hhh * (ε * Y * π) - h₀ * F4 * (ε * Y * π)

/-- Ring form of `p h = 0`. Auxiliary, `PROVED`. -/
theorem ph_eq (hhh : h₀ * h₀ = 0) (hπh : π * h₀ = 0) (hXl : X * (1 + ε * h₀) = 1) :
    π * X * (h₀ * X) = 0 := by
  have F4 := inv_mul_homotopy hhh hXl
  linear_combination (norm := noncomm_ring) π * F4 * X + hπh * X

/-- Ring form of `1 - i p = d h + h d` (tex 4437). After multiplying by `1 + h₀ ε` on the left
and `1 + ε h₀` on the right, the identity reduces to `h₀ (d² - d₀²) h₀ = 0`.
Auxiliary, `PROVED`. -/
theorem homotopy_eq (hcontr : 1 - π = d₀ * h₀ + h₀ * d₀) (hd₀d₀ : d₀ * d₀ = 0)
    (hdd : (d₀ + ε) * (d₀ + ε) = 0)
    (hXl : X * (1 + ε * h₀) = 1) (hXr : (1 + ε * h₀) * X = 1)
    (hYl : Y * (1 + h₀ * ε) = 1) (hYr : (1 + h₀ * ε) * Y = 1) :
    1 - Y * π * X = (d₀ + ε) * (h₀ * X) + h₀ * X * (d₀ + ε) := by
  apply cancel_left_right hYl hXr
  linear_combination (norm := noncomm_ring) hcontr - h₀ * hdd * h₀ + h₀ * hd₀d₀ * h₀
    - hYr * (π * X * (1 + ε * h₀)) - π * hXl - ((1 + h₀ * ε) * (d₀ + ε) * h₀) * hXl
    - h₀ * hXr * ((d₀ + ε) * (1 + ε * h₀))

/-- Ring form of `d i = i d_C`; reduces to `h₀ (d² - d₀²) Y π = 0`. Auxiliary, `PROVED`. -/
theorem di_eq (hcontr : 1 - π = d₀ * h₀ + h₀ * d₀) (hd₀d₀ : d₀ * d₀ = 0) (hd₀π : d₀ * π = 0)
    (hdd : (d₀ + ε) * (d₀ + ε) = 0)
    (hYl : Y * (1 + h₀ * ε) = 1) (hYr : (1 + h₀ * ε) * Y = 1) :
    (d₀ + ε) * Y * π = Y * π * (ε * Y * π) := by
  apply cancel_left hYl
  linear_combination (norm := noncomm_ring) hd₀π + d₀ * hYr * π + h₀ * hdd * (Y * π)
    - h₀ * hd₀d₀ * (Y * π) + hcontr * (ε * Y * π) - hYr * (π * ε * Y * π)

/-- Ring form of `p d = d_C p`; reduces to `π X (d² - d₀²) h₀ = 0`. Auxiliary, `PROVED`. -/
theorem pd_eq (hcontr : 1 - π = d₀ * h₀ + h₀ * d₀) (hd₀d₀ : d₀ * d₀ = 0) (hπd₀ : π * d₀ = 0)
    (hdd : (d₀ + ε) * (d₀ + ε) = 0)
    (hXl : X * (1 + ε * h₀) = 1) (hXr : (1 + ε * h₀) * X = 1)
    (hYr : (1 + h₀ * ε) * Y = 1) :
    π * X * (d₀ + ε) = π * (ε * Y * π) * X := by
  have F6 := inv_mul_pert_comm hXl hYr
  apply cancel_right hXr
  linear_combination (norm := noncomm_ring) hπd₀ + π * hXl * d₀ + (π * X) * hdd * h₀
    - (π * X) * hd₀d₀ * h₀ + (π * X * ε) * hcontr + π * F6 * π - (π * ε * Y * π) * hXl

end PerturbationRing

section Perturbation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {C : Type*} [AddCommGroup C] [Module A C]

/-- Elliot's normalized contraction (tex 4421-4427): `i₀, p₀` include and project the cohomology
summand, `h₀` inverts `d₀` from disk targets to disk sources and is zero on the other summands, and
`p₀ i₀ = 1`, `h₀² = h₀ i₀ = p₀ h₀ = 0`, `1 - i₀ p₀ = d₀ h₀ + h₀ d₀`.
Kind: hypothesis bundle (the manuscript's displayed identities).
DEPARTURE: the decomposition itself is not constructed here (see the module docstring). -/
structure NormalizedContraction (d₀ h₀ : Module.End A M) (i₀ : C →ₗ[A] M) (p₀ : M →ₗ[A] C) :
    Prop where
  proj_comp_incl : p₀ ∘ₗ i₀ = LinearMap.id
  homotopy_mul_self : h₀ * h₀ = 0
  homotopy_comp_incl : h₀ ∘ₗ i₀ = 0
  proj_comp_homotopy : p₀ ∘ₗ h₀ = 0
  contraction : 1 - i₀ ∘ₗ p₀ = d₀ * h₀ + h₀ * d₀

/-- Structure of the split residual complex (tex 4416-4423). In the decomposition of the residual
complex into cohomology, disk sources and disk targets, `d₀` is the lifted disk differential: it is
zero on the cohomology summand and lands in the disk targets, on which it is zero. Hence
`d₀² = 0`, `d₀ i₀ = 0` and `p₀ d₀ = 0`. Kind: hypothesis bundle.
DEPARTURE: these consequences are assumed, not derived from a constructed decomposition. -/
structure SplitResidualComplex (d₀ : Module.End A M) (i₀ : C →ₗ[A] M) (p₀ : M →ₗ[A] C) :
    Prop where
  diff_mul_self : d₀ * d₀ = 0
  diff_comp_incl : d₀ ∘ₗ i₀ = 0
  proj_comp_diff : p₀ ∘ₗ d₀ = 0

namespace NormalizedContraction

variable {d₀ h₀ : Module.End A M} {i₀ : C →ₗ[A] M} {p₀ : M →ₗ[A] C}

/-- `i₀ p₀` is idempotent. Auxiliary, `PROVED`. -/
theorem idem (hN : NormalizedContraction d₀ h₀ i₀ p₀) :
    (i₀ ∘ₗ p₀) * (i₀ ∘ₗ p₀) = i₀ ∘ₗ p₀ := by
  change i₀ ∘ₗ (p₀ ∘ₗ i₀) ∘ₗ p₀ = i₀ ∘ₗ p₀
  rw [hN.proj_comp_incl, LinearMap.id_comp]

/-- `h₀ (i₀ p₀) = 0`. Auxiliary, `PROVED`. -/
theorem homotopy_mul_idem (hN : NormalizedContraction d₀ h₀ i₀ p₀) :
    h₀ * (i₀ ∘ₗ p₀) = 0 := by
  change (h₀ ∘ₗ i₀) ∘ₗ p₀ = 0
  rw [hN.homotopy_comp_incl, LinearMap.zero_comp]

/-- `(i₀ p₀) h₀ = 0`. Auxiliary, `PROVED`. -/
theorem idem_mul_homotopy (hN : NormalizedContraction d₀ h₀ i₀ p₀) :
    (i₀ ∘ₗ p₀) * h₀ = 0 := by
  change i₀ ∘ₗ (p₀ ∘ₗ h₀) = 0
  rw [hN.proj_comp_homotopy, LinearMap.comp_zero]

/-- `p₀` is a split epimorphism: maps out of `C` are determined after composing with `p₀`.
Auxiliary, `PROVED`. -/
theorem ext_of_comp_proj (hN : NormalizedContraction d₀ h₀ i₀ p₀) {N : Type*} [AddCommGroup N]
    [Module A N] {f g : C →ₗ[A] N} (h : f ∘ₗ p₀ = g ∘ₗ p₀) : f = g := by
  calc f = (f ∘ₗ p₀) ∘ₗ i₀ := by rw [LinearMap.comp_assoc, hN.proj_comp_incl, LinearMap.comp_id]
    _ = (g ∘ₗ p₀) ∘ₗ i₀ := by rw [h]
    _ = g := by rw [LinearMap.comp_assoc, hN.proj_comp_incl, LinearMap.comp_id]

/-- `i₀` is a split monomorphism: maps into `C` are determined after composing with `i₀`.
Auxiliary, `PROVED`. -/
theorem ext_of_incl_comp (hN : NormalizedContraction d₀ h₀ i₀ p₀) {N : Type*} [AddCommGroup N]
    [Module A N] {f g : N →ₗ[A] C} (h : i₀ ∘ₗ f = i₀ ∘ₗ g) : f = g := by
  calc f = p₀ ∘ₗ (i₀ ∘ₗ f) := by rw [← LinearMap.comp_assoc, hN.proj_comp_incl, LinearMap.id_comp]
    _ = p₀ ∘ₗ (i₀ ∘ₗ g) := by rw [h]
    _ = g := by rw [← LinearMap.comp_assoc, hN.proj_comp_incl, LinearMap.id_comp]

end NormalizedContraction

namespace SplitResidualComplex

variable {d₀ : Module.End A M} {i₀ : C →ₗ[A] M} {p₀ : M →ₗ[A] C}

/-- `d₀ (i₀ p₀) = 0`. Auxiliary, `PROVED`. -/
theorem diff_mul_idem (hS : SplitResidualComplex d₀ i₀ p₀) : d₀ * (i₀ ∘ₗ p₀) = 0 := by
  change (d₀ ∘ₗ i₀) ∘ₗ p₀ = 0
  rw [hS.diff_comp_incl, LinearMap.zero_comp]

/-- `(i₀ p₀) d₀ = 0`. Auxiliary, `PROVED`. -/
theorem idem_mul_diff (hS : SplitResidualComplex d₀ i₀ p₀) : (i₀ ∘ₗ p₀) * d₀ = 0 := by
  change i₀ ∘ₗ (p₀ ∘ₗ d₀) = 0
  rw [hS.proj_comp_diff, LinearMap.comp_zero]

end SplitResidualComplex

/-- Elliot's perturbed model differential (tex 4431): `d_C = p₀ ε (1 + h₀ ε)⁻¹ i₀`.
Kind: definition. DEPARTURE: `(1 + h₀ ε)⁻¹` is `Ring.inverse` in `End_A M` (the unit inverse
whenever `1 + h₀ ε` is a unit; the finite geometric series in the Artin layer). -/
noncomputable def perturbedDifferential (ε h₀ : Module.End A M) (i₀ : C →ₗ[A] M)
    (p₀ : M →ₗ[A] C) : Module.End A C :=
  p₀ ∘ₗ ε ∘ₗ Ring.inverse (1 + h₀ * ε) ∘ₗ i₀

/-- Elliot's perturbed inclusion (tex 4432): `i = (1 + h₀ ε)⁻¹ i₀`. Kind: definition. -/
noncomputable def perturbedInclusion (ε h₀ : Module.End A M) (i₀ : C →ₗ[A] M) : C →ₗ[A] M :=
  Ring.inverse (1 + h₀ * ε) ∘ₗ i₀

/-- Elliot's perturbed projection (tex 4433): `p = p₀ (1 + ε h₀)⁻¹`. Kind: definition. -/
noncomputable def perturbedProjection (ε h₀ : Module.End A M) (p₀ : M →ₗ[A] C) : M →ₗ[A] C :=
  p₀ ∘ₗ Ring.inverse (1 + ε * h₀)

/-- Elliot's perturbed homotopy (tex 4434): `h = h₀ (1 + ε h₀)⁻¹`. Kind: definition. -/
noncomputable def perturbedHomotopy (ε h₀ : Module.End A M) : Module.End A M :=
  h₀ * Ring.inverse (1 + ε * h₀)

variable {d₀ ε h₀ : Module.End A M} {i₀ : C →ₗ[A] M} {p₀ : M →ₗ[A] C}

/-- Elliot's claim `p i = 1` (tex 4437). Only the side conditions of the normalized contraction
are used (not `d² = 0`). `PROVED`. -/
theorem perturbed_proj_comp_incl (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    perturbedProjection ε h₀ p₀ ∘ₗ perturbedInclusion ε h₀ i₀ = LinearMap.id := by
  apply hN.ext_of_incl_comp
  apply hN.ext_of_comp_proj
  change (i₀ ∘ₗ p₀) * Ring.inverse (1 + ε * h₀) * Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀) =
    i₀ ∘ₗ p₀
  exact PerturbationRing.pi_eq hN.homotopy_mul_self hN.homotopy_mul_idem hN.idem_mul_homotopy
    hN.idem (Ring.inverse_mul_cancel _ hv) (Ring.mul_inverse_cancel _ hu)

/-- Elliot's claim `1 - i p = d h + h d` for `d = d₀ + ε` (tex 4419, 4437), by substitution
using `d² = 0`. `PROVED`. -/
theorem perturbed_homotopy_identity (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    1 - perturbedInclusion ε h₀ i₀ ∘ₗ perturbedProjection ε h₀ p₀ =
      (d₀ + ε) * perturbedHomotopy ε h₀ + perturbedHomotopy ε h₀ * (d₀ + ε) := by
  change 1 - Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀) * Ring.inverse (1 + ε * h₀) =
    (d₀ + ε) * (h₀ * Ring.inverse (1 + ε * h₀)) + h₀ * Ring.inverse (1 + ε * h₀) * (d₀ + ε)
  exact PerturbationRing.homotopy_eq hN.contraction hS.diff_mul_self hd
    (Ring.inverse_mul_cancel _ hv) (Ring.mul_inverse_cancel _ hv)
    (Ring.inverse_mul_cancel _ hu) (Ring.mul_inverse_cancel _ hu)

/-- `d i = i d_C`: the perturbed inclusion is a chain map (implicit in tex 4438, "actual maps").
`PROVED`. -/
theorem perturbed_diff_comp_incl (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) :
    (d₀ + ε) ∘ₗ perturbedInclusion ε h₀ i₀ =
      perturbedInclusion ε h₀ i₀ ∘ₗ perturbedDifferential ε h₀ i₀ p₀ := by
  apply hN.ext_of_comp_proj
  change (d₀ + ε) * Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀) =
    Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀) * (ε * Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀))
  exact PerturbationRing.di_eq hN.contraction hS.diff_mul_self hS.diff_mul_idem hd
    (Ring.inverse_mul_cancel _ hu) (Ring.mul_inverse_cancel _ hu)

/-- `p d = d_C p`: the perturbed projection is a chain map (implicit in tex 4438). `PROVED`. -/
theorem perturbed_proj_comp_diff (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    perturbedProjection ε h₀ p₀ ∘ₗ (d₀ + ε) =
      perturbedDifferential ε h₀ i₀ p₀ ∘ₗ perturbedProjection ε h₀ p₀ := by
  apply hN.ext_of_incl_comp
  change (i₀ ∘ₗ p₀) * Ring.inverse (1 + ε * h₀) * (d₀ + ε) =
    (i₀ ∘ₗ p₀) * (ε * Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀)) * Ring.inverse (1 + ε * h₀)
  exact PerturbationRing.pd_eq hN.contraction hS.diff_mul_self hS.idem_mul_diff hd
    (Ring.inverse_mul_cancel _ hv) (Ring.mul_inverse_cancel _ hv) (Ring.mul_inverse_cancel _ hu)

/-- `d_C² = 0`: the finite free model is a complex (implicit in tex 4438). Proof:
`d_C d_C = p i d_C d_C = p d d i = 0`. `PROVED`. -/
theorem perturbedDifferential_mul_self (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    perturbedDifferential ε h₀ i₀ p₀ * perturbedDifferential ε h₀ i₀ p₀ = 0 := by
  set dC := perturbedDifferential ε h₀ i₀ p₀
  set i := perturbedInclusion ε h₀ i₀
  set p := perturbedProjection ε h₀ p₀
  have h1 : p ∘ₗ i = LinearMap.id := perturbed_proj_comp_incl hN hu hv
  have h3 : (d₀ + ε) ∘ₗ i = i ∘ₗ dC := perturbed_diff_comp_incl hN hS hd hu
  calc dC * dC = (p ∘ₗ i) ∘ₗ (dC ∘ₗ dC) := by rw [h1, LinearMap.id_comp]; rfl
    _ = p ∘ₗ ((i ∘ₗ dC) ∘ₗ dC) := rfl
    _ = p ∘ₗ (((d₀ + ε) ∘ₗ i) ∘ₗ dC) := by rw [h3]
    _ = p ∘ₗ ((d₀ + ε) ∘ₗ (i ∘ₗ dC)) := rfl
    _ = p ∘ₗ ((d₀ + ε) ∘ₗ ((d₀ + ε) ∘ₗ i)) := by rw [h3]
    _ = p ∘ₗ (((d₀ + ε) * (d₀ + ε)) ∘ₗ i) := rfl
    _ = 0 := by rw [hd, LinearMap.zero_comp, LinearMap.comp_zero]

/-- `h² = 0`: the new contraction is again normalized (tex 4425, for the perturbed data).
`PROVED`. -/
theorem perturbed_homotopy_mul_self (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hv : IsUnit (1 + ε * h₀)) : perturbedHomotopy ε h₀ * perturbedHomotopy ε h₀ = 0 :=
  PerturbationRing.hh_eq hN.homotopy_mul_self (Ring.inverse_mul_cancel _ hv)

/-- `h i = 0`: the new contraction is again normalized. `PROVED`. -/
theorem perturbed_homotopy_comp_incl (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    perturbedHomotopy ε h₀ ∘ₗ perturbedInclusion ε h₀ i₀ = 0 := by
  apply hN.ext_of_comp_proj
  rw [LinearMap.zero_comp]
  change h₀ * Ring.inverse (1 + ε * h₀) * Ring.inverse (1 + h₀ * ε) * (i₀ ∘ₗ p₀) = 0
  exact PerturbationRing.hi_eq hN.homotopy_mul_self hN.homotopy_mul_idem
    (Ring.inverse_mul_cancel _ hv) (Ring.mul_inverse_cancel _ hu)

/-- `p h = 0`: the new contraction is again normalized. `PROVED`. -/
theorem perturbed_proj_comp_homotopy (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hv : IsUnit (1 + ε * h₀)) :
    perturbedProjection ε h₀ p₀ ∘ₗ perturbedHomotopy ε h₀ = 0 := by
  apply hN.ext_of_incl_comp
  rw [LinearMap.comp_zero]
  change (i₀ ∘ₗ p₀) * Ring.inverse (1 + ε * h₀) * (h₀ * Ring.inverse (1 + ε * h₀)) = 0
  exact PerturbationRing.ph_eq hN.homotopy_mul_self hN.idem_mul_homotopy
    (Ring.inverse_mul_cancel _ hv)

end Perturbation



section Artin

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- If `f` has entries in `𝔪` (`f M ⊆ 𝔪 M`), then `f (I M) ⊆ (I 𝔪) M`. Auxiliary, `PROVED`. -/
theorem apply_mem_ideal_mul_smul_top (𝔪 I : Ideal A) {f : Module.End A M}
    (hf : ∀ x, f x ∈ 𝔪 • (⊤ : Submodule A M)) {y : M} (hy : y ∈ I • (⊤ : Submodule A M)) :
    f y ∈ (I * 𝔪) • (⊤ : Submodule A M) := by
  rw [Submodule.mul_smul]
  have h2 : Submodule.map f ⊤ ≤ 𝔪 • (⊤ : Submodule A M) := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  have h3 : f y ∈ Submodule.map f (I • (⊤ : Submodule A M)) := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h3
  exact Submodule.smul_mono le_rfl h2 h3

/-- If `f` has entries in `𝔪`, then `f^k` has entries in `𝔪^k`. Auxiliary, `PROVED`. -/
theorem pow_apply_mem_pow_smul_top (𝔪 : Ideal A) {f : Module.End A M}
    (hf : ∀ x, f x ∈ 𝔪 • (⊤ : Submodule A M)) (k : ℕ) (x : M) :
    (f ^ k) x ∈ (𝔪 ^ k) • (⊤ : Submodule A M) := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, Module.End.one_apply, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.mem_top
  | succ k ih =>
    rw [pow_succ' f k, Module.End.mul_apply, pow_succ 𝔪 k]
    exact apply_mem_ideal_mul_smul_top 𝔪 (𝔪 ^ k) hf (ih x)

/-- If `𝔪^n = 0` and `f` has entries in `𝔪`, then `f^n = 0` (tex 4419, 4428). `PROVED`. -/
theorem pow_eq_zero_of_entries (𝔪 : Ideal A) {n : ℕ} (hn : 𝔪 ^ n = ⊥) {f : Module.End A M}
    (hf : ∀ x, f x ∈ 𝔪 • (⊤ : Submodule A M)) : f ^ n = 0 := by
  ext x
  have h := pow_apply_mem_pow_smul_top 𝔪 hf n x
  rw [hn, Submodule.bot_smul, Submodule.mem_bot] at h
  rw [h, LinearMap.zero_apply]

/-- `h₀ ε` has entries in `𝔪` when `ε` does. Auxiliary, `PROVED`. -/
theorem homotopy_mul_pert_entries (𝔪 : Ideal A) (h₀ : Module.End A M) {ε : Module.End A M}
    (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M)) : ∀ x, (h₀ * ε) x ∈ 𝔪 • (⊤ : Submodule A M) :=
  fun x => Submodule.smul_top_le_comap_smul_top 𝔪 h₀ (hε x)

/-- `ε h₀` has entries in `𝔪` when `ε` does. Auxiliary, `PROVED`. -/
theorem pert_mul_homotopy_entries (𝔪 : Ideal A) (h₀ : Module.End A M) {ε : Module.End A M}
    (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M)) : ∀ x, (ε * h₀) x ∈ 𝔪 • (⊤ : Submodule A M) :=
  fun x => hε (h₀ x)

/-- The finite geometric series (tex 4428): if `f^n = 0` in a ring, then `1 + f` is a unit and
`(1 + f)⁻¹ = ∑_{k<n} (-f)^k`. `PROVED`. -/
theorem inverse_one_add_eq_geom_sum {R : Type*} [Ring R] {f : R} {n : ℕ} (hn : f ^ n = 0) :
    IsUnit (1 + f) ∧ Ring.inverse (1 + f) = ∑ k ∈ Finset.range n, (-f) ^ k := by
  have hneg : (-f) ^ n = 0 := by rw [neg_pow, hn, mul_zero]
  have h1 : (1 + f) * ∑ k ∈ Finset.range n, (-f) ^ k = 1 := by
    have := mul_neg_geom_sum (-f) n
    rwa [sub_neg_eq_add, hneg, sub_zero] at this
  have h2 : (∑ k ∈ Finset.range n, (-f) ^ k) * (1 + f) = 1 := by
    have := geom_sum_mul_neg (-f) n
    rwa [sub_neg_eq_add, hneg, sub_zero] at this
  have hu : IsUnit (1 + f) := ⟨⟨1 + f, _, h1, h2⟩, rfl⟩
  refine ⟨hu, ?_⟩
  calc Ring.inverse (1 + f)
      = Ring.inverse (1 + f) * ((1 + f) * ∑ k ∈ Finset.range n, (-f) ^ k) := by
        rw [h1, mul_one]
    _ = ∑ k ∈ Finset.range n, (-f) ^ k := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- Artin layer of the invertibility (tex 4409, 4419, 4428): if `𝔪^n = 0` and `ε` has entries in
`𝔪`, then `(h₀ ε)^n = 0`, `(ε h₀)^n = 0`, both `1 + h₀ ε` and `1 + ε h₀` are units, and the
inverses are the finite geometric series `(1 + h₀ ε)⁻¹ = ∑_{k<n} (-h₀ ε)^k`,
`(1 + ε h₀)⁻¹ = ∑_{k<n} (-ε h₀)^k`. `PROVED`.
DEPARTURE: `𝔪` is any nilpotent ideal (locality is not needed), entries in `𝔪` means
`ε M ⊆ 𝔪 M`. -/
theorem artin_inverse_eq_geom_sum (𝔪 : Ideal A) {n : ℕ} (hn : 𝔪 ^ n = ⊥)
    (h₀ : Module.End A M) {ε : Module.End A M} (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M)) :
    (h₀ * ε) ^ n = 0 ∧ (ε * h₀) ^ n = 0 ∧
    IsUnit (1 + h₀ * ε) ∧ Ring.inverse (1 + h₀ * ε) = ∑ k ∈ Finset.range n, (-(h₀ * ε)) ^ k ∧
    IsUnit (1 + ε * h₀) ∧ Ring.inverse (1 + ε * h₀) = ∑ k ∈ Finset.range n, (-(ε * h₀)) ^ k := by
  have e1 := pow_eq_zero_of_entries 𝔪 hn (homotopy_mul_pert_entries 𝔪 h₀ hε)
  have e2 := pow_eq_zero_of_entries 𝔪 hn (pert_mul_homotopy_entries 𝔪 h₀ hε)
  exact ⟨e1, e2, (inverse_one_add_eq_geom_sum e1).1, (inverse_one_add_eq_geom_sum e1).2,
    (inverse_one_add_eq_geom_sum e2).1, (inverse_one_add_eq_geom_sum e2).2⟩

/-- Artin layer (tex 4409, 4419, 4428): for a nilpotent ideal `𝔪` and `ε` with entries in `𝔪`,
`h₀ ε` and `ε h₀` are nilpotent, hence `1 + h₀ ε` and `1 + ε h₀` are units. `PROVED`. -/
theorem artin_isNilpotent (𝔪 : Ideal A) (h𝔪 : IsNilpotent 𝔪)
    (h₀ : Module.End A M) {ε : Module.End A M} (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M)) :
    IsNilpotent (h₀ * ε) ∧ IsNilpotent (ε * h₀) ∧ IsUnit (1 + h₀ * ε) ∧ IsUnit (1 + ε * h₀) := by
  obtain ⟨n, hn⟩ := h𝔪
  have hn' : 𝔪 ^ n = ⊥ := hn
  obtain ⟨e1, e2, u1, -, u2, -⟩ := artin_inverse_eq_geom_sum 𝔪 hn' h₀ hε
  exact ⟨⟨n, e1⟩, ⟨n, e2⟩, u1, u2⟩

end Artin


section Transport

variable {A : Type*} [CommRing A]
  {M C M' C' M'' C'' M₁ C₁ : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup C] [Module A C]
  [AddCommGroup M'] [Module A M'] [AddCommGroup C'] [Module A C']
  [AddCommGroup M''] [Module A M''] [AddCommGroup C''] [Module A C'']
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup C₁] [Module A C₁]

/-- Deformation retract data (abstract form of the data used in tex 4438-4442): a model `(C, d_C)`
of `(M, d)` with `i : C → M`, `p : M → C`, `h : M → M`, `p i = 1`, `1 - i p = d h + h d`,
`d i = i d_C` and `p d = d_C p`. Kind: hypothesis bundle. -/
structure IsDeformationRetract (d : Module.End A M) (dC : Module.End A C) (i : C →ₗ[A] M)
    (p : M →ₗ[A] C) (h : Module.End A M) : Prop where
  proj_comp_incl : p ∘ₗ i = LinearMap.id
  homotopy : 1 - i ∘ₗ p = d * h + h * d
  diff_comp_incl : d ∘ₗ i = i ∘ₗ dC
  proj_comp_diff : p ∘ₗ d = dC ∘ₗ p

/-- Elliot's transport of maps (tex 4439-4440): `T(f) = p' f i`, an `A`-linear map from
`Hom(M, M')` to `Hom(C, C')`. Kind: definition. -/
def retractTransport (i : C →ₗ[A] M) (p' : M' →ₗ[A] C') :
    (M →ₗ[A] M') →ₗ[A] (C →ₗ[A] C') where
  toFun φ := p' ∘ₗ φ ∘ₗ i
  map_add' φ ψ := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c φ := by rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

/-- `T(φ) = p' φ i`. Auxiliary, `PROVED`. -/
theorem retractTransport_apply (i : C →ₗ[A] M) (p' : M' →ₗ[A] C') (φ : M →ₗ[A] M') :
    retractTransport i p' φ = p' ∘ₗ φ ∘ₗ i := rfl

variable {d : Module.End A M} {dC : Module.End A C} {i : C →ₗ[A] M} {p : M →ₗ[A] C}
  {h : Module.End A M}
  {d' : Module.End A M'} {dC' : Module.End A C'} {i' : C' →ₗ[A] M'} {p' : M' →ₗ[A] C'}
  {h' : Module.End A M'}
  {d'' : Module.End A M''} {dC'' : Module.End A C''} {i'' : C'' →ₗ[A] M''}
  {p'' : M'' →ₗ[A] C''} {h'' : Module.End A M''}
  {d₁ : Module.End A M₁} {dC₁ : Module.End A C₁} {i₁ : C₁ →ₗ[A] M₁} {p₁ : M₁ →ₗ[A] C₁}
  {h₁ : Module.End A M₁}

/-- `T(d' φ) = d_C' T(φ)` (uses `p' d' = d_C' p'`). Auxiliary, `PROVED`. -/
theorem retractTransport_diff_comp (hM' : IsDeformationRetract d' dC' i' p' h')
    (i : C →ₗ[A] M) (φ : M →ₗ[A] M') :
    retractTransport i p' (d' ∘ₗ φ) = dC' ∘ₗ retractTransport i p' φ := by
  change (p' ∘ₗ d') ∘ₗ φ ∘ₗ i = dC' ∘ₗ p' ∘ₗ φ ∘ₗ i
  rw [hM'.proj_comp_diff]
  rfl

/-- `T(φ d) = T(φ) d_C` (uses `d i = i d_C`). Auxiliary, `PROVED`. -/
theorem retractTransport_comp_diff (hM : IsDeformationRetract d dC i p h)
    (p' : M' →ₗ[A] C') (φ : M →ₗ[A] M') :
    retractTransport i p' (φ ∘ₗ d) = retractTransport i p' φ ∘ₗ dC := by
  change p' ∘ₗ φ ∘ₗ (d ∘ₗ i) = (p' ∘ₗ φ ∘ₗ i) ∘ₗ dC
  rw [hM.diff_comp_incl]
  rfl

/-- Item (e), odd case (tex 4441-4442): `T(d' φ + φ d) = d_C' T(φ) + T(φ) d_C`. `PROVED`. -/
theorem retractTransport_diff_add (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') (φ : M →ₗ[A] M') :
    retractTransport i p' (d' ∘ₗ φ + φ ∘ₗ d) =
      dC' ∘ₗ retractTransport i p' φ + retractTransport i p' φ ∘ₗ dC := by
  rw [map_add, retractTransport_diff_comp hM' i φ, retractTransport_comp_diff hM p' φ]

/-- Item (e), even case (tex 4441-4442): `T(d' φ - φ d) = d_C' T(φ) - T(φ) d_C`. `PROVED`. -/
theorem retractTransport_diff_sub (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') (φ : M →ₗ[A] M') :
    retractTransport i p' (d' ∘ₗ φ - φ ∘ₗ d) =
      dC' ∘ₗ retractTransport i p' φ - retractTransport i p' φ ∘ₗ dC := by
  rw [map_sub, retractTransport_diff_comp hM' i φ, retractTransport_comp_diff hM p' φ]

/-- Item (e), general principle (tex 4441-4442): any linear relation `∑ c_j φ_j = d' Ψ + Ψ d`
among maps and a homotopy `Ψ` transports to `∑ c_j T(φ_j) = d_C' T(Ψ) + T(Ψ) d_C`. `PROVED`. -/
theorem retractTransport_linear_relation_add (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') {ι : Type*} (s : Finset ι) (c : ι → A)
    (φ : ι → M →ₗ[A] M') (Ψ : M →ₗ[A] M')
    (hrel : ∑ j ∈ s, c j • φ j = d' ∘ₗ Ψ + Ψ ∘ₗ d) :
    ∑ j ∈ s, c j • retractTransport i p' (φ j) =
      dC' ∘ₗ retractTransport i p' Ψ + retractTransport i p' Ψ ∘ₗ dC := by
  have e : ∑ j ∈ s, c j • retractTransport i p' (φ j) =
      retractTransport i p' (∑ j ∈ s, c j • φ j) := by
    rw [map_sum]
    simp_rw [map_smul]
  rw [e, hrel, retractTransport_diff_add hM hM']

/-- Item (e), general principle for second homotopies (tex 4441-4442, "including the second
homotopies"): a linear relation `∑ c_j H_j = d' G - G d` among homotopies and a second homotopy
`G` transports to `∑ c_j T(H_j) = d_C' T(G) - T(G) d_C`. `PROVED`. -/
theorem retractTransport_linear_relation_sub (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') {ι : Type*} (s : Finset ι) (c : ι → A)
    (φ : ι → M →ₗ[A] M') (Ψ : M →ₗ[A] M')
    (hrel : ∑ j ∈ s, c j • φ j = d' ∘ₗ Ψ - Ψ ∘ₗ d) :
    ∑ j ∈ s, c j • retractTransport i p' (φ j) =
      dC' ∘ₗ retractTransport i p' Ψ - retractTransport i p' Ψ ∘ₗ dC := by
  have e : ∑ j ∈ s, c j • retractTransport i p' (φ j) =
      retractTransport i p' (∑ j ∈ s, c j • φ j) := by
    rw [map_sum]
    simp_rw [map_smul]
  rw [e, hrel, retractTransport_diff_sub hM hM']

/-- Item (a) (tex 4439-4440): for a chain map `f` (`d' f = f d`), `f_C = p' f i` is a chain map.
`PROVED`. -/
theorem retractTransport_chainMap (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') {f : M →ₗ[A] M'} (hf : d' ∘ₗ f = f ∘ₗ d) :
    dC' ∘ₗ retractTransport i p' f = retractTransport i p' f ∘ₗ dC := by
  rw [← retractTransport_diff_comp hM' i f, hf, retractTransport_comp_diff hM p' f]

/-- Item (b) (tex 4440-4441): homotopies transport; `f - f̃ = d' H + H d` gives
`f_C - f̃_C = d_C' (p' H i) + (p' H i) d_C`. `PROVED`. -/
theorem retractTransport_homotopy (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') {f f' H : M →ₗ[A] M'}
    (hH : f - f' = d' ∘ₗ H + H ∘ₗ d) :
    retractTransport i p' f - retractTransport i p' f' =
      dC' ∘ₗ retractTransport i p' H + retractTransport i p' H ∘ₗ dC := by
  rw [← map_sub, hH, retractTransport_diff_add hM hM']

/-- Second homotopies transport (tex 4441-4442): `H - H' = d' G - G d` gives
`T(H) - T(H') = d_C' T(G) - T(G) d_C`. `PROVED`. -/
theorem retractTransport_second_homotopy (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') {H H' G : M →ₗ[A] M'}
    (hG : H - H' = d' ∘ₗ G - G ∘ₗ d) :
    retractTransport i p' H - retractTransport i p' H' =
      dC' ∘ₗ retractTransport i p' G - retractTransport i p' G ∘ₗ dC := by
  rw [← map_sub, hG, retractTransport_diff_sub hM hM']

/-- Item (c) (tex 4440-4441): composition is preserved up to an explicit homotopy,
`g_C f_C = (g f)_C - (d_C'' K + K d_C)` with `K = p'' g h' f i`; it uses `i' p' = 1 - d' h' - h' d'`.
`PROVED`. -/
theorem retractTransport_comp (hM : IsDeformationRetract d dC i p h)
    (hM' : IsDeformationRetract d' dC' i' p' h') (hM'' : IsDeformationRetract d'' dC'' i'' p'' h'')
    {f : M →ₗ[A] M'} {g : M' →ₗ[A] M''} (hf : d' ∘ₗ f = f ∘ₗ d) (hg : d'' ∘ₗ g = g ∘ₗ d') :
    retractTransport i' p'' g ∘ₗ retractTransport i p' f =
      retractTransport i p'' (g ∘ₗ f) -
        (dC'' ∘ₗ (p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i) + (p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i) ∘ₗ dC) := by
  have hip : i' ∘ₗ p' = 1 - (d' * h' + h' * d') := by
    rw [← hM'.homotopy, sub_sub_cancel]
  have e0 : retractTransport i' p'' g ∘ₗ retractTransport i p' f =
      retractTransport (f ∘ₗ i) (p'' ∘ₗ g) (i' ∘ₗ p') := rfl
  have e1 : retractTransport (f ∘ₗ i) (p'' ∘ₗ g) 1 = retractTransport i p'' (g ∘ₗ f) := rfl
  have e2 : retractTransport (f ∘ₗ i) (p'' ∘ₗ g) (d' * h') =
      dC'' ∘ₗ (p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i) := by
    change p'' ∘ₗ (g ∘ₗ d') ∘ₗ h' ∘ₗ f ∘ₗ i = _
    rw [← hg]
    change (p'' ∘ₗ d'') ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i = _
    rw [hM''.proj_comp_diff]
    rfl
  have e3 : retractTransport (f ∘ₗ i) (p'' ∘ₗ g) (h' * d') =
      (p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i) ∘ₗ dC := by
    change p'' ∘ₗ g ∘ₗ h' ∘ₗ (d' ∘ₗ f) ∘ₗ i = _
    rw [hf]
    change p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ (d ∘ₗ i) = _
    rw [hM.diff_comp_incl]
    rfl
  rw [e0, hip, map_sub, map_add, e1, e2, e3]

/-- Item (d) (tex 4440-4442): homotopy-commutative squares transport. If
`g f - k l = d'' H + H d` for chain maps `l : M → M₁`, `k : M₁ → M''`, `f : M → M'`,
`g : M' → M''`, then `g_C f_C - k_C l_C = d_C'' H_C + H_C d_C` with
`H_C = p'' H i - p'' g h' f i + p'' k h₁ l i`. `PROVED`. -/
theorem retractTransport_square (hM : IsDeformationRetract d dC i p h)
    (hM₁ : IsDeformationRetract d₁ dC₁ i₁ p₁ h₁) (hM' : IsDeformationRetract d' dC' i' p' h')
    (hM'' : IsDeformationRetract d'' dC'' i'' p'' h'')
    {f : M →ₗ[A] M'} {g : M' →ₗ[A] M''} {l : M →ₗ[A] M₁} {k : M₁ →ₗ[A] M''}
    {H : M →ₗ[A] M''}
    (hf : d' ∘ₗ f = f ∘ₗ d) (hg : d'' ∘ₗ g = g ∘ₗ d') (hl : d₁ ∘ₗ l = l ∘ₗ d)
    (hk : d'' ∘ₗ k = k ∘ₗ d₁) (hH : g ∘ₗ f - k ∘ₗ l = d'' ∘ₗ H + H ∘ₗ d) :
    retractTransport i' p'' g ∘ₗ retractTransport i p' f -
        retractTransport i₁ p'' k ∘ₗ retractTransport i p₁ l =
      dC'' ∘ₗ (retractTransport i p'' H - p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i +
          p'' ∘ₗ k ∘ₗ h₁ ∘ₗ l ∘ₗ i) +
        (retractTransport i p'' H - p'' ∘ₗ g ∘ₗ h' ∘ₗ f ∘ₗ i +
          p'' ∘ₗ k ∘ₗ h₁ ∘ₗ l ∘ₗ i) ∘ₗ dC := by
  rw [retractTransport_comp hM hM' hM'' hf hg, retractTransport_comp hM hM₁ hM'' hl hk]
  have hT : retractTransport i p'' (g ∘ₗ f) - retractTransport i p'' (k ∘ₗ l) =
      dC'' ∘ₗ retractTransport i p'' H + retractTransport i p'' H ∘ₗ dC :=
    retractTransport_homotopy hM hM'' hH
  simp only [LinearMap.comp_add, LinearMap.comp_sub, LinearMap.add_comp, LinearMap.sub_comp]
  linear_combination (norm := abel) hT

end Transport


section Bundled

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {C : Type*} [AddCommGroup C] [Module A C]

/-- Normalized deformation retract data: deformation retract data whose model is a complex
(`d_C² = 0`) and whose homotopy satisfies `h² = h i = p h = 0` (tex 4425 for the new data).
Kind: hypothesis bundle. -/
structure IsNormalizedDeformationRetract (d : Module.End A M) (dC : Module.End A C)
    (i : C →ₗ[A] M) (p : M →ₗ[A] C) (h : Module.End A M) : Prop
    extends IsDeformationRetract d dC i p h where
  model_diff_mul_self : dC * dC = 0
  homotopy_mul_self : h * h = 0
  homotopy_comp_incl : h ∘ₗ i = 0
  proj_comp_homotopy : p ∘ₗ h = 0

variable {d₀ ε h₀ : Module.End A M} {i₀ : C →ₗ[A] M} {p₀ : M →ₗ[A] C}

/-- The perturbation step of tex 4428-4437, core layer: with units `1 + h₀ ε`, `1 + ε h₀`, the
perturbed data `(d_C, i, p, h)` is normalized deformation retract data for `d = d₀ + ε`. `PROVED`. -/
theorem perturbation_lemma (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    IsNormalizedDeformationRetract (d₀ + ε) (perturbedDifferential ε h₀ i₀ p₀)
      (perturbedInclusion ε h₀ i₀) (perturbedProjection ε h₀ p₀) (perturbedHomotopy ε h₀) where
  proj_comp_incl := perturbed_proj_comp_incl hN hu hv
  homotopy := perturbed_homotopy_identity hN hS hd hu hv
  diff_comp_incl := perturbed_diff_comp_incl hN hS hd hu
  proj_comp_diff := perturbed_proj_comp_diff hN hS hd hu hv
  model_diff_mul_self := perturbedDifferential_mul_self hN hS hd hu hv
  homotopy_mul_self := perturbed_homotopy_mul_self hN hv
  homotopy_comp_incl := perturbed_homotopy_comp_incl hN hu hv
  proj_comp_homotopy := perturbed_proj_comp_homotopy hN hv

/-- The perturbation construction produces deformation retract data, so items (a)-(e) apply to
it (tex 4438-4442). `PROVED`. -/
theorem perturbation_isDeformationRetract (hN : NormalizedContraction d₀ h₀ i₀ p₀)
    (hS : SplitResidualComplex d₀ i₀ p₀) (hd : (d₀ + ε) * (d₀ + ε) = 0)
    (hu : IsUnit (1 + h₀ * ε)) (hv : IsUnit (1 + ε * h₀)) :
    IsDeformationRetract (d₀ + ε) (perturbedDifferential ε h₀ i₀ p₀)
      (perturbedInclusion ε h₀ i₀) (perturbedProjection ε h₀ p₀) (perturbedHomotopy ε h₀) :=
  (perturbation_lemma hN hS hd hu hv).toIsDeformationRetract

/-- The perturbation step of tex 4408-4437 in Elliot's setting: `𝔪` nilpotent, `ε` with entries in
`𝔪`, `d = d₀ + ε` with `d² = 0`. The perturbed data is normalized deformation retract data.
`PROVED`. -/
theorem perturbation_lemma_artin (𝔪 : Ideal A) (h𝔪 : IsNilpotent 𝔪)
    (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M))
    (hN : NormalizedContraction d₀ h₀ i₀ p₀) (hS : SplitResidualComplex d₀ i₀ p₀)
    (hd : (d₀ + ε) * (d₀ + ε) = 0) :
    IsNormalizedDeformationRetract (d₀ + ε) (perturbedDifferential ε h₀ i₀ p₀)
      (perturbedInclusion ε h₀ i₀) (perturbedProjection ε h₀ p₀) (perturbedHomotopy ε h₀) := by
  obtain ⟨-, -, hu, hv⟩ := artin_isNilpotent 𝔪 h𝔪 h₀ hε
  exact perturbation_lemma hN hS hd hu hv

/-- Elliot's formulas with the finite geometric series (tex 4428-4436): if `𝔪^n = 0`, then
`d_C = p₀ ε (∑_{k<n} (-h₀ ε)^k) i₀`, `i = (∑_{k<n} (-h₀ ε)^k) i₀`, `p = p₀ ∑_{k<n} (-ε h₀)^k`,
and `h = h₀ ∑_{k<n} (-ε h₀)^k`. `PROVED`. -/
theorem perturbation_formulas_artin (𝔪 : Ideal A) {n : ℕ} (hn : 𝔪 ^ n = ⊥)
    (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M)) :
    perturbedDifferential ε h₀ i₀ p₀ =
        p₀ ∘ₗ ε ∘ₗ (∑ k ∈ Finset.range n, (-(h₀ * ε)) ^ k) ∘ₗ i₀ ∧
      perturbedInclusion ε h₀ i₀ = (∑ k ∈ Finset.range n, (-(h₀ * ε)) ^ k) ∘ₗ i₀ ∧
      perturbedProjection ε h₀ p₀ = p₀ ∘ₗ (∑ k ∈ Finset.range n, (-(ε * h₀)) ^ k) ∧
      perturbedHomotopy ε h₀ = h₀ * ∑ k ∈ Finset.range n, (-(ε * h₀)) ^ k := by
  obtain ⟨-, -, -, eY, -, eX⟩ := artin_inverse_eq_geom_sum 𝔪 hn h₀ hε
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [perturbedDifferential, eY]
  · rw [perturbedInclusion, eY]
  · rw [perturbedProjection, eX]
  · rw [perturbedHomotopy, eX]

end Bundled

section Example

variable {A : Type*} [CommRing A]

/-- Example (one disk): `M = C × S × T` with `C = S = T = A`; `i₀` includes the cohomology
summand `C`. -/
def diskIncl : A →ₗ[A] A × A × A := LinearMap.inl A A (A × A)

/-- Example: `p₀` projects onto the cohomology summand. -/
def diskProj : A × A × A →ₗ[A] A := LinearMap.fst A A (A × A)

/-- Example: the disk differential `d₀ (c, s, t) = (0, 0, s)` (disk source to disk target). -/
def diskDiff : Module.End A (A × A × A) :=
  LinearMap.inr A A (A × A) ∘ₗ LinearMap.inr A A A ∘ₗ LinearMap.fst A A A ∘ₗ
    LinearMap.snd A A (A × A)

/-- Example: `h₀ (c, s, t) = (0, t, 0)` inverts `d₀` from disk targets to disk sources. -/
def diskHomotopy : Module.End A (A × A × A) :=
  LinearMap.inr A A (A × A) ∘ₗ LinearMap.inl A A A ∘ₗ LinearMap.snd A A A ∘ₗ
    LinearMap.snd A A (A × A)

/-- Example: the perturbation `ε (c, s, t) = (0, 0, a c)`. -/
def diskPert (a : A) : Module.End A (A × A × A) :=
  a • (LinearMap.inr A A (A × A) ∘ₗ LinearMap.inr A A A ∘ₗ LinearMap.fst A A (A × A))

/-- Formula for the example inclusion. Auxiliary, `PROVED`. -/
@[simp] theorem diskIncl_apply (c : A) : diskIncl c = (c, 0, 0) := rfl
/-- Formula for the example projection. Auxiliary, `PROVED`. -/
@[simp] theorem diskProj_apply (x : A × A × A) : diskProj x = x.1 := rfl
/-- Formula for the example differential. Auxiliary, `PROVED`. -/
@[simp] theorem diskDiff_apply (x : A × A × A) : diskDiff x = (0, 0, x.2.1) := rfl
/-- Formula for the example homotopy. Auxiliary, `PROVED`. -/
@[simp] theorem diskHomotopy_apply (x : A × A × A) : diskHomotopy x = (0, x.2.2, 0) := rfl
/-- Formula for the example perturbation. Auxiliary, `PROVED`. -/
@[simp] theorem diskPert_apply (a : A) (x : A × A × A) : diskPert a x = (0, 0, a * x.1) := by
  simp [diskPert]

/-- The one-disk example satisfies the normalized contraction identities. `PROVED`. -/
theorem disk_normalizedContraction :
    NormalizedContraction (diskDiff (A := A)) diskHomotopy diskIncl diskProj where
  proj_comp_incl := by ext; simp
  homotopy_mul_self := by ext <;> simp
  homotopy_comp_incl := by ext <;> simp
  proj_comp_homotopy := by ext <;> simp
  contraction := by ext <;> simp

/-- The one-disk example satisfies `d₀² = d₀ i₀ = p₀ d₀ = 0`. `PROVED`. -/
theorem disk_splitResidualComplex :
    SplitResidualComplex (diskDiff (A := A)) diskIncl diskProj where
  diff_mul_self := by ext <;> simp
  diff_comp_incl := by ext <;> simp
  proj_comp_diff := by ext <;> simp

/-- In the one-disk example `d = d₀ + ε` satisfies `d² = 0` for every `a`. `PROVED`. -/
theorem disk_diff_sq (a : A) : (diskDiff + diskPert a) * (diskDiff + diskPert a) = 0 := by
  ext <;> simp

/-- In the one-disk example `1 + h₀ ε` and `1 + ε h₀` are units for every `a`. `PROVED`. -/
theorem disk_isUnit (a : A) :
    IsUnit (1 + diskHomotopy * diskPert a) ∧ IsUnit (1 + diskPert a * diskHomotopy) := by
  have h1 : (diskHomotopy * diskPert a) ^ 2 = 0 := by
    rw [pow_two]; ext <;> simp
  have h2 : diskPert a * diskHomotopy = 0 := by ext <;> simp
  exact ⟨IsNilpotent.isUnit_one_add ⟨2, h1⟩, by rw [h2, add_zero]; exact isUnit_one⟩

/-! Non-vacuity of the core layer: over `ℤ` with `a = 1`, every hypothesis of `perturbation_lemma`
holds, with `ε ≠ 0` and `d₀ ≠ 0`. -/
example : NormalizedContraction (diskDiff (A := ℤ)) diskHomotopy diskIncl diskProj ∧
    SplitResidualComplex (diskDiff (A := ℤ)) diskIncl diskProj ∧
    (diskDiff + diskPert (1 : ℤ)) * (diskDiff + diskPert 1) = 0 ∧
    IsUnit (1 + diskHomotopy * diskPert (1 : ℤ)) ∧ IsUnit (1 + diskPert (1 : ℤ) * diskHomotopy) ∧
    diskPert (1 : ℤ) ≠ 0 ∧ diskDiff (A := ℤ) ≠ 0 := by
  refine ⟨disk_normalizedContraction, disk_splitResidualComplex, disk_diff_sq 1,
    (disk_isUnit 1).1, (disk_isUnit 1).2, ?_, ?_⟩
  · intro h
    have := LinearMap.congr_fun h (1, 0, 0)
    simp at this
  · intro h
    have := LinearMap.congr_fun h (0, 1, 0)
    simp at this

/-- In the one-disk example the perturbed inclusion is `i c = (c, -a c, 0)`. `PROVED`. -/
theorem disk_perturbedInclusion (a : A) (c : A) :
    perturbedInclusion (diskPert a) diskHomotopy diskIncl c = (c, -(a * c), 0) := by
  have h1 : (diskHomotopy * diskPert a) ^ 2 = 0 := by
    rw [pow_two]; ext <;> simp
  rw [perturbedInclusion, (inverse_one_add_eq_geom_sum h1).2]
  simp [Finset.sum_range_succ]

/-! The perturbation genuinely changes the inclusion: `i ≠ i₀` in the example over `ℤ`. -/
example : perturbedInclusion (diskPert (1 : ℤ)) diskHomotopy diskIncl ≠ diskIncl := by
  intro h
  have := LinearMap.congr_fun h 1
  rw [disk_perturbedInclusion] at this
  simp at this

/-! Non-vacuity of the Artin layer: over the Artin local ring `ZMod 4` with maximal ideal
`𝔪 = (2)`, `𝔪` is nilpotent and `ε = diskPert 2 ≠ 0` has entries in `𝔪`. -/
example : IsNilpotent (Ideal.span {(2 : ZMod 4)}) ∧
    (∀ x, diskPert (2 : ZMod 4) x ∈ Ideal.span {(2 : ZMod 4)} • (⊤ : Submodule (ZMod 4) _)) ∧
    diskPert (2 : ZMod 4) ≠ 0 := by
  refine ⟨⟨2, ?_⟩, ?_, ?_⟩
  · rw [Ideal.span_singleton_pow, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    decide
  · intro x
    have : diskPert (2 : ZMod 4) x = (2 : ZMod 4) • ((0, 0, x.1) : ZMod 4 × ZMod 4 × ZMod 4) := by
      simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 2) Submodule.mem_top
  · intro h
    have := LinearMap.congr_fun h (1, 0, 0)
    simp at this
    revert this
    decide

/-! The Artin-layer theorem applies to the `ZMod 4` instance. -/
example : IsNormalizedDeformationRetract (diskDiff + diskPert (2 : ZMod 4))
    (perturbedDifferential (diskPert 2) diskHomotopy diskIncl diskProj)
    (perturbedInclusion (diskPert 2) diskHomotopy diskIncl)
    (perturbedProjection (diskPert 2) diskHomotopy diskProj)
    (perturbedHomotopy (diskPert 2) diskHomotopy) := by
  refine perturbation_lemma_artin (Ideal.span {(2 : ZMod 4)}) ⟨2, ?_⟩ ?_
    disk_normalizedContraction disk_splitResidualComplex (disk_diff_sq 2)
  · rw [Ideal.span_singleton_pow, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    decide
  · intro x
    have : diskPert (2 : ZMod 4) x = (2 : ZMod 4) • ((0, 0, x.1) : ZMod 4 × ZMod 4 × ZMod 4) := by
      simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 2) Submodule.mem_top

end Example


section Graded

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]

/-- Graded refinement (optional): `f` has degree `k` for degree pieces `Mdeg`, `Ndeg` if it maps
`Mdeg n` into `Ndeg (n + k)`. Kind: definition. -/
def HasDegree (Mdeg : ℤ → Submodule A M) (Ndeg : ℤ → Submodule A N) (k : ℤ)
    (f : M →ₗ[A] N) : Prop :=
  ∀ n, ∀ x ∈ Mdeg n, f x ∈ Ndeg (n + k)

namespace HasDegree

variable {Mdeg : ℤ → Submodule A M} {Ndeg : ℤ → Submodule A N} {Pdeg : ℤ → Submodule A P}

/-- Change the degree along an equality. Auxiliary, `PROVED`. -/
theorem of_eq {k l : ℤ} {f : M →ₗ[A] N} (hf : HasDegree Mdeg Ndeg k f) (hkl : k = l) :
    HasDegree Mdeg Ndeg l f :=
  hkl ▸ hf

/-- Degrees add under composition. Auxiliary, `PROVED`. -/
theorem comp {k l : ℤ} {f : M →ₗ[A] N} {g : N →ₗ[A] P} (hf : HasDegree Mdeg Ndeg k f)
    (hg : HasDegree Ndeg Pdeg l g) : HasDegree Mdeg Pdeg (k + l) (g ∘ₗ f) := by
  intro n x hx
  rw [← add_assoc]
  exact hg (n + k) (f x) (hf n x hx)

/-- Degrees add under multiplication of endomorphisms. Auxiliary, `PROVED`. -/
theorem mul {k l : ℤ} {f g : Module.End A M} (hf : HasDegree Mdeg Mdeg k f)
    (hg : HasDegree Mdeg Mdeg l g) : HasDegree Mdeg Mdeg (l + k) (f * g) :=
  hg.comp hf

/-- The identity has degree `0`. Auxiliary, `PROVED`. -/
theorem one : HasDegree Mdeg Mdeg 0 (1 : Module.End A M) := by
  intro n x hx
  rw [add_zero]
  exact hx

/-- Sums of maps of degree `k` have degree `k`. Auxiliary, `PROVED`. -/
theorem add {k : ℤ} {f g : M →ₗ[A] N} (hf : HasDegree Mdeg Ndeg k f)
    (hg : HasDegree Mdeg Ndeg k g) : HasDegree Mdeg Ndeg k (f + g) :=
  fun n x hx => Submodule.add_mem _ (hf n x hx) (hg n x hx)

/-- Negatives of maps of degree `k` have degree `k`. Auxiliary, `PROVED`. -/
theorem neg {k : ℤ} {f : M →ₗ[A] N} (hf : HasDegree Mdeg Ndeg k f) :
    HasDegree Mdeg Ndeg k (-f) :=
  fun n x hx => Submodule.neg_mem _ (hf n x hx)

/-- Finite sums of maps of degree `k` have degree `k`. Auxiliary, `PROVED`. -/
theorem sum {k : ℤ} {ι : Type*} (s : Finset ι) {f : ι → M →ₗ[A] N}
    (hf : ∀ j ∈ s, HasDegree Mdeg Ndeg k (f j)) : HasDegree Mdeg Ndeg k (∑ j ∈ s, f j) := by
  intro n x hx
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun j hj => hf j hj n x hx

/-- Powers of a map of degree `0` have degree `0`. Auxiliary, `PROVED`. -/
theorem pow {f : Module.End A M} (hf : HasDegree Mdeg Mdeg 0 f) (k : ℕ) :
    HasDegree Mdeg Mdeg 0 (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact one
  | succ k ih => rw [pow_succ]; exact (ih.mul hf).of_eq (add_zero 0)

end HasDegree

variable {C : Type*} [AddCommGroup C] [Module A C]
  {ε h₀ : Module.End A M} {i₀ : C →ₗ[A] M} {p₀ : M →ₗ[A] C}

/-- Graded refinement (optional; tex 4417-4436): if `ε` has degree `1`, `h₀` degree `-1` and
`i₀, p₀` degree `0`, then in the Artin layer `d_C, i, p, h` have degrees `1, 0, 0, -1`. The proof
uses the finite geometric series. `PROVED`.
DEPARTURE: degree pieces are an arbitrary family of submodules; no direct-sum condition is needed. -/
theorem perturbed_degrees_artin (𝔪 : Ideal A) (h𝔪 : IsNilpotent 𝔪)
    (hε : ∀ x, ε x ∈ 𝔪 • (⊤ : Submodule A M))
    (Mdeg : ℤ → Submodule A M) (Cdeg : ℤ → Submodule A C)
    (hεdeg : HasDegree Mdeg Mdeg 1 ε) (hh₀deg : HasDegree Mdeg Mdeg (-1) h₀)
    (hi₀deg : HasDegree Cdeg Mdeg 0 i₀) (hp₀deg : HasDegree Mdeg Cdeg 0 p₀) :
    HasDegree Cdeg Cdeg 1 (perturbedDifferential ε h₀ i₀ p₀) ∧
      HasDegree Cdeg Mdeg 0 (perturbedInclusion ε h₀ i₀) ∧
      HasDegree Mdeg Cdeg 0 (perturbedProjection ε h₀ p₀) ∧
      HasDegree Mdeg Mdeg (-1) (perturbedHomotopy ε h₀) := by
  obtain ⟨n, hn⟩ := h𝔪
  have hn' : 𝔪 ^ n = ⊥ := hn
  obtain ⟨eD, eI, eP, eH⟩ := perturbation_formulas_artin (h₀ := h₀) (i₀ := i₀) (p₀ := p₀) 𝔪 hn' hε
  have hY : HasDegree Mdeg Mdeg 0 (∑ k ∈ Finset.range n, (-(h₀ * ε)) ^ k) :=
    HasDegree.sum _ fun k _ => (((hh₀deg.mul hεdeg).of_eq (by norm_num)).neg).pow k
  have hX : HasDegree Mdeg Mdeg 0 (∑ k ∈ Finset.range n, (-(ε * h₀)) ^ k) :=
    HasDegree.sum _ fun k _ => (((hεdeg.mul hh₀deg).of_eq (by norm_num)).neg).pow k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eD]
    exact (((hi₀deg.comp hY).comp hεdeg).comp hp₀deg).of_eq (by norm_num)
  · rw [eI]
    exact (hi₀deg.comp hY).of_eq (by norm_num)
  · rw [eP]
    exact (hX.comp hp₀deg).of_eq (by norm_num)
  · rw [eH]
    exact (hh₀deg.mul hX).of_eq (by norm_num)

end Graded


section GradedExample

variable {A : Type*} [CommRing A]

/-- Example grading of the one-disk model: `C` and `S` in degree `0`, `T` in degree `1`. -/
def diskDeg (n : ℤ) : Submodule A (A × A × A) :=
  if n = 0 then (⊤ : Submodule A A).prod ((⊤ : Submodule A A).prod ⊥)
  else if n = 1 then (⊥ : Submodule A A).prod ((⊥ : Submodule A A).prod ⊤) else ⊥

/-- Example grading of the cohomology summand `C`: degree `0`. -/
def diskCDeg (n : ℤ) : Submodule A A := if n = 0 then ⊤ else ⊥

/-- Membership in the example degree pieces. Auxiliary, `PROVED`. -/
theorem mem_diskDeg_iff (n : ℤ) (x : A × A × A) :
    x ∈ diskDeg n ↔ (n = 0 ∧ x.2.2 = 0) ∨ (n = 1 ∧ x.1 = 0 ∧ x.2.1 = 0) ∨ x = 0 := by
  obtain ⟨c, s, t⟩ := x
  unfold diskDeg
  split_ifs with h0 h1
  · subst h0
    simp only [Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, Prod.mk_eq_zero]
    tauto
  · subst h1
    simp only [Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, Prod.mk_eq_zero]
    have : (1 : ℤ) ≠ 0 := one_ne_zero
    tauto
  · simp only [Submodule.mem_bot, Prod.mk_eq_zero]
    tauto

/-- Membership in the example degree pieces of `C`. Auxiliary, `PROVED`. -/
theorem mem_diskCDeg_iff (n : ℤ) (c : A) : c ∈ diskCDeg n ↔ n = 0 ∨ c = 0 := by
  unfold diskCDeg
  split_ifs with h0
  · simp [h0]
  · simp [h0]

/-- The example perturbation has degree `1`. `PROVED`. -/
theorem diskPert_hasDegree (a : A) : HasDegree diskDeg diskDeg 1 (diskPert a) := by
  intro n x hx
  rw [mem_diskDeg_iff] at hx ⊢
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, h1, -⟩ | rfl
  · right; left; simp
  · right; right; simp [h1]
  · right; right; simp

/-- The example homotopy has degree `-1`. `PROVED`. -/
theorem diskHomotopy_hasDegree : HasDegree diskDeg diskDeg (-1) (diskHomotopy (A := A)) := by
  intro n x hx
  rw [mem_diskDeg_iff] at hx ⊢
  rcases hx with ⟨rfl, h2⟩ | ⟨rfl, -, -⟩ | rfl
  · right; right; simp [h2]
  · left; simp
  · right; right; simp

/-- The example inclusion has degree `0`. `PROVED`. -/
theorem diskIncl_hasDegree : HasDegree diskCDeg diskDeg 0 (diskIncl (A := A)) := by
  intro n c hc
  rw [mem_diskCDeg_iff] at hc
  rw [mem_diskDeg_iff]
  rcases hc with rfl | rfl
  · left; simp
  · right; right; simp

/-- The example projection has degree `0`. `PROVED`. -/
theorem diskProj_hasDegree : HasDegree diskDeg diskCDeg 0 (diskProj (A := A)) := by
  intro n x hx
  rw [mem_diskDeg_iff] at hx
  rw [mem_diskCDeg_iff]
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, h1, -⟩ | rfl
  · left; simp
  · right; simpa using h1
  · right; simp

/-! Non-vacuity of the graded hypotheses: in the graded one-disk model over `ZMod 4`, `ε, h₀, i₀,
p₀, d₀` have the required degrees, and the degree condition on `ε` is not automatic. -/
example : HasDegree diskDeg diskDeg 1 (diskPert (2 : ZMod 4)) ∧
    HasDegree diskDeg diskDeg (-1) (diskHomotopy (A := ZMod 4)) ∧
    HasDegree diskCDeg diskDeg 0 (diskIncl (A := ZMod 4)) ∧
    HasDegree diskDeg diskCDeg 0 (diskProj (A := ZMod 4)) ∧
    HasDegree diskDeg diskDeg 1 (diskDiff (A := ZMod 4)) ∧
    ¬ HasDegree diskDeg diskDeg 0 (diskPert (2 : ZMod 4)) := by
  refine ⟨diskPert_hasDegree 2, diskHomotopy_hasDegree, diskIncl_hasDegree, diskProj_hasDegree,
    ?_, ?_⟩
  · intro n x hx
    rw [mem_diskDeg_iff] at hx ⊢
    rcases hx with ⟨rfl, -⟩ | ⟨rfl, -, h2⟩ | rfl
    · right; left; simp
    · right; right; simp [h2]
    · right; right; simp
  · intro h
    have := h 0 (1, 0, 0) ((mem_diskDeg_iff _ _).2 (Or.inl ⟨rfl, rfl⟩))
    rw [mem_diskDeg_iff] at this
    revert this
    decide

end GradedExample

end ZInQ.Manuscript.RC.Limits
