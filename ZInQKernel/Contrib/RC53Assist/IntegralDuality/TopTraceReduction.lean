import Mathlib

/-!
# Reduction of a fixed top-degree integral trace

Let `φ : R →+* S` be a ring map with `φ π = 0` and `ker φ ⊆ (π)`. Consider four consecutive
terms of a complex `C` of `R`-modules and three consecutive terms of a complex `C'` of
`S`-modules,

```
C^{m-1} --d₀--> C^m --d₁--> C^{m+1} --d₂--> C^{m+2}
  |ρ₀            |ρ₁          |ρ₂
C'^{m-1} --d₀'--> C'^m --d₁'--> C'^{m+1}
```

with `φ`-semilinear coefficient maps `ρᵢ` commuting with the differentials. Assume

* `ρ₀` and `ρ₁` are surjective, and the kernel of `ρ₂` is contained in `π • C^{m+1}`;
* `π` is a non-zero-divisor on `C^{m+2}`;
* `H^{m+1}(C) = 0` (every `d₂`-cycle is a `d₁`-boundary);
* `tr_R : C^m → R` kills boundaries and induces `H^m(C) ≅ R` in the concrete sense: a cycle of
  trace zero is a boundary, and some cycle has trace one.

Then any given `tr_S : C'^m → S` with `tr_S (ρ₁ z) = φ (tr_R z)` kills boundaries and induces
`H^m(C') ≅ S` in the same concrete sense (`reducedTrace_isTopTraceIso`). No finiteness of the
terms is used, and no duality is assumed.

## Proof
1. *Cycle lifting* (`exists_cycle_lift`). Given a cycle `c'`, lift it to `z` with `ρ₁ z = c'`.
   Then `ρ₂ (d₁ z) = d₁' c' = 0`, so `d₁ z = π • w`. Since `π • d₂ w = d₂ (d₁ z) = 0` and `π` is
   regular on `C^{m+2}`, `w` is a cycle, hence `w = d₁ v`. Now `z - π • v` is a cycle with
   `ρ₁ (z - π • v) = c' - φ π • ρ₁ v = c'`.
2. *Trace-zero cycles are boundaries*. If `tr_S c' = 0` and `z` is a cycle lift of `c'`, then
   `φ (tr_R z) = 0`, so `tr_R z = π * r`. With `z₀` a cycle of trace one, `z - (π * r) • z₀` is a
   cycle of trace zero, hence `d₀ x`. Its image under `ρ₁` is still `c'`, so `c' = d₀' (ρ₀ x)`.
3. *Trace one and boundaries*. `ρ₁ z₀` is a cycle of trace `φ 1 = 1`; and
   `tr_S (d₀' (ρ₀ x)) = φ (tr_R (d₀ x)) = 0`, so boundaries are killed because `ρ₀` is onto.

`IsTopTraceIso.equiv` turns the concrete condition into an actual linear isomorphism from
cycles modulo boundaries to the ring, induced by the trace.

The `2`-adic specialisation (`φ = PadicInt.toZMod`, `π = 2`) is
`reducedTrace_isTopTraceIso_modTwo`, which takes torsion-freeness of `C^{m+2}`.

At the end, `reducedTrace_example` is a nonzero instance, and
`topTraceIso_fails_without_vanishing` shows that the hypothesis `H^{m+1}(C) = 0` cannot be
dropped: a concrete integral complex satisfying every other hypothesis whose reduction has a
cycle of trace zero that is not a boundary.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

section Generic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A linear functional `tr` on the middle term of `X₀ --d₀--> X₁ --d₁--> X₂` *induces an
isomorphism of the middle cohomology with the ring*, in the concrete sense: it kills boundaries,
a cycle of trace zero is a boundary, and some cycle has trace one. -/
def IsTopTraceIso {A : Type*} [CommRing A] {X₀ X₁ X₂ : Type*}
    [AddCommGroup X₀] [Module A X₀] [AddCommGroup X₁] [Module A X₁]
    [AddCommGroup X₂] [Module A X₂]
    (d₀ : X₀ →ₗ[A] X₁) (d₁ : X₁ →ₗ[A] X₂) (tr : X₁ →ₗ[A] A) : Prop :=
  (∀ x, tr (d₀ x) = 0) ∧ (∀ z, d₁ z = 0 → tr z = 0 → ∃ x, d₀ x = z) ∧
    ∃ z, d₁ z = 0 ∧ tr z = 1

section Equiv

variable {A : Type*} [CommRing A] {X₀ X₁ X₂ : Type*}
  [AddCommGroup X₀] [Module A X₀] [AddCommGroup X₁] [Module A X₁]
  [AddCommGroup X₂] [Module A X₂]
  {d₀ : X₀ →ₗ[A] X₁} {d₁ : X₁ →ₗ[A] X₂} {tr : X₁ →ₗ[A] A}

/-- The kernel of the trace restricted to cycles is exactly the boundaries. -/
theorem IsTopTraceIso.ker_eq (h : IsTopTraceIso d₀ d₁ tr) :
    LinearMap.ker (tr ∘ₗ (LinearMap.ker d₁).subtype) =
      (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype := by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · exact h.2.1 z hz
  · rintro ⟨x, rfl⟩
    exact h.1 x

/-- The concrete condition yields an actual linear isomorphism from cycles modulo boundaries to
the ring, induced by the trace. -/
def IsTopTraceIso.equiv (h : IsTopTraceIso d₀ d₁ tr) :
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype) ≃ₗ[A] A :=
  (Submodule.quotEquivOfEq _ _ h.ker_eq.symm).trans
    (LinearMap.quotKerEquivOfSurjective (tr ∘ₗ (LinearMap.ker d₁).subtype) (by
      obtain ⟨z₀, hz₀, htr₀⟩ := h.2.2
      intro a
      refine ⟨a • ⟨z₀, hz₀⟩, ?_⟩
      simp [htr₀]))

theorem IsTopTraceIso.equiv_mk (h : IsTopTraceIso d₀ d₁ tr) (z : LinearMap.ker d₁) :
    h.equiv (Submodule.Quotient.mk z) = tr z := rfl

end Equiv

variable {φ : R →+* S} {π : R}
  {X₀ X₁ X₂ X₃ : Type*} [AddCommGroup X₀] [Module R X₀] [AddCommGroup X₁] [Module R X₁]
  [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
  {Y₀ Y₁ Y₂ : Type*} [AddCommGroup Y₀] [Module S Y₀] [AddCommGroup Y₁] [Module S Y₁]
  [AddCommGroup Y₂] [Module S Y₂]

/-- **Cycle lifting.** A cycle of the reduced complex in degree `m` lifts to an integral cycle,
using `H^{m+1}(C) = 0`, regularity of `π` on `C^{m+2}`, `ker ρ₂ ⊆ π C^{m+1}` and surjectivity
of `ρ₁`. -/
theorem exists_cycle_lift
    (d₁ : X₁ →ₗ[R] X₂) (d₂ : X₂ →ₗ[R] X₃) (d₁' : Y₁ →ₗ[S] Y₂)
    (ρ₁ : X₁ →ₛₗ[φ] Y₁) (ρ₂ : X₂ →ₛₗ[φ] Y₂)
    (hdd : ∀ x, d₂ (d₁ x) = 0) (hφπ : φ π = 0)
    (hρ₁ : Function.Surjective ρ₁) (hker₂ : ∀ x, ρ₂ x = 0 → ∃ w, x = π • w)
    (hreg : IsSMulRegular X₃ π) (hcomm₁ : ∀ x, ρ₂ (d₁ x) = d₁' (ρ₁ x))
    (hH : ∀ w, d₂ w = 0 → ∃ v, d₁ v = w)
    {c : Y₁} (hc : d₁' c = 0) : ∃ z, d₁ z = 0 ∧ ρ₁ z = c := by
  obtain ⟨z, rfl⟩ := hρ₁ c
  obtain ⟨w, hw⟩ := hker₂ (d₁ z) (by rw [hcomm₁, hc])
  have hw2 : d₂ w = 0 := by
    apply hreg
    change π • d₂ w = π • (0 : X₃)
    rw [smul_zero, ← map_smul, ← hw, hdd]
  obtain ⟨v, rfl⟩ := hH w hw2
  refine ⟨z - π • v, ?_, ?_⟩
  · rw [map_sub, map_smul, ← hw, sub_self]
  · rw [map_sub, map_smulₛₗ, hφπ, zero_smul, sub_zero]

/-- **Reduction of a fixed top-degree trace.** If `tr_R` induces `H^m(C) ≅ R` and the given
`tr_S` is compatible with it through the coefficient maps, then `tr_S` induces
`H^m(C') ≅ S`. -/
theorem reducedTrace_isTopTraceIso
    (d₀ : X₀ →ₗ[R] X₁) (d₁ : X₁ →ₗ[R] X₂) (d₂ : X₂ →ₗ[R] X₃)
    (d₀' : Y₀ →ₗ[S] Y₁) (d₁' : Y₁ →ₗ[S] Y₂)
    (ρ₀ : X₀ →ₛₗ[φ] Y₀) (ρ₁ : X₁ →ₛₗ[φ] Y₁) (ρ₂ : X₂ →ₛₗ[φ] Y₂)
    (hdd : ∀ x, d₂ (d₁ x) = 0)
    (hφπ : φ π = 0) (hkerφ : ∀ r, φ r = 0 → ∃ s, r = π * s)
    (hρ₀ : Function.Surjective ρ₀) (hρ₁ : Function.Surjective ρ₁)
    (hker₂ : ∀ x, ρ₂ x = 0 → ∃ w, x = π • w) (hreg : IsSMulRegular X₃ π)
    (hcomm₀ : ∀ x, ρ₁ (d₀ x) = d₀' (ρ₀ x)) (hcomm₁ : ∀ x, ρ₂ (d₁ x) = d₁' (ρ₁ x))
    (hH : ∀ w, d₂ w = 0 → ∃ v, d₁ v = w)
    (trR : X₁ →ₗ[R] R) (trS : Y₁ →ₗ[S] S)
    (htrR : IsTopTraceIso d₀ d₁ trR)
    (hcompat : ∀ z, trS (ρ₁ z) = φ (trR z)) :
    IsTopTraceIso d₀' d₁' trS := by
  obtain ⟨hbd, hker, z₀, hz₀, htr₀⟩ := htrR
  refine ⟨?_, ?_, ρ₁ z₀, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hρ₀ y
    rw [← hcomm₀, hcompat, hbd, map_zero]
  · intro c hc htc
    obtain ⟨z, hz, rfl⟩ :=
      exists_cycle_lift d₁ d₂ d₁' ρ₁ ρ₂ hdd hφπ hρ₁ hker₂ hreg hcomm₁ hH hc
    obtain ⟨r, hr⟩ := hkerφ (trR z) (by rw [← hcompat, htc])
    obtain ⟨x, hx⟩ := hker (z - (π * r) • z₀)
      (by rw [map_sub, map_smul, hz, hz₀, smul_zero, sub_zero])
      (by rw [map_sub, map_smul, htr₀, hr, smul_eq_mul, mul_one, sub_self])
    refine ⟨ρ₀ x, ?_⟩
    rw [← hcomm₀, hx, map_sub, map_smulₛₗ, map_mul, hφπ, zero_mul, zero_smul, sub_zero]
  · rw [← hcomm₁, hz₀, map_zero]
  · rw [hcompat, htr₀, map_one]

end Generic

section ModTwo

variable {X₀ X₁ X₂ X₃ : Type*} [AddCommGroup X₀] [Module ℤ_[2] X₀]
  [AddCommGroup X₁] [Module ℤ_[2] X₁] [AddCommGroup X₂] [Module ℤ_[2] X₂]
  [AddCommGroup X₃] [Module ℤ_[2] X₃]
  {Y₀ Y₁ Y₂ : Type*} [AddCommGroup Y₀] [Module (ZMod 2) Y₀] [AddCommGroup Y₁]
  [Module (ZMod 2) Y₁] [AddCommGroup Y₂] [Module (ZMod 2) Y₂]

/-- `PadicInt.toZMod` kills `2`. -/
theorem toZMod_two : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 2 = 0 := by
  have h : (2 : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (by norm_num)
  exact h

/-- The kernel of `PadicInt.toZMod` is contained in `(2)`. -/
theorem exists_eq_two_mul_of_toZMod_eq_zero (r : ℤ_[2])
    (hr : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) r = 0) : ∃ s, r = 2 * s := by
  have h : r ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := hr
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by rw [← hs, mul_comm]; norm_num⟩

/-- `2` is a regular element of `ℤ_[2]`. -/
theorem isRegular_two_padicInt : IsRegular (2 : ℤ_[2]) :=
  IsRegular.of_ne_zero two_ne_zero

/-- **2-adic specialisation.** Reduction modulo `2` along `PadicInt.toZMod` of a fixed top-degree
trace, with `C^{m+2}` torsion-free. -/
theorem reducedTrace_isTopTraceIso_modTwo [Module.IsTorsionFree ℤ_[2] X₃]
    (d₀ : X₀ →ₗ[ℤ_[2]] X₁) (d₁ : X₁ →ₗ[ℤ_[2]] X₂) (d₂ : X₂ →ₗ[ℤ_[2]] X₃)
    (d₀' : Y₀ →ₗ[ZMod 2] Y₁) (d₁' : Y₁ →ₗ[ZMod 2] Y₂)
    (ρ₀ : X₀ →ₛₗ[(PadicInt.toZMod : ℤ_[2] →+* ZMod 2)] Y₀)
    (ρ₁ : X₁ →ₛₗ[(PadicInt.toZMod : ℤ_[2] →+* ZMod 2)] Y₁)
    (ρ₂ : X₂ →ₛₗ[(PadicInt.toZMod : ℤ_[2] →+* ZMod 2)] Y₂)
    (hdd : ∀ x, d₂ (d₁ x) = 0)
    (hρ₀ : Function.Surjective ρ₀) (hρ₁ : Function.Surjective ρ₁)
    (hker₂ : ∀ x, ρ₂ x = 0 → ∃ w, x = (2 : ℤ_[2]) • w)
    (hcomm₀ : ∀ x, ρ₁ (d₀ x) = d₀' (ρ₀ x)) (hcomm₁ : ∀ x, ρ₂ (d₁ x) = d₁' (ρ₁ x))
    (hH : ∀ w, d₂ w = 0 → ∃ v, d₁ v = w)
    (trR : X₁ →ₗ[ℤ_[2]] ℤ_[2]) (trS : Y₁ →ₗ[ZMod 2] ZMod 2)
    (htrR : IsTopTraceIso d₀ d₁ trR)
    (hcompat : ∀ z, trS (ρ₁ z) = PadicInt.toZMod (trR z)) :
    IsTopTraceIso d₀' d₁' trS :=
  reducedTrace_isTopTraceIso d₀ d₁ d₂ d₀' d₁' ρ₀ ρ₁ ρ₂ hdd toZMod_two
    exists_eq_two_mul_of_toZMod_eq_zero hρ₀ hρ₁ hker₂
    (isRegular_two_padicInt.isSMulRegular) hcomm₀ hcomm₁ hH trR trS htrR hcompat

end ModTwo

section Examples

/-- `PadicInt.toZMod` as a semilinear map of the rings viewed as modules over themselves. -/
def toZModSL : ℤ_[2] →ₛₗ[(PadicInt.toZMod : ℤ_[2] →+* ZMod 2)] ZMod 2 where
  toFun := PadicInt.toZMod
  map_add' := map_add _
  map_smul' r x := by simp [smul_eq_mul]

theorem toZModSL_surjective : Function.Surjective toZModSL := fun y => by
  refine ⟨(y.val : ℤ_[2]), ?_⟩
  change PadicInt.toZMod (y.val : ℤ_[2]) = y
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- **Nonzero instance.** The complex `0 → ℤ_[2] → 0 → 0` (degrees `m-1, …, m+2`) with the identity
trace, reduced modulo `2`: the theorem applies, and the reduced trace is the identity of `ZMod 2`,
which takes the value `1` on a cycle. -/
theorem reducedTrace_example :
    IsTopTraceIso (0 : PUnit.{1} →ₗ[ZMod 2] ZMod 2) (0 : ZMod 2 →ₗ[ZMod 2] PUnit.{1})
      (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) ∧
      (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 ≠ 0 := by
  refine ⟨reducedTrace_isTopTraceIso_modTwo (X₀ := PUnit.{1}) (X₂ := PUnit.{1})
    (X₃ := PUnit.{1}) (Y₀ := PUnit.{1}) (Y₂ := PUnit.{1}) 0 0 0 0 0 0 toZModSL 0 (fun _ => rfl)
    (fun _ => ⟨PUnit.unit, rfl⟩) toZModSL_surjective (fun _ _ => ⟨PUnit.unit, rfl⟩)
    (fun _ => by simp) (fun _ => rfl) (fun _ _ => ⟨0, rfl⟩) LinearMap.id LinearMap.id
    ⟨fun _ => by simp, fun z _ hz => ⟨PUnit.unit, by simpa using hz.symm⟩, 1, rfl, rfl⟩
    (fun _ => rfl), ?_⟩
  exact one_ne_zero

/-! ### Negative control: `H^{m+1}(C) = 0` cannot be dropped

The integral complex `0 → ℤ_[2]² --(a, b) ↦ 2b--> ℤ_[2] → 0` (degrees `m-1, …, m+2`) with
`tr_R (a, b) = a` satisfies every hypothesis except `H^{m+1}(C) = 0` (here `H^{m+1} = ℤ_[2]/2`).
Its reduction modulo `2` is `0 → (ZMod 2)² --0--> ZMod 2`, and `(0, 1)` is a cycle of trace zero
that is not a boundary. -/

/-- The integral differential `(a, b) ↦ 2 b`. -/
def ncD₁ : (ℤ_[2] × ℤ_[2]) →ₗ[ℤ_[2]] ℤ_[2] := (2 : ℤ_[2]) • LinearMap.snd ℤ_[2] ℤ_[2] ℤ_[2]

/-- Reduction of the middle term. -/
def ncρ₁ : (ℤ_[2] × ℤ_[2]) →ₛₗ[(PadicInt.toZMod : ℤ_[2] →+* ZMod 2)] (ZMod 2 × ZMod 2) where
  toFun x := (PadicInt.toZMod x.1, PadicInt.toZMod x.2)
  map_add' x y := by simp
  map_smul' r x := by simp [smul_eq_mul]

theorem ncρ₁_surjective : Function.Surjective ncρ₁ := fun y => by
  obtain ⟨a, ha⟩ := toZModSL_surjective y.1
  obtain ⟨b, hb⟩ := toZModSL_surjective y.2
  exact ⟨(a, b), Prod.ext ha hb⟩

/-- The integral data: `tr_R = fst` induces `H^m(C) ≅ ℤ_[2]`, `ρ₁` is onto, `ker toZModSL = (2)`,
the differentials commute with reduction, the traces are compatible; but `H^{m+1}(C) ≠ 0`. -/
theorem negativeControl_hypotheses :
    IsTopTraceIso (0 : PUnit.{1} →ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]) ncD₁ (LinearMap.fst ℤ_[2] ℤ_[2] ℤ_[2]) ∧
    Function.Surjective ncρ₁ ∧
    (∀ x, toZModSL x = 0 → ∃ w, x = (2 : ℤ_[2]) • w) ∧
    (∀ x, toZModSL (ncD₁ x) = (0 : ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2) (ncρ₁ x)) ∧
    (∀ z, (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)) (ncρ₁ z) =
      PadicInt.toZMod (LinearMap.fst ℤ_[2] ℤ_[2] ℤ_[2] z)) ∧
    ¬ (∀ w, (0 : ℤ_[2] →ₗ[ℤ_[2]] PUnit.{1}) w = 0 → ∃ v, ncD₁ v = w) := by
  refine ⟨⟨fun _ => by simp, ?_, ⟨(1, 0), by simp [ncD₁], rfl⟩⟩, ncρ₁_surjective, ?_, ?_,
    fun _ => rfl, ?_⟩
  · rintro ⟨a, b⟩ hz ha
    have hb : (2 : ℤ_[2]) * b = 0 := by simpa [ncD₁] using hz
    have hb' : b = 0 := (mul_eq_zero.mp hb).resolve_left two_ne_zero
    simp only [LinearMap.fst_apply] at ha
    exact ⟨PUnit.unit, by rw [ha, hb', LinearMap.zero_apply, Prod.mk_zero_zero]⟩
  · intro x hx
    obtain ⟨s, hs⟩ := exists_eq_two_mul_of_toZMod_eq_zero x hx
    exact ⟨s, by rw [hs, smul_eq_mul]⟩
  · intro x
    change PadicInt.toZMod (2 * x.2) = 0
    rw [map_mul, toZMod_two, zero_mul]
  · intro h
    obtain ⟨v, hv⟩ := h 1 rfl
    have h1 : (2 : ℤ_[2]) * v.2 = 1 := by simpa [ncD₁] using hv
    have h2 := congrArg (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) h1
    rw [map_mul, toZMod_two, zero_mul, map_one] at h2
    exact zero_ne_one h2

/-- The conclusion fails for the reduction of the negative-control complex: the cycle `(0, 1)` of
`(ZMod 2)²` has trace zero but is not a boundary. -/
theorem topTraceIso_fails_without_vanishing :
    ¬ IsTopTraceIso (0 : PUnit.{1} →ₗ[ZMod 2] ZMod 2 × ZMod 2)
      (0 : ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2) (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)) := by
  rintro ⟨-, h, -⟩
  obtain ⟨x, hx⟩ := h (0, 1) rfl rfl
  rw [LinearMap.zero_apply] at hx
  exact zero_ne_one (congrArg Prod.snd hx)

end Examples

end ZInQ.Contrib.RC53Assist.IntegralDuality
