import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Traces agreeing on cycles give homotopic adjoints

Let `T` be a complex over a ring `R` that is injective as a module over itself, for example
a field. Let `tr₁` and `tr₂` be two degree-`m` traces on `T` that agree on degree-`m` cocycles.
Then their difference factors through the differential: `tr₁ − tr₂ = h ∘ d` for a linear form
`h` on `T^{m+1}`. The form `h` is obtained by extending from the image of `d` using
injectivity of `R`. No agreement of the two traces off cocycles is assumed.

For any pairing `P : A × B → T`, the adjoints `A → Hom(B, R)[−m]` of the two traces are then
chain homotopic. The homotopy is `x ↦ (y ↦ h (P x y))`, so the two adjoints induce the same
maps on cohomology, and one is a quasi-isomorphism exactly when the other is.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- A field is injective as a module over itself (Baer's criterion and extension from subspaces). -/
theorem moduleInjective_self_of_field (k : Type) [Field k] : Module.Injective k k :=
  Module.Baer.injective fun I g => by
    obtain ⟨g', hg'⟩ := LinearMap.exists_extend g
    exact ⟨g', fun x hx => LinearMap.congr_fun hg' ⟨x, hx⟩⟩

variable {R : Type} [CommRing R]

section Factor

variable {T : GCx R} (m : ℤ) (tr₁ tr₂ : T.X m →ₗ[R] R)

/-- Two traces that agree on cocycles differ by a form composed with the differential. -/
theorem exists_trace_sub_eq_comp_d [Module.Injective R R]
    (hcyc : ∀ z : T.X m, T.d m (m + 1) rfl z = 0 → tr₁ z = tr₂ z) :
    ∃ h : T.X (m + 1) →ₗ[R] R, ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x) := by
  let δ : T.X m →ₗ[R] R := tr₁ - tr₂
  let d := T.d m (m + 1) rfl
  have hker : LinearMap.ker d ≤ LinearMap.ker δ := by
    intro z hz
    change tr₁ z - tr₂ z = 0
    rw [hcyc z hz, sub_self]
  let g : LinearMap.range d →ₗ[R] R :=
    ((LinearMap.ker d).liftQ δ hker).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨h, hh⟩ := Module.Injective.out (LinearMap.range d).subtype
    (Submodule.injective_subtype _) g
  refine ⟨h, fun x => ?_⟩
  have h1 := hh ⟨d x, LinearMap.mem_range_self d x⟩
  change h (d x) = g ⟨d x, _⟩ at h1
  rw [h1]
  change δ x = ((LinearMap.ker d).liftQ δ hker) (d.quotKerEquivRange.symm ⟨d x, _⟩)
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Factor

section Adjoint

variable {A B T : GCx R} (P : GPair A B T) (m : ℤ) (tr₁ tr₂ : T.X m →ₗ[R] R)
  (htr₁ : ∀ z, tr₁ (T.d (m - 1) m (by omega) z) = 0)
  (htr₂ : ∀ z, tr₂ (T.d (m - 1) m (by omega) z) = 0)
  (h : T.X (m + 1) →ₗ[R] R)

/-- The homotopy component `A^i → Hom(B^{m−j}, R)` for `j + 1 = i`, `x ↦ (y ↦ h (x ∪ y))`. -/
def traceHomotopyFun (i j : ℤ) (hij : j + 1 = i) : A.X i →ₗ[R] (dualCx B m).X j :=
  (P.P i (m - j) (m + 1) (by omega)).compr₂ h

theorem traceHomotopyFun_apply (i j : ℤ) (hij : j + 1 = i) (x : A.X i) (y : B.X (m - j)) :
    asDual (traceHomotopyFun P m h i j hij x) y = h (P.P i (m - j) (m + 1) (by omega) x y) :=
  rfl

/-- The homotopy identity in relation-indexed form:
`adj₁ x − adj₂ x = d (H x) + H (d x)`. -/
theorem adjFun_sub_eq (hh : ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x)) (i i₀ i₁ : ℤ) (h₀ : i₀ + 1 = i) (h₁ : i + 1 = i₁) (x : A.X i) :
    adjFun P m tr₁ i i rfl x - adjFun P m tr₂ i i rfl x =
      (dualCx B m).d i₀ i h₀ (traceHomotopyFun P m h i i₀ h₀ x) +
        traceHomotopyFun P m h i₁ i h₁ (A.d i i₁ h₁ x) := by
  subst h₀ h₁
  refine dualCx_ext fun y => ?_
  have hl := P.leib (i₀ + 1) (i₀ + 1 + 1) (m - (i₀ + 1)) (m - i₀) m (m + 1) (by omega) rfl
    (by omega) rfl x y
  change tr₁ (P.P (i₀ + 1) (m - (i₀ + 1)) m _ x y) - tr₂ (P.P (i₀ + 1) (m - (i₀ + 1)) m _ x y) =
    (-(sgn i₀)) • h (P.P (i₀ + 1) (m - i₀) (m + 1) _ x (B.d (m - (i₀ + 1)) (m - i₀) _ y)) +
      h (P.P (i₀ + 1 + 1) (m - (i₀ + 1)) (m + 1) _ (A.d (i₀ + 1) (i₀ + 1 + 1) rfl x) y)
  rw [hh, hl, map_add, map_zsmul, add_comm]
  congr 1
  congr 1
  simp only [sgn, Int.negOnePow_succ, Units.val_neg]

/-- The degreewise homotopy maps, zero off the relation. -/
def traceHomotopyHom (i j : ℤ) : A.toCC.X i ⟶ (dualCx B m).toCC.X j :=
  if hij : j + 1 = i then ModuleCat.ofHom (traceHomotopyFun P m h i j hij) else 0

/-- **The adjoints of two traces agreeing on cocycles are chain homotopic.** -/
def adjHomHomotopy (hh : ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x)) :
    Homotopy (GHom.toCC (adjHom P m tr₁ htr₁)) (GHom.toCC (adjHom P m tr₂ htr₂)) where
  hom := traceHomotopyHom P m h
  zero i j hij := by
    have hn : ¬ j + 1 = i := hij
    simp only [traceHomotopyHom, hn, ↓reduceDIte]
  comm i := by
    have hd1 : (traceHomotopyHom P m h (i + 1) i) =
        ModuleCat.ofHom (traceHomotopyFun P m h (i + 1) i rfl) := dite_eq_left rfl
    have hd0 : (traceHomotopyHom P m h i (i - 1)) =
        ModuleCat.ofHom (traceHomotopyFun P m h i (i - 1) (by omega)) :=
      dite_eq_left (show i - 1 + 1 = i by omega)
    rw [dNext_eq (traceHomotopyHom P m h) (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq (traceHomotopyHom P m h) (show (ComplexShape.up ℤ).Rel (i - 1) i by simp),
      hd1, hd0]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have key := adjFun_sub_eq P m tr₁ tr₂ h hh i (i - 1) (i + 1) (by omega) rfl x
    rw [sub_eq_iff_eq_add] at key
    rw [ModuleCat.hom_add, ModuleCat.hom_add, LinearMap.add_apply, LinearMap.add_apply]
    change adjFun P m tr₁ i i rfl x =
      traceHomotopyFun P m h (i + 1) i rfl ((A.toCC.d i (i + 1)).hom x) +
        (show (dualCx B m).X i from
          ((dualCx B m).toCC.d (i - 1) i).hom (traceHomotopyFun P m h i (i - 1) (by omega) x)) +
          adjFun P m tr₂ i i rfl x
    erw [GCx.toCC_d_hom A i (i + 1) rfl x,
      GCx.toCC_d_hom (dualCx B m) (i - 1) i (by omega)]
    change adjFun P m tr₁ i i rfl x =
      traceHomotopyFun P m h (i + 1) i rfl (A.d i (i + 1) rfl x) +
        (dualCx B m).d (i - 1) i (by omega) (traceHomotopyFun P m h i (i - 1) (by omega) x) +
          adjFun P m tr₂ i i rfl x
    rw [key]
    abel

/-- The two adjoints induce the same maps on cohomology. -/
theorem adjHom_homologyMap_eq (hh : ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x))
    (n : ℤ) :
    HomologicalComplex.homologyMap (GHom.toCC (adjHom P m tr₁ htr₁)) n =
      HomologicalComplex.homologyMap (GHom.toCC (adjHom P m tr₂ htr₂)) n :=
  (adjHomHomotopy P m tr₁ tr₂ htr₁ htr₂ h hh).homologyMap_eq n

/-- One adjoint is a quasi-isomorphism exactly when the other is. -/
theorem adjHom_quasiIso_iff (hh : ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x)) :
    QuasiIso (GHom.toCC (adjHom P m tr₁ htr₁)) ↔ QuasiIso (GHom.toCC (adjHom P m tr₂ htr₂)) := by
  simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap,
    adjHom_homologyMap_eq P m tr₁ tr₂ htr₁ htr₂ h hh]

end Adjoint

/-- **Traces agreeing on cocycles have homotopic adjoints** (over a self-injective ring). -/
theorem adjHom_quasiIso_iff_of_eq_on_cycles [Module.Injective R R] {A B T : GCx R}
    (P : GPair A B T) (m : ℤ) (tr₁ tr₂ : T.X m →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ (T.d (m - 1) m (by omega) z) = 0)
    (htr₂ : ∀ z, tr₂ (T.d (m - 1) m (by omega) z) = 0)
    (hcyc : ∀ z : T.X m, T.d m (m + 1) rfl z = 0 → tr₁ z = tr₂ z) :
    Nonempty (Homotopy (GHom.toCC (adjHom P m tr₁ htr₁)) (GHom.toCC (adjHom P m tr₂ htr₂))) ∧
      (QuasiIso (GHom.toCC (adjHom P m tr₁ htr₁)) ↔
        QuasiIso (GHom.toCC (adjHom P m tr₂ htr₂))) := by
  obtain ⟨h, hh⟩ := exists_trace_sub_eq_comp_d m tr₁ tr₂ hcyc
  exact ⟨⟨adjHomHomotopy P m tr₁ tr₂ htr₁ htr₂ h hh⟩,
    adjHom_quasiIso_iff P m tr₁ tr₂ htr₁ htr₂ h hh⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
