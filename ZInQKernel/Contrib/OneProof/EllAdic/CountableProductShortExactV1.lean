import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private abbrev productShortFirst (S : ℕ → ShortComplex C) := fun n => (S n).X₁
private abbrev productShortMiddle (S : ℕ → ShortComplex C) := fun n => (S n).X₂
private abbrev productShortLast (S : ℕ → ShortComplex C) := fun n => (S n).X₃

variable [HasLimitsOfShape (Discrete ℕ) C]

/-- The product short complex, with each of its two arrows the actual product map. -/
noncomputable def countableProductShortComplex (S : ℕ → ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (Limits.Pi.map (f := productShortFirst S) (g := productShortMiddle S) (fun n => (S n).f))
    (Limits.Pi.map (f := productShortMiddle S) (g := productShortLast S) (fun n => (S n).g)) (by
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Pi.map_π, Pi.map_π_assoc, (S n).zero, Limits.comp_zero,
        Limits.zero_comp])

/-- The component projections are morphisms of those same short complexes. -/
noncomputable def countableProductShortComplexProjection (S : ℕ → ShortComplex C) (n : ℕ) :
    countableProductShortComplex S ⟶ S n where
  τ₁ := Pi.π (productShortFirst S) n
  τ₂ := Pi.π (productShortMiddle S) n
  τ₃ := Pi.π (productShortLast S) n
  comm₁₂ := (Pi.map_π (fun n => (S n).f) n).symm
  comm₂₃ := (Pi.map_π (fun n => (S n).g) n).symm

/-- For countable exact products, a product of short exact sequences is
short exact on the literal product objects and product maps. -/
theorem countableProductShortComplex_shortExact [HasExactLimitsOfShape (Discrete ℕ) C]
    (S : ℕ → ShortComplex C) (hS : ∀ n, (S n).ShortExact) :
    (countableProductShortComplex S).ShortExact := by
  let A := Discrete.functor (productShortFirst S)
  let B := Discrete.functor (productShortMiddle S)
  let D := Discrete.functor (productShortLast S)
  let α : A ⟶ B := Discrete.natTrans (fun d => (S d.as).f)
  let β : B ⟶ D := Discrete.natTrans (fun d => (S d.as).g)
  have hz : α ≫ β = 0 := by
    apply NatTrans.ext
    funext d
    exact (S d.as).zero
  let liftTo (U : Discrete ℕ ⥤ C) (k : B ⟶ U) (hk : α ≫ k = 0) (d : Discrete ℕ) :=
    CokernelCofork.IsColimit.desc' (hS d.as).gIsCokernel (k.app d)
      (congrArg (fun f => NatTrans.app f d) hk)
  have hcolim : IsColimit (CokernelCofork.ofπ β hz) :=
    CokernelCofork.IsColimit.ofπ β hz (fun k hk => Discrete.natTrans (fun d => (liftTo _ k hk d).1))
      (by
        intro U k hk
        apply NatTrans.ext
        funext d
        exact (liftTo U k hk d).2)
      (by
        intro U k hk m hm
        apply NatTrans.ext
        funext d
        have : Epi (S d.as).g := (hS d.as).epi_g
        apply (cancel_epi (S d.as).g).1
        exact (congrArg (fun f => NatTrans.app f d) hm).trans (liftTo U k hk d).2.symm)
  let P := countableProductShortComplex S
  have hP : Nonempty (IsColimit (CokernelCofork.ofπ P.g P.zero)) :=
    ⟨CokernelCofork.mapIsColimit _ hcolim (lim (J := Discrete ℕ) (C := C))⟩
  obtain ⟨he, hep⟩ := (P.exact_and_epi_g_iff_g_is_cokernel).2 hP
  let : ∀ n, Mono ((S n).f) := fun n => (hS n).mono_f
  have hm : Mono P.f := by
    change Mono (Limits.Pi.map (fun n => (S n).f))
    infer_instance
  exact ShortComplex.ShortExact.mk' he hm hep

end RC53.EllAdic
