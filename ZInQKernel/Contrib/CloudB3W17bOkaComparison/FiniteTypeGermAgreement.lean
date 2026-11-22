import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.FiniteType

/-!
# Finite-type regular-ring maps that agree on germs agree on a common neighbourhood

The common neighbourhood is obtained from actual finite algebra generators and
the genuine structure-sheaf germ colimit.  It does not assume a common local
model or an algebraic F/H witness.  This is the finite-generation step needed
after actual unramified local-spectrum uniqueness.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Finite algebra generators turn equality of all germs into equality of the actual
regular-ring pullbacks on one genuine open neighbourhood. -/
theorem finiteType_germ_maps_eq_locally
    {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (Z : LocallyRingedSpace)
    (f g : B →+* Z.presheaf.obj (op ⊤))
    (hb : f.comp (algebraMap R B) = g.comp (algebraMap R B)) (z : Z)
    (hg : ∀ b, Z.presheaf.Γgerm z (f b) = Z.presheaf.Γgerm z (g b)) :
    ∃ (W : Opens Z) (_ : z ∈ W), ∀ b,
      (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (f b) =
        (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g b) := by
  classical
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := R) (A := B)
  have hlocal : ∀ b : S, ∃ (U : Opens Z) (_ : z ∈ U) (i₁ i₂ : U ⟶ ⊤),
      (Z.presheaf.map i₁.op).hom (f b.1) = (Z.presheaf.map i₂.op).hom (g b.1) := fun b =>
    Z.presheaf.germ_eq (U := ⊤) (V := ⊤) z trivial trivial (f b.1) (g b.1) (hg b.1)
  choose U hzU i₁ i₂ heq using hlocal
  let W : Opens Z := ⟨⋂ b : S, (U b : Set Z), isOpen_iInter_of_finite fun b => (U b).isOpen⟩
  have hzW : z ∈ W := Set.mem_iInter.mpr hzU
  have hWU (b : S) : W ≤ U b := fun _ h => Set.mem_iInter.mp h b
  let ρ := (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  have hgen (b : S) : ρ (f b.1) = ρ (g b.1) := by
    have H := congrArg (Z.presheaf.map (homOfLE (hWU b)).op).hom (heq b)
    exact (Z.map_map_apply (hWU b) (i₁ b).le le_top (f b.1)).symm.trans
      (H.trans (Z.map_map_apply (hWU b) (i₂ b).le le_top (g b.1)))
  let fW : B →+* Z.presheaf.obj (op W) := ρ.comp f
  let gW : B →+* Z.presheaf.obj (op W) := ρ.comp g
  letI : Algebra R (Z.presheaf.obj (op W)) := (fW.comp (algebraMap R B)).toAlgebra
  let fa : B →ₐ[R] Z.presheaf.obj (op W) := ⟨fW, fun _ => rfl⟩
  let ga : B →ₐ[R] Z.presheaf.obj (op W) :=
    ⟨gW, fun r => (congrArg ρ (RingHom.congr_fun hb r)).symm⟩
  have hall : fa = ga := AlgHom.ext_of_adjoin_eq_top hS fun b hb => hgen ⟨b, hb⟩
  exact ⟨W, hzW, fun b => AlgHom.congr_fun hall b⟩

end ZInQ.Contrib.CloudB3W17bOkaComparison
