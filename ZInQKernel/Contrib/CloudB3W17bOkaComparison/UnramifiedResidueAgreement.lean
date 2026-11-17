import ZInQKernel.Contrib.CloudB3W17bOkaComparison.FiniteTypeGermAgreement
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.UnramifiedStalkMaps

/-!
# Genuine unramified residue/germ agreement for regular-ring pullbacks

The algebra is finite type and formally unramified over its actual coordinate
base. Residue maps are local homomorphisms out of the actual source stalks.
The resulting regular sheaf pullback agreement is proved, not assumed.
No completeness, Henselianity, analytic-model compatibility or GAGA premise.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable {R B K : Type} [CommRing R] [CommRing B] [Field K]
variable [Algebra R B] [Algebra.FiniteType R B] [Algebra.FormallyUnramified R B]

/-- Actual residue and coordinate-base agreement imply equality of the real
regular-ring maps on one genuine source neighbourhood. -/
theorem unramified_residue_maps_eq_locally (Z : LocallyRingedSpace.{0})
    (f g : B →+* Z.presheaf.obj (op ⊤))
    (hb : f.comp (algebraMap R B) = g.comp (algebraMap R B)) (z : Z)
    (v : Z.presheaf.stalk z →+* K) [IsLocalHom v]
    (hv : ∀ b, v (Z.presheaf.Γgerm z (f b)) = v (Z.presheaf.Γgerm z (g b))) :
    ∃ (W : Opens Z) (_ : z ∈ W), ∀ b,
      (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (f b) =
        (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g b) := by
  let γ := (Z.presheaf.Γgerm z).hom
  have hbase : (γ.comp f).comp (algebraMap R B) = (γ.comp g).comp (algebraMap R B) :=
    congrArg (fun h => γ.comp h) hb
  have hvalue : v.comp (γ.comp f) = v.comp (γ.comp g) := RingHom.ext hv
  have H := unramified_local_ringMaps_ext (γ.comp f) (γ.comp g) hbase v hvalue
  exact finiteType_germ_maps_eq_locally Z f g hb z (fun b => RingHom.congr_fun H b)

/-- On the actual source sheaf, genuine pointwise residue agreement gives equality
of ALL regular-ring pullbacks, not merely equality of scalar values. -/
theorem unramified_residue_all_points_maps_ext (Z : LocallyRingedSpace.{0})
    (f g : B →+* Z.presheaf.obj (op ⊤))
    (hb : f.comp (algebraMap R B) = g.comp (algebraMap R B))
    (v : ∀ z : Z, Z.presheaf.stalk z →+* K) [∀ z, IsLocalHom (v z)]
    (hv : ∀ (z : Z) b, v z (Z.presheaf.Γgerm z (f b)) = v z (Z.presheaf.Γgerm z (g b))) : f = g := by
  apply RingHom.ext
  intro b
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤ (f b) (g b)
  intro z hz
  let γ := (Z.presheaf.Γgerm z).hom
  have hbase : (γ.comp f).comp (algebraMap R B) = (γ.comp g).comp (algebraMap R B) :=
    congrArg (fun h => γ.comp h) hb
  have hvalue : (v z).comp (γ.comp f) = (v z).comp (γ.comp g) := RingHom.ext (hv z)
  have H := unramified_local_ringMaps_ext (γ.comp f) (γ.comp g) hbase (v z) hvalue
  exact RingHom.congr_fun H b

end ZInQ.Contrib.CloudB3W17bOkaComparison
