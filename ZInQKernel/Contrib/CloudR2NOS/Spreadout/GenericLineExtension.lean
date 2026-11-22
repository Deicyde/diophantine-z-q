/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the invertible extension on lane 5's actual generic open

New glue (no vendored source in this file), at lane 6's request.

Lane 5's `GoodDescent.genericModelOfGroupIso p V G A e` (consumed read-only) uses:
* the stage map `p : Spec Bs ⟶ S`;
* the original generic open `V ⊆ S`;
* the stage group model `G` over the DVR `Bs`;
* the ORIGINAL group `A` over `V`;
* the PRESERVED generic group-object isomorphism
  `e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A`.

It gives the actual scheme map `q : G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V) ⟶ A.X.left` on the generic OPEN `W` of the
model.

`exists_extension_on_genericOpen`: for every invertible `L` on the ORIGINAL `A.X.left` there is an
invertible `M` on the model `G.X.left` with `(pullback W.ι).obj M ≅ (pullback q).obj L`, on exactly
that open. `M` is obtained directly from lane 3's frozen universe-`u` supplier
`InvertibleExtension.extension_of_ufd_stalks`, applied to the open immersion `W.ι` and the
invertible `q^* L` (source `IsInvertible.pullback`). So no comparison between the open generic
fibre and the `Spec(Frac Bs)` pullback is needed, and none is assumed. No `β`, `M`, `K` or `A`
replacement hypothesis is used. The model inputs are lane 6's `goodModel_isIntegral` and
`smoothDVR_uniqueFactorization_stalk`, and lane 3's `isNoetherian_goodModel`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.InvertibleExtension
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupInput

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.InvertibleExtension

local notation "SrcInvertible" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Extension from ANY open of a good model over a DVR. -/
theorem exists_extension_of_open {Bs : Type u} [CommRing Bs] [IsDomain Bs]
    [IsDiscreteValuationRing Bs] (G : Grp (Over (Spec (CommRingCat.of Bs))))
    [PkgI2.IsAbelianScheme G] (W : G.X.left.Opens) (LW : W.toScheme.Modules)
    (hLW : SrcInvertible LW) :
    ∃ M : G.X.left.Modules, SrcInvertible M ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ LW) := by
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsIntegral G.X.left := ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.goodModel_isIntegral G
  haveI : IsNoetherian G.X.left := isNoetherian_goodModel G
  exact extension_of_ufd_stalks
    (ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.smoothDVR_uniqueFactorization_stalk G.X.hom)
    W.ι LW hLW

/-- **The invertible extension on lane 5's actual generic open**, from an invertible sheaf on the
ORIGINAL `A.X.left`, through the ORIGINAL group isomorphism's scheme map `q`. -/
theorem exists_extension_on_genericOpen {Bs : Type u} [CommRing Bs] [IsDomain Bs]
    [IsDiscreteValuationRing Bs] {S : Scheme.{u}} (p : Spec (CommRingCat.of Bs) ⟶ S)
    (V : S.Opens) (G : Grp (Over (Spec (CommRingCat.of Bs)))) [PkgI2.IsAbelianScheme G]
    (A : Grp (Over V.toScheme))
    (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)
    (L : A.X.left.Modules) (hL : SrcInvertible L) :
    ∃ M : G.X.left.Modules, SrcInvertible M ∧
      Nonempty ((Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
        (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L) :=
  exists_extension_of_open G (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) _
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback
      (GoodDescent.genericModelOfGroupIso p V G A e).q hL)

end ZInQ.Contrib.CloudR2NOS.Spreadout.InvertibleExtension
