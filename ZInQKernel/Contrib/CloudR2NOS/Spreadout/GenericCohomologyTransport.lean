/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): generic-fibre cohomology transport

New glue (no vendored source in this file), at the lead's and lane 6's request.

Setting (lane 5's `GoodDescent.genericModelOfGroupIso`, consumed read-only):
* `p : Spec Bs ⟶ S`, the original generic open `V ⊆ S`;
* the stage group model `G` over `Spec Bs` and the ORIGINAL group `A` over `V`;
* the preserved generic group-object isomorphism `e`;
* `q : f⁻¹(p⁻¹V) ⟶ A.X.left` with lane 5's cartesian square
  `IsPullback q (f ∣_ p⁻¹V) A.X.hom (p ∣_ V)`, where `f := G.X.hom`;
* `M` on the model, `L` on the ORIGINAL `A.X.left`, and lane 3's
  `β : (pullback (f⁻¹(p⁻¹V)).ι).obj M ≅ (pullback q).obj L` (`GenericLineExtension`).

`hFiber_transport`: for every point `t` of `p⁻¹V` and EVERY degree `n`,
`M.hFiber f n t = L.hFiber A.X.hom n ((p ∣_ V) t)`. These are the W07 native fibre-cohomology
dimensions (`Scheme.Modules.hFiber`, W07 sheaf cohomology `H` = Ext from the constant sheaf).
The proof chains three steps:
1. W07's `hFiber_pullback_of_isPullback` on the open-restriction square
   `(isPullback_morphismRestrict f (p⁻¹V)).flip`;
2. `hFiber_congr β`;
3. `hFiber_pullback_of_isPullback` on lane 5's cartesian square. Through W07's
   `finrankH_pullback`, this is the actual flat base change along the original field extension.

Consequently `eulerCharFiber_transport` gives the same equality for the W07 native Euler
characteristics, and `hFiber_genericPoint` specialises to the literal generic point of `Spec Bs`.
No cohomology equality, positivity, nonzero `χ`, transition or Čech hypothesis is used. Both
quasi-coherence hypotheses follow from invertibility (`IsInvertible.isLocallyFree` and Mathlib's
`IsLocallyFree → IsQuasicoherent`). The only geometric hypotheses are quasi-compactness and
quasi-separatedness of the two structure maps.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupInput

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

section Transport

variable {Bs : Type u} [CommRing Bs] {S : Scheme.{u}} (p : Spec (CommRingCat.of Bs) ⟶ S)
  (V : S.Opens) (G : Grp (Over (Spec (CommRingCat.of Bs)))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- Fibre cohomology of the restriction to the preimage of an open of the base. -/
theorem hFiber_restrict [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom] (M : G.X.left.Modules)
    [M.IsQuasicoherent] (U : (Spec (CommRingCat.of Bs)).Opens) (n : ℕ) (t : U.toScheme) :
    ((Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ U).ι).obj M).hFiber (G.X.hom ∣_ U) n t =
      M.hFiber G.X.hom n (U.ι.base t) :=
  Scheme.Modules.hFiber_pullback_of_isPullback G.X.hom M U.ι (G.X.hom ⁻¹ᵁ U).ι (G.X.hom ∣_ U)
    (isPullback_morphismRestrict G.X.hom U).flip n t

/-- Fibre cohomology along lane 5's actual generic cartesian square. -/
theorem hFiber_genericModel [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom]
    (L : A.X.left.Modules) [L.IsQuasicoherent] (n : ℕ) (t : (p ⁻¹ᵁ V).toScheme) :
    ((Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L).hFiber
        (G.X.hom ∣_ (p ⁻¹ᵁ V)) n t = L.hFiber A.X.hom n ((p ∣_ V).base t) :=
  Scheme.Modules.hFiber_pullback_of_isPullback A.X.hom L (p ∣_ V)
    (GoodDescent.genericModelOfGroupIso p V G A e).q (G.X.hom ∣_ (p ⁻¹ᵁ V))
    (GoodDescent.genericModelOfGroupIso p V G A e).cartesian n t

/-- **Generic fibre cohomology transport, all degrees.** -/
theorem hFiber_transport [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (n : ℕ) (t : (p ⁻¹ᵁ V).toScheme) :
    M.hFiber G.X.hom n ((p ⁻¹ᵁ V).ι.base t) = L.hFiber A.X.hom n ((p ∣_ V).base t) := by
  rw [← hFiber_restrict G M (p ⁻¹ᵁ V) n t, Scheme.Modules.hFiber_congr β,
    hFiber_genericModel p V G A e L n t]

/-- **Generic fibre Euler characteristic transport.** -/
theorem eulerCharFiber_transport [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (t : (p ⁻¹ᵁ V).toScheme) :
    M.eulerCharFiber G.X.hom ((p ⁻¹ᵁ V).ι.base t) = L.eulerCharFiber A.X.hom ((p ∣_ V).base t) := by
  simp only [Scheme.Modules.eulerCharFiber, hFiber_transport p V G A e M L β]

/-- **At the literal generic point of `Spec Bs`** (which lies in `p⁻¹V`). -/
theorem hFiber_genericPoint [IsDomain Bs] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (hη : genericPoint (Spec (CommRingCat.of Bs)) ∈ p ⁻¹ᵁ V) (n : ℕ) :
    M.hFiber G.X.hom n (genericPoint (Spec (CommRingCat.of Bs))) =
      L.hFiber A.X.hom n ((p ∣_ V).base ⟨_, hη⟩) :=
  hFiber_transport p V G A e M L β n ⟨_, hη⟩

/-- Euler characteristic at the literal generic point. -/
theorem eulerCharFiber_genericPoint [IsDomain Bs] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (hη : genericPoint (Spec (CommRingCat.of Bs)) ∈ p ⁻¹ᵁ V) :
    M.eulerCharFiber G.X.hom (genericPoint (Spec (CommRingCat.of Bs))) =
      L.eulerCharFiber A.X.hom ((p ∣_ V).base ⟨_, hη⟩) :=
  eulerCharFiber_transport p V G A e M L β ⟨_, hη⟩

end Transport

end ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport
