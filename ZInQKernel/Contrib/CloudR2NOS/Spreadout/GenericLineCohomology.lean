/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the original line over the generic open

New glue (no vendored source in this file), at lane 6's request. It continues `GenericCohomologyField`,
which is unchanged.

Setting:
* `A₀ : Grp (Over (Spec K))`, the ORIGINAL group;
* `iV : V ≅ Spec K` (lane 5's `DVRGenericOpen` iso);
* `A_V := (Over.pullback iV.hom).mapGrp.obj A₀`;
* `L₀ : A₀.X.left.Modules`, the ORIGINAL line;
* `L_V := (Scheme.Modules.pullback (pullback.fst A₀.X.hom iV.hom)).obj L₀` (`pullbackLine`).

The literal model, checked by `rfl`: `A_V.X.left = pullback A₀.X.hom iV.hom` and
`A_V.X.hom = pullback.snd A₀.X.hom iV.hom` (`pullbackGroup_X_hom`). This is the definition of
`Over.pullback` and `Functor.mapGrp`, not an assumed caption.

Results:
* `finrankH_pullbackLine` / `eulerChar_pullbackLine`: the native W07 `K`-cohomology of `L_V`, with
  structure map `A_V.X.hom ≫ iV.hom`, equals the native W07 `K`-cohomology of the ORIGINAL `L₀`
  with structure map `A₀.X.hom`, in every degree, and likewise for the Euler characteristic.
  - The proof uses `pullback.condition` (`A_V.X.hom ≫ iV.hom = pullback.fst ≫ A₀.X.hom`).
  - `pullback.fst` is an isomorphism (`pullback_fst_iso_of_right_iso`, as `iV.hom` is one), so
    W07's `finrankH_pullback_of_isIso` applies.
  - No quasi-coherence or finiteness hypothesis is needed.
* `hFiber_genericPoint_originalLine` / `eulerCharFiber_genericPoint_originalLine` (convenience
  joins): combined with `hFiber_genericPoint_originalField`, at the LITERAL generic point of the
  stage DVR, `M.hFiber G.X.hom n η = L₀.finrankH K n` and `χ = L₀.eulerChar K`. The `β` here is
  exactly `GenericLineExtension`'s, for `A := A_V`, `L := L_V`. The qc/qs of `A_V.X.hom` are
  derived from those of `A₀.X.hom` (base change). Quasi-coherence of `L_V` is derived from that of
  `L₀` (W07 `isQuasicoherent_pullback`); `M`, `L₀` quasi-coherent are instance arguments.

No cohomology equality, positivity, nonzero `χ`, transition or Čech hypothesis is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericCohomologyField

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

section OriginalLine

variable {K : Type u} [Field K] {V : Scheme.{u}} (iV : V ≅ Spec (CommRingCat.of K))
  (A₀ : Grp (Over (Spec (CommRingCat.of K))))

/-- The literal model of the base-changed group: its structure map is `pullback.snd`. -/
theorem pullbackGroup_X_hom :
    ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom = pullback.snd A₀.X.hom iV.hom :=
  rfl

/-- The original line pulled back to the base-changed group (lane 6's `L_V`). -/
abbrev pullbackLine (L₀ : A₀.X.left.Modules) :
    ((Over.pullback iV.hom).mapGrp.obj A₀).X.left.Modules :=
  (Scheme.Modules.pullback (pullback.fst A₀.X.hom iV.hom)).obj L₀

/-- `finrankH` depends on the structure morphism only through its value. -/
theorem finrankH_congr_over {X : Scheme.{u}} (M : X.Modules) {a b : X ⟶ Spec (CommRingCat.of K)}
    (h : a = b) (n : ℕ) :
    (letI : X.Over (Spec (CommRingCat.of K)) := ⟨a⟩; M.finrankH K n) =
      (letI : X.Over (Spec (CommRingCat.of K)) := ⟨b⟩; M.finrankH K n) := by
  subst h
  rfl

/-- **The `K`-cohomology of `L_V` over the generic open is that of the ORIGINAL `L₀`.** -/
theorem finrankH_pullbackLine (L₀ : A₀.X.left.Modules) (n : ℕ) :
    (letI : ((Over.pullback iV.hom).mapGrp.obj A₀).X.left.Over (Spec (CommRingCat.of K)) :=
        ⟨((Over.pullback iV.hom).mapGrp.obj A₀).X.hom ≫ iV.hom⟩;
      (pullbackLine iV A₀ L₀).finrankH K n) =
      (letI : A₀.X.left.Over (Spec (CommRingCat.of K)) := ⟨A₀.X.hom⟩; L₀.finrankH K n) := by
  have hcond : ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom ≫ iV.hom =
      pullback.fst A₀.X.hom iV.hom ≫ A₀.X.hom := pullback.condition.symm
  exact (finrankH_congr_over (pullbackLine iV A₀ L₀) hcond n).trans
    (Scheme.Modules.finrankH_pullback_of_isIso (pullback.fst A₀.X.hom iV.hom) A₀.X.hom L₀ n)

/-- **The `K`-Euler characteristic of `L_V` is that of the ORIGINAL `L₀`.** -/
theorem eulerChar_pullbackLine (L₀ : A₀.X.left.Modules) :
    (letI : ((Over.pullback iV.hom).mapGrp.obj A₀).X.left.Over (Spec (CommRingCat.of K)) :=
        ⟨((Over.pullback iV.hom).mapGrp.obj A₀).X.hom ≫ iV.hom⟩;
      (pullbackLine iV A₀ L₀).eulerChar K) =
      (letI : A₀.X.left.Over (Spec (CommRingCat.of K)) := ⟨A₀.X.hom⟩; L₀.eulerChar K) := by
  simp only [Scheme.Modules.eulerChar, finrankH_pullbackLine iV A₀ L₀]

end OriginalLine

section Join

variable {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Bs]
  [IsDomain Bs] [Algebra O Bs] (hinj : Function.Injective (algebraMap O Bs))
  (V : (Spec (CommRingCat.of O)).Opens)
  (hV : ∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O)
  {K : Type u} [Field K] (iV : V.toScheme ≅ Spec (CommRingCat.of K))
  (G : Grp (Over (Spec (CommRingCat.of Bs)))) (A₀ : Grp (Over (Spec (CommRingCat.of K))))
  (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj
      ((Over.pullback iV.hom).mapGrp.obj A₀))

include hinj hV

/-- **Join: at the literal generic point of the stage DVR, the model's fibre cohomology is the
ORIGINAL line's `K`-cohomology, in every degree.** -/
theorem hFiber_genericPoint_originalLine [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A₀.X.hom] [QuasiSeparated A₀.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L₀ : A₀.X.left.Modules) [L₀.IsQuasicoherent]
    (β : (Scheme.Modules.pullback
        (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
        (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
          ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀))
    (n : ℕ) :
    M.hFiber G.X.hom n (genericPoint (Spec (CommRingCat.of Bs))) =
      (letI : A₀.X.left.Over (Spec (CommRingCat.of K)) := ⟨A₀.X.hom⟩; L₀.finrankH K n) := by
  haveI : QuasiCompact ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd A₀.X.hom iV.hom))
  haveI : QuasiSeparated ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd A₀.X.hom iV.hom))
  haveI : (pullbackLine iV A₀ L₀).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback (pullback.fst A₀.X.hom iV.hom)).obj L₀).IsQuasicoherent
  exact (hFiber_genericPoint_originalField hinj V hV G _ e iV M (pullbackLine iV A₀ L₀) β n).trans
    (finrankH_pullbackLine iV A₀ L₀ n)

/-- **Join, Euler characteristic.** -/
theorem eulerCharFiber_genericPoint_originalLine [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A₀.X.hom] [QuasiSeparated A₀.X.hom] (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L₀ : A₀.X.left.Modules) [L₀.IsQuasicoherent]
    (β : (Scheme.Modules.pullback
        (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
        (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
          ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀)) :
    M.eulerCharFiber G.X.hom (genericPoint (Spec (CommRingCat.of Bs))) =
      (letI : A₀.X.left.Over (Spec (CommRingCat.of K)) := ⟨A₀.X.hom⟩; L₀.eulerChar K) := by
  haveI : QuasiCompact ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd A₀.X.hom iV.hom))
  haveI : QuasiSeparated ((Over.pullback iV.hom).mapGrp.obj A₀).X.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd A₀.X.hom iV.hom))
  haveI : (pullbackLine iV A₀ L₀).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback (pullback.fst A₀.X.hom iV.hom)).obj L₀).IsQuasicoherent
  exact (eulerCharFiber_genericPoint_originalField hinj V hV G _ e iV M (pullbackLine iV A₀ L₀)
    β).trans (eulerChar_pullbackLine iV A₀ L₀)

end Join

end ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport
