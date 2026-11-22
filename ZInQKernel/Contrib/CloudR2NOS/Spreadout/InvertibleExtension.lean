/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): extending an invertible sheaf from the generic fibre

New glue (no vendored source in this file). Written at lane 6's lead-approved request.

`IsInvertible` here is the canonical source predicate
`ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible`
(`Def_AlgebraicGeometry_RelativePicardFunctor`): every point has an open neighbourhood on which
the module is isomorphic to the unit.

* `extension_of_ufd_stalks`, at universe `u`: for an integral Noetherian scheme `X` with factorial
  stalks and an open immersion `j : U ⟶ X`, every invertible `𝓛U` on `U` extends to an invertible
  `𝓛` on `X` with `j^* 𝓛 ≅ 𝓛U`.
  - The FLT source states this only for `Scheme.{0}` (anthropics/fermats-last-theorem@6e837e75,
    `S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk`,
    Apache-2.0). Its Noetherian-induction proof is RE-WRITTEN here at universe `u`.
  - It uses the three universe-polymorphic source helpers, read-only from lane 4's canonical port:
    1. extension to the range with local triviality;
    2. trivialisation near a factorial stalk;
    3. gluing along `W ⊓ V`.
  - Induction: a maximal open `W ⊇ range j` carrying a locally trivial extension exists
    (Noetherian). If `z ∉ W`, glue a trivialisation near `z` to obtain a strictly larger `W ⊔ V`.
* `isOpenImmersion_specMap_fractionRing` / `isOpenImmersion_genericFibre`: for a DVR `R` with
  fraction field `K`, `Spec K ⟶ Spec R` is the open immersion of `D(ϖ)`, so is the inclusion of
  the generic fibre of any `X ⟶ Spec R`.
* `exists_invertible_extension`: for the ORIGINAL good model `G` over an arbitrary DVR
  (`PkgI2.IsAbelianScheme`, any characteristic, universe `u`), every invertible `L` on the actual
  generic fibre `pullback G.X.hom (Spec K ⟶ Spec R)` extends to an invertible
  `M : G.X.left.Modules` with `β : (pullback (generic-fibre inclusion)).obj M ≅ L`.
  - Integrality of `G.X.left` and factorial stalks come from lane 6's proved `goodModel_isIntegral`
    and `smoothDVR_uniqueFactorization_stalk`.
  - Noetherianity comes from properness and finite type over the DVR.
  - No `M`-extension, Picard, cube, descent, order-one or transition-unit hypothesis is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericField
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleRegular
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleGoodGeometry

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.InvertibleExtension

local notation "SrcInvertible" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Local triviality of `𝓛` on `W` (the source's `LocTriv`). -/
def LocTriv {X : Scheme.{u}} (𝓛 : X.Modules) (W : X.Opens) : Prop :=
  ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

theorem isInvertible_of_locTriv_top {X : Scheme.{u}} {𝓛 : X.Modules} (h : LocTriv 𝓛 ⊤) :
    SrcInvertible 𝓛 :=
  ⟨fun x => by obtain ⟨U, hxU, -, hU⟩ := h x trivial; exact ⟨U, hxU, hU⟩⟩

theorem nonempty_pullback_iso_of_pullback_ι_iso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.Opens) (hW : j.opensRange ≤ W) {𝓛 𝓛' : X.Modules}
    (e : (Scheme.Modules.pullback W.ι).obj 𝓛' ≅ (Scheme.Modules.pullback W.ι).obj 𝓛) :
    Nonempty ((Scheme.Modules.pullback j).obj 𝓛' ≅ (Scheme.Modules.pullback j).obj 𝓛) := by
  have hr : Set.range j.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hW
  let j' : U ⟶ W := IsOpenImmersion.lift W.ι j hr
  have hj : j' ≫ W.ι = j := IsOpenImmersion.lift_fac W.ι j hr
  exact ⟨((Scheme.Modules.pullbackCongr hj).app 𝓛').symm ≪≫
    ((Scheme.Modules.pullbackComp j' W.ι).app 𝓛').symm ≪≫
    (Scheme.Modules.pullback j').mapIso e ≪≫ (Scheme.Modules.pullbackComp j' W.ι).app 𝓛 ≪≫
    (Scheme.Modules.pullbackCongr hj).app 𝓛⟩

/-- **Extension of invertible sheaves along an open immersion into an integral Noetherian scheme
with factorial stalks**, at universe `u` (the source states it for `Scheme.{0}`). -/
theorem extension_of_ufd_stalks {X U : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hfact : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (j : U ⟶ X) [IsOpenImmersion j] (𝓛U : U.Modules) (h𝓛U : SrcInvertible 𝓛U) :
    ∃ 𝓛 : X.Modules, SrcInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ 𝓛U) := by
  classical
  let S : Set X.Opens := fun W => j.opensRange ≤ W ∧
    ∃ 𝓛 : X.Modules, LocTriv 𝓛 W ∧ Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ 𝓛U)
  have hS₀ : j.opensRange ∈ S := by
    obtain ⟨𝓛₀, h₀, e₀⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_locallyTrivial_opensRange_nonempty_pullback_iso
        j h𝓛U
    exact ⟨le_rfl, 𝓛₀, h₀, e₀⟩
  have hwf : WellFounded ((· > ·) : X.Opens → X.Opens → Prop) := by
    have : NoetherianSpace X := inferInstance
    exact wellFounded_gt
  obtain ⟨W, ⟨hjW, 𝓛, h𝓛, ⟨e𝓛⟩⟩, hmax⟩ := hwf.has_min S ⟨_, hS₀⟩
  by_cases htop : W = ⊤
  · subst htop
    exact ⟨𝓛, isInvertible_of_locTriv_top h𝓛, ⟨e𝓛⟩⟩
  · obtain ⟨z, hz⟩ : ∃ z : X, z ∉ W := by
      by_contra h
      push Not at h
      exact htop (top_unique fun x _ => h x)
    obtain ⟨V, hzV, ⟨eV⟩⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
        W h𝓛 z (hfact z)
    obtain ⟨𝓛', h𝓛', ⟨e'⟩⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
        W V h𝓛 ⟨eV⟩
    have hmem : W ⊔ V ∈ S := by
      refine ⟨hjW.trans le_sup_left, 𝓛', h𝓛', ?_⟩
      obtain ⟨e''⟩ := nonempty_pullback_iso_of_pullback_ι_iso j W hjW e'
      exact ⟨e'' ≪≫ e𝓛⟩
    have hlt : W ⊔ V > W :=
      lt_of_le_of_ne le_sup_left (fun h => hz (h.symm ▸ (Opens.mem_sup.2 (Or.inr hzV))))
    exact absurd (hmax _ hmem) (not_not.2 hlt)

/-- For a DVR, `Spec K ⟶ Spec R` is an open immersion (it is `D(ϖ)`). -/
theorem isOpenImmersion_specMap_fractionRing {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.isLocalization_powers_of_dvr K hϖ.ne_zero hϖ.not_isUnit
  exact IsOpenImmersion.of_isLocalization ϖ

/-- The inclusion of the generic fibre of a scheme over a DVR is an open immersion. -/
theorem isOpenImmersion_genericFibre {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    IsOpenImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  haveI := isOpenImmersion_specMap_fractionRing (R := R) (K := K)
  infer_instance

/-- The total space of a good model over a DVR is Noetherian. -/
theorem isNoetherian_goodModel {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G] :
    IsNoetherian G.X.left := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  haveI : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  exact {}

/-- **Every invertible sheaf on the actual generic fibre of the ORIGINAL good model over an
arbitrary DVR extends to an invertible sheaf on the model**, with the generic restriction iso `β`. -/
theorem exists_invertible_extension {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (L : (pullback G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Modules)
    (hL : SrcInvertible L) :
    ∃ M : G.X.left.Modules, SrcInvertible M ∧
      Nonempty ((Scheme.Modules.pullback
        (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M ≅ L) := by
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsIntegral G.X.left := ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.goodModel_isIntegral G
  haveI : IsNoetherian G.X.left := isNoetherian_goodModel G
  haveI := isOpenImmersion_genericFibre (R := R) (K := K) G.X.hom
  exact extension_of_ufd_stalks
    (ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.smoothDVR_uniqueFactorization_stalk G.X.hom)
    (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) L hL

end ZInQ.Contrib.CloudR2NOS.Spreadout.InvertibleExtension
