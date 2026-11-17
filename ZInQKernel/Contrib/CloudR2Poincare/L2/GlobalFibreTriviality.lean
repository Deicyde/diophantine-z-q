import ZInQKernel.Contrib.CloudR2Poincare.L2.FibreRestriction
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedClosedLocus

/-!
# Global residue-fibre triviality locus

The native affine closed loci agree on overlaps through actual isomorphisms
of residue fibres. Their closedness therefore glues over an affine cover of
the parameter scheme. The resulting global closed subset is given its actual
radical reduced scheme structure. No global seesaw or Picard-triviality Fact
is used: classification here is only by residue-fibre classes/image containment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Topology

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- The literal global set of points where the actual residue-fibre class is trivial. -/
def fibrePicardTrivialitySet {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Pic) : Set Y :=
  {y | Scheme.Pic.map (f.fiberι y) L = 1}

/-- On an affine open chart, the global predicate is exactly the native affine
fibre-triviality predicate for the actual pullback bundle. -/
theorem isClosed_preimage_fibrePicardTriviality_affine
    {X Y : Scheme.{u}} (R : Type u) [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (L : X.Pic) (g : Spec (.of R) ⟶ Y) [IsOpenImmersion g] :
    IsClosed (g ⁻¹' fibrePicardTrivialitySet f L) := by
  obtain ⟨M, hM, hrep⟩ := Scheme.Pic.exists_mk_eq L
  letI : M.IsInvertible := hM
  let M' := (Scheme.Modules.pullback (pullback.fst f g)).obj M
  have hc := L1.isClosed_fibrePicardClass_trivial R (pullback.snd f g) M'
  convert hc using 1
  ext u
  change Scheme.Pic.map (f.fiberι (g u)) L = 1 ↔
    Scheme.Pic.map ((pullback.snd f g).fiberι u) (Scheme.Pic.mk M') = 1
  have hb := fibrePicardClass_open_baseChange_iff (IsPullback.of_hasPullback f g) L u
  simpa only [← hrep, Scheme.Pic.map_mk] using hb.symm

/-- **Global closedness**, obtained by genuine compatibility of the affine
closed loci. This does not say that the whole family is trivial on this locus. -/
theorem isClosed_fibrePicardTrivialitySet
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) :
    IsClosed (fibrePicardTrivialitySet f L) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨i, u, hu⟩ := Y.affineCover.exists_eq y
  let Xi := Y.affineCover.X i
  let R := Γ(Xi, ⊤)
  let g : Spec R ⟶ Y := Xi.isoSpec.inv ≫ Y.affineCover.f i
  let u' : Spec R := Xi.isoSpec.hom u
  have hu' : g u' = y := by
    dsimp only [g, u']
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    exact hu
  letI : IsLocallyNoetherian Xi := LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian (⟨⊤, isAffineOpen_top Xi⟩ : Xi.affineOpens)
  have hc := isClosed_preimage_fibrePicardTriviality_affine R f L g
  have hopen : IsOpen (g '' (g ⁻¹' fibrePicardTrivialitySet f L)ᶜ) :=
    g.isOpenMap _ hc.isOpen_compl
  have hmem : y ∈ g '' (g ⁻¹' fibrePicardTrivialitySet f L)ᶜ := by
    refine ⟨u', ?_, hu'⟩
    simpa only [Set.mem_compl_iff, Set.mem_preimage, hu'] using hy
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) (by
    rintro z ⟨v, hv, rfl⟩
    exact hv)

/-- The global closed subset, with its literal residue-fibre definition. -/
def globalFibreTrivialityClosed
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) : Closeds Y :=
  ⟨fibrePicardTrivialitySet f L, isClosed_fibrePicardTrivialitySet f L⟩

/-- The actual global REDUCED closed subscheme of the parameter scheme. -/
def globalReducedFibreTrivialityLocus
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) : Scheme.{u} :=
  L1.reducedClosedSupport Y (globalFibreTrivialityClosed f L)

/-- Actual global closed inclusion, not an asserted representing morphism for
global line-bundle triviality on nonreduced tests. -/
def globalReducedFibreTrivialityLocusι
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) :
    globalReducedFibreTrivialityLocus f L ⟶ Y :=
  L1.reducedClosedSupportι Y (globalFibreTrivialityClosed f L)

instance globalReducedFibreTrivialityLocus_closed
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) :
    IsClosedImmersion (globalReducedFibreTrivialityLocusι f L) :=
  L1.reducedClosedSupport_closed _ _

instance globalReducedFibreTrivialityLocus_reduced
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) :
    AlgebraicGeometry.IsReduced (globalReducedFibreTrivialityLocus f L) :=
  L1.reducedClosedSupport_reduced _ _

/-- Its range is EXACTLY the original global residue-fibre triviality set. -/
theorem range_globalReducedFibreTrivialityLocusι
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) :
    Set.range (globalReducedFibreTrivialityLocusι f L) = fibrePicardTrivialitySet f L :=
  L1.range_reducedClosedSupportι _ _

/-- Genuine REDUCED-test classification by image containment/residue-fibre
classes. This is not a global normalized seesaw assertion. -/
theorem factor_globalReducedFibreTrivialityLocus_iff
    {X Y T : Scheme.{u}} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced T]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f] (L : X.Pic) (g : T ⟶ Y) :
    (∃ a : T ⟶ globalReducedFibreTrivialityLocus f L,
      a ≫ globalReducedFibreTrivialityLocusι f L = g) ↔
    ∀ t : T, Scheme.Pic.map (f.fiberι (g t)) L = 1 := by
  change (∃ a : T ⟶ L1.reducedClosedSupport Y (globalFibreTrivialityClosed f L),
    a ≫ L1.reducedClosedSupportι Y (globalFibreTrivialityClosed f L) = g) ↔ _
  rw [L1.factor_reducedClosedSupport_iff]
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    exact h t

end ZInQ.Contrib.CloudR2Poincare.L2
