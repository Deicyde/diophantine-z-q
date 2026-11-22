import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Embedding-dimension subadditivity for a local homomorphism

Adapted, with credit, from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
`RingTheory/RegularLocalRing/FlatLocalHom.lean:95–99,141–185,209–256`, Apache-2.0.
Prominent change notice, 2026-11-14: this is a separate owned L3 module, leaving the
four shared L4 base files unchanged. The required subadditivity statement has NO
flatness assumption; regularity later turns embedding dimensions into dimensions.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

open StacksPort _root_.IsLocalRing _root_.Submodule

set_option linter.style.haveILetI false

private theorem ClosedFibre.maximalIdeal_eq_map (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    maximalIdeal (ClosedFibre R S) =
      (maximalIdeal S).map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))) :=
  (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm

private theorem Submodule.spanRank_le_spanRank_add_spanRank_map_mkQ {A M : Type*} [Ring A]
    [AddCommGroup M] [Module A M] {p K : Submodule A M} (h : K ≤ p) :
    p.spanRank ≤ K.spanRank + (p.map K.mkQ).spanRank := by
  obtain ⟨a, ha_card, ha_span⟩ := Submodule.exists_span_set_card_eq_spanRank K
  obtain ⟨b, hb_card, hb_span⟩ := Submodule.exists_span_set_card_eq_spanRank (p.map K.mkQ)
  have hb : ∀ y ∈ b, y ∈ p.map K.mkQ := fun y hy => by
    rw [← hb_span]
    exact Submodule.subset_span hy
  choose! g hgp hgK using fun y hy => Submodule.mem_map.mp (hb y hy)
  set c : Set M := a ∪ (g '' b) with hc
  have hsub : g '' b ⊆ (p : Set M) := by
    rintro x ⟨y, hyb, rfl⟩
    exact hgp y hyb
  have himg : K.mkQ '' (g '' b) = b := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hwb, rfl⟩, rfl⟩
      rw [hgK w hwb]
      exact hwb
    · intro hyb
      exact ⟨g y, ⟨y, hyb, rfl⟩, hgK y hyb⟩
  have hspan : Submodule.span A c = p := by
    apply le_antisymm
    · rw [hc, Submodule.span_union, sup_le_iff]
      exact ⟨by rw [ha_span]; exact h, by rw [Submodule.span_le]; exact hsub⟩
    · intro x hx
      have hmkx : K.mkQ x ∈ Submodule.map K.mkQ (Submodule.span A (g '' b)) := by
        rw [Submodule.map_span, himg, hb_span]
        exact Submodule.mem_map_of_mem hx
      obtain ⟨z, hz, hzx⟩ := hmkx
      have hxz : x - z ∈ K := by
        have hzero : K.mkQ (x - z) = 0 := by rw [map_sub, hzx, sub_self]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
        exact hzero
      have hz' : z ∈ Submodule.span A c :=
        Submodule.span_mono (by rw [hc]; exact Set.subset_union_right) hz
      have hxz' : x - z ∈ Submodule.span A c := by
        have hmem : x - z ∈ Submodule.span A a := by rw [ha_span]; exact hxz
        exact Submodule.span_mono (by rw [hc]; exact Set.subset_union_left) hmem
      simpa using Submodule.add_mem _ hxz' hz'
  calc p.spanRank = (Submodule.span A c).spanRank := by rw [hspan]
    _ ≤ Cardinal.mk c := Submodule.spanRank_span_le_card c
    _ ≤ Cardinal.mk a + Cardinal.mk (g '' b) := Cardinal.mk_union_le a (g '' b)
    _ ≤ Cardinal.mk a + Cardinal.mk b := by gcongr; exact Cardinal.mk_image_le
    _ = K.spanRank + (p.map K.mkQ).spanRank := by rw [ha_card, hb_card]

theorem spanFinrank_maximalIdeal_le_add_spanFinrank_closedFibre (R S : Type*) [CommRing R] [CommRing
  S]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] :
    spanFinrank (maximalIdeal S)
      ≤ spanFinrank (maximalIdeal R) + spanFinrank (maximalIdeal (ClosedFibre R S)) := by
  -- Set up the ideal `I = m_R · S` and the quotient `F = S / I = ClosedFibre R S`.
  set I : Ideal S := (maximalIdeal R).map (algebraMap R S) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  -- `K = I ≤ p = m_S`.
  have hIle : I ≤ maximalIdeal S := ClosedFibre.mapMaximalIdeal_le R S
  -- Apply the general lemma (over `S`, so a single-universe cardinal inequality).
  have hmain := Submodule.spanRank_le_spanRank_add_spanRank_map_mkQ hIle
  -- Identify `(m_S).map I.mkQ` (over `S`) with `(maximalIdeal F).restrictScalars S`.
  have hbridge : ((maximalIdeal (ClosedFibre R S)).restrictScalars S)
      = Submodule.map I.mkQ (maximalIdeal S) := by
    rw [ClosedFibre.maximalIdeal_eq_map]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_map]
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    rfl
  -- The restriction of scalars preserves `spanRank` since `S → F` is surjective.
  have hsurjAlg : Function.Surjective (algebraMap S (ClosedFibre R S)) := hsurj
  have hrest : (Submodule.map I.mkQ (maximalIdeal S)).spanRank
      = (maximalIdeal (ClosedFibre R S)).spanRank := by
    rw [← hbridge, Submodule.spanRank_restrictScalars_eq hsurjAlg]
  -- Finiteness (Noetherian ⇒ FG ⇒ spanRank finite) to pass to `toNat`.
  have hfinI : I.spanRank < Cardinal.aleph0 :=
    Submodule.spanRank_finite_iff_fg.mpr (IsNoetherian.noetherian _)
  have hfinM : (Submodule.map I.mkQ (maximalIdeal S)).spanRank < Cardinal.aleph0 := by
    rw [hrest]
    exact Submodule.spanRank_finite_iff_fg.mpr (IsNoetherian.noetherian _)
  -- Convert the cardinal inequality `hmain` to a `ℕ` inequality on `spanFinrank`.
  have hSF : (maximalIdeal S).spanFinrank
      ≤ I.spanFinrank + (Submodule.map I.mkQ (maximalIdeal S)).spanFinrank := by
    have hle := Cardinal.toNat_le_toNat hmain (Cardinal.add_lt_aleph0 hfinI hfinM)
    rwa [Cardinal.toNat_add hfinI hfinM] at hle
  -- Subadditivity of `spanFinrank` (in `ℕ`) under a ring-hom image: for an ideal
  -- `q` of a Noetherian ring `A`, the image `Ideal.map f q` is generated by the
  -- images of a minimal generating set of `q`, so its `spanFinrank` is no larger.
  -- `spanFinrank I ≤ spanFinrank m_R` and the fibre identification.
  have hIfin : I.spanFinrank ≤ (maximalIdeal R).spanFinrank :=
    Ideal.spanFinrank_map_le_of_fg (algebraMap R S) (IsNoetherian.noetherian _)
  have hFfin : (Submodule.map I.mkQ (maximalIdeal S)).spanFinrank
      = (maximalIdeal (ClosedFibre R S)).spanFinrank := by
    rw [Submodule.spanFinrank, Submodule.spanFinrank, hrest]
  -- Chain the `ℕ` inequalities.
  omega


/-- For regular source, target and closed fibre, embedding-dimension subadditivity
    becomes the Krull-dimension inequality. No flatness of the map is assumed. -/
theorem regular_local_dimension_le_closedFibre (R S : Type*) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsRegularLocalRing (ClosedFibre R S)] :
    ringKrullDim S ≤ ringKrullDim R + ringKrullDim (ClosedFibre R S) := by
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := S),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := ClosedFibre R S)]
  exact_mod_cast spanFinrank_maximalIdeal_le_add_spanFinrank_closedFibre R S

end ZInQ.Contrib.CloudR2Poincare.L3
