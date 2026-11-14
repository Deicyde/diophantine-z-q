import ZInQKernel.Contrib.Mobius.Main
import Mathlib

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Polynomial

namespace MCRGlue

/-- In characteristic `p`, if `K` is algebraic over its prime field, the image of any ring in `K`
is a field, so every kernel of a map to `K` is maximal. -/
theorem ker_isMaximal_of_isAlgebraic {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : Algebra.IsAlgebraic (⊥ : Subfield K) K) {A : Type*} [CommRing A] (ψ : A →+* K) :
    (RingHom.ker ψ).IsMaximal := by
  let S : Subalgebra (⊥ : Subfield K) K :=
    { ψ.range with
      algebraMap_mem' := fun c => by
        obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p K).1 c.2
        exact ⟨n, by rw [map_intCast]; exact hn⟩ }
  have hS : IsField S := Subalgebra.isField_of_algebraic S
  letI := hS.toField
  let ψ' : A →+* S := ψ.codRestrict S (fun a => ⟨a, rfl⟩)
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨s, a, rfl⟩
    exact ⟨a, rfl⟩
  have hk : RingHom.ker ψ' = RingHom.ker ψ := by
    ext a
    simp only [RingHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [← hk]
  exact RingHom.ker_isMaximal_of_surjective ψ' hsurj

theorem not_isAlgebraic_residueField_of_smooth {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ}
    [hp : Fact p.Prime] (hR : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (𝒴 : Over (Spec (CommRingCat.of R))) (hsm : SmoothOfRelativeDimension 1 𝒴.hom)
    (ξ : 𝒴.left)
    (hmax : IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
      Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)}) :
    ¬ Algebra.IsAlgebraic (⊥ : Subfield (𝒴.left.residueField ξ)) (𝒴.left.residueField ξ) := by
  intro halg
  have hpξ : (p : 𝒴.left.presheaf.stalk ξ) ∈ IsLocalRing.maximalIdeal _ := by rw [hmax]; exact Ideal.subset_span rfl
  have hpκ : (p : 𝒴.left.residueField ξ) = 0 := by
    have : IsLocalRing.residue (𝒴.left.presheaf.stalk ξ) (p : 𝒴.left.presheaf.stalk ξ) =
        (p : 𝒴.left.residueField ξ) := map_natCast _ _
    rw [← this]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hpξ
  haveI hcharξ : CharP (𝒴.left.residueField ξ) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpκ
  -- an affine chart
  obtain ⟨_, ⟨V, hV, rfl⟩, hξV, -⟩ :=
    𝒴.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
  have hV' : IsAffineOpen V := hV
  set ev := 𝒴.left.evaluation V ξ hξV
  have hmaxker : (RingHom.ker ev.hom).IsMaximal := ker_isMaximal_of_isAlgebraic p halg ev.hom
  set 𝔮 := hV'.primeIdealOf ⟨ξ, hξV⟩
  have hfs : hV'.fromSpec 𝔮 = ξ := hV'.fromSpec_primeIdealOf ⟨ξ, hξV⟩
  have hker : 𝔮.asIdeal = RingHom.ker ev.hom := by
    ext a
    rw [RingHom.mem_ker]
    have h1 : 𝔮 ∈ PrimeSpectrum.basicOpen a ↔ ξ ∈ 𝒴.left.basicOpen a := by
      have : 𝔮 ∈ hV'.fromSpec ⁻¹ᵁ 𝒴.left.basicOpen a ↔ ξ ∈ 𝒴.left.basicOpen a := by
        rw [← hfs]; rfl
      rwa [hV'.fromSpec_preimage_basicOpen] at this
    have h2 : ev.hom a = 0 ↔ ξ ∉ 𝒴.left.basicOpen a :=
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen 𝒴.left ξ hξV a
    rw [h2, ← h1, PrimeSpectrum.mem_basicOpen, not_not]
  -- `{ξ}` is locally closed in `X`
  have hlc : IsLocallyClosed ({ξ} : Set 𝒴.left) := by
    have hcl : IsClosed ({𝔮} : Set (Spec Γ(𝒴.left, V))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔮).2 (hker ▸ hmaxker)
    have := hcl.isLocallyClosed.image hV'.fromSpec.isOpenEmbedding.isInducing
      (by rw [hV'.range_fromSpec]; exact V.isOpen.isLocallyClosed)
    convert this using 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨𝔮, rfl, hfs⟩
    · rintro ⟨a, rfl, rfl⟩; exact hfs
  -- the special fibre
  set K := IsLocalRing.ResidueField R
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hι : ∀ s, ι s = IsLocalRing.closedPoint R := fun s =>
    IsLocalRing.PrimeSpectrum.comap_residue _ s
  have hfξ : 𝒴.hom ξ = IsLocalRing.closedPoint R := by
    have hnot : ξ ∉ 𝒴.left.basicOpen (𝒴.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R))) := by
      rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen 𝒴.left (U := ⊤) ξ trivial]
      simp only [map_natCast]
      exact hpκ
    have hmem : (p : R) ∈ (𝒴.hom ξ).asIdeal := by
      rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hnot
      by_contra h
      exact hnot h
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal (𝒴.hom ξ).isPrime.ne_top) ?_
    show IsLocalRing.maximalIdeal R ≤ _
    rw [hR, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  obtain ⟨ξ', hξ'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒴.hom) (g := ι) ξ
    (IsLocalRing.closedPoint K) (by rw [hfξ, hι (IsLocalRing.closedPoint K)])
  haveI : IsClosedImmersion ι := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hsm' : SmoothOfRelativeDimension 1 𝒴.hom := hsm
  have hsmp : SmoothOfRelativeDimension 1 (pullback.snd 𝒴.hom ι) := inferInstance
  have : Smooth (pullback.snd 𝒴.hom ι) := SmoothOfRelativeDimension.smooth 1 _
  have hJ : JacobsonSpace (pullback (C := Scheme) 𝒴.hom ι) := LocallyOfFiniteType.jacobsonSpace (pullback.snd 𝒴.hom ι)
  have hinj : Function.Injective (pullback.fst 𝒴.hom ι) :=
    (pullback.fst 𝒴.hom ι).isClosedEmbedding.injective
  have hpre : (pullback.fst 𝒴.hom ι) ⁻¹' {ξ} = {ξ'} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact hinj (h.trans hξ'1.symm)
    · rintro rfl; exact hξ'1
  have hcl' : IsClosed ({ξ'} : Set (pullback (C := Scheme) 𝒴.hom ι)) := by
    have := hlc.preimage (pullback.fst 𝒴.hom ι).continuous
    rw [hpre] at this
    exact isClosed_singleton_of_isLocallyClosed_singleton this
  have hd1 := LeafQM.AV.Pin.smoothStalkDimOne K (pullback (C := Scheme) 𝒴.hom ι) (pullback.snd 𝒴.hom ι) hsmp ξ' hcl'
  subst hξ'1
  have hsurj := (pullback.fst 𝒴.hom ι).stalkMap_surjective ξ'
  have hpK : (p : K) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff, hR]
    exact Ideal.subset_span rfl
  have hp0 : (p : (pullback (C := Scheme) 𝒴.hom ι).presheaf.stalk ξ') = 0 := by
    have h := map_natCast ((pullback (C := Scheme) 𝒴.hom ι).presheaf.germ ⊤ ξ' trivial).hom p
    have h2 := map_natCast ((pullback.snd 𝒴.hom ι).appTop).hom p
    have h3 := map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom p
    rw [← h, ← h2, ← h3, hpK]
    simp
  have hfield : IsField ((pullback (C := Scheme) 𝒴.hom ι).presheaf.stalk ξ') := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {s} hs => ?_⟩
    obtain ⟨t, rfl⟩ := hsurj s
    by_cases ht : t ∈ IsLocalRing.maximalIdeal _
    · rw [hmax, Ideal.mem_span_singleton'] at ht
      obtain ⟨u, rfl⟩ := ht
      exact absurd (by rw [map_mul, map_natCast, hp0, mul_zero]) hs
    · have hu : IsUnit t := by
        by_contra h
        exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
      exact (hu.map ((pullback.fst 𝒴.hom ι).stalkMap ξ').hom).exists_right_inv
  rw [ringKrullDim_eq_zero_of_isField hfield] at hd1
  exact absurd hd1 (by decide)

end MCRGlue
