import ZInQKernel.Contrib.OneProof.QuotientP1.FixedDisjoint

namespace HDec

set_option maxHeartbeats 1000000
set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- A ring homomorphism to `ℚ̄` from a ring receiving `ℚ` has a maximal kernel (its image is a subring of
`ℚ̄` containing `ℚ`, algebraic, hence a field). -/
theorem ker_isMaximal_of_qbar {A : Type*} [CommRing A] (c : ℚ →+* A) (ψ : A →+* Qbar) :
    (RingHom.ker ψ).IsMaximal := by
  let S : Subalgebra ℚ Qbar :=
    { ψ.range with
      algebraMap_mem' := fun q => ⟨c q, by
        show (ψ.comp c) q = algebraMap ℚ Qbar q
        rw [RingHom.ext_rat (ψ.comp c) (algebraMap ℚ Qbar)]⟩ }
  have hS : IsField S := Subalgebra.isField_of_algebraic S
  let _ := hS.toField
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

/-- **The point of a `ℚ̄`-point of a `ℚ`-scheme locally of finite type is closed.** -/
theorem isClosed_ptOf_of_qbar (X : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType X.hom]
    (t : Spec (CommRingCat.of Qbar) ⟶ X.left) : IsClosed ({ptOf t} : Set X.left) := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  set ξ := ptOf t with hξ
  set φ := (Scheme.SpecToEquivOfField Qbar X.left t).2 with hφ
  obtain ⟨_, ⟨V, hV, rfl⟩, hξV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
  have hV' : IsAffineOpen V := hV
  set ev := X.left.evaluation V ξ hξV
  let c : ℚ →+* Γ(X.left, V) :=
    (X.left.presheaf.map (homOfLE le_top).op).hom.comp
      ((X.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom)
  have hmax' : (RingHom.ker (φ.hom.comp ev.hom)).IsMaximal := ker_isMaximal_of_qbar c _
  have hk : RingHom.ker (φ.hom.comp ev.hom) = RingHom.ker ev.hom := by
    ext a
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    constructor
    · intro h; exact φ.hom.injective (h.trans (map_zero _).symm)
    · intro h; rw [h, map_zero]
  have hmaxker : (RingHom.ker ev.hom).IsMaximal := hk ▸ hmax'
  set 𝔮 := hV'.primeIdealOf ⟨ξ, hξV⟩
  have hfs : hV'.fromSpec 𝔮 = ξ := hV'.fromSpec_primeIdealOf ⟨ξ, hξV⟩
  have hker : 𝔮.asIdeal = RingHom.ker ev.hom := by
    ext a
    rw [RingHom.mem_ker]
    have h1 : 𝔮 ∈ PrimeSpectrum.basicOpen a ↔ ξ ∈ X.left.basicOpen a := by
      have : 𝔮 ∈ hV'.fromSpec ⁻¹ᵁ X.left.basicOpen a ↔ ξ ∈ X.left.basicOpen a := by
        rw [← hfs]; rfl
      rwa [hV'.fromSpec_preimage_basicOpen] at this
    have h2 : ev.hom a = 0 ↔ ξ ∉ X.left.basicOpen a :=
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen X.left ξ hξV a
    rw [h2, ← h1, PrimeSpectrum.mem_basicOpen, not_not]
  have hlc : IsLocallyClosed ({ξ} : Set X.left) := by
    have hcl : IsClosed ({𝔮} : Set (Spec Γ(X.left, V))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔮).2 (hker ▸ hmaxker)
    have := hcl.isLocallyClosed.image hV'.fromSpec.isOpenEmbedding.isInducing
      (by rw [hV'.range_fromSpec]; exact V.isOpen.isLocallyClosed)
    convert this using 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨𝔮, rfl, hfs⟩
    · rintro ⟨a, rfl, rfl⟩; exact hfs
  exact isClosed_singleton_of_isLocallyClosed_singleton hlc

/-- The generic point of `Spec ℤ_(p)` is the image of `Spec ℚ`. -/
theorem specRatToZloc_closedPoint (p : ℕ) [Fact p.Prime] :
    specRatToZloc p (IsLocalRing.closedPoint ℚ) =
      (⟨⊥, Ideal.isPrime_bot⟩ : Spec (CommRingCat.of (Zloc p))) := by
  apply PrimeSpectrum.ext
  show Ideal.comap (zlocToRat p) (IsLocalRing.maximalIdeal ℚ) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  apply zloc_prime_eq_bot
  rw [Ideal.mem_comap, map_natCast, Ideal.mem_bot]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- **A specialization of the point of a `ℚ̄`-point inside the generic fibre is that point.** -/
theorem eq_of_specializes_generic {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    [LocallyOfFiniteType 𝒴.hom] (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (ζ : 𝒴.left)
    (hζ : 𝒴.hom ζ = ⟨⊥, Ideal.isPrime_bot⟩) (h : qbarPoint y ⤳ ζ) : ζ = qbarPoint y := by
  set G := genFib 𝒴 with hG
  set j : G.left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)
  haveI : LocallyOfFiniteType G.hom := by
    show LocallyOfFiniteType (pullback.snd 𝒴.hom (specRatToZloc p)); infer_instance
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
  have hsv : j (ptOf s.left) = qbarPoint y := by rw [← hs]; rfl
  obtain ⟨ζ', hζ'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒴.hom)
    (g := specRatToZloc p) ζ (IsLocalRing.closedPoint ℚ) (by rw [hζ, specRatToZloc_closedPoint])
  have hjζ : j ζ' = ζ := hζ'1
  subst hjζ
  have h' : ptOf s.left ⤳ ζ' :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (by rw [hsv]; exact h)
  have hcl := isClosed_ptOf_of_qbar G s.left
  have : ζ' ∈ ({ptOf s.left} : Set G.left) := by
    rw [← hcl.closure_eq]; exact specializes_iff_mem_closure.mp h'
  rw [Set.mem_singleton_iff.mp this, hsv]

end MCRQuot
