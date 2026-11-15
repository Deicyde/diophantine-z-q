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


/-- **LEAF (Edixhoven's tame fixed-point theorem, for a group generated by two automorphisms, over `ℤ_(p)`).**
B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), 291-306, Prop. 3.4 (locator
UNVERIFIED): for a smooth `S`-scheme `X` and a finite group `G` of `S`-automorphisms of order invertible on `S`, the
fixed-point scheme `X^G` is smooth over `S`. Here `S = Spec ℤ_(p)`, `G = ⟨σ, τ⟩` (finite, `p ∤ |G|`), and `X^G`,
which represents `T ↦ X(T)^G`, is the fibre product over `X` of the fixed schemes (equalizers with the identity in
schemes over `S`) of the two generators. -/
def EdixhovenFixedSmooth2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))), Smooth 𝒴.hom →
    ∀ (σ τ : Aut 𝒴.left) (hσ : σ.asIso.hom ≫ 𝒴.hom = 𝒴.hom) (hτ : τ.asIso.hom ≫ 𝒴.hom = 𝒴.hom),
      Finite (Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left))) →
      ¬ p ∣ Nat.card (Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left))) →
      Smooth (pullback.fst (equalizer.ι (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left
          (equalizer.ι (Over.homMk τ.asIso.hom hτ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left ≫
        (equalizer.ι (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left ≫ 𝒴.hom)

/-- The cyclic case of `EdixhovenFixedSmooth2` (`τ = σ`; the fibre product of a monomorphism with itself). -/
theorem fixed_smooth_of_two (hE : EdixhovenFixedSmooth2) {p : ℕ} [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) [Smooth 𝒴.hom] (σ : Aut 𝒴.left)
    (hσ : σ.asIso.hom ≫ 𝒴.hom = 𝒴.hom) (hG : Finite (Subgroup.closure ({σ, σ} : Set (Aut 𝒴.left))))
    (hpG : ¬ p ∣ Nat.card (Subgroup.closure ({σ, σ} : Set (Aut 𝒴.left)))) :
    Smooth ((equalizer.ι (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left ≫ 𝒴.hom) := by
  have h := hE p 𝒴 inferInstance σ σ hσ hσ hG hpG
  set ι := (equalizer.ι (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left with hιdef
  haveI : Smooth (pullback.fst ι ι ≫ ι ≫ 𝒴.hom) := h
  have e : inv (pullback.fst ι ι) ≫ pullback.fst ι ι ≫ ι ≫ 𝒴.hom = ι ≫ 𝒴.hom := by simp
  rw [← e]; infer_instance

/-- **Fixed schemes force generizations back to the fixed point.** If `ρ` has finitely many fixed `ℚ̄`-points and
a smooth fixed scheme, `t` is a fixed `ℚ̄`-point, `z` lies in the closure of its point, and `ζ ⤳ z` lies in the fixed
locus, then the point of `t` generizes `ζ`. -/
theorem fixed_generization {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    [IsSeparated 𝒴.hom] [LocallyOfFiniteType 𝒴.hom] (ρ : Aut 𝒴.left)
    (hρ : ρ.asIso.hom ≫ 𝒴.hom = 𝒴.hom)
    (hfin : {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | t ≫ ρ.asIso.hom = t}.Finite)
    (hsm : Smooth ((equalizer.ι (Over.homMk ρ.asIso.hom hρ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left ≫ 𝒴.hom))
    (t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (ht : t ≫ ρ.asIso.hom = t) (z ζ : 𝒴.left)
    (hz : z ∈ closure {qbarPoint t}) (hζz : ζ ⤳ z)
    (hζr : ζ ∈ Set.range (equalizer.ι (Over.homMk ρ.asIso.hom hρ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left) :
    qbarPoint t ⤳ ζ := by
  haveI : IsDiscreteValuationRing (Zloc p) := zloc_isDVR p
  let f : 𝒴 ⟶ 𝒴 := Over.homMk ρ.asIso.hom hρ
  let ι := (equalizer.ι f (𝟙 𝒴)).left
  have hι : ι ≫ ρ.asIso.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f (𝟙 𝒴))
    simpa [f, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hxt : qbarPoint t ∈ Set.range ι := by
    let t' : Over.mk (t ≫ 𝒴.hom) ⟶ 𝒴 := Over.homMk t rfl
    have hc : t' ≫ f = t' ≫ 𝟙 𝒴 := by
      ext1; simpa [f, t'] using ht
    refine ⟨(equalizer.lift t' hc).left (IsLocalRing.closedPoint Qbar), ?_⟩
    show ((equalizer.lift t' hc).left ≫ (equalizer.ι f (𝟙 𝒴)).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hbad : ∀ w ∈ Set.range ι,
      ¬ {s : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | qbarPoint s ∈ closure {w}}.Infinite := by
    intro w hw hinf
    apply hinf
    refine hfin.subset ?_
    intro s hs
    have hsr : ptOf s ∈ Set.range ι :=
      closure_minimal (Set.singleton_subset_iff.2 hw) hcl hs
    obtain ⟨s', rfl⟩ := exists_factor_of_mem_range_closedImm ι s hsr
    show (s' ≫ ι) ≫ ρ.asIso.hom = s' ≫ ι
    rw [Category.assoc, hι]
  obtain ⟨xt, hxt'⟩ := hxt
  have hzr : z ∈ Set.range ι := closure_minimal
    (Set.singleton_subset_iff.2 (show qbarPoint t ∈ Set.range ι from ⟨xt, hxt'⟩)) hcl hz
  obtain ⟨zt, rfl⟩ := hzr
  obtain ⟨ζt, rfl⟩ := hζr
  have hind := ι.isClosedEmbedding.isInducing
  have h1 : xt ⤳ zt := by
    rw [← hind.specializes_iff, hxt']; exact specializes_iff_mem_closure.mpr hz
  have h2 : ζt ⤳ zt := hind.specializes_iff.mp hζz
  haveI : IsDomain ((equalizer f (𝟙 𝒴)).left.presheaf.stalk zt) :=
    (_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
      (Zloc p) (ι ≫ 𝒴.hom) zt).1
  obtain ⟨ξ, hξ1, hξ2⟩ := exists_common_generization zt h1 h2
  have k1 : ι ξ ⤳ qbarPoint t := by rw [← hxt']; exact hξ1.map ι.continuous
  by_cases hξx : ι ξ = qbarPoint t
  · rw [← hξx]; exact hξ2.map ι.continuous
  · exact absurd (infinite_qbar_closure 𝒴 t _ k1 hξx) (hbad _ ⟨ξ, rfl⟩)

/-- **Distinct `ℚ̄`-points fixed by two automorphisms generating a finite tame group have disjoint closures**
(from Edixhoven's theorem for the group `⟨σ, τ⟩`). A common point `z` of the closures lies in `X^{⟨σ,τ⟩}`, which is
smooth, hence flat, over `ℤ_(p)`; so `z` has a generization `ζ` in `X^{⟨σ,τ⟩}` over the generic point of
`Spec ℤ_(p)` (flat maps are generalizing). By `fixed_generization` for `σ` and for `τ`, both points generize `ζ`,
and a specialization of the point of a `ℚ̄`-point inside the generic fibre is that point. -/
theorem disjoint_closure_of_two (hE : EdixhovenFixedSmooth2) {p : ℕ} [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (hP : IsProper 𝒴.hom)
    (hS : SmoothOfRelativeDimension 1 𝒴.hom) (σ τ : Aut 𝒴.left)
    (hσ : σ.asIso.hom ≫ 𝒴.hom = 𝒴.hom) (hτ : τ.asIso.hom ≫ 𝒴.hom = 𝒴.hom)
    (hG : Finite (Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left))))
    (hpG : ¬ p ∣ Nat.card (Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left))))
    (hfσ : {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | t ≫ σ.asIso.hom = t}.Finite)
    (hfτ : {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | t ≫ τ.asIso.hom = t}.Finite)
    (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (hy : y ≫ σ.asIso.hom = y)
    (hy' : y' ≫ τ.asIso.hom = y') (hne : qbarPoint y ≠ qbarPoint y') :
    Disjoint (closure {qbarPoint y}) (closure {qbarPoint y'}) := by
  haveI := hP
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  -- the finiteness and tameness of the cyclic subgroups
  have hsub : ∀ ρ ∈ ({σ, τ} : Set (Aut 𝒴.left)),
      Subgroup.closure ({ρ, ρ} : Set (Aut 𝒴.left)) ≤ Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left)) := by
    intro ρ hρ
    rw [Set.pair_eq_singleton, Subgroup.closure_le]
    exact Set.singleton_subset_iff.2 (Subgroup.subset_closure hρ)
  have hcyc : ∀ ρ ∈ ({σ, τ} : Set (Aut 𝒴.left)),
      Finite (Subgroup.closure ({ρ, ρ} : Set (Aut 𝒴.left))) ∧
        ¬ p ∣ Nat.card (Subgroup.closure ({ρ, ρ} : Set (Aut 𝒴.left))) := by
    intro ρ hρ
    have hle := hsub ρ hρ
    refine ⟨Finite.of_injective (fun x : Subgroup.closure ({ρ, ρ} : Set (Aut 𝒴.left)) =>
      (⟨x.1, hle x.2⟩ : Subgroup.closure ({σ, τ} : Set (Aut 𝒴.left))))
      (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e)), fun hd => hpG ?_⟩
    exact hd.trans (Subgroup.card_dvd_of_le hle)
  have hsmσ := fixed_smooth_of_two hE 𝒴 σ hσ (hcyc σ (by simp)).1 (hcyc σ (by simp)).2
  have hsmτ := fixed_smooth_of_two hE 𝒴 τ hτ (hcyc τ (by simp)).1 (hcyc τ (by simp)).2
  let ι₁ := (equalizer.ι (Over.homMk σ.asIso.hom hσ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left
  let ι₂ := (equalizer.ι (Over.homMk τ.asIso.hom hτ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left
  have hfix : ∀ (ρ : Aut 𝒴.left) (hρ : ρ.asIso.hom ≫ 𝒴.hom = 𝒴.hom)
      (t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left), t ≫ ρ.asIso.hom = t →
      qbarPoint t ∈ Set.range (equalizer.ι (Over.homMk ρ.asIso.hom hρ : 𝒴 ⟶ 𝒴) (𝟙 𝒴)).left := by
    intro ρ hρ t ht
    let f : 𝒴 ⟶ 𝒴 := Over.homMk ρ.asIso.hom hρ
    let t' : Over.mk (t ≫ 𝒴.hom) ⟶ 𝒴 := Over.homMk t rfl
    have hc : t' ≫ f = t' ≫ 𝟙 𝒴 := by
      ext1; simpa [f, t'] using ht
    refine ⟨(equalizer.lift t' hc).left (IsLocalRing.closedPoint Qbar), ?_⟩
    show ((equalizer.lift t' hc).left ≫ (equalizer.ι f (𝟙 𝒴)).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  rw [Set.disjoint_left]
  intro z hz hz'
  have hz1 : z ∈ Set.range ι₁ := closure_minimal (Set.singleton_subset_iff.2 (hfix σ hσ y hy))
    ι₁.isClosedEmbedding.isClosed_range hz
  have hz2 : z ∈ Set.range ι₂ := closure_minimal (Set.singleton_subset_iff.2 (hfix τ hτ y' hy'))
    ι₂.isClosedEmbedding.isClosed_range hz'
  obtain ⟨z₁, hz₁⟩ := hz1
  obtain ⟨z₂, hz₂⟩ := hz2
  obtain ⟨zF, hzF1, hzF2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι₁) (g := ι₂) z₁ z₂
    (hz₁.trans hz₂.symm)
  have hsmF := hE p 𝒴 inferInstance σ τ hσ hτ hG hpG
  have hgen := Flat.generalizingMap (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ 𝒴.hom)
  set t0 : Spec (CommRingCat.of (Zloc p)) := ⟨⊥, Ideal.isPrime_bot⟩ with ht0
  have ht0s : t0 ⤳ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ 𝒴.hom) zF :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨ζF, hζF, hζFt⟩ := hgen ht0s
  set ζ := ι₁ (pullback.fst ι₁ ι₂ ζF) with hζ
  have hζz : ζ ⤳ z := by
    rw [← hz₁, ← hzF1]
    exact (hζF.map (pullback.fst ι₁ ι₂).continuous).map ι₁.continuous
  have hζ1 : ζ ∈ Set.range ι₁ := ⟨_, rfl⟩
  have hζ2 : ζ ∈ Set.range ι₂ := by
    refine ⟨pullback.snd ι₁ ι₂ ζF, ?_⟩
    rw [hζ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hζη : 𝒴.hom ζ = t0 := by
    rw [← hζFt]; rfl
  have e1 := fixed_generization 𝒴 σ hσ hfσ hsmσ y hy z ζ hz hζz hζ1
  have e2 := fixed_generization 𝒴 τ hτ hfτ hsmτ y' hy' z ζ hz' hζz hζ2
  exact hne ((eq_of_specializes_generic 𝒴 y ζ hζη e1).symm.trans
    (eq_of_specializes_generic 𝒴 y' ζ hζη e2))


/-- **L5 `TameFixedPointsDisjoint` from Edixhoven's theorem (two generators)**: the case `τ = σ` of
`disjoint_closure_of_two` (`⟨σ⟩` is finite of order dividing `n`). -/
theorem tameFixedPointsDisjoint_of_edixhoven2 (hE : EdixhovenFixedSmooth2) : TameFixedPointsDisjoint := by
  intro p _ 𝒴 hP hS σ n hσ hn hpn hσn hfin y y' hy hy' hne
  have hcl : Subgroup.closure ({σ, σ} : Set (Aut 𝒴.left)) = Subgroup.zpowers σ := by
    rw [Set.pair_eq_singleton, Subgroup.zpowers_eq_closure]
  have hfo : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hσn⟩
  have hG : Finite (Subgroup.closure ({σ, σ} : Set (Aut 𝒴.left))) := by
    rw [hcl]; exact hfo.finite_zpowers
  have hpG : ¬ p ∣ Nat.card (Subgroup.closure ({σ, σ} : Set (Aut 𝒴.left))) := by
    rw [hcl, Nat.card_zpowers]
    exact fun hd => hpn (hd.trans (orderOf_dvd_of_pow_eq_one hσn))
  exact disjoint_closure_of_two hE 𝒴 hP hS σ σ hσ hσ hG hpG hfin hfin y y' hy hy' hne

/-- **Glue (C1b-weak): the stabilizer of a CM point in `fibreAut` is nontrivial** (mcr-quot's
`CMStabInvolution` without `ι² = 1`). -/
def CMStabNontrivial : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P : QML3 Qbar), IsFibreOf 𝒜 y P →
      (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∃ ι ∈ fibreAut 𝒴 𝒜, ι ≠ 1 ∧ y ≫ ι.asIso.hom = y

/-- `CMStabInvolution` implies `CMStabNontrivial`. -/
theorem cMStabNontrivial_of_involution (h : CMStabInvolution) : CMStabNontrivial := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP hCM
  obtain ⟨ι, hιG, hι1, -, hιy⟩ := h p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP hCM
  exact ⟨ι, hιG, hι1, hιy⟩

/-- **Glue C1 without the leaves L5, L6** (mcr-glue's `CMSectionsDisjoint` with its two premises
`TameFixedPointsDisjoint → TameInertiaCyclic` removed). -/
def CMSectionsDisjoint' : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
    ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})

/-- **C1 from Edixhoven's theorem, glue A, (A-fix), (C1a), (C1d) and the nontrivial stabilizers**
(no L5, no L6, no involutions). A common point `z` of the closures of `q(x)` and `q(x')` lifts to `w` in the
closures of `x` and `h x'` (C1a); `x` and `h x'` differ (C1d, R2fp values); nontrivial elements of `fibreAut`
fix them (`CMStabNontrivial`), with finitely many fixed points (A-fix), generating a finite tame group (A);
`disjoint_closure_of_two` contradicts `w`. -/
theorem cMSectionsDisjoint'_of (hE : EdixhovenFixedSmooth2) (hA : FibreAutTame)
    (hfix : FibreAutFixFinite) (hO : GQuotientPointOrbits) (hI : CMStabNontrivial)
    (hC : QbarPointsConjugate) : CMSectionsDisjoint' := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf y y' P P' hP hP' htype
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  rw [Set.disjoint_left]
  intro z hz hz'
  have hcl : ∀ u : 𝒴.left, closure {q.left u} ⊆ q.left '' closure {u} := by
    intro u
    refine closure_minimal ?_ (q.left.isClosedMap _ isClosed_closure)
    rintro _ rfl
    exact ⟨u, subset_closure rfl, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hcl _ hz
  obtain ⟨w', hw', hww'⟩ := hcl _ hz'
  obtain ⟨h, hhG, hhw⟩ := hO _ _ _ _ hfin hq w w' hww'.symm
  set y'' := y' ≫ h.asIso.hom with hy''
  have hw'' : w ∈ closure {qbarPoint y''} := by
    rw [hy'', qbarPoint_comp, ← hhw, ← Set.image_singleton]
    exact image_closure_subset_closure_image h.asIso.hom.continuous ⟨w', hw', rfl⟩
  obtain ⟨P'', hP''⟩ := hM.2.2.1 Qbar y''
  have hover := fibreAut_over 𝒴 𝒜
  have htype1 : HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q := by
    rcases htype with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩
    · exact Or.inl a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
  have htype2 : HasCM4 P'.q ∨ HasCM3 P'.q ∨ HasCM24 P'.q := by
    rcases htype with ⟨-, a⟩ | ⟨-, a⟩ | ⟨-, a⟩
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr a)
    · exact Or.inr (Or.inr a)
  obtain ⟨ι, hιG, hι1, hιy⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP htype1
  obtain ⟨ι', hι'G, hι'1, hι'y⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y' P' hP' htype2
  set ι'' := h * ι' * h⁻¹ with hι''
  have hι''G : ι'' ∈ fibreAut 𝒴 𝒜 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhG hι'G) (Subgroup.inv_mem _ hhG)
  have hι''1 : ι'' ≠ 1 := by
    intro e
    apply hι'1
    have : ι' = h⁻¹ * ι'' * h := by rw [hι'']; group
    rw [this, e]; group
  have hι''y : y'' ≫ ι''.asIso.hom = y'' := by
    simp only [hy'', hι'', Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hι'y]
  -- the two points differ
  have hne : qbarPoint y ≠ qbarPoint y'' := by
    intro e
    obtain ⟨σ, hσ⟩ := hC _ y y'' e
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    obtain ⟨s'', hs''⟩ := genFib_pt 𝒴 y''
    have hP2 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    have hP2'' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs'').mpr hP''
    set sσ : fieldPt Qbar ⟶ genFib 𝒴 := fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ s with hsσ
    have hsσl : sσ.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) = y'' := by
      rw [hσ, ← hs]
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ _ = _
      exact Category.assoc _ _ _
    have hsσ'' : sσ = s'' := genFib_pt_inj 𝒴 _ _ (hsσl.trans hs''.symm)
    have hl : (sσ ≫ g).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ (s ≫ g).left := by
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ g.left = _
      exact Category.assoc _ _ _
    have hπσ : π.val (K := Qbar) (s'' ≫ g).left =
        (π.val (K := Qbar) (s ≫ g).left).map (σ : Qbar →+* Qbar) := by
      rw [← hsσ'']
      exact (congrArg (fun t => π.val (K := Qbar) t) hl).trans (ToP1.val_comp π _ _)
    have hte : TwistEq P' P'' := twistEq_of_mem_fibreAut hM huniq hhG y' P' P'' hP' hP''
    have hR' := h2 (s' ≫ g) (s'' ≫ g) P' P'' (hg Qbar s' P' hP2') (hg Qbar s'' P'' hP2'')
    have hR := h2 (s ≫ g) (s ≫ g) P P (hg Qbar s P hP2) (hg Qbar s P hP2)
    have hv : π.val (K := Qbar) (s' ≫ g).left = π.val (K := Qbar) (s'' ≫ g).left :=
      hR'.1.2 hte
    rw [hπσ] at hv
    rcases htype with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [hR.2.1 a, hR'.2.2.1 b] at hv
      norm_num at hv
    · rw [hR.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
    · rw [hR.2.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
  -- Edixhoven for `⟨ι, ι''⟩`
  have hle : Subgroup.closure ({ι, ι''} : Set (Aut 𝒴.left)) ≤ fibreAut 𝒴 𝒜 := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hιG
    · exact hι''G
  have hG : Finite (Subgroup.closure ({ι, ι''} : Set (Aut 𝒴.left))) :=
    Finite.of_injective (fun x : Subgroup.closure ({ι, ι''} : Set (Aut 𝒴.left)) =>
      (⟨x.1, hle x.2⟩ : fibreAut 𝒴 𝒜))
      (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
  have hpG : ¬ p ∣ Nat.card (Subgroup.closure ({ι, ι''} : Set (Aut 𝒴.left))) :=
    fun hd => htame (hd.trans (Subgroup.card_dvd_of_le hle))
  have hdisj := disjoint_closure_of_two hE 𝒴 hM.1 hM.2.1 ι ι'' (hover ι hιG) (hover ι'' hι''G) hG hpG
    (hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 ι hιG hι1) (hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 ι'' hι''G hι''1)
    y y'' hιy hι''y hne
  exact Set.disjoint_left.mp hdisj hw hw''


/-- **Glue (C1b-obj-weak): a CM object is fixed by a Hecke operation on classes that is not the identity**
(mcr-quot's `CMStabObj` without the involution clause `T ∘ T = id`). -/
def CMStabObjWeak : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

/-- `CMStabObj` implies `CMStabObjWeak`. -/
theorem cMStabObjWeak_of (h : CMStabObj) : CMStabObjWeak := by
  intro P hP
  obtain ⟨α, u, h1, -, h3⟩ := h P hP
  exact ⟨α, u, h1, h3⟩

/-- **`CMStabNontrivial` from `CMStabObjWeak`** (mcr-quot's `cMStabInvolution_of` without the involution
part, which was the only use of `CurveBijIso` and `ModelYIrreducible` there). -/
theorem cMStabNontrivial_of (hO : CMStabObjWeak) : CMStabNontrivial := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP hCM
  obtain ⟨α, u, hfixP, m0, hm0⟩ := hO P hCM
  obtain ⟨htw, hru⟩ := hecke_mem_fibreAut hM
  obtain ⟨ga, hgaG, hga⟩ := htw α
  obtain ⟨gu, hguG, hgu⟩ := hru u
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  set ι : Aut 𝒴.left := ga * gu with hιdef
  have hιG : ι ∈ fibreAut 𝒴 𝒜 := Subgroup.mul_mem _ hgaG hguG
  have hιhom : ι.asIso.hom = gu.asIso.hom ≫ ga.asIso.hom := rfl
  have hact : ∀ (z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (Q Q' : QML3 Qbar), IsFibreOf 𝒜 z Q →
      IsFibreOf 𝒜 (z ≫ ι.asIso.hom) Q' →
        M3.mk Q' = M3.twist α (M3.rightMul u (M3.mk Q)) := by
    intro z Q Q' hQ hQ'
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ gu.asIso.hom)
    have e1 := hgu z Q Q1 hQ hQ1
    rw [hιhom, ← Category.assoc] at hQ'
    have e2 := hga _ Q1 Q' hQ1 hQ'
    rw [e2, e1]
  refine ⟨ι, hιG, ?_, ?_⟩
  · intro hι1
    obtain ⟨Q, rfl⟩ : ∃ Q : QML3 Qbar, M3.mk Q = m0 := Quotient.exists_rep m0
    obtain ⟨z, hz⟩ := hM.2.2.2.2.1 Q
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ ι.asIso.hom)
    have e1 := hact z Q Q1 hz hQ1
    have hz1 : z ≫ ι.asIso.hom = z := by rw [hι1]; simp
    rw [hz1] at hQ1
    apply hm0
    have e2 := huniq z Q1 Q hQ1 hz
    rw [← e1]
    exact e2
  · obtain ⟨P1, hP1⟩ := hM.2.2.1 Qbar (y ≫ ι.asIso.hom)
    have e := hact y P P1 hP hP1
    rw [hfixP] at e
    exact hM.2.2.2.1 _ y P1 P hP1 hP e

end MCRQuot

#print axioms HDec.MCRQuot.cMStabNontrivial_of
