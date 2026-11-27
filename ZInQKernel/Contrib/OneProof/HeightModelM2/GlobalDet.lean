import ZInQKernel.Contrib.OneProof.HeightDictionary
import ZInQKernel.Contrib.OneProof.HeightModelM2.GlobalSections

/-! # The tree's `printedDetLattice` is `Γ(S, ε*Ω^g)`

GR1 §2.3 (p. 351) takes the invertible sheaf `ω_{𝒜/𝒪_K} = ε*Ω^g_{𝒜/𝒪_K}` and its global
sections. Here `ε*Ω^g = ⋀^g e*Ω¹`, and its sections over `V` (through `W ⊇ e(V)`) are the span
of the wedges of `g` sections of `e*Ω¹` over `V` (`detSec`), inside the tree's Hodge line
`hodgeSpace g = L ⊗ ⋀^g ω_{A_L}` (carried there by the injective `θ`). `globalDetLattice g` is
the module of global sections: elements that are sections near every point.

`globalDetLattice_eq`: **`globalDetLattice 𝒢 g = printedDetLattice 𝒢 g`**, so the tree's
lattice `⋀^g Γ(S, e*Ω¹)` is `Γ(S, ⋀^g e*Ω¹)`. The proof: a section over `V ∋ s` becomes, after
a multiplier `d ∉ s`, an element of every stalk (`exists_smul_mem_iInf`: the complement of `V`
is finite, and at each of its points the stalk spans the generic fibre and is saturated); hence a
global section of `ε*Ω^g` lies in `printedDetLattice` at every maximal ideal, hence lies in it. -/
open CategoryTheory AlgebraicGeometry Limits
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM2

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-- **The global lattice localizes to the stalks**: a section over `V ∋ s` becomes, after a
multiplier `d ∉ s`, an element of every stalk, hence of `Γ(S, e*Ω¹)`. -/
theorem exists_smul_mem_iInf {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {W : 𝒢.G.left.Opens}
    {s : Spec (CommRingCat.of (𝓞 L))} (hs : s ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)
    {u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]}
    (hu : u ∈ secOmega 𝒢 V W (genericPt_mem hs) hVW) :
    ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • u ∈ ⨅ s', printedOmegaAt 𝒢 s' := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((V : Set (Spec (CommRingCat.of (𝓞 L))))ᶜ)).mp V.isOpen.isClosed_compl
  have hsI : ¬ ((I : Set (𝓞 L)) ⊆ s.asIdeal) := by
    intro h
    have : s ∈ (V : Set (Spec (CommRingCat.of (𝓞 L))))ᶜ :=
      (Set.ext_iff.mp hI s).mpr ((PrimeSpectrum.mem_zeroLocus _ _).mpr h)
    exact this hs
  obtain ⟨f, hfI, hfs⟩ := Set.not_subset.mp hsI
  have hf0 : f ≠ 0 := fun h => hfs (h ▸ s.asIdeal.zero_mem)
  have hbad : {p : Spec (CommRingCat.of (𝓞 L)) | f ∈ p.asIdeal}.Finite :=
    finite_setOf_mem (R := 𝓞 L) hf0
  have hout : ∀ p : Spec (CommRingCat.of (𝓞 L)), p ∉ V → f ∈ p.asIdeal := by
    intro p hp
    have : p ∈ PrimeSpectrum.zeroLocus (I : Set (𝓞 L)) := (Set.ext_iff.mp hI p).mp hp
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp this hfI
  have hchoice : ∀ p : Spec (CommRingCat.of (𝓞 L)), ∃ d : 𝓞 L, d ∉ s.asIdeal ∧
      (p ∉ V → d • u ∈ printedOmegaAt 𝒢 p) := by
    intro p
    by_cases hpV : p ∈ V
    · exact ⟨1, fun h => s.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h),
        fun h => absurd hpV h⟩
    · obtain ⟨a, ha, hau⟩ := exists_smul_mem_printedOmegaAt 𝒢 p u
      have hp0 : p.asIdeal ≠ ⊥ := by
        intro h
        apply hpV
        have : p = genericPt L := PrimeSpectrum.ext h
        rw [this]; exact genericPt_mem hs
      have hps : ¬ p.asIdeal ≤ s.asIdeal := by
        intro hle
        apply hpV
        have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal hp0
        have : p = s := PrimeSpectrum.ext (hmax.eq_of_le s.isPrime.ne_top hle)
        rw [this]; exact hs
      haveI := s.isPrime
      haveI := p.isPrime
      obtain ⟨d, hd, t, ht, y, hty⟩ := exists_mul_eq_of_not_le s.asIdeal p.asIdeal hp0 hps ha
      refine ⟨d, hd, fun _ => mem_of_smul_mem 𝒢 p ht ?_⟩
      rw [smul_smul, hty, mul_comm, mul_smul]
      exact Submodule.smul_mem _ y hau
  choose d hd hdu using hchoice
  refine ⟨∏ p ∈ hbad.toFinset, d p, ?_, ?_⟩
  · intro h
    haveI := s.isPrime
    obtain ⟨p, -, hp⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hd p hp
  · rw [Submodule.mem_iInf]
    intro p
    by_cases hpV : p ∈ V
    · exact Submodule.smul_mem _ _ (secOmega_le 𝒢 hpV hVW hu)
    · have hp : p ∈ hbad.toFinset := by
        rw [Set.Finite.mem_toFinset]; exact hout p hpV
      rw [← Finset.mul_prod_erase _ _ hp, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (hdu p hpV)

/-! ## The global sections of `ε*Ω^g` -/

/-- **The sections over `V` of `ε*Ω^g = ⋀^g e*Ω¹`**, through `W ⊇ e(V)`, in the Hodge line
`L ⊗ ⋀^g ω_{A_L}`: the span of the wedges of `g` sections of `e*Ω¹` over `V` (carried to
`ω_{A_L} = 𝔪_ξ/𝔪_ξ²` by the injective `θ`). -/
noncomputable def detSec (g : ℕ) (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (W : 𝒢.G.left.Opens)
    (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W) :
    Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → (secOmega 𝒢 V W hV hVW).comap (theta' 𝒢) =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

theorem detSec_mono (g : ℕ) {V V' : (Spec (CommRingCat.of (𝓞 L))).Opens}
    {W W' : 𝒢.G.left.Opens} (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)
    (hV' : genericPt L ∈ V') (hVW' : V' ≤ 𝒢.unitSection ⁻¹ᵁ W') (h1 : V' ≤ V) (h2 : W' ≤ W) :
    detSec 𝒢 g V W hV hVW ≤ detSec 𝒢 g V' W' hV' hVW' := by
  rw [detSec, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact Submodule.subset_span ⟨fun i => ⟨v i, secOmega_mono 𝒢 hV hVW hV' hVW' h1 h2 (v i).2⟩, rfl⟩

/-- The sections of `ε*Ω^g` near `s`. -/
noncomputable def detSecNear (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L))) :
    Submodule (𝓞 L) (𝒢.hodgeSpace g) where
  carrier := {x | ∃ (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (W : 𝒢.G.left.Opens) (hs : s ∈ V)
    (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W), x ∈ detSec 𝒢 g V W (genericPt_mem hs) hVW}
  zero_mem' := ⟨𝒢.unitSection ⁻¹ᵁ ⊤, ⊤, trivial, le_rfl, Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨V₁, W₁, hs₁, h₁, hx⟩ ⟨V₂, W₂, hs₂, h₂, hy⟩
    refine ⟨V₁ ⊓ V₂, W₁ ⊓ W₂, ⟨hs₁, hs₂⟩, ?_, Submodule.add_mem _ ?_ ?_⟩
    · intro z hz; exact ⟨h₁ hz.1, h₂ hz.2⟩
    · exact detSec_mono 𝒢 g _ _ _ _ inf_le_left inf_le_left hx
    · exact detSec_mono 𝒢 g _ _ _ _ inf_le_right inf_le_right hy
  smul_mem' := by
    rintro a x ⟨V, W, hs, h, hx⟩
    exact ⟨V, W, hs, h, Submodule.smul_mem _ a hx⟩

/-- **`Γ(S, ε*Ω^g)` inside the Hodge line**: the elements that are sections of `ε*Ω^g` near every
point of `S = Spec 𝓞_L`. -/
noncomputable def globalDetLattice (g : ℕ) : Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  ⨅ s, detSecNear 𝒢 g s

/-- Finitely many sections near `s` are sections over one common `V ∋ s`. -/
theorem exists_common_secOmega {g : ℕ} (s : Spec (CommRingCat.of (𝓞 L)))
    (u : Fin g → (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) (hu : ∀ i, u i ∈ secNear 𝒢 s) :
    ∃ (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (W : 𝒢.G.left.Opens) (hs : s ∈ V)
      (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W), ∀ i, u i ∈ secOmega 𝒢 V W (genericPt_mem hs) hVW := by
  classical
  suffices h : ∀ T : Finset (Fin g), ∃ (V : (Spec (CommRingCat.of (𝓞 L))).Opens)
      (W : 𝒢.G.left.Opens) (hs : s ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W),
      ∀ i ∈ T, u i ∈ secOmega 𝒢 V W (genericPt_mem hs) hVW by
    obtain ⟨V, W, hs, hVW, h⟩ := h Finset.univ
    exact ⟨V, W, hs, hVW, fun i => h i (Finset.mem_univ i)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨𝒢.unitSection ⁻¹ᵁ ⊤, ⊤, trivial, le_rfl, fun i hi => absurd hi (by simp)⟩
  | insert j T _ ih =>
    obtain ⟨V₁, W₁, hs₁, h₁, hT⟩ := ih
    obtain ⟨V₂, W₂, hs₂, h₂, hj⟩ := hu j
    refine ⟨V₁ ⊓ V₂, W₁ ⊓ W₂, ⟨hs₁, hs₂⟩, fun z hz => ⟨h₁ hz.1, h₂ hz.2⟩, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact secOmega_mono 𝒢 _ _ _ _ inf_le_right inf_le_right hj
    · exact secOmega_mono 𝒢 _ _ _ _ inf_le_left inf_le_left (hT i hi)

/-- A section of `ε*Ω^g` over `V ∋ s` has a multiple by some `d ∉ s` in `printedDetLattice`. -/
theorem exists_smul_mem_printedDetLattice (g : ℕ) {V : (Spec (CommRingCat.of (𝓞 L))).Opens}
    {W : 𝒢.G.left.Opens} {s : Spec (CommRingCat.of (𝓞 L))} (hs : s ∈ V)
    (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W) {x : 𝒢.hodgeSpace g}
    (hx : x ∈ detSec 𝒢 g V W (genericPt_mem hs) hVW) :
    ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • x ∈ printedDetLattice 𝒢 g := by
  haveI := s.isPrime
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hv : ∀ i, ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • theta' 𝒢 (v i : 𝒢.cotangent) ∈
        ⨅ s', printedOmegaAt 𝒢 s' := fun i => exists_smul_mem_iInf 𝒢 hs hVW (v i).2
    choose d hd hdv using hv
    refine ⟨∏ i, d i, ?_, ?_⟩
    · intro h
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hd i hi
    · have hmem : ∀ i, d i • (v i : 𝒢.cotangent) ∈ printedOmega 𝒢 := by
        intro i
        show theta' 𝒢 (d i • (v i : 𝒢.cotangent)) ∈ ⨅ s', printedOmegaAt 𝒢 s'
        rw [map_smul]; exact hdv i
      rw [← TensorProduct.tmul_smul, ← AlternatingMap.map_smul_univ]
      exact Submodule.subset_span ⟨fun i => ⟨d i • (v i : 𝒢.cotangent), hmem i⟩, rfl⟩
  | zero => exact ⟨1, fun h => s.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h),
      by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, fun h => (s.isPrime.mem_or_mem h).elim hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h₁
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h₂
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    exact ⟨d, hd, by rw [smul_comm]; exact Submodule.smul_mem _ a h⟩

/-- **The tree's lattice is `Γ(S, ε*Ω^g)`**: `printedDetLattice 𝒢 g = ⋀^g Γ(S, e*Ω¹)` is the
`𝓞_L`-module of global sections of `ε*Ω^g` in the Hodge line. -/
theorem globalDetLattice_eq (g : ℕ) : globalDetLattice 𝒢 g = printedDetLattice 𝒢 g := by
  apply le_antisymm
  · intro x hx
    let I : Ideal (𝓞 L) :=
      { carrier := {d | d • x ∈ printedDetLattice 𝒢 g}
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, zero_smul]; exact Submodule.zero_mem _
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, add_smul] at *; exact Submodule.add_mem _ ha hb
        smul_mem' := by
          intro c a ha
          simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul] at *
          exact Submodule.smul_mem _ c ha }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
      let s : Spec (CommRingCat.of (𝓞 L)) := ⟨M, hM.isPrime⟩
      obtain ⟨V, W, hs, hVW, hxV⟩ := (Submodule.mem_iInf _).mp hx s
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem_printedDetLattice 𝒢 g hs hVW hxV
      exact hd (hIM hdx)
    have h1 : (1 : 𝓞 L) ∈ I := by rw [hI]; trivial
    have h2 : (1 : 𝓞 L) • x ∈ printedDetLattice 𝒢 g := h1
    rwa [one_smul] at h2
  · rw [printedDetLattice, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, globalDetLattice, Submodule.mem_iInf]
    intro s
    have hu : ∀ i, theta' 𝒢 (v i : 𝒢.cotangent) ∈ secNear 𝒢 s := fun i =>
      printedOmegaAt_le_secNear 𝒢 s ((Submodule.mem_iInf _).mp (v i).2 s)
    obtain ⟨V, W, hs, hVW, h⟩ := exists_common_secOmega 𝒢 s _ hu
    exact ⟨V, W, hs, hVW, Submodule.subset_span ⟨fun i => ⟨v i, h i⟩, rfl⟩⟩

/-- The global sections of `ε*Ω^g` are the kernel's Hodge lattice `detLattice` (through
`ZInQ.HeightDict.printedDetLattice_eq`). -/
theorem globalDetLattice_eq_detLattice (g : ℕ) : globalDetLattice 𝒢 g = 𝒢.detLattice g :=
  (globalDetLattice_eq 𝒢 g).trans (printedDetLattice_eq 𝒢 g)

end ZInQ.HeightModelM2
