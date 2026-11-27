import ZInQKernel.Contrib.OneProof.HeightDictionary.Conormal
import ZInQKernel.Contrib.OneProof.HeightModelM2.Arith

/-! # `ω = Γ(S, e*Ω¹_{𝒢/S})` as a theorem: global sections, not stalks

The tree's lattice `Conormal.printedOmega` is built from the stalks `(e*Ω¹)_s` of `e*Ω¹_{𝒢/S}`
(`Conormal.printedOmegaAt s`, the image of `𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]` in the generic fibre
`𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`), as their intersection. Gaudron–Rémond (GR1, Comment. Math. Helv.
89 (2014), §2.3, p. 351) use the global sections of `ε*Ω^g_{𝒜/𝒪_K}`. The fidelity reading of
the rows recorded the step "global sections of a locally free sheaf on the integral `S` are the
intersection of its stalks" as standard but not a Lean theorem. Mathlib has no sheaf of relative
differentials, so this file builds the sections over opens directly from Kähler differentials of
the opens of `𝒢`:

* `secOmega V W`: the sections over an open `V ⊆ S` of `e*Ω¹`, through an open `W ⊇ e(V)` of
  `𝒢`: the image in the generic fibre of `𝒪_S(V) ⊗_{𝒪_𝒢(W)} Ω[𝒪_𝒢(W)/𝓞_L]`, spanned by the
  `c|_η · (1 ⊗ d(b|_ξ))`, `c ∈ 𝒪_S(V)`, `b ∈ 𝒪_𝒢(W)`;
* `secNear s`: the elements that are such sections over some `V ∋ s`;
* `globalOmega`: the elements that are sections near every point, i.e. the global sections of
  the sheaf (the generic fibre carries the gluing: compatible local sections are one element).

Proved: `globalOmega_eq` (the global sections are the intersection of the stalks) and
`printedOmega_eq_comap_globalOmega` (the tree's `ω` is the preimage of the global sections
under the injective `θ`). For the exterior power (`GlobalDet.lean`) the file also proves that
the stalks are `𝒪_{S,s}`-lattices spanning the generic fibre (`mem_of_smul_mem`,
`exists_smul_mem_printedOmegaAt`). Reading, not a Lean theorem: that the image of `e*Ω¹` in its
generic fibre is `e*Ω¹` itself (it is locally free, `𝒢` being smooth). -/
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
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

/-- The generic point of `Spec 𝓞_L` specializes to every point. -/
theorem genericPt_specializes (s : Spec (CommRingCat.of (𝓞 L))) : genericPt L ⤳ s :=
  (PrimeSpectrum.le_iff_specializes (genericPt L) s).mp bot_le

/-- An open subset of `Spec 𝓞_L` containing a point contains the generic point. -/
theorem genericPt_mem {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {s : Spec (CommRingCat.of (𝓞 L))}
    (hs : s ∈ V) : genericPt L ∈ V :=
  (genericPt_specializes s).mem_open V.isOpen hs

/-- The germ at the generic point `η` of a function on an open `V ∋ η` of `Spec 𝓞_L`. -/
noncomputable def germEta (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (hV : genericPt L ∈ V)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) : Reta L :=
  ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ V (genericPt L) hV).hom c

/-- The germ at `ξ = e(η)` of a function on an open `W ∋ ξ` of `𝒢`. -/
noncomputable def germXi (W : 𝒢.G.left.Opens) (hW : 𝒢.genericUnit ∈ W) (b : Γ(𝒢.G.left, W)) :
    𝒢.genStalk :=
  (𝒢.G.left.presheaf.germ W 𝒢.genericUnit hW).hom b

theorem genericUnit_mem {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {W : 𝒢.G.left.Opens}
    (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W) : 𝒢.genericUnit ∈ W :=
  hVW hV

/-- **The sections over `V` of `e*Ω¹_{𝒢/S}`, through an open `W ⊇ e(V)` of `𝒢`, in the generic
fibre**: the image of `𝒪_S(V) ⊗_{𝒪_𝒢(W)} Ω[𝒪_𝒢(W)/𝓞_L]` in `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`, that is
the span of the `c|_η · (1 ⊗ d(b|_ξ))` for `c ∈ 𝒪_S(V)` and `b ∈ 𝒪_𝒢(W)`. -/
noncomputable def secOmega (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (W : 𝒢.G.left.Opens)
    (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W) :
    Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :=
  Submodule.span (𝓞 L) (Set.range fun cb : Γ(Spec (CommRingCat.of (𝓞 L)), V) × Γ(𝒢.G.left, W) =>
    germEta V hV cb.1 •
      ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk
        (germXi 𝒢 W (genericUnit_mem 𝒢 hV hVW) cb.2)))

/-- `t` is a section of `e*Ω¹_{𝒢/S}` near `s`. -/
def IsSecNear (s : Spec (CommRingCat.of (𝓞 L)))
    (t : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) : Prop :=
  ∃ (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (W : 𝒢.G.left.Opens) (hs : s ∈ V)
    (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W), t ∈ secOmega 𝒢 V W (genericPt_mem hs) hVW

theorem secOmega_mono {V V' : (Spec (CommRingCat.of (𝓞 L))).Opens} {W W' : 𝒢.G.left.Opens}
    (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)
    (hV' : genericPt L ∈ V') (hVW' : V' ≤ 𝒢.unitSection ⁻¹ᵁ W') (h1 : V' ≤ V) (h2 : W' ≤ W) :
    secOmega 𝒢 V W hV hVW ≤ secOmega 𝒢 V' W' hV' hVW' := by
  rw [secOmega, Submodule.span_le]
  rintro _ ⟨⟨c, b⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨(Spec (CommRingCat.of (𝓞 L))).presheaf.map (homOfLE h1).op c,
    𝒢.G.left.presheaf.map (homOfLE h2).op b⟩, ?_⟩
  simp only [germEta, germXi]
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- Being a section near `s` is closed under addition and `𝓞_L`-multiples. -/
noncomputable def secNear (s : Spec (CommRingCat.of (𝓞 L))) :
    Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) where
  carrier := {t | IsSecNear 𝒢 s t}
  zero_mem' := by
    refine ⟨𝒢.unitSection ⁻¹ᵁ ⊤, ⊤, trivial, le_rfl, Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨V₁, W₁, hs₁, h₁, hx⟩ ⟨V₂, W₂, hs₂, h₂, hy⟩
    refine ⟨V₁ ⊓ V₂, W₁ ⊓ W₂, ⟨hs₁, hs₂⟩, ?_, Submodule.add_mem _ ?_ ?_⟩
    · intro z hz; exact ⟨h₁ hz.1, h₂ hz.2⟩
    · exact secOmega_mono 𝒢 _ _ _ _ inf_le_left inf_le_left hx
    · exact secOmega_mono 𝒢 _ _ _ _ inf_le_right inf_le_right hy
  smul_mem' := by
    rintro a x ⟨V, W, hs, h, hx⟩
    exact ⟨V, W, hs, h, Submodule.smul_mem _ a hx⟩

/-! ## Sections near `s` lie in the stalk, and conversely -/

/-- The stalk `(e*Ω¹)_s` is stable under the fractions `a/t`, `t ∉ s`. -/
theorem smul_mem_printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L)))
    (β : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) (a t : 𝓞 L) (ht : t ∉ s.asIdeal)
    (r : Reta L) (hr : r * baseStalk (genericPt L) t = baseStalk (genericPt L) a) :
    r • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s β)) ∈
      printedOmegaAt 𝒢 s := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  set Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s
  letI : Algebra (𝓞 L) Os := (baseStalk s).toAlgebra
  haveI : IsLocalization.AtPrime Os s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
  have htu : IsUnit (unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) := by
    rw [unitStalk_stalkAlg]
    exact IsLocalization.map_units Os (⟨t, ht⟩ : s.asIdeal.primeCompl)
  have hu : IsUnit (stalkAlg 𝒢 (𝒢.unitSection s) t) := isUnit_of_map_unit (unitStalk 𝒢 s) _ htu
  set c := stalkAlg 𝒢 (𝒢.unitSection s) a * ↑hu.unit⁻¹
  have hsu : IsUnit (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) := hu.map (specMap 𝒢 s)
  have hinv : specMap 𝒢 s (↑hu.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) =
      ↑hsu.unit⁻¹ := by
    apply Units.eq_inv_of_mul_eq_one_left
    rw [IsUnit.unit_spec, ← map_mul]
    have h0 := hu.unit.mul_inv
    rw [hu.unit_spec] at h0
    rw [h0, map_one]
  have hDc : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s c) = 0 := by
    have hDt : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) = 0 := by
      rw [specMap_stalkAlg]; exact (D (𝓞 L) 𝒢.genStalk).map_algebraMap t
    have hDp : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) a)) = 0 := by
      rw [specMap_stalkAlg]; exact (D (𝓞 L) 𝒢.genStalk).map_algebraMap a
    rw [map_mul, Derivation.leibniz, hinv, D_inv_of_unit 𝒢 hsu hDt, hDp, smul_zero, smul_zero,
      add_zero]
  -- the image of `c` in `𝒪_{S,η}` is `r`
  have hcr : algebraMap 𝒢.genStalk (Reta L) (specMap 𝒢 s c) = r := by
    have hbt : IsUnit (baseStalk (genericPt L) t) := by
      have h1 := hsu.map (algebraMap 𝒢.genStalk (Reta L))
      rw [specMap_stalkAlg] at h1
      have h2 : algebraMap 𝒢.genStalk (Reta L) (𝒢.structMap t) = baseStalk (genericPt L) t :=
        unitStalk_stalkAlg 𝒢 (genericPt L) t
      rwa [h2] at h1
    apply hbt.mul_left_injective
    show _ * _ = _ * _
    rw [hr]
    have h3 : ∀ x : 𝓞 L, algebraMap 𝒢.genStalk (Reta L) (𝒢.structMap x) =
        baseStalk (genericPt L) x := fun x => unitStalk_stalkAlg 𝒢 (genericPt L) x
    rw [← h3 t, ← h3 a, ← map_mul]
    congr 1
    rw [map_mul, specMap_stalkAlg, hinv, _root_.mul_assoc, ← specMap_stalkAlg 𝒢 s t,
      IsUnit.val_inv_mul, _root_.mul_one]
  have key : r • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s β)) =
      (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s (c * β)) := by
    rw [map_mul, Derivation.leibniz, hDc, smul_zero, add_zero, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def (specMap 𝒢 s c), hcr, smul_eq_mul]
  rw [key]
  exact Submodule.subset_span ⟨c * β, rfl⟩

/-- A function on an open `V ∋ s` of `Spec 𝓞_L` is a fraction `a/t` with `t ∉ s`, at `η`. -/
theorem germEta_frac {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {s : Spec (CommRingCat.of (𝓞 L))}
    (hs : s ∈ V) (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) :
    ∃ a t : 𝓞 L, t ∉ s.asIdeal ∧
      germEta V (genericPt_mem hs) c * baseStalk (genericPt L) t = baseStalk (genericPt L) a := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  set Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s
  letI : Algebra (𝓞 L) Os := (baseStalk s).toAlgebra
  haveI : IsLocalization.AtPrime Os s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
  obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj s.asIdeal.primeCompl
    (((Spec (CommRingCat.of (𝓞 L))).presheaf.germ V s hs).hom c)
  refine ⟨a, t, t.2, ?_⟩
  set σ := ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalkSpecializes
    (genericPt_specializes s)).hom
  have hb : ∀ x : 𝓞 L, σ (baseStalk s x) = baseStalk (genericPt L) x := by
    intro x
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have hc : σ (((Spec (CommRingCat.of (𝓞 L))).presheaf.germ V s hs).hom c) =
      germEta V (genericPt_mem hs) c :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have h' := congrArg σ h
  rw [map_mul, hc] at h'
  rw [← hb, ← hb]
  exact h'

/-- **Sections over `V` lie in the stalk at every `s ∈ V`.** -/
theorem secOmega_le {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {W : 𝒢.G.left.Opens}
    {s : Spec (CommRingCat.of (𝓞 L))} (hs : s ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W) :
    secOmega 𝒢 V W (genericPt_mem hs) hVW ≤ printedOmegaAt 𝒢 s := by
  rw [secOmega, Submodule.span_le]
  rintro _ ⟨⟨c, b⟩, rfl⟩
  obtain ⟨a, t, ht, hr⟩ := germEta_frac hs c
  have hb : germXi 𝒢 W (genericUnit_mem 𝒢 (genericPt_mem hs) hVW) b =
      specMap 𝒢 s ((𝒢.G.left.presheaf.germ W (𝒢.unitSection s) (hVW hs)).hom b) :=
    (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  show _ • _ ∈ _
  rw [hb]
  exact smul_mem_printedOmegaAt 𝒢 s _ a t ht _ hr

/-- **Every element of the stalk at `s` is a section near `s`.** -/
theorem printedOmegaAt_le_secNear (s : Spec (CommRingCat.of (𝓞 L))) :
    printedOmegaAt 𝒢 s ≤ secNear 𝒢 s := by
  rw [printedOmegaAt, Submodule.span_le]
  rintro _ ⟨β, rfl⟩
  obtain ⟨W, hW, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ β
  refine ⟨𝒢.unitSection ⁻¹ᵁ W, W, hW, le_rfl, ?_⟩
  apply Submodule.subset_span
  refine ⟨⟨1, b⟩, ?_⟩
  simp only [germEta, map_one, one_smul, germXi]
  rw [← TopCat.Presheaf.germ_stalkSpecializes_apply _ hW (𝒢.specializes_genericUnit s)]
  rfl

/-- **`Γ(S, e*Ω¹_{𝒢/S})` in the generic fibre**: the elements that are sections near every point
of `S = Spec 𝓞_L` (the sheaf condition; the generic fibre carries the gluing). -/
noncomputable def globalOmega : Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :=
  ⨅ s, secNear 𝒢 s

/-- **The global sections of `e*Ω¹` are the intersection of the stalks.** -/
theorem globalOmega_eq : globalOmega 𝒢 = ⨅ s, printedOmegaAt 𝒢 s := by
  apply le_antisymm
  · refine le_iInf fun s => ?_
    intro t ht
    obtain ⟨V, W, hs, hVW, h⟩ := (Submodule.mem_iInf _).mp ht s
    exact secOmega_le 𝒢 hs hVW h
  · exact iInf_mono fun s => printedOmegaAt_le_secNear 𝒢 s

/-- **The tree's `ω` is `Γ(S, e*Ω¹_{𝒢/S})`**: `printedOmega` is the preimage of the global
sections under the injective `θ`. -/
theorem printedOmega_eq_comap_globalOmega :
    printedOmega 𝒢 = (globalOmega 𝒢).comap (theta' 𝒢) := by
  rw [globalOmega_eq]; rfl

end ZInQ.HeightModelM2

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

/-! ## The stalks are `𝒪_{S,s}`-lattices -/

/-- The stalk at `s` is stable under every fraction `a/t` with `t ∉ s`. -/
theorem smul_mem_printedOmegaAt_of_mem (s : Spec (CommRingCat.of (𝓞 L)))
    {u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (hu : u ∈ printedOmegaAt 𝒢 s)
    (a t : 𝓞 L) (ht : t ∉ s.asIdeal) (r : Reta L)
    (hr : r * baseStalk (genericPt L) t = baseStalk (genericPt L) a) :
    r • u ∈ printedOmegaAt 𝒢 s := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, rfl⟩ := hx
    exact smul_mem_printedOmegaAt 𝒢 s β a t ht r hr
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

theorem baseStalk_isUnit {t : 𝓞 L} (ht : t ≠ 0) : IsUnit (baseStalk (genericPt L) t) := by
  haveI := isLocalization_Reta (L := L)
  exact IsLocalization.map_units (Reta L) (⟨t, Ideal.mem_primeCompl_iff.mpr (by simpa using ht)⟩ :
    (⊥ : Ideal (𝓞 L)).primeCompl)

/-- **Saturation**: `t • u ∈ (e*Ω¹)_s` with `t ∉ s` gives `u ∈ (e*Ω¹)_s`. -/
theorem mem_of_smul_mem (s : Spec (CommRingCat.of (𝓞 L))) {t : 𝓞 L} (ht : t ∉ s.asIdeal)
    {u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (h : t • u ∈ printedOmegaAt 𝒢 s) :
    u ∈ printedOmegaAt 𝒢 s := by
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ Ideal.zero_mem _)
  have hbt := baseStalk_isUnit ht0
  have hr : (↑hbt.unit⁻¹ : Reta L) * baseStalk (genericPt L) t = baseStalk (genericPt L) 1 := by
    rw [map_one, IsUnit.val_inv_mul]
  have key := smul_mem_printedOmegaAt_of_mem 𝒢 s h 1 t ht _ hr
  rwa [← algebraMap_smul (Reta L) t u, smul_smul,
    show algebraMap (𝓞 L) (Reta L) t = baseStalk (genericPt L) t from rfl, IsUnit.val_inv_mul,
    one_smul] at key

/-- `1 ⊗ (x • ω) = x|_η • (1 ⊗ ω)`. -/
theorem one_tmul_smul (x : 𝒢.genStalk) (ω : Ω[𝒢.genStalk⁄𝓞 L]) :
    (1 : Reta L) ⊗ₜ[𝒢.genStalk] (x • ω) =
      algebraMap 𝒢.genStalk (Reta L) x • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] ω) := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul, _root_.mul_one]

/-- The elements with a nonzero `𝓞_L`-multiple in the stalk at `s`: an `𝒪_{S,η}`-submodule. -/
noncomputable def torsionHull (s : Spec (CommRingCat.of (𝓞 L))) :
    Submodule (Reta L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) where
  carrier := {u | ∃ a : 𝓞 L, a ≠ 0 ∧ a • u ∈ printedOmegaAt 𝒢 s}
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ b hx
    · rw [mul_smul]; exact Submodule.smul_mem _ a hy
  smul_mem' := by
    rintro r x ⟨a, ha, hx⟩
    haveI := isLocalization_Reta (L := L)
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (⊥ : Ideal (𝓞 L)).primeCompl r
    have hc : (c : 𝓞 L) ≠ 0 := fun h =>
      (Ideal.mem_primeCompl_iff.mp c.2) (by rw [h]; exact Ideal.zero_mem _)
    refine ⟨a * c, mul_ne_zero ha hc, ?_⟩
    have e1 : (a * c : 𝓞 L) • (r • x) = b • (a • x) := by
      rw [← algebraMap_smul (Reta L) (a * c), ← algebraMap_smul (Reta L) b,
        ← algebraMap_smul (Reta L) a, smul_smul, smul_smul, map_mul, _root_.mul_assoc,
        mul_comm (algebraMap (𝓞 L) (Reta L) c), hbc, mul_comm]
    show (a * c : 𝓞 L) • (r • x) ∈ printedOmegaAt 𝒢 s
    rw [e1]
    exact Submodule.smul_mem _ b hx

/-- **The stalk at `s` spans the generic fibre**: every element has a nonzero `𝓞_L`-multiple in
`(e*Ω¹)_s` (`𝒪_{𝒢,ξ}` is a localization of `𝒪_{𝒢,e(s)}`). -/
theorem torsionHull_eq_top (s : Spec (CommRingCat.of (𝓞 L))) : torsionHull 𝒢 s = ⊤ := by
  have hgen : ∀ β : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s),
      (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s β) ∈ torsionHull 𝒢 s :=
    fun β => ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨β, rfl⟩⟩
  have hD : ∀ f : 𝒢.genStalk, (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk f ∈
      torsionHull 𝒢 s := by
    intro f
    obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := 𝒢.unitSection s)
      (U := ⊤) trivial
    have hξU : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit s).mem_open U.isOpen hsU
    letI := TopCat.Presheaf.algebra_section_stalk 𝒢.G.left.presheaf
      (⟨𝒢.genericUnit, hξU⟩ : U)
    haveI := hU.isLocalization_stalk ⟨𝒢.genericUnit, hξU⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
      (hU.primeIdealOf ⟨𝒢.genericUnit, hξU⟩).asIdeal.primeCompl f
    have hq : IsUnit (algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk q) := IsLocalization.map_units _ q
    have hgerm : ∀ y : Γ(𝒢.G.left, U), algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk y =
        specMap 𝒢 s ((𝒢.G.left.presheaf.germ U (𝒢.unitSection s) hsU).hom y) := by
      intro y
      show (𝒢.G.left.presheaf.germ U 𝒢.genericUnit hξU).hom y = _
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply 𝒢.G.left.presheaf hsU
        (𝒢.specializes_genericUnit s) y).symm
    set Q := algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk q
    set P := algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk p
    have hP : (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk P ∈ torsionHull 𝒢 s := by
      have h := hgen ((𝒢.G.left.presheaf.germ U (𝒢.unitSection s) hsU).hom p)
      rwa [← hgerm] at h
    have hQ : (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk Q ∈ torsionHull 𝒢 s := by
      have h := hgen ((𝒢.G.left.presheaf.germ U (𝒢.unitSection s) hsU).hom q)
      rwa [← hgerm] at h
    -- `f = P / Q`, so `df = Q⁻¹ dP - Q⁻¹ f dQ`
    have hdf : D (𝓞 L) 𝒢.genStalk f =
        (↑hq.unit⁻¹ : 𝒢.genStalk) • D (𝓞 L) 𝒢.genStalk P -
          ((↑hq.unit⁻¹ : 𝒢.genStalk) * f) • D (𝓞 L) 𝒢.genStalk Q := by
      have h1 : D (𝓞 L) 𝒢.genStalk (f * Q) = D (𝓞 L) 𝒢.genStalk P := by
        rw [show f * Q = P from hpq]
      rw [Derivation.leibniz] at h1
      rw [← h1, smul_add, smul_smul, add_sub_cancel_left, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [hdf, TensorProduct.tmul_sub, one_tmul_smul, one_tmul_smul]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hP) (Submodule.smul_mem _ _ hQ)
  rw [eq_top_iff]
  rintro u -
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul r ω =>
    have hω : ω ∈ Submodule.span 𝒢.genStalk (Set.range (D (𝓞 L) 𝒢.genStalk)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction generalizing r with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      have : r ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk f =
          r • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this]; exact Submodule.smul_mem _ r (hD f)
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ (hx r) (hy r)
    | smul g x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _

/-- Every element has a nonzero `𝓞_L`-multiple in the stalk at `s`. -/
theorem exists_smul_mem_printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L)))
    (u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :
    ∃ a : 𝓞 L, a ≠ 0 ∧ a • u ∈ printedOmegaAt 𝒢 s := by
  have : u ∈ torsionHull 𝒢 s := by rw [torsionHull_eq_top]; trivial
  exact this

end ZInQ.HeightModelM2
