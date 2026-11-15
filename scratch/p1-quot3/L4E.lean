import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelC
import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelD

/-!
# p1-quot3, L4 part E: the chart rings of the extended coordinate are polynomial rings (scratch)
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace HDec.MCRGlue.P1Model

open VertWitness LeafQM.AV ModelGlue

section Rings

variable {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
  [IsIntegral 𝒵.left]

/-- Restriction from an open containing the image of a nonempty chart to the chart is injective. -/
theorem appLE_injective (σ : ToP1 (genFib 𝒵).left) (hne : (σ.U : Set (genFib 𝒵).left).Nonempty)
    (W : 𝒵.left.Opens) (hf : σ.U ≤ jj 𝒵 ⁻¹ᵁ W) :
    Function.Injective ((jj 𝒵).appLE W σ.U hf) := by
  have hle : jj 𝒵 ''ᵁ σ.U ≤ W := by rintro _ ⟨y, hy, rfl⟩; exact hf hy
  haveI : Nonempty (jj 𝒵 ''ᵁ σ.U) := by
    obtain ⟨y, hy⟩ := hne; exact ⟨⟨jj 𝒵 y, y, hy, rfl⟩⟩
  intro a b hab
  have e : ∀ s, (jj 𝒵).appLE W σ.U hf s =
      ((jj 𝒵).appIso σ.U).hom (𝒵.left.presheaf.map (homOfLE hle).op s) := by
    intro s
    rw [Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply]
    erw [Scheme.Hom.map_appLE]
  rw [e, e] at hab
  exact map_injective_of_isIntegral 𝒵.left (homOfLE hle)
    ((ConcreteCategory.bijective_of_isIso ((jj 𝒵).appIso σ.U).hom).1 hab)

/-- A constant of `ℤ_(p)` is invertible at a point of the special fibre iff it is a unit. -/
theorem mem_basicOpen_cst_iff (c : Zloc p) (W : 𝒵.left.Opens) (x : 𝒵.left) (hxW : x ∈ W)
    (hx : 𝒵.hom x = s0 p) : x ∈ 𝒵.left.basicOpen (cst 𝒵 c W) ↔ IsUnit c := by
  haveI := zloc_isDVR' (p := p)
  constructor
  · intro h
    have h1 : 𝒵.left.basicOpen (cst 𝒵 c W) = W ⊓ 𝒵.hom ⁻¹ᵁ
        (Spec (CommRingCat.of (Zloc p))).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv c) := by
      rw [cst, baseToSectionsOver_eq_appLE]
      exact Scheme.basicOpen_appLE _ _ _ _ _
    rw [h1] at h
    have h2 := h.2
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe] at h2
    rw [basicOpen_eq_of_affine, hx] at h2
    by_contra hnu
    exact h2 ((IsLocalRing.mem_maximalIdeal c).2 hnu)
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ (hu.map _)]
    exact hxW

theorem map_divX' {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (h : A[X]) :
    (h.divX).map φ = (h.map φ).divX := by
  ext n; simp [Polynomial.coeff_divX]

variable [IsProper 𝒵.hom] [SmoothOfRelativeDimension 1 𝒵.hom] [GeometricallyConnected 𝒵.hom]

/-- **The residue of the extended coordinate at `ξ` is transcendental over `𝔽_p`**: a polynomial with nonzero
reduction mod `p` does not vanish at `ξ` when evaluated at the coordinate (it vanishes at the zero `x0` only through
its constant term). -/
theorem xi_mem_basicOpen_eval (ρ : ToP1 𝒵.left) (x0 : 𝒵.left) (hx0U : x0 ∈ ρ.U)
    (hx0s : 𝒵.hom x0 = s0 p) (hx0f : x0 ∉ 𝒵.left.basicOpen ρ.f)
    (hξf : xi 𝒵 ∈ 𝒵.left.basicOpen ρ.f) (h : (Zloc p)[X])
    (hh : h.map (IsLocalRing.residue (Zloc p)) ≠ 0) :
    xi 𝒵 ∈ 𝒵.left.basicOpen (eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h) := by
  haveI := zloc_isDVR' (p := p)
  have hξU : xi 𝒵 ∈ ρ.U := 𝒵.left.basicOpen_le _ hξf
  have hξx0 : xi 𝒵 ⤳ x0 := xi_specializes 𝒵 hx0s
  induction hn : h.natDegree using Nat.strong_induction_on generalizing h with
  | _ n ih =>
    have hdec : eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h =
        ρ.f * eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h.divX + cst 𝒵 (h.coeff 0) ρ.U := by
      have e := congrArg (eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f) (X_mul_divX_add h).symm
      rw [eval₂_add, eval₂_mul, eval₂_X, eval₂_C] at e
      exact e
    by_cases hu : IsUnit (h.coeff 0)
    · -- the value at `x0` is the unit `h(0)`
      have hx0 : x0 ∈ 𝒵.left.basicOpen (eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h) := by
        by_contra hx
        have h1 := basicOpen_sub_le (eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h) (ρ.f * eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h.divX)
        rw [hdec, add_sub_cancel_left] at h1
        have h2 := (mem_basicOpen_cst_iff 𝒵 (h.coeff 0) ρ.U x0 hx0U hx0s).2 hu
        rcases h1 h2 with h3 | h3
        · exact hx (by rw [hdec]; exact h3)
        · rw [Scheme.basicOpen_mul] at h3; exact hx0f h3.1
      exact hξx0.mem_open (𝒵.left.basicOpen _).isOpen hx0
    · -- the constant term vanishes on the special fibre: induct on `h / X`
      have hres0 : IsLocalRing.residue (Zloc p) (h.coeff 0) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
      have hd : (h.divX).map (IsLocalRing.residue (Zloc p)) ≠ 0 := by
        intro h0
        apply hh
        rw [← X_mul_divX_add (h.map (IsLocalRing.residue (Zloc p))), ← map_divX', h0, coeff_map,
          hres0]
        simp
      have hlt : h.divX.natDegree < n := by
        rw [natDegree_divX_eq_natDegree_tsub_one, hn]
        have hpos : 0 < n := by
          rw [← hn]
          by_contra hz
          push Not at hz
          apply hh
          rw [eq_C_of_natDegree_eq_zero (Nat.le_zero.1 hz), Polynomial.map_C, hres0, C_0]
        omega
      have ih' := ih _ hlt h.divX hd rfl
      by_contra hx
      have h1 := basicOpen_sub_le (eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h) (cst 𝒵 (h.coeff 0) ρ.U)
      rw [hdec, add_sub_cancel_right] at h1
      have h2 : xi 𝒵 ∈ 𝒵.left.basicOpen (ρ.f * eval₂ (baseToSectionsOver _ 𝒵 ρ.U) ρ.f h.divX) := by
        rw [Scheme.basicOpen_mul]; exact ⟨hξf, ih'⟩
      rcases h1 h2 with h3 | h3
      · exact hx (by rw [hdec]; exact h3)
      · exact hu ((mem_basicOpen_cst_iff 𝒵 (h.coeff 0) ρ.U (xi 𝒵) hξU (xi_mem 𝒵)).1 h3)

/-- **The chart ring is the polynomial ring in the extended coordinate.** -/
theorem eval_bijective (σ : ToP1 (genFib 𝒵).left) (hσ : IsP1CoordinateQ (genFib 𝒵) σ)
    (hne : (σ.U : Set (genFib 𝒵).left).Nonempty) (ρ : ToP1 𝒵.left) (hf : σ.U ≤ jj 𝒵 ⁻¹ᵁ ρ.U)
    (hf1 : (jj 𝒵).appLE _ σ.U hf ρ.f = σ.f) (x0 : 𝒵.left) (hx0U : x0 ∈ ρ.U)
    (hx0s : 𝒵.hom x0 = s0 p) (hx0f : x0 ∉ 𝒵.left.basicOpen ρ.f)
    (hξf : xi 𝒵 ∈ 𝒵.left.basicOpen ρ.f) :
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 ρ.U) ρ.f) := by
  haveI := zloc_isDVR' (p := p)
  set ev := eval₂RingHom (baseToSectionsOver _ 𝒵 ρ.U) ρ.f
  set res := ((jj 𝒵).appLE _ σ.U hf).hom
  set evQ := eval₂RingHom (baseToSectionsOver (CommRingCat.of ℚ) (genFib 𝒵) σ.U) σ.f
  have hres : Function.Injective res := appLE_injective 𝒵 σ hne _ hf
  have hcomm : res.comp ev = evQ.comp (mapRingHom (zlocToRat p)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, ev, evQ, coe_eval₂RingHom, eval₂_C, coe_mapRingHom,
        Polynomial.map_C, res]
      exact appLE_cst 𝒵 c ρ.U σ.U hf
    · simp only [RingHom.comp_apply, ev, evQ, coe_eval₂RingHom, eval₂_X, coe_mapRingHom,
        Polynomial.map_X, res]
      exact hf1
  have hcomm' : ∀ q, res (ev q) = evQ (q.map (zlocToRat p)) := fun q =>
    congrArg (fun φ => φ q) hcomm
  have hmapinj : Function.Injective (Polynomial.map (zlocToRat p)) :=
    Polynomial.map_injective _ (zlocToRat_injective p)
  refine ⟨fun a b hab => hmapinj (hσ.2.2.1.1 ?_), fun s => ?_⟩
  · rw [← hcomm', ← hcomm', hab]
  -- surjectivity: clear the denominators of the polynomial representing `s` on the generic fibre
  obtain ⟨Q, hQ⟩ := hσ.2.2.1.2 (res s)
  letI : Algebra (Zloc p) ℚ := (zlocToRat p).toAlgebra
  haveI := zloc_away p
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.integerNormalization_spec
    (Submonoid.powers (p : Zloc p)) Q
  have hp0 : (p : Zloc p) ∉ IsLocalRing.maximalIdeal (Zloc p) → False := fun h =>
    h (by rw [maximalIdeal_Zloc]; exact Ideal.subset_span rfl)
  have hpξ : xi 𝒵 ∉ 𝒵.left.basicOpen (cst 𝒵 (p : Zloc p) ρ.U) := fun h =>
    hp0 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm
      ((mem_basicOpen_cst_iff 𝒵 _ ρ.U (xi 𝒵) (𝒵.left.basicOpen_le _ hξf) (xi_mem 𝒵)).1 h)
  suffices H : ∀ (k : ℕ) (h : (Zloc p)[X]), h.map (zlocToRat p) = ((p : Zloc p) ^ k) • Q →
      ∃ a, ev a = s from H k _ hk
  intro k
  induction k with
  | zero =>
    intro h hh
    refine ⟨h, hres ?_⟩
    rw [hcomm', hh, pow_zero, one_smul]
    exact hQ
  | succ m ihm =>
    intro h hh
    -- `ev h = p^(m+1) s`
    have hevh : ev h = cst 𝒵 (p : Zloc p) ρ.U ^ (m + 1) * s := by
      apply hres
      rw [hcomm', hh, map_mul, map_pow]
      simp only [res]
      rw [appLE_cst 𝒵 _ ρ.U σ.U hf, Algebra.smul_def, map_mul, ← hQ]
      congr 1
      rw [Polynomial.algebraMap_apply]
      simp only [evQ, coe_eval₂RingHom, eval₂_C, map_pow]
      rfl
    by_cases hr : h.map (IsLocalRing.residue (Zloc p)) = 0
    · -- all coefficients are divisible by `p`
      have hcoef : ∀ n, h.coeff n ∈ Ideal.span {(p : Zloc p)} := by
        intro n
        rw [← maximalIdeal_Zloc, ← IsLocalRing.residue_eq_zero_iff]
        have := congrArg (fun q => q.coeff n) hr
        simpa [coeff_map] using this
      have hmem : h ∈ Ideal.span {C (p : Zloc p)} := by
        have : h ∈ Ideal.map (C : Zloc p →+* (Zloc p)[X]) (Ideal.span {(p : Zloc p)}) :=
          (Ideal.mem_map_C_iff).2 hcoef
        rwa [Ideal.map_span, Set.image_singleton] at this
      obtain ⟨h', rfl⟩ := (Ideal.mem_span_singleton').1 hmem
      refine ihm h' ?_
      have hp0 : (C ((zlocToRat p) (p : Zloc p)) : ℚ[X]) ≠ 0 := by
        rw [Ne, C_eq_zero, map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply mul_right_cancel₀ hp0
      rw [← Polynomial.map_C, ← Polynomial.map_mul, hh, Algebra.smul_def, Algebra.smul_def,
        Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
      simp only [map_pow, Polynomial.map_C, RingHom.algebraMap_toAlgebra]
      ring
    · exfalso
      have h1 := xi_mem_basicOpen_eval 𝒵 ρ x0 hx0U hx0s hx0f hξf h hr
      change xi 𝒵 ∈ 𝒵.left.basicOpen (ev h) at h1
      rw [hevh, Scheme.basicOpen_mul] at h1
      have hle : 𝒵.left.basicOpen (cst 𝒵 (p : Zloc p) ρ.U ^ (m + 1)) ≤
          𝒵.left.basicOpen (cst 𝒵 (p : Zloc p) ρ.U) := by
        rw [pow_succ, Scheme.basicOpen_mul]; exact inf_le_right
      exact hpξ (hle h1.1)

end Rings

/-! ## Fibres of the map to `P¹` are finite -/

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- In an irreducible noetherian sober space without strict chains of length `2`, a continuous map sending closed
points to closed points and not constant has finite fibres. -/
theorem finite_preimage_of_dim_le_one [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [IrreducibleSpace X]
    [T0Space X]
    (hchain : ∀ a b c : X, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False)
    (g : X → Y) (hg : Continuous g) (hcl : ∀ a, IsClosed ({a} : Set X) → IsClosed ({g a} : Set Y))
    (hnc : ∃ a b, g a ≠ g b) (w : Y) : (g ⁻¹' {w}).Finite := by
  set gen := genericPoint X
  have hgen : ∀ a : X, gen ⤳ a := fun a => (genericPoint_spec X).specializes trivial
  have hclosed : ∀ a : X, a ≠ gen → IsClosed ({a} : Set X) := by
    intro a ha
    refine closure_subset_iff_isClosed.1 fun b hb => ?_
    have hab : a ⤳ b := specializes_iff_mem_closure.2 hb
    by_contra hne
    exact hchain gen a b (hgen a) hab (Ne.symm ha) (fun h => hne h.symm)
  by_cases hw : IsClosed ({w} : Set Y)
  · have hZ : IsClosed (g ⁻¹' {w}) := hw.preimage hg
    by_cases hgZ : gen ∈ g ⁻¹' {w}
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : g a = w := (hgen a).mem_closed hZ hgZ
      have hb : g b = w := (hgen b).mem_closed hZ hgZ
      exact hab (ha.trans hb.symm)
    · obtain ⟨S, hSf, hSc, hSi, hSeq⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
      rw [hSeq]
      refine hSf.sUnion fun t ht => ?_
      obtain ⟨gt, hgt⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
      have hmem : gt ∈ g ⁻¹' {w} := by
        rw [hSeq]; exact ⟨t, ht, hgt.mem⟩
      have hne : gt ≠ gen := fun h => hgZ (h ▸ hmem)
      have hc := hclosed _ hne
      have : t = {gt} := by
        rw [← hgt.def, hc.closure_eq]
      rw [this]; exact Set.finite_singleton _
  · refine (Set.finite_singleton gen).subset fun a ha => ?_
    by_contra hne
    exact hw (by rw [← ha]; exact hcl a (hclosed a hne))

end Topology

section FiniteMap

variable {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
  [IsIntegral 𝒵.left] [IsProper 𝒵.hom] [SmoothOfRelativeDimension 1 𝒵.hom]
  [GeometricallyConnected 𝒵.hom]
  (φ : 𝒵.left ⟶ PR.LR (Zloc p)) (hφ : φ ≫ (PR.LR (Zloc p) ↘ PR.SR (Zloc p)) = 𝒵.hom)

/-- The map on fibres over a point of `Spec ℤ_(p)`. -/
def phiFib (s : Spec (CommRingCat.of (Zloc p))) :
    𝒵.hom.fiber s ⟶ (PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiber s :=
  pullback.map _ _ _ _ φ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hφ]) (by simp)

include hφ in
theorem phiFib_ι (s : Spec (CommRingCat.of (Zloc p))) :
    phiFib 𝒵 φ hφ s ≫ (PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberι s = 𝒵.hom.fiberι s ≫ φ :=
  pullback.lift_fst _ _ _

include hφ in
theorem phiFib_toSpec (s : Spec (CommRingCat.of (Zloc p))) :
    phiFib 𝒵 φ hφ s ≫ (PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberToSpecResidueField s =
      𝒵.hom.fiberToSpecResidueField s := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

include hφ in
/-- **The fibres of `φ` are finite** if on each fibre of the model two points have different images. -/
theorem preimage_finite (hpts : ∀ s, ∃ a b : 𝒵.left, 𝒵.hom a = s ∧ 𝒵.hom b = s ∧ φ a ≠ φ b)
    (w : PR.LR (Zloc p)) : (φ ⁻¹' {w}).Finite := by
  set s := (PR.LR (Zloc p) ↘ PR.SR (Zloc p)) w
  obtain ⟨a, b, ha, hb, hab⟩ := hpts s
  haveI : Nonempty (𝒵.hom.fiber s) := ⟨(𝒵.hom.fiberHomeo s).symm ⟨a, ha⟩⟩
  haveI := isIntegral_fiber 𝒵 s
  haveI : IsNoetherian 𝒵.left :=
    { toCompactSpace := (quasiCompact_iff_compactSpace 𝒵.hom).mp inferInstance }
  haveI : TopologicalSpace.NoetherianSpace (𝒵.hom.fiber s) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph (𝒵.hom.fiberHomeo s)).mpr inferInstance
  have hlft : LocallyOfFiniteType (phiFib 𝒵 φ hφ s ≫
      (PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberToSpecResidueField s) := by
    rw [phiFib_toSpec]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback 𝒵.hom _) inferInstance
  haveI := hlft
  haveI := locallyOfFiniteType_of_comp (phiFib 𝒵 φ hφ s)
    ((PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberToSpecResidueField s)
  have hchain : ∀ x y z : 𝒵.hom.fiber s, x ⤳ y → y ⤳ z → x ≠ y → y ≠ z → False := by
    intro x y z hxy hyz hne1 hne2
    haveI := zloc_isDVR' (p := p)
    have h1 : z < y := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hyz)
      (fun h => hne2 (hyz.antisymm (Scheme.le_iff_specializes.1 h)).eq)
    have h2 : y < x := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hxy)
      (fun h => hne1 (hxy.antisymm (Scheme.le_iff_specializes.1 h)).eq)
    have hd := QuotientP1Proof.topologicalKrullDim_fiber_le (R := Zloc p) 𝒵.hom s
    rw [QuotientP1Proof.topologicalKrullDim_eq_krullDim] at hd
    have hl := Order.LTSeries.length_le_krullDim (QuotientP1Proof.lt3 h1 h2)
    rw [QuotientP1Proof.lt3_length] at hl
    have : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := hl.trans hd
    exact absurd this (by decide)
  have hcl : ∀ x : 𝒵.hom.fiber s, IsClosed ({x} : Set _) →
      IsClosed ({phiFib 𝒵 φ hφ s x} : Set _) := fun x hx =>
    (phiFib 𝒵 φ hφ s).closedPoints_subset_preimage_closedPoints hx
  have hι : ∀ x : 𝒵.hom.fiber s,
      (PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberι s (phiFib 𝒵 φ hφ s x) = φ (𝒵.hom.fiberι s x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, phiFib_ι, Scheme.Hom.comp_apply]
  have hnc : ∃ x y : 𝒵.hom.fiber s, phiFib 𝒵 φ hφ s x ≠ phiFib 𝒵 φ hφ s y := by
    refine ⟨(𝒵.hom.fiberHomeo s).symm ⟨a, ha⟩, (𝒵.hom.fiberHomeo s).symm ⟨b, hb⟩, fun h => hab ?_⟩
    have := congrArg ((PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberι s) h
    rwa [hι, hι, Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_fiberHomeo_symm] at this
  obtain ⟨w', hw'⟩ : w ∈ Set.range ((PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberι s) := by
    rw [Scheme.Hom.range_fiberι]; rfl
  have hfin := finite_preimage_of_dim_le_one hchain (phiFib 𝒵 φ hφ s)
    (phiFib 𝒵 φ hφ s).continuous hcl hnc w'
  refine (hfin.image (𝒵.hom.fiberι s)).subset fun x hx => ?_
  have hxs : 𝒵.hom x = s := by
    rw [← hφ, Scheme.Hom.comp_apply]
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [hx]
  refine ⟨(𝒵.hom.fiberHomeo s).symm ⟨x, hxs⟩, ?_, Scheme.Hom.fiberι_fiberHomeo_symm _ _ _⟩
  apply ((PR.LR (Zloc p) ↘ PR.SR (Zloc p)).fiberι s).isEmbedding.injective
  rw [hι, Scheme.Hom.fiberι_fiberHomeo_symm, hw']
  exact hx

include hφ in
/-- **The map to `P¹` is finite.** -/
theorem isFinite_phi (hpts : ∀ s, ∃ a b : 𝒵.left, 𝒵.hom a = s ∧ 𝒵.hom b = s ∧ φ a ≠ φ b) :
    IsFinite φ := by
  haveI : IsProper (φ ≫ (PR.LR (Zloc p) ↘ PR.SR (Zloc p))) := by rw [hφ]; infer_instance
  haveI : IsProper φ := IsProper.of_comp φ (PR.LR (Zloc p) ↘ PR.SR (Zloc p))
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ (PR.LR (Zloc p) ↘ PR.SR (Zloc p))
  haveI : LocallyQuasiFinite φ :=
    LocallyQuasiFinite.of_finite_preimage_singleton φ (preimage_finite 𝒵 φ hφ hpts)
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ

end FiniteMap

/-! ## The model is `P¹_{ℤ_(p)}` -/

section Main

variable {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
  [IsIntegral 𝒵.left] [IsProper 𝒵.hom] [SmoothOfRelativeDimension 1 𝒵.hom]

theorem hom_eq_of_ne_s0 {s t : Spec (CommRingCat.of (Zloc p))} (hs : s ≠ s0 p) (ht : t ≠ s0 p) :
    s = t := by
  haveI := zloc_isDVR' (p := p)
  exact PrimeSpectrum.ext ((QuotientP1Proof.asIdeal_eq_bot_of_ne_closedPoint _ _ hs).trans
    (QuotientP1Proof.asIdeal_eq_bot_of_ne_closedPoint _ _ ht).symm)

/-- **A smooth proper model of `P¹_ℚ` over `ℤ_(p)` with three generic points (zero, pole, unit value) whose closures
are pairwise disjoint is `P¹_{ℤ_(p)}`, in a coordinate extending the generic one.** -/
theorem exists_p1Coordinate (σ : ToP1 (genFib 𝒵).left) (hσ : IsP1CoordinateQ (genFib 𝒵) σ)
    (y0 yinf yc : (genFib 𝒵).left) (c : Zloc p) (hc : IsUnit c)
    (hy0U : y0 ∈ σ.U) (hy0 : y0 ∉ (genFib 𝒵).left.basicOpen σ.f) (hyinf : yinf ∉ σ.U)
    (hycU : yc ∈ σ.U)
    (hycv : yc ∉ (genFib 𝒵).left.basicOpen
      (σ.f - baseToSectionsOver (CommRingCat.of ℚ) (genFib 𝒵) σ.U (zlocToRat p c)))
    (hcl0 : ∀ x ∈ closure {jj 𝒵 y0}, 𝒵.hom x ≠ s0 p → x = jj 𝒵 y0)
    (hclinf : ∀ x ∈ closure {jj 𝒵 yinf}, 𝒵.hom x ≠ s0 p → x = jj 𝒵 yinf)
    (d0inf : Disjoint (closure {jj 𝒵 y0}) (closure {jj 𝒵 yinf}))
    (d0c : Disjoint (closure {jj 𝒵 yc}) (closure {jj 𝒵 y0}))
    (dinfc : Disjoint (closure {jj 𝒵 yc}) (closure {jj 𝒵 yinf})) :
    ∃ ρ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ ∧
      ∀ (K : Type) [Field K] (z : Spec (CommRingCat.of K) ⟶ (genFib 𝒵).left),
        ρ.val (z ≫ jj 𝒵) = σ.val z := by
  haveI : Smooth 𝒵.hom := SmoothOfRelativeDimension.smooth 1 _
  haveI : GeometricallyConnected 𝒵.hom := geometricallyConnected 𝒵 σ hσ
  obtain ⟨ρ, hU, hV, hf, hg, hf1, hg1⟩ := exists_toP1 𝒵 σ hσ y0 yinf yc c hc hy0U hy0 hyinf hycU
    hycv hcl0 hclinf d0inf d0c dinfc
  have hyinfV : yinf ∈ σ.V := by
    have : yinf ∈ σ.U ⊔ σ.V := by rw [σ.cover]; trivial
    exact this.resolve_left hyinf
  -- the special points
  obtain ⟨x0, hx0, hx0s⟩ := exists_s0_mem_closure 𝒵 (jj 𝒵 y0)
  obtain ⟨xi', hxi', hxi's⟩ := exists_s0_mem_closure 𝒵 (jj 𝒵 yinf)
  have hξinf := xi_notMem_closure 𝒵 yc dinfc
  have hξ0 := xi_notMem_closure 𝒵 yc d0c
  have hx0U : x0 ∈ ρ.U := by rw [hU]; exact fun h => Set.disjoint_left.mp d0inf hx0 h
  have hx0V : x0 ∉ ρ.V := by rw [hV]; exact fun h => h hx0
  have hxiV : xi' ∈ ρ.V := by rw [hV]; exact fun h => Set.disjoint_left.mp d0inf h hxi'
  have hxiU : xi' ∉ ρ.U := by rw [hU]; exact fun h => h hxi'
  have hξU : xi 𝒵 ∈ ρ.U := by rw [hU]; exact hξinf
  have hξV : xi 𝒵 ∈ ρ.V := by rw [hV]; exact hξ0
  have hξf : xi 𝒵 ∈ 𝒵.left.basicOpen ρ.f := by rw [ρ.basicOpen_f]; exact ⟨hξU, hξV⟩
  have hξg : xi 𝒵 ∈ 𝒵.left.basicOpen ρ.g := by rw [ρ.basicOpen_g]; exact ⟨hξU, hξV⟩
  have hx0f : x0 ∉ 𝒵.left.basicOpen ρ.f := by rw [ρ.basicOpen_f]; exact fun h => hx0V h.2
  have hxig : xi' ∉ 𝒵.left.basicOpen ρ.g := by rw [ρ.basicOpen_g]; exact fun h => hxiU h.1
  -- the map to `P¹_{ℤ_(p)}` is finite
  set φ := PR.zHom (Zloc p) ρ 𝒵.hom
  have hφ : φ ≫ (PR.LR (Zloc p) ↘ PR.SR (Zloc p)) = 𝒵.hom := PR.zHom_over (Zloc p) ρ 𝒵.hom
  have hpre0 : φ ⁻¹ᵁ PR.stdR (Zloc p) QuotientP1Proof.i0 = ρ.U := PR.zHom_preimage0 (Zloc p) ρ 𝒵.hom
  have hpre1 : φ ⁻¹ᵁ PR.stdR (Zloc p) QuotientP1Proof.i1 = ρ.V := PR.zHom_preimage1 (Zloc p) ρ 𝒵.hom
  have hsep : ∀ a b : 𝒵.left, a ∈ ρ.U → b ∉ ρ.U → φ a ≠ φ b := by
    intro a b ha hb hab
    apply hb
    rw [← hpre0] at ha ⊢
    change φ b ∈ PR.stdR (Zloc p) QuotientP1Proof.i0
    rw [← hab]; exact ha
  have hpts : ∀ s, ∃ a b : 𝒵.left, 𝒵.hom a = s ∧ 𝒵.hom b = s ∧ φ a ≠ φ b := by
    intro s
    by_cases hs : s = s0 p
    · exact ⟨x0, xi', hx0s.trans hs.symm, hxi's.trans hs.symm, hsep _ _ hx0U hxiU⟩
    · refine ⟨jj 𝒵 y0, jj 𝒵 yinf, hom_eq_of_ne_s0 (hom_jj_ne 𝒵 y0) hs,
        hom_eq_of_ne_s0 (hom_jj_ne 𝒵 yinf) hs, hsep _ _ ?_ ?_⟩
      · rw [hU]; exact fun h => Set.disjoint_left.mp d0inf (subset_closure rfl) h
      · rw [hU]; exact fun h => h (subset_closure rfl)
  haveI := isFinite_phi 𝒵 φ hφ hpts
  have hUa : IsAffineOpen ρ.U := by
    rw [← hpre0]; exact (AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen _ _ _).preimage φ
  have hVa : IsAffineOpen ρ.V := by
    rw [← hpre1]; exact (AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen _ _ _).preimage φ
  refine ⟨ρ, ⟨hUa, hVa, ?_, ?_⟩, ?_⟩
  · exact eval_bijective 𝒵 σ hσ ⟨y0, hy0U⟩ ρ hf hf1 x0 hx0U hx0s hx0f hξf
  · exact eval_bijective 𝒵 (swapP1 σ) (isP1CoordinateQ_swap _ σ hσ) ⟨yinf, hyinfV⟩ (swapP1 ρ) hg
      hg1 xi' hxiV hxi's hxig hξg
  · intro K _ z
    rw [← ToP1.val_comp_right]
    have hpre : jj 𝒵 ⁻¹ᵁ ρ.U = σ.U := by
      refine le_antisymm (fun y hy => ?_) hf
      by_contra hyU
      have := eq_of_notMem_U _ σ hσ hyU hyinf
      subst this
      have hy' : jj 𝒵 y ∈ ρ.U := hy
      rw [hU] at hy'
      exact hy' (subset_closure rfl)
    refine val_eq_of_res (ρ.comp (jj 𝒵)) σ hpre ?_ z
    rw [← hf1]
    simp only [ToP1.comp, Scheme.Hom.appLE]
    rfl

end Main

end HDec.MCRGlue.P1Model
