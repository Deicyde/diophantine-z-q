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

end HDec.MCRGlue.P1Model
