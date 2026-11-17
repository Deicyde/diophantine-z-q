import ZInQKernel.Contrib.OneProof.AnalyticStableHeight

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set Filter MonObj MonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix ZInQ.R3Residual

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.R3Etale

/-! ## §0. Evaluation of sections at complex points; sections of fibre products -/

section Eval

open Limits

/-- The value at a complex point `y : Spec ℂ → Y` of a section `s ∈ Γ(Y, U)` (`0` off `U(ℂ)`). -/
noncomputable def evS {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ y ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (y.appLE U ⊤ h s) else 0

theorem evS_of_le {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U))
    (h : ⊤ ≤ y ⁻¹ᵁ U) :
    evS y U s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (y.appLE U ⊤ h s) := by
  rw [evS, dite_eq_left_of_eq_true (eq_true h)]

/-- Functoriality of evaluation. -/
theorem evS_comp {Y Z : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) (h : ⊤ ≤ (y ≫ f) ⁻¹ᵁ U) : evS (y ≫ f) U s = evS y (f ⁻¹ᵁ U) (f.app U s) := by
  have h' : ⊤ ≤ y ⁻¹ᵁ (f ⁻¹ᵁ U) := h
  rw [evS_of_le _ _ _ h, evS_of_le _ _ _ h', Scheme.Hom.comp_appLE]
  rfl

/-- Evaluation commutes with restriction. -/
theorem evS_res {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) {U U' : Y.Opens} (i : U' ≤ U)
    (s : Γ(Y, U)) (h : ⊤ ≤ y ⁻¹ᵁ U') :
    evS y U s = evS y U' (Y.presheaf.map (homOfLE i).op s) := by
  have h2 : ⊤ ≤ y ⁻¹ᵁ U := h.trans (fun x hx => i hx)
  rw [evS_of_le _ _ _ h2, evS_of_le _ _ _ h]
  rw [← Scheme.Hom.map_appLE y h (homOfLE i).op]
  rfl

/-- Evaluation is a ring homomorphism on sections over an open containing the point. -/
noncomputable def evHom {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    Γ(Y, U) →+* ℂ :=
  ((y.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem evHom_apply {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(Y, U)) : evHom y U h s = evS y U s := by
  rw [evS_of_le _ _ _ h]; rfl

/-- Evaluation of global sections of an affine `Spec T` at the point given by `ξ : T → ℂ`. -/
theorem evS_spec_top {T : CommRingCat} (ξ : T ⟶ CommRingCat.of ℂ) (t : T) :
    evS (Spec.map ξ) ⊤ ((Scheme.ΓSpecIso T).inv t) = ξ t := by
  rw [evS_of_le _ _ _ (by simp)]
  have h1 := Scheme.ΓSpecIso_naturality ξ
  have h2 : (Spec.map ξ).appLE ⊤ ⊤ (by simp) = (Spec.map ξ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h2]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso T).inv t)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp

theorem top_le_preimage_basicOpen_iff {T : CommRingCat} (ξ : T ⟶ CommRingCat.of ℂ) (f : Γ(Spec T, ⊤)) :
    ⊤ ≤ (Spec.map ξ) ⁻¹ᵁ (Spec T).basicOpen f ↔ ξ ((Scheme.ΓSpecIso T).hom f) ≠ 0 := by
  rw [Scheme.preimage_basicOpen_top]
  have hnat : (Spec.map ξ).appTop f =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (ξ ((Scheme.ΓSpecIso T).hom f)) := by
    have h1 := congrArg (fun φ => φ.hom f) (Scheme.ΓSpecIso_naturality ξ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    rw [← h1]; simp
  rw [hnat]
  constructor
  · intro h h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at h
    exact (h (Set.mem_univ (IsLocalRing.closedPoint ℂ))).elim
  · intro h
    rw [Scheme.basicOpen_of_isUnit]
    exact (isUnit_iff_ne_zero.mpr h).map _

/-- **Sections near a point of `Spec T` are fractions.** -/
theorem exists_fraction {T : CommRingCat} (ξ : T ⟶ CommRingCat.of ℂ) (O : (Spec T).Opens)
    (σ : Γ(Spec T, O)) (hO : ⊤ ≤ (Spec.map ξ) ⁻¹ᵁ O) :
    ∃ (t r : T) (n : ℕ), ξ r ≠ 0 ∧ ∀ ξ' : T ⟶ CommRingCat.of ℂ, ξ' r ≠ 0 →
      ⊤ ≤ (Spec.map ξ') ⁻¹ᵁ O ∧ evS (Spec.map ξ') O σ * (ξ' r) ^ n = ξ' t := by
  classical
  have hx : (Spec.map ξ) (IsLocalRing.closedPoint ℂ) ∈ O := hO (Set.mem_univ _)
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfO⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen (Spec T)) hx
  have hDO : (Spec T).basicOpen f ≤ O := hfO
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f ((Spec T).presheaf.map (homOfLE hDO).op σ)
  refine ⟨(Scheme.ΓSpecIso T).hom a, (Scheme.ΓSpecIso T).hom f, n, ?_, ?_⟩
  · rw [← top_le_preimage_basicOpen_iff]
    intro z _
    have : z = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hxf
  · intro ξ' hξ'
    have h1 : ⊤ ≤ (Spec.map ξ') ⁻¹ᵁ (Spec T).basicOpen f := (top_le_preimage_basicOpen_iff ξ' f).mpr hξ'
    have h2 : ⊤ ≤ (Spec.map ξ') ⁻¹ᵁ O := h1.trans (fun z hz => hDO hz)
    refine ⟨h2, ?_⟩
    have hev : ∀ u : Γ(Spec T, ⊤), evHom (Spec.map ξ') _ h1
        (algebraMap Γ(Spec T, ⊤) Γ(Spec T, (Spec T).basicOpen f) u) = ξ' ((Scheme.ΓSpecIso T).hom u) := by
      intro u
      rw [evHom_apply]
      have : algebraMap Γ(Spec T, ⊤) Γ(Spec T, (Spec T).basicOpen f) u =
          (Spec T).presheaf.map (homOfLE le_top).op u := rfl
      rw [this, ← evS_res _ le_top u h1]
      have hu : u = (Scheme.ΓSpecIso T).inv ((Scheme.ΓSpecIso T).hom u) := by simp
      conv_lhs => rw [hu]
      exact evS_spec_top ξ' _
    have := congrArg (evHom (Spec.map ξ') _ h1) ha
    rw [map_mul, hev, map_pow, hev, evHom_apply, ← evS_res _ hDO σ h1] at this
    exact this

/-- A complex point of an affine open factors through `fromSpec`. -/
theorem exists_spec_factor {X : Scheme} {V : X.Opens} (hV : IsAffineOpen V)
    (b : Spec (CommRingCat.of ℂ) ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ V) :
    ∃ β : Γ(X, V) ⟶ CommRingCat.of ℂ, b = Spec.map β ≫ hV.fromSpec := by
  have hr : Set.range b ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; exact hb (show z ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
  refine ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec b hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

/-- Evaluation of a section of an affine open at a point factored through `fromSpec`. -/
theorem evS_fromSpec {X : Scheme} {V : X.Opens} (hV : IsAffineOpen V)
    (β : Γ(X, V) ⟶ CommRingCat.of ℂ) (c : Γ(X, V)) :
    evS (Spec.map β ≫ hV.fromSpec) V c = β c := by
  have h' : ⊤ ≤ (Spec.map β) ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ V) := by
    rw [hV.fromSpec_preimage_self]; exact le_top
  have h : ⊤ ≤ (Spec.map β ≫ hV.fromSpec) ⁻¹ᵁ V := h'
  rw [evS_comp _ _ _ _ h, hV.fromSpec_app_self_apply]
  have hle : hV.fromSpec ⁻¹ᵁ V ≤ ⊤ := le_top
  rw [← evS_spec_top β c, evS_res _ hle _ h']
  congr 2

theorem tensor_sum_repr {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (t : TensorProduct R A B) :
    ∃ (m : ℕ) (x : Fin m → A) (y : Fin m → B), t = ∑ k, x k ⊗ₜ[R] y k := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨m₁, x₁, y₁, rfl⟩ := h₁
    obtain ⟨m₂, x₂, y₂, rfl⟩ := h₂
    refine ⟨m₁ + m₂, Fin.append x₁ x₂, Fin.append y₁ y₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp

theorem top_le_of_mem {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (V : Y.Opens)
    (h : y (IsLocalRing.closedPoint ℂ) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro z _
  have : z = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  subst this; exact h

/-- **Sections of a fibre product, read at `(a, b)` as functions of `b`.** For `X, Y` over an affine
`Spec R₀`, a section `σ` of `X ×_{R₀} Y` over `W` and complex points `a, b₀` with `(a, b₀) ∈ W(ℂ)`,
there are an open `V ∋ b₀` of `Y`, sections `c_j ∈ Γ(Y, V)` and constants `u_j, v_j` with
`σ(a, b) · (Σ v_j c_j(b))^N = Σ u_j c_j(b)` whenever `b ∈ V(ℂ)` and `Σ v_j c_j(b) ≠ 0` (which holds at
`b₀`). (Tensor decomposition on `V₁ ×_{R₀} V₂ = Spec(Γ(V₁) ⊗ Γ(V₂))` and a fraction on a basic open.) -/
theorem exists_tensor_formula {R₀ : CommRingCat} {X Y : Scheme} (f : X ⟶ Spec R₀) (g : Y ⟶ Spec R₀)
    (W : (pullback f g).Opens) (σ : Γ(pullback f g, W)) (a : Spec (CommRingCat.of ℂ) ⟶ X)
    (b₀ : Spec (CommRingCat.of ℂ) ⟶ Y) (hab₀ : a ≫ f = b₀ ≫ g)
    (hW : ⊤ ≤ (pullback.lift a b₀ hab₀) ⁻¹ᵁ W) :
    ∃ (V : Y.Opens) (m : ℕ) (c : Fin m → Γ(Y, V)) (u v : Fin m → ℂ) (N : ℕ),
      ⊤ ≤ b₀ ⁻¹ᵁ V ∧ ∑ j, v j * evS b₀ V (c j) ≠ 0 ∧
      ∀ (b : Spec (CommRingCat.of ℂ) ⟶ Y) (hab : a ≫ f = b ≫ g), ⊤ ≤ b ⁻¹ᵁ V →
        ∑ j, v j * evS b V (c j) ≠ 0 →
        ⊤ ≤ (pullback.lift a b hab) ⁻¹ᵁ W ∧
        evS (pullback.lift a b hab) W σ * (∑ j, v j * evS b V (c j)) ^ N =
          ∑ j, u j * evS b V (c j) := by
  classical
  obtain ⟨V₁, hV₁, ha1, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show a (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V₂, hV₂, hb1, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show b₀ (IsLocalRing.closedPoint ℂ) ∈ (⊤ : Y.Opens) from trivial)
  have hV₁' : IsAffineOpen V₁ := hV₁
  have hV₂' : IsAffineOpen V₂ := hV₂
  have hb₀V : ⊤ ≤ b₀ ⁻¹ᵁ V₂ := top_le_of_mem _ _ hb1
  set R₁ := Γ(X, V₁)
  set R₂ := Γ(Y, V₂)
  set j₁ := hV₁'.fromSpec
  set j₂ := hV₂'.fromSpec
  obtain ⟨α, rfl⟩ := exists_spec_factor hV₁' a (top_le_of_mem _ _ ha1)
  let φ₁ : R₀ ⟶ R₁ := Spec.preimage (j₁ ≫ f)
  let φ₂ : R₀ ⟶ R₂ := Spec.preimage (j₂ ≫ g)
  letI : Algebra R₀ R₁ := φ₁.hom.toAlgebra
  letI : Algebra R₀ R₂ := φ₂.hom.toAlgebra
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap R₀ R₁)) ≫ 𝟙 _ = j₁ ≫ f := by
    rw [Category.comp_id]; exact Spec.map_preimage _
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap R₀ R₂)) ≫ 𝟙 _ = j₂ ≫ g := by
    rw [Category.comp_id]; exact Spec.map_preimage _
  let κ : Spec (CommRingCat.of (TensorProduct R₀ R₁ R₂)) ⟶ pullback f g :=
    (pullbackSpecIso R₀ R₁ R₂).inv ≫ pullback.map _ _ f g j₁ j₂ (𝟙 _) e₁ e₂
  -- the ring map of `(a, b)` for `b = Spec β ≫ j₂`
  have key : ∀ (β : R₂ ⟶ CommRingCat.of ℂ)
      (h : (Spec.map α ≫ j₁) ≫ f = (Spec.map β ≫ j₂) ≫ g),
      ∃ ξ : CommRingCat.of (TensorProduct R₀ R₁ R₂) ⟶ CommRingCat.of ℂ,
        (∀ x y, ξ (x ⊗ₜ[R₀] y) = α x * β y) ∧
        pullback.lift (Spec.map α ≫ j₁) (Spec.map β ≫ j₂) h = Spec.map ξ ≫ κ := by
    intro β h
    have hc : φ₂ ≫ β = φ₁ ≫ α := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
      simpa only [Category.assoc] using h.symm
    letI : Algebra R₀ ℂ := (φ₁ ≫ α).hom.toAlgebra
    let αA : R₁ →ₐ[R₀] ℂ := { α.hom with commutes' := fun r => rfl }
    have hβc : ∀ r, β.hom (algebraMap R₀ R₂ r) = algebraMap R₀ ℂ r := fun r => by
      have := congrArg (fun φ => φ.hom r) hc
      exact this
    let βA : R₂ →ₐ[R₀] ℂ := { β.hom with commutes' := hβc }
    let ξ := CommRingCat.ofHom (Algebra.TensorProduct.lift αA βA (fun _ _ => Commute.all _ _)).toRingHom
    have hξ : ∀ x y, ξ (x ⊗ₜ[R₀] y) = α x * β y := fun x y => by
      simp [ξ, αA, βA]
    refine ⟨ξ, hξ, ?_⟩
    apply pullback.hom_ext
    · simp only [κ, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.map]
      rw [← Category.assoc (pullbackSpecIso R₀ R₁ R₂).inv, pullbackSpecIso_inv_fst,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext x
      simp [hξ]
    · simp only [κ, pullback.lift_snd, Category.assoc, pullback.map]
      rw [← Category.assoc (pullbackSpecIso R₀ R₁ R₂).inv, pullbackSpecIso_inv_snd,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext y
      simp [hξ]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, b₀ = Spec.map β₀ ≫ j₂ := exists_spec_factor hV₂' b₀ hb₀V
  obtain ⟨ξ₀, hξ₀, hl₀⟩ := key β₀ hab₀
  have hW' : ⊤ ≤ (Spec.map ξ₀) ⁻¹ᵁ (κ ⁻¹ᵁ W) := by rw [hl₀] at hW; exact hW
  obtain ⟨t, r, N, hr0, hfr⟩ := exists_fraction ξ₀ (κ ⁻¹ᵁ W) (κ.app W σ) hW'
  obtain ⟨m₁, x, y, rfl⟩ := tensor_sum_repr t
  obtain ⟨m₂, x', y', rfl⟩ := tensor_sum_repr r
  have hsum : ∀ (β : R₂ ⟶ CommRingCat.of ℂ)
      (ξ : CommRingCat.of (TensorProduct R₀ R₁ R₂) ⟶ CommRingCat.of ℂ)
      (_ : ∀ x y, ξ (x ⊗ₜ[R₀] y) = α x * β y) (m : ℕ) (x : Fin m → R₁) (y : Fin m → R₂),
      ξ (∑ k, x k ⊗ₜ[R₀] y k) = ∑ k, α (x k) * evS (Spec.map β ≫ j₂) V₂ (y k) := by
    intro β ξ hξ m x y
    rw [map_sum]
    simp only [hξ]
    exact Finset.sum_congr rfl fun k _ => by rw [show j₂ = hV₂'.fromSpec from rfl, evS_fromSpec]
  have happ : ∀ b, (∑ j, Fin.append (0 : Fin m₁ → ℂ) (fun k => α (x' k)) j *
      evS b V₂ (Fin.append y y' j)) = ∑ k, α (x' k) * evS b V₂ (y' k) := by
    intro b; rw [Fin.sum_univ_add]; simp
  have happ' : ∀ b, (∑ j, Fin.append (fun k => α (x k)) (0 : Fin m₂ → ℂ) j *
      evS b V₂ (Fin.append y y' j)) = ∑ k, α (x k) * evS b V₂ (y k) := by
    intro b; rw [Fin.sum_univ_add]; simp
  refine ⟨V₂, m₁ + m₂, Fin.append y y', Fin.append (fun k => α (x k)) 0,
    Fin.append 0 (fun k => α (x' k)), N, hb₀V, ?_, ?_⟩
  · rw [happ, ← hsum β₀ ξ₀ hξ₀]; exact hr0
  · intro b hab hbV hden
    obtain ⟨β, rfl⟩ := exists_spec_factor hV₂' b hbV
    obtain ⟨ξ, hξ, hl⟩ := key β hab
    rw [happ, ← hsum β ξ hξ] at hden
    obtain ⟨h1, h2⟩ := hfr ξ hden
    have hlW : ⊤ ≤ (pullback.lift _ _ hab) ⁻¹ᵁ W := by rw [hl]; exact h1
    refine ⟨hlW, ?_⟩
    have hlW' : ⊤ ≤ (Spec.map ξ ≫ κ) ⁻¹ᵁ W := by rw [← hl]; exact hlW
    rw [happ, happ', ← hsum β ξ hξ, ← hsum β ξ hξ, hl, evS_comp _ _ _ _ hlW']
    exact h2

end Eval

/-! ## §1. Serre's sheaf of holomorphic functions on `A_τ(ℂ)^an` and its charts -/

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The values `(s₁(x), …, s_m(x))` of finitely many regular functions at a complex point. -/
noncomputable def evalVec (𝒢 : GroupModel A L) (τ : L →+* ℂ) {m : ℕ} (U : Fin m → 𝒢.G.left.Opens)
    (s : ∀ j, Γ(𝒢.G.left, U j)) (x : 𝒢.Pts τ) : Fin m → ℂ :=
  fun j => 𝒢.evalAt x (U j) (s j)

/-- **Serre's sheaf of holomorphic functions on `A_τ(ℂ)^an`** (Serre, GAGA §2; SGA 1 XII 1.1, the
reduced structure sheaf): `h` is holomorphic at `q` when, near `q` (analytic topology `anTop`), it is
`H(s₁, …, s_m)` for finitely many regular functions `s_j ∈ Γ(U_j, 𝒪_𝒢)` defined at `q` and a function
`H` holomorphic near `(s_j(q))_j ∈ ℂ^m`. On an affine piece `U ↪ ℂ^n` (generators of `Γ(U)`) this is
"locally the restriction of a holomorphic function of the coordinates". No étale coordinates enter. -/
def AnHolAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) (h : 𝒢.Pts τ → ℂ) (q : 𝒢.Pts τ) : Prop :=
  ∃ (m : ℕ) (U : Fin m → 𝒢.G.left.Opens) (s : ∀ j, Γ(𝒢.G.left, U j)) (H : (Fin m → ℂ) → ℂ),
    (∀ j, ⊤ ≤ q.left ⁻¹ᵁ U j) ∧ (∀ᶠ y in 𝓝 (evalVec 𝒢 τ U s q), DifferentiableAt ℂ H y) ∧
    ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, h x = H (evalVec 𝒢 τ U s x)

/-- **`φ` is a chart of the complex space `(A_τ(ℂ), 𝒪^an)`**: a homeomorphism from an open subset of
`A_τ(ℂ)` onto an open subset of `ℂ^g` which is an isomorphism of ringed spaces, i.e. at every point
`q` of its domain a function is holomorphic at `q` in Serre's sense (`AnHolAt`) iff it is a holomorphic
function of the chart coordinate near `φ q`. -/
def IsSerreChart (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) : Prop :=
  letI := anTop 𝒢 τ
  ∀ q ∈ φ.source, ∀ h : 𝒢.Pts τ → ℂ,
    AnHolAt 𝒢 τ h q ↔ ∀ᶠ y in 𝓝 (φ q), DifferentiableAt ℂ (h ∘ φ.symm) y

end Defs

/-- **GLUE `TranslationAnHol`: left translation by a complex point is holomorphic.** For a group
model `𝒢`, `τ`, a regular function `s ∈ Γ(U, 𝒪_𝒢)` and complex points `p, x₀` with `p x₀ ∈ U(ℂ)`,
the function `x ↦ s(p x)` is holomorphic at `x₀` in Serre's sense. (Left translation by `p` is a
morphism of the complex variety `𝒢 ×_{𝓞_L,τ} ℂ`; morphisms are holomorphic, GAGA §2 / SGA 1 XII 1.1.
Concretely: on an affine open of `𝒢 ×_{𝓞_L} 𝒢` around `(p, x₀)`, `μ^* s = r / b^N` with
`r, b ∈ R₁ ⊗ R₂`, so `s(p x) = Σ αₖ(p) βₖ(x) / (Σ aⱼ(p) cⱼ(x))^N`.) -/
def TranslationAnHol : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (p x₀ : 𝒢.Pts τ),
    ⊤ ≤ (p * x₀).left ⁻¹ᵁ U → AnHolAt 𝒢 τ (fun x => 𝒢.evalAt (p * x) U s) x₀


section Translation

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem evalAt_eq_evS (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) : 𝒢.evalAt p U s = evS p.left U s := rfl

/-- `p ∈ V(ℂ)` is an open condition for the analytic topology. -/
theorem isOpen_ptsIn (𝒢 : GroupModel A L) (τ : L →+* ℂ) (V : 𝒢.G.left.Opens) :
    @IsOpen _ (anTop 𝒢 τ) {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V} := by
  refine TopologicalSpace.isOpen_generateFrom_of_mem ⟨V, 0, Set.univ, isOpen_univ, ?_⟩
  ext p; simp

/-- Regular functions are continuous at the points of their domain (analytic topology). -/
theorem continuousAt_evalAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) (V : 𝒢.G.left.Opens)
    (c : Γ(𝒢.G.left, V)) {q : 𝒢.Pts τ} (hq : ⊤ ≤ q.left ⁻¹ᵁ V) :
    @ContinuousAt _ _ (anTop 𝒢 τ) _ (fun p => 𝒢.evalAt p V c) q := by
  letI := anTop 𝒢 τ
  intro O hO
  obtain ⟨O', hO'sub, hO'o, hqO'⟩ := mem_nhds_iff.mp hO
  have hopen : IsOpen {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V ∧ 𝒢.evalAt p V c ∈ O'} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨V, c, O', hO'o, rfl⟩
  exact Filter.mem_map.mpr (Filter.mem_of_superset (hopen.mem_nhds ⟨hq, hqO'⟩) fun p hp => hO'sub hp.2)

/-- **`TranslationAnHol` is a theorem.** -/
theorem translationAnHol : TranslationAnHol := by
  intro K _ A L _ _ _ 𝒢 τ U s p x₀ hpx
  letI := anTop 𝒢 τ
  have hw : ∀ x : 𝒢.Pts τ, p.left ≫ 𝒢.G.hom = x.left ≫ 𝒢.G.hom := fun x =>
    (Over.w p).trans (Over.w x).symm
  have hmul : ∀ x : 𝒢.Pts τ, (p * x).left =
      Limits.pullback.lift p.left x.left (hw x) ≫ (MonObj.mul : 𝒢.G ⊗ 𝒢.G ⟶ 𝒢.G).left := fun x => rfl
  have hW : ⊤ ≤ (Limits.pullback.lift p.left x₀.left (hw x₀)) ⁻¹ᵁ
      ((MonObj.mul : 𝒢.G ⊗ 𝒢.G ⟶ 𝒢.G).left ⁻¹ᵁ U) := by
    rw [hmul] at hpx; exact hpx
  obtain ⟨V, m, c, u, v, N, hb₀, hden₀, hall⟩ := exists_tensor_formula 𝒢.G.hom 𝒢.G.hom _
    ((MonObj.mul : 𝒢.G ⊗ 𝒢.G ⟶ 𝒢.G).left.app U s) p.left x₀.left (hw x₀) hW
  let num : (Fin m → ℂ) → ℂ := fun z => ∑ j, u j * z j
  let den : (Fin m → ℂ) → ℂ := fun z => ∑ j, v j * z j
  have hnum : Continuous num := continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hden : Continuous den := continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hnumd : Differentiable ℂ num := fun z =>
    DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (differentiableAt_apply j z)
  have hdend : Differentiable ℂ den := fun z =>
    DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (differentiableAt_apply j z)
  refine ⟨m, fun _ => V, c, fun z => num z / den z ^ N, fun _ => hb₀, ?_, ?_⟩
  · have h0 : den (evalVec 𝒢 τ (fun _ => V) c x₀) ≠ 0 := hden₀
    filter_upwards [hden.continuousAt.eventually (isOpen_ne.mem_nhds h0)] with z hz
    have hp : DifferentiableAt ℂ (fun w => den w ^ N) z := (hdend z).pow N
    have hq := (hnumd z).mul (hp.inv (pow_ne_zero N hz))
    have hfun : (fun z => num z / den z ^ N) = num * (fun w => den w ^ N)⁻¹ := by
      funext w; simp [div_eq_mul_inv]
    rw [hfun]; exact hq
  · have hcont : ContinuousAt (fun x => evalVec 𝒢 τ (fun _ => V) c x) x₀ :=
      continuousAt_pi.mpr fun j => continuousAt_evalAt 𝒢 τ V (c j) hb₀
    have h0 : den (evalVec 𝒢 τ (fun _ => V) c x₀) ≠ 0 := hden₀
    filter_upwards [(isOpen_ptsIn 𝒢 τ V).mem_nhds hb₀,
      (hden.continuousAt.comp hcont).eventually (isOpen_ne.mem_nhds h0)] with x hxV hxd
    obtain ⟨h1, h2⟩ := hall x.left (hw x) hxV hxd
    have hpx' : ⊤ ≤ (p * x).left ⁻¹ᵁ U := by rw [hmul]; exact h1
    show 𝒢.evalAt (p * x) U s = num (evalVec 𝒢 τ (fun _ => V) c x) / den (evalVec 𝒢 τ (fun _ => V) c x) ^ N
    rw [evalAt_eq_evS, hmul]
    refine (evS_comp _ _ _ _ hpx').trans ?_
    exact eq_div_of_mul_eq (pow_ne_zero N hxd) h2

end Translation

/-! ## §2. Generic analysis -/

section Generic

variable {g : ℕ}

/-- A holomorphic map with invertible derivative at `z` has a holomorphic local inverse. -/
theorem exists_localInverse {ψ : (Fin g → ℂ) → (Fin g → ℂ)} {z : Fin g → ℂ}
    (hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w) (hdet : (fderiv ℂ ψ z).det ≠ 0) :
    ∃ σ : (Fin g → ℂ) → (Fin g → ℂ), σ (ψ z) = z ∧ ContinuousAt σ (ψ z) ∧
      (∀ᶠ y in 𝓝 (ψ z), DifferentiableAt ℂ σ y) ∧ (∀ᶠ w in 𝓝 z, σ (ψ w) = w) := by
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp hd
  have hdV : DifferentiableOn ℂ ψ V := fun w hw => (hVsub hw).differentiableWithinAt
  have hstrict : HasStrictFDerivAt ψ
      ((equivOfDet _ hdet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) z := by
    rw [equivOfDet_coe]; exact Holomorphic.hasStrictFDerivAt hVo hdV hzV
  set P := hstrict.toOpenPartialHomeomorph ψ
  have hPcoe : (P : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hstrict.toOpenPartialHomeomorph_coe
  have hzs : z ∈ P.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hzt : ψ z ∈ P.target := by rw [← hPcoe]; exact P.map_source hzs
  have hσz : P.symm (ψ z) = z := by
    have := P.left_inv hzs; rwa [hPcoe] at this
  have hcσ : ContinuousAt P.symm (ψ z) := P.continuousAt_symm hzt
  refine ⟨P.symm, hσz, hcσ, ?_, ?_⟩
  · have hgood := eventually_det_ne hVo hdV hzV hdet
    rw [← hσz] at hgood
    filter_upwards [hcσ.eventually hgood, P.open_target.mem_nhds hzt] with y hy hyt
    obtain ⟨hyV, hydet⟩ := hy
    have hfd : HasFDerivAt (P : (Fin g → ℂ) → (Fin g → ℂ))
        ((equivOfDet _ hydet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
        (P.symm y) := by
      rw [hPcoe, equivOfDet_coe]; exact (hdV.differentiableAt (hVo.mem_nhds hyV)).hasFDerivAt
    exact (P.hasFDerivAt_symm hyt hfd).differentiableAt
  · filter_upwards [P.open_source.mem_nhds hzs] with w hw
    have := P.left_inv hw; rwa [hPcoe] at this

theorem det_comp_eq (A B : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
    (A.comp B).det = A.det * B.det := by
  change LinearMap.det ((A : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) =
    LinearMap.det (A : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) * LinearMap.det (B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  exact LinearMap.det_comp _ _

end Generic

/-! ## §3. Serre's sheaf along a uniformization -/

section Along

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Finitely many Serre-holomorphic functions are jointly a holomorphic function of one finite
family of regular functions. -/
theorem anHolAt_pi (𝒢 : GroupModel A L) (τ : L →+* ℂ) {n : ℕ} {f : 𝒢.Pts τ → (Fin n → ℂ)}
    {q : 𝒢.Pts τ} (hf : ∀ i, AnHolAt 𝒢 τ (fun x => f x i) q) :
    ∃ (m : ℕ) (U : Fin m → 𝒢.G.left.Opens) (s : ∀ j, Γ(𝒢.G.left, U j))
      (H : (Fin m → ℂ) → (Fin n → ℂ)),
      (∀ j, ⊤ ≤ q.left ⁻¹ᵁ U j) ∧ (∀ᶠ y in 𝓝 (evalVec 𝒢 τ U s q), DifferentiableAt ℂ H y) ∧
      ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, f x = H (evalVec 𝒢 τ U s x) := by
  letI := anTop 𝒢 τ
  choose m U s H hU hH hev using hf
  let e : Fin (∑ i, m i) ≃ (Σ i, Fin (m i)) := finSigmaFinEquiv.symm
  let W : Fin (∑ i, m i) → 𝒢.G.left.Opens := fun j => U (e j).1 (e j).2
  let t : ∀ j, Γ(𝒢.G.left, W j) := fun j => s (e j).1 (e j).2
  let Lm : ∀ i : Fin n, (Fin (∑ i, m i) → ℂ) →L[ℂ] (Fin (m i) → ℂ) := fun i =>
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm ⟨i, j⟩)
  have hL : ∀ x i, Lm i (evalVec 𝒢 τ W t x) = evalVec 𝒢 τ (U i) (s i) x := by
    intro x i
    funext j
    let F : (Σ i, Fin (m i)) → ℂ := fun σ => 𝒢.evalAt x (U σ.1 σ.2) (s σ.1 σ.2)
    show F (e (e.symm ⟨i, j⟩)) = F ⟨i, j⟩
    rw [Equiv.apply_symm_apply]
  refine ⟨∑ i, m i, W, t, fun y i => H i (Lm i y), fun j => hU _ _, ?_, ?_⟩
  · have hi : ∀ i, ∀ᶠ y in 𝓝 (evalVec 𝒢 τ W t q), DifferentiableAt ℂ (H i) (Lm i y) := by
      intro i
      have h1 := hH i
      rw [← hL q i] at h1
      exact (Lm i).continuous.continuousAt.eventually h1
    filter_upwards [Filter.eventually_all.mpr hi] with y hy
    exact differentiableAt_pi.mpr fun i => (hy i).comp y (Lm i).differentiableAt
  · filter_upwards [Filter.eventually_all.mpr hev] with x hx
    funext i
    rw [hx i, hL x i]

/-- Serre-holomorphic functions are holomorphic along an analytic uniformization. -/
theorem holo_of_anHolAt (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (hΦc : @Continuous _ _ _ (anTop 𝒢 τ) Φ) {h : 𝒢.Pts τ → ℂ} {z : Fin g → ℂ}
    (hh : AnHolAt 𝒢 τ h (Φ z)) : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (h ∘ Φ) w := by
  letI := anTop 𝒢 τ
  obtain ⟨m, U, s, H, hU, hH, hev⟩ := hh
  set D := ⋂ j, 𝒢.dom Φ (U j)
  have hDo : IsOpen D := isOpen_iInter_of_finite fun j => hΦ.2.2.2.1 (U j)
  have hzD : z ∈ D := mem_iInter.mpr fun j => hU j
  have hψd : DifferentiableOn ℂ (evalVec 𝒢 τ U s ∘ Φ) D :=
    differentiableOn_pi.mpr fun j => (hΦ.2.2.2.2 (U j) (s j)).mono (iInter_subset _ j)
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (evalVec 𝒢 τ U s ∘ Φ) w :=
    Filter.eventually_of_mem (hDo.mem_nhds hzD) fun w hw => hψd.differentiableAt (hDo.mem_nhds hw)
  have hcont : ContinuousAt (evalVec 𝒢 τ U s ∘ Φ) z :=
    (hψd.differentiableAt (hDo.mem_nhds hzD)).continuousAt
  have hH' := hcont.eventually hH
  have hev' := (hΦc.continuousAt.eventually hev).eventually_nhds
  filter_upwards [hψ, hH', hev'] with w hw1 hw2 hw3
  have : DifferentiableAt ℂ (H ∘ (evalVec 𝒢 τ U s ∘ Φ)) w := hw2.comp w hw1
  exact this.congr_of_eventuallyEq hw3

/-- `1 ∈ U(ℂ)` for an open `U` containing the origin of the generic fibre. -/
theorem one_mem_of_genericUnit (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := by
  have h0 : Φ 0 = 1 := (hΦ.2.1 0).2 Λ.zero_mem
  have := ZInQ.Metrization.zero_mem_dom 𝒢 hΦ U hU
  rw [← h0]; exact this

/-- The translated algebraic coordinates are Serre-holomorphic (from `TranslationAnHol`). -/
theorem chartAt_anHolAt (hTH : TranslationAnHol) (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : Fin g → 𝒢.G.left.Opens)
    (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i)) (q : 𝒢.Pts τ) (i : Fin g) :
    AnHolAt 𝒢 τ (fun x => chartAt 𝒢 τ U s q x i) q := by
  refine hTH K A L 𝒢 τ (U i) (s i) q⁻¹ q ?_
  rw [inv_mul_cancel]
  exact one_mem_of_genericUnit 𝒢 hΦ (U i) (hU i)

variable [NumberField K]

/-- **Holomorphic along the uniformization ⇒ Serre-holomorphic** (from `TranslationAnHol`). -/
theorem anHolAt_of_holo (hTH : TranslationAnHol) {g : ℕ} (M : MetrizedModel A L g)
    (τ : L →+* ℂ) {Φ : (Fin g → ℂ) → M.model.Pts τ}
    (hΦ : M.model.IsAnalyticUniformization τ (M.hodge.periods τ) Φ)
    (hc : ∀ f, M.hodge.coeff τ (M.model.wedge f) = M.model.jacDet Φ f)
    {h : M.model.Pts τ → ℂ} {z : Fin g → ℂ} (hh : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (h ∘ Φ) w) :
    AnHolAt M.model τ h (Φ z) := by
  letI := anTop M.model τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  obtain ⟨U, hU, s, hm, hw⟩ := exists_algCoord M τ
  set q := Φ z with hqdef
  set k := chartAt M.model τ U s q with hkdef
  obtain ⟨m, W, t, Hk, hWq, hHk, hkev⟩ :=
    anHolAt_pi M.model τ (f := k) (chartAt_anHolAt hTH M.model hΦ U hU s q)
  obtain ⟨V, hVo, hzV, hdV, hdet⟩ := chart_comp_unif M.model hΦ U hU s hm z
  have hdet' : (fderiv ℂ (k ∘ Φ) z).det ≠ 0 := by rw [hdet]; exact jacDet_ne_zero M hc _ hw
  have hψd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (k ∘ Φ) w :=
    Filter.eventually_of_mem (hVo.mem_nhds hzV) fun w hw => hdV.differentiableAt (hVo.mem_nhds hw)
  obtain ⟨σ, hσz, hσc, hσd, hσψ⟩ := exists_localInverse hψd hdet'
  have hkq : Hk (evalVec M.model τ W t q) = k q := hkev.self_of_nhds.symm
  have hkz : (k ∘ Φ) z = k q := rfl
  rw [hkz] at hσz hσc hσd
  have hHc : ContinuousAt Hk (evalVec M.model τ W t q) := hHk.self_of_nhds.continuousAt
  refine ⟨m, W, t, (h ∘ Φ) ∘ σ ∘ Hk, hWq, ?_, ?_⟩
  · have h2 : ∀ᶠ y in 𝓝 (evalVec M.model τ W t q), DifferentiableAt ℂ σ (Hk y) := by
      rw [← hkq] at hσd
      exact hHc.eventually hσd
    have hc2 : ContinuousAt (σ ∘ Hk) (evalVec M.model τ W t q) := by
      refine ContinuousAt.comp ?_ hHc
      rw [hkq]; exact hσc
    have h3 : ∀ᶠ y in 𝓝 (evalVec M.model τ W t q), DifferentiableAt ℂ (h ∘ Φ) (σ (Hk y)) := by
      have hσq : (σ ∘ Hk) (evalVec M.model τ W t q) = z := by
        show σ (Hk _) = z; rw [hkq]; exact hσz
      have hh' := hh
      rw [← hσq] at hh'
      exact hc2.eventually hh'
    filter_upwards [hHk, h2, h3] with y hy1 hy2 hy3
    exact hy3.comp y (hy2.comp y hy1)
  · obtain ⟨O, hOsub, hOo, hzO⟩ := mem_nhds_iff.mp hσψ
    have hΦO : Φ '' O ∈ 𝓝 q := (hUnif.isOpenMap O hOo).mem_nhds ⟨z, hzO, rfl⟩
    filter_upwards [hΦO, hkev] with x hx hx2
    obtain ⟨w, hwO, rfl⟩ := hx
    show h (Φ w) = h (Φ (σ (Hk (evalVec M.model τ W t (Φ w)))))
    rw [← hx2]
    exact congrArg (fun w' => h (Φ w')) (hOsub hwO).symm

end Along

/-! ## §4. R3′: the holomorphic charts are the charts of Serre's complex structure -/

section Main

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L]
  [NumberField L] [Algebra K L]

/-- **R3′.** For every group model `𝒢` of `A_L` (`g = dim A`) and every `τ`, a homeomorphism `φ` from
an open subset of `A_τ(ℂ)` onto an open subset of `ℂ^g` is a holomorphic chart in the sense of
`IsHolChart` (algebraic coordinates, translated, are holomorphic coordinates in `φ`) iff it is a chart
of Serre's complex space `(A_τ(ℂ), 𝒪^an)` (`IsSerreChart`). Through T35 and `TranslationAnHol`. -/
theorem isHolChart_iff_isSerreChart (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hTH : TranslationAnHol) (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (τ : L →+* ℂ) (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ := by
  letI := anTop 𝒢 τ
  obtain ⟨M, rfl⟩ := exists_metrized hT35 𝒢 g hg
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  constructor
  · intro hφ q hq h
    obtain ⟨z, rfl⟩ := hUnif.surj q
    obtain ⟨O, hOo, hzO, hdO, hdetO⟩ := unif_holChart hT35 M.model g hg τ hΦ φ hφ z hq
    constructor
    · intro hh
      have hhΦ := holo_of_anHolAt M.model hΦ hUnif.cont hh
      obtain ⟨O₂, hO₂sub, hO₂o, hzO₂⟩ := mem_nhds_iff.mp hhΦ
      obtain ⟨V, hVo, hV, hdV⟩ := holo_in_chart_of_lift φ Φ hUnif.cont hq hOo hzO hdO hdetO h
        hO₂o hzO₂ (fun w hw => (hO₂sub hw).differentiableWithinAt)
      exact Filter.eventually_of_mem (hVo.mem_nhds hV) fun y hy =>
        hdV.differentiableAt (hVo.mem_nhds hy)
    · intro hh
      apply anHolAt_of_holo hTH M τ hΦ hc
      have hcφ : ContinuousAt (φ ∘ Φ) z := (hdO.differentiableAt (hOo.mem_nhds hzO)).continuousAt
      have hh' := hcφ.eventually hh
      have hsrc : ∀ᶠ w in 𝓝 z, Φ w ∈ φ.source :=
        hUnif.cont.continuousAt.eventually (φ.open_source.mem_nhds hq)
      filter_upwards [hh', hOo.mem_nhds hzO, hsrc.eventually_nhds] with w hw1 hw2 hw3
      have hd : DifferentiableAt ℂ ((h ∘ φ.symm) ∘ (φ ∘ Φ)) w :=
        hw1.comp w (hdO.differentiableAt (hOo.mem_nhds hw2))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hw3] with w' hw'
      simp only [Function.comp_apply, φ.left_inv hw']
  · intro hφ q hq U hU s hm hw
    obtain ⟨z, rfl⟩ := hUnif.surj q
    set k := chartAt M.model τ U s (Φ z) with hkdef
    have hkd : ∀ i, ∀ᶠ y in 𝓝 (φ (Φ z)), DifferentiableAt ℂ ((fun x => k x i) ∘ φ.symm) y :=
      fun i => (hφ _ hq _).mp (chartAt_anHolAt hTH M.model hΦ U hU s (Φ z) i)
    have hkd' : ∀ᶠ y in 𝓝 (φ (Φ z)), DifferentiableAt ℂ (k ∘ φ.symm) y := by
      filter_upwards [Filter.eventually_all.mpr hkd] with y hy
      exact differentiableAt_pi.mpr hy
    have hφi : ∀ i, AnHolAt M.model τ (fun x => φ x i) (Φ z) := fun i => by
      refine (hφ _ hq _).mpr ?_
      filter_upwards [φ.open_target.mem_nhds (φ.map_source hq)] with y hy
      have heq : ((fun x => φ x i) ∘ φ.symm) =ᶠ[𝓝 y] (fun y : Fin g → ℂ => y i) := by
        filter_upwards [φ.open_target.mem_nhds hy] with y' hy'
        simp only [Function.comp_apply, φ.right_inv hy']
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).differentiableAt.congr_of_eventuallyEq
        heq
    have hφΦ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (φ ∘ Φ) w := by
      filter_upwards [Filter.eventually_all.mpr fun i =>
        holo_of_anHolAt M.model hΦ hUnif.cont (hφi i)] with w hw
      exact differentiableAt_pi.mpr hw
    obtain ⟨V, hVo, hzV, hdV, hdet⟩ := chart_comp_unif M.model hΦ U hU s hm z
    have hdet' : (fderiv ℂ (k ∘ Φ) z).det ≠ 0 := by rw [hdet]; exact jacDet_ne_zero M hc _ hw
    have heq : (k ∘ Φ) =ᶠ[𝓝 z] (k ∘ φ.symm) ∘ (φ ∘ Φ) := by
      filter_upwards [hUnif.cont.continuousAt.eventually (φ.open_source.mem_nhds hq)] with w hw
      simp only [Function.comp_apply, φ.left_inv hw]
    have hfd : fderiv ℂ (k ∘ Φ) z =
        (fderiv ℂ (k ∘ φ.symm) (φ (Φ z))).comp (fderiv ℂ (φ ∘ Φ) z) := by
      rw [heq.fderiv_eq]; exact fderiv_comp z hkd'.self_of_nhds hφΦ.self_of_nhds
    refine ⟨interior {y | DifferentiableAt ℂ (k ∘ φ.symm) y}, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hkd', fun y hy =>
        (interior_subset (s := {y | DifferentiableAt ℂ (k ∘ φ.symm) y}) hy :
          DifferentiableAt ℂ (k ∘ φ.symm) y).differentiableWithinAt, ?_⟩
    intro h0
    apply hdet'
    rw [hfd, det_comp_eq, h0, zero_mul]

/-- **R3′ (unconditional form).** `IsHolChart` charts are exactly the charts of Serre's complex space
`(A_τ(ℂ), 𝒪^an)`, from T35 alone (`TranslationAnHol` is proved, `translationAnHol`). -/
theorem isHolChart_iff_isSerreChart' (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ :=
  isHolChart_iff_isSerreChart hT35 translationAnHol 𝒢 g hg τ φ

/-- Serre charts exist at every point (T35). -/
theorem exists_serreChart_at (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    letI := anTop 𝒢 τ
    ∃ e : OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ), p ∈ e.source ∧ IsSerreChart 𝒢 τ e := by
  obtain ⟨e, hp, he⟩ := exists_holChart_at hT35 𝒢 g hg τ p
  exact ⟨e, hp, (isHolChart_iff_isSerreChart' hT35 𝒢 g hg τ e).mp he⟩

end Main

/-! ## §5. The print's metric read in Serre's charts -/

section SerreMetric

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- r3-residual's `HasAnFormDensityAt` verbatim with `IsHolChart` replaced by `IsSerreChart` (the charts of
Serre's complex space `(A_τ(ℂ), 𝒪^an)`). -/
def HasSerreFormDensityAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ φ : OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ), IsSerreChart 𝒢 τ φ → p ∈ φ.source →
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - ‖τ l‖ ^ 2 * ‖(fderiv ℂ (chartAt 𝒢 τ U s p ∘ φ.symm) (φ p)).det‖ ^ 2 *
          (volume (φ '' E)).toReal| ≤ ε * (volume (φ '' E)).toReal

/-- `IsAnFormMeasure` with Serre's charts. -/
def IsSerreFormMeasure (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  @IsFiniteMeasure _ (anBorel 𝒢 τ) nu ∧ ∀ p, HasSerreFormDensityAt 𝒢 τ nu eta p

/-- `IsAnMetricSq` with Serre's charts: `‖η‖²_τ = (i/2)^g ∫_{(A_τ(ℂ), 𝒪^an)} η̃ ∧ η̄̃ = r`. -/
def IsSerreMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anBorel 𝒢 τ
  (∃ nu : Measure (𝒢.Pts τ), IsSerreFormMeasure 𝒢 τ nu eta) ∧
    ∀ nu : Measure (𝒢.Pts τ), IsSerreFormMeasure 𝒢 τ nu eta → (nu univ).toReal = r

variable [NumberField K]

theorem hasSerreFormDensityAt_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) :
    HasSerreFormDensityAt 𝒢 τ nu eta p ↔ HasAnFormDensityAt 𝒢 τ nu eta p := by
  constructor
  · intro h φ hφ
    exact h φ ((isHolChart_iff_isSerreChart' hT35 𝒢 g hg τ φ).mp hφ)
  · intro h φ hφ
    exact h φ ((isHolChart_iff_isSerreChart' hT35 𝒢 g hg τ φ).mpr hφ)

theorem isSerreFormMeasure_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) :
    IsSerreFormMeasure 𝒢 τ nu eta ↔ IsAnFormMeasure 𝒢 τ nu eta :=
  and_congr Iff.rfl (forall_congr' fun p => hasSerreFormDensityAt_iff hT35 𝒢 g hg τ nu eta p)

/-- **The heights' archimedean metric is the integral over Serre's complex space.** For `g = dim A`,
r3-residual's `IsAnMetricSq` (densities in the `IsHolChart` atlas), on which `IsAnStableHeight`,
`IsAnStableHeightSS` and `IsStableHeightBarAn` are built, is `IsSerreMetricSq` (densities in the charts of
Serre's `(A_τ(ℂ), 𝒪^an)`). -/
theorem isSerreMetricSq_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ) (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    IsSerreMetricSq 𝒢 τ eta r ↔ IsAnMetricSq 𝒢 τ eta r := by
  unfold IsSerreMetricSq IsAnMetricSq
  simp only [isSerreFormMeasure_iff hT35 𝒢 g hg τ]

end SerreMetric

end ZInQ.R3Etale

#print axioms ZInQ.R3Etale.isHolChart_iff_isSerreChart'
#print axioms ZInQ.R3Etale.translationAnHol
#print axioms ZInQ.R3Etale.isSerreMetricSq_iff
