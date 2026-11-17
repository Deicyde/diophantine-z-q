import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Analysis.Complex.Basic

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ZInQ.R3Etale

/-- The value at a complex point `y : Spec ℂ → Y` of a section `s ∈ Γ(Y, U)` (`0` off `U(ℂ)`). -/
def evS {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ y ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (y.appLE U ⊤ h s) else 0

theorem evS_of_le {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U))
    (h : ⊤ ≤ y ⁻¹ᵁ U) :
    evS y U s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (y.appLE U ⊤ h s) := by
  unfold evS; rw [dif_pos h]

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
def evHom {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    Γ(Y, U) →+* ℂ :=
  ((y.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem evHom_apply {Y : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(Y, U)) : evHom y U h s = evS y U s := by
  rw [evS_of_le _ _ _ h]; rfl

/-- Evaluation of global sections of an affine `Spec T` at the point given by `γ : T → ℂ`. -/
theorem evS_spec_top {T : CommRingCat} (γ : T ⟶ CommRingCat.of ℂ) (t : T) :
    evS (Spec.map γ) ⊤ ((Scheme.ΓSpecIso T).inv t) = γ t := by
  rw [evS_of_le _ _ _ (by simp)]
  have h1 := Scheme.ΓSpecIso_naturality γ
  have h2 : (Spec.map γ).appLE ⊤ ⊤ (by simp) = (Spec.map γ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h2]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso T).inv t)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp

theorem top_le_preimage_basicOpen_iff {T : CommRingCat} (γ : T ⟶ CommRingCat.of ℂ) (f : Γ(Spec T, ⊤)) :
    ⊤ ≤ (Spec.map γ) ⁻¹ᵁ (Spec T).basicOpen f ↔ γ ((Scheme.ΓSpecIso T).hom f) ≠ 0 := by
  rw [Scheme.preimage_basicOpen_top]
  have hnat : (Spec.map γ).appTop f =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (γ ((Scheme.ΓSpecIso T).hom f)) := by
    have h1 := congrArg (fun φ => φ.hom f) (Scheme.ΓSpecIso_naturality γ)
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
theorem exists_fraction {T : CommRingCat} (γ : T ⟶ CommRingCat.of ℂ) (O : (Spec T).Opens)
    (σ : Γ(Spec T, O)) (hO : ⊤ ≤ (Spec.map γ) ⁻¹ᵁ O) :
    ∃ (t r : T) (n : ℕ), γ r ≠ 0 ∧ ∀ γ' : T ⟶ CommRingCat.of ℂ, γ' r ≠ 0 →
      ⊤ ≤ (Spec.map γ') ⁻¹ᵁ O ∧ evS (Spec.map γ') O σ * (γ' r) ^ n = γ' t := by
  classical
  have hx : (Spec.map γ) (IsLocalRing.closedPoint ℂ) ∈ O := hO (Set.mem_univ _)
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
  · intro γ' hγ'
    have h1 : ⊤ ≤ (Spec.map γ') ⁻¹ᵁ (Spec T).basicOpen f := (top_le_preimage_basicOpen_iff γ' f).mpr hγ'
    have h2 : ⊤ ≤ (Spec.map γ') ⁻¹ᵁ O := h1.trans (fun z hz => hDO hz)
    refine ⟨h2, ?_⟩
    have hev : ∀ u : Γ(Spec T, ⊤), evHom (Spec.map γ') _ h1
        (algebraMap Γ(Spec T, ⊤) Γ(Spec T, (Spec T).basicOpen f) u) = γ' ((Scheme.ΓSpecIso T).hom u) := by
      intro u
      rw [evHom_apply]
      have : algebraMap Γ(Spec T, ⊤) Γ(Spec T, (Spec T).basicOpen f) u =
          (Spec T).presheaf.map (homOfLE le_top).op u := rfl
      rw [this, ← evS_res _ le_top u h1]
      have hu : u = (Scheme.ΓSpecIso T).inv ((Scheme.ΓSpecIso T).hom u) := by simp
      conv_lhs => rw [hu]
      exact evS_spec_top γ' _
    have := congrArg (evHom (Spec.map γ') _ h1) ha
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
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
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
      ∃ γ : CommRingCat.of (TensorProduct R₀ R₁ R₂) ⟶ CommRingCat.of ℂ,
        (∀ x y, γ (x ⊗ₜ[R₀] y) = α x * β y) ∧
        pullback.lift (Spec.map α ≫ j₁) (Spec.map β ≫ j₂) h = Spec.map γ ≫ κ := by
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
    let γ := CommRingCat.ofHom (Algebra.TensorProduct.lift αA βA (fun _ _ => Commute.all _ _)).toRingHom
    have hγ : ∀ x y, γ (x ⊗ₜ[R₀] y) = α x * β y := fun x y => by
      simp [γ, αA, βA]
    refine ⟨γ, hγ, ?_⟩
    apply pullback.hom_ext
    · simp only [κ, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.map]
      rw [← Category.assoc (pullbackSpecIso R₀ R₁ R₂).inv, pullbackSpecIso_inv_fst,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext x
      simp [hγ]
    · simp only [κ, pullback.lift_snd, Category.assoc, pullback.map]
      rw [← Category.assoc (pullbackSpecIso R₀ R₁ R₂).inv, pullbackSpecIso_inv_snd,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext y
      simp [hγ]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, b₀ = Spec.map β₀ ≫ j₂ := exists_spec_factor hV₂' b₀ hb₀V
  obtain ⟨γ₀, hγ₀, hl₀⟩ := key β₀ hab₀
  have hW' : ⊤ ≤ (Spec.map γ₀) ⁻¹ᵁ (κ ⁻¹ᵁ W) := by rw [hl₀] at hW; exact hW
  obtain ⟨t, r, N, hr0, hfr⟩ := exists_fraction γ₀ (κ ⁻¹ᵁ W) (κ.app W σ) hW'
  obtain ⟨m₁, x, y, rfl⟩ := tensor_sum_repr t
  obtain ⟨m₂, x', y', rfl⟩ := tensor_sum_repr r
  have hsum : ∀ (β : R₂ ⟶ CommRingCat.of ℂ)
      (γ : CommRingCat.of (TensorProduct R₀ R₁ R₂) ⟶ CommRingCat.of ℂ)
      (_ : ∀ x y, γ (x ⊗ₜ[R₀] y) = α x * β y) (m : ℕ) (x : Fin m → R₁) (y : Fin m → R₂),
      γ (∑ k, x k ⊗ₜ[R₀] y k) = ∑ k, α (x k) * evS (Spec.map β ≫ j₂) V₂ (y k) := by
    intro β γ hγ m x y
    rw [map_sum]
    simp only [hγ]
    exact Finset.sum_congr rfl fun k _ => by rw [show j₂ = hV₂'.fromSpec from rfl, evS_fromSpec]
  have happ : ∀ b, (∑ j, Fin.append (0 : Fin m₁ → ℂ) (fun k => α (x' k)) j *
      evS b V₂ (Fin.append y y' j)) = ∑ k, α (x' k) * evS b V₂ (y' k) := by
    intro b; rw [Fin.sum_univ_add]; simp
  have happ' : ∀ b, (∑ j, Fin.append (fun k => α (x k)) (0 : Fin m₂ → ℂ) j *
      evS b V₂ (Fin.append y y' j)) = ∑ k, α (x k) * evS b V₂ (y k) := by
    intro b; rw [Fin.sum_univ_add]; simp
  refine ⟨V₂, m₁ + m₂, Fin.append y y', Fin.append (fun k => α (x k)) 0,
    Fin.append 0 (fun k => α (x' k)), N, hb₀V, ?_, ?_⟩
  · rw [happ, ← hsum β₀ γ₀ hγ₀]; exact hr0
  · intro b hab hbV hden
    obtain ⟨β, rfl⟩ := exists_spec_factor hV₂' b hbV
    obtain ⟨γ, hγ, hl⟩ := key β hab
    rw [happ, ← hsum β γ hγ] at hden
    obtain ⟨h1, h2⟩ := hfr γ hden
    have hlW : ⊤ ≤ (pullback.lift _ _ hab) ⁻¹ᵁ W := by rw [hl]; exact h1
    refine ⟨hlW, ?_⟩
    have hlW' : ⊤ ≤ (Spec.map γ ≫ κ) ⁻¹ᵁ W := by rw [← hl]; exact hlW
    rw [happ, happ', ← hsum β γ hγ, ← hsum β γ hγ, hl, evS_comp _ _ _ _ hlW']
    exact h2

end ZInQ.R3Etale
#print axioms ZInQ.R3Etale.exists_tensor_formula
