import MetrBase
/-! ## metrization2: toward `ProductMapLocalStructure` — evaluation at complex points of schemes,
and sums of products in a pushout of commutative rings -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The value at a complex point `q : Spec ℂ → X` of `s ∈ Γ(X, U)` (`0` if `q ∉ U(ℂ)`). Same
formula as def-faltings' `GroupModel.evalAt` (which is `ev p.left`). -/
noncomputable def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ h s)
    else 0

section Ev

variable {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X)

theorem ev_comp (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    ev (q ≫ f) U s = ev q (f ⁻¹ᵁ U) (f.app U s) := by
  unfold ev
  by_cases h : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem ev_res {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) :
    ev q V (X.presheaf.map i.op s) = ev q U s := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := hV.trans ((TopologicalSpace.Opens.map q.base).map i).le
  unfold ev
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem ev_add (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s + s') = ev q U s + ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_mul (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s * s') = ev q U s * ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_zero (U : X.Opens) : ev q U 0 = 0 := by
  unfold ev
  split_ifs with h
  · rw [map_zero]
    exact map_zero (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
  · rfl

theorem ev_one (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) : ev q U 1 = 1 := by
  unfold ev
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

theorem ev_pow (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) :
    ev q U (s ^ n) = ev q U s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one q U h]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul, ih]

theorem ev_sum (U : X.Opens) {n : ℕ} (s : Fin n → Γ(X, U)) :
    ev q U (∑ k, s k) = ∑ k, ev q U (s k) := by
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ev_add, ih]

/-- A complex point in `X.basicOpen s` gives `s` a nonzero value. -/
theorem ev_ne_zero_of_mem {U : X.Opens} (s : Γ(X, U)) (h : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s) :
    ev q U s ≠ 0 := by
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  rw [← ev_res q (homOfLE (X.basicOpen_le s)) h]
  obtain ⟨u, hu'⟩ := hu
  intro h0
  have h1 := congrArg (ev q (X.basicOpen s)) u.mul_inv
  rw [ev_mul, ev_one q _ h, hu', h0, zero_mul] at h1
  exact zero_ne_one h1

/-- A complex point of `U` at which `s` has a nonzero value lies in `X.basicOpen s`. -/
theorem mem_basicOpen_of_ev_ne_zero {U : X.Opens} (s : Γ(X, U)) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (h : ev q U s ≠ 0) : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s := by
  unfold ev at h
  rw [dif_pos hU] at h
  have hu : IsUnit (q.appLE U ⊤ hU s) := by
    have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hU s)) :=
      isUnit_iff_ne_zero.mpr h
    have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using this
  have hb := (Spec (CommRingCat.of ℂ)).basicOpen_of_isUnit hu
  rw [Scheme.Hom.preimage_basicOpen]
  have he : q.appLE U ⊤ hU s = (Spec (CommRingCat.of ℂ)).presheaf.map (homOfLE hU).op
      (q.app U s) := rfl
  rw [he, Scheme.basicOpen_res] at hb
  rw [← hb]
  exact inf_le_right

end Ev

/-- Finite sums of products `inl(α) · inr(β)`. -/
def IsSumProd {B C P : Type} [CommRing B] [CommRing C] [CommRing P] (inl : B →+* P)
    (inr : C →+* P) (r : P) : Prop :=
  ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k)

theorem isSumProd_add {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r + r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n + m, Fin.append α α', Fin.append β β', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSumProd_mul {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r * r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n * m, fun k => α (finProdFinEquiv.symm k).1 * α' (finProdFinEquiv.symm k).2,
    fun k => β (finProdFinEquiv.symm k).1 * β' (finProdFinEquiv.symm k).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  show _ = ∑ k, (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))
    (finProdFinEquiv.symm k)
  refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul]
  ring

theorem isSumProd_neg {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r : P} (h : IsSumProd inl inr r) : IsSumProd inl inr (-r) := by
  obtain ⟨n, α, β, rfl⟩ := h
  exact ⟨n, fun k => -α k, β, by simp [Finset.sum_neg_distrib]⟩

/-- In a pushout square of commutative rings, every element of the pushout is a finite sum of
products `inl(α) · inr(β)`. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (r : P) :
    ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k) := by
  let T : Subring P := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  have hT : ∀ x ∈ T, IsSumProd inl.hom inr.hom x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact ⟨1, fun _ => b, fun _ => 1, by simp⟩
      · exact ⟨1, fun _ => 1, fun _ => c, by simp⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
    | add x y _ _ hx hy => exact isSumProd_add hx hy
    | neg x _ hx => exact isSumProd_neg hx
    | mul x y _ _ hx hy => exact isSumProd_mul hx hy
  let jl : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let jr : C ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ jl = g ≫ jr := by
    ext a
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) h.w
  let ι : CommRingCat.of T ⟶ P := CommRingCat.ofHom T.subtype
  have hid : h.desc jl jr w ≫ ι = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]; rfl
    · rw [h.inr_desc_assoc, Category.comp_id]; rfl
  have hr : r ∈ T := by
    have : ι (h.desc jl jr w r) = r := by rw [← ConcreteCategory.comp_apply, hid]; rfl
    rw [← this]
    exact ((h.desc jl jr w) r).2
  exact hT r hr

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, proved

The local structure of a fibre product of schemes over an affine base at complex points
(`core_local`): affine opens `Vᵢ`, the affine scheme `Q = V₁ ×_S V₂` (an open of the product
through `j`), whose ring is the pushout `Γ(V₁) ⊗_{Γ(S)} Γ(V₂)` (`isPushout_appTop_of_isPullback`),
a basic open `D(h) ⊆ j⁻¹W` of `Q` and a fraction `t = a/h^N` on it. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem specC_eq (z w : Spec (CommRingCat.of ℂ)) : z = w := by
  have hz : z.asIdeal = ⊥ := by
    haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  have hw : w.asIdeal = ⊥ := by
    haveI := w.isPrime; exact Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext (hz.trans hw.symm)

theorem top_le_of_mem {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (pt : Spec (CommRingCat.of ℂ)) (h : q pt ∈ U) : ⊤ ≤ q ⁻¹ᵁ U := by
  intro z _
  rw [specC_eq z pt]
  exact h

/-- The section of `X` on `U` corresponding to a global section of `U.toScheme`. -/
noncomputable def secOf {X : Scheme.{0}} (U : X.Opens) (α : Γ(U.toScheme, ⊤)) : Γ(X, U) :=
  (inv (U.ι.appLE U ⊤ U.ι_preimage_self.ge)) α

theorem ev_secOf {X : Scheme.{0}} (U : X.Opens) (y : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (α : Γ(U.toScheme, ⊤)) : ev (y ≫ U.ι) U (secOf U α) = ev y ⊤ α := by
  have h1 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
    intro z _
    show U.ι (y z) ∈ U
    exact (y z).2
  have h2 : ⊤ ≤ y ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  unfold ev
  rw [dif_pos h1, dif_pos h2]
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ U.ι_preimage_self.ge h2]
  unfold secOf
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem ev_comp_top {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : ev (q ≫ f) ⊤ s = ev q ⊤ (f.appTop s) :=
  ev_comp q f ⊤ s

section Core

variable {S X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)

/-- **The local structure of a fibre product over an affine base, at complex points.** -/
theorem core_local [IsAffine S] (W : (pullback f₁ f₂).Opens) (t : Γ(pullback f₁ f₂, W))
    (x₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (x₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
    (hx12 : x₁ ≫ f₁ = x₂ ≫ f₂) (hx : ⊤ ≤ (pullback.lift x₁ x₂ hx12) ⁻¹ᵁ W) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (n : ℕ) (a c : Fin n → Γ(X₁, V₁))
      (b d : Fin n → Γ(X₂, V₂)),
      ⊤ ≤ x₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ x₂ ⁻¹ᵁ V₂ ∧
      (∑ k, ev x₁ V₁ (c k) * ev x₂ V₂ (d k)) ≠ 0 ∧
      ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
        (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
        (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift y₁ y₂ hy) ⁻¹ᵁ W ∧
        ev (pullback.lift y₁ y₂ hy) W t * (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) =
          ∑ k, ev y₁ V₁ (a k) * ev y₂ V₂ (b k) := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
  have hpt : pt ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := trivial
  obtain ⟨V₁, hV₁, m₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₁ pt ∈ (⊤ : X₁.Opens) from trivial)
  obtain ⟨V₂, hV₂, m₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₂ pt ∈ (⊤ : X₂.Opens) from trivial)
  haveI : IsAffine V₁.toScheme := hV₁
  haveI : IsAffine V₂.toScheme := hV₂
  set g₁ := V₁.ι ≫ f₁ with hg₁
  set g₂ := V₂.ι ≫ f₂ with hg₂
  let j : pullback g₁ g₂ ⟶ pullback f₁ f₂ :=
    pullback.map g₁ g₂ f₁ f₂ V₁.ι V₂.ι (𝟙 S) (by simp [hg₁]) (by simp [hg₂])
  have hj1 : j ≫ pullback.fst f₁ f₂ = pullback.fst g₁ g₂ ≫ V₁.ι := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ V₂.ι := pullback.lift_snd _ _ _
  -- complex points of `V₁ × V₂` lift to `Q`
  have lift_pt : ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
      (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
      ∃ yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂, yQ ≫ j = pullback.lift y₁ y₂ hy ∧
        yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι = y₁ ∧ yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι = y₂ := by
    intro y₁ y₂ hy h1 h2
    have r1 : Set.range y₁ ⊆ Set.range V₁.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h1 (show z ∈ ⊤ from trivial)
    have r2 : Set.range y₂ ⊆ Set.range V₂.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h2 (show z ∈ ⊤ from trivial)
    let z₁ := IsOpenImmersion.lift V₁.ι y₁ r1
    let z₂ := IsOpenImmersion.lift V₂.ι y₂ r2
    have hz₁ : z₁ ≫ V₁.ι = y₁ := IsOpenImmersion.lift_fac _ _ _
    have hz₂ : z₂ ≫ V₂.ι = y₂ := IsOpenImmersion.lift_fac _ _ _
    have hc : z₁ ≫ g₁ = z₂ ≫ g₂ := by
      rw [hg₁, hg₂, ← Category.assoc, hz₁, ← Category.assoc, hz₂, hy]
    refine ⟨pullback.lift z₁ z₂ hc, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, pullback.lift_fst, pullback.lift_fst_assoc, hz₁]
      · rw [Category.assoc, hj2, pullback.lift_snd, pullback.lift_snd_assoc, hz₂]
    · rw [pullback.lift_fst_assoc, hz₁]
    · rw [pullback.lift_snd_assoc, hz₂]
  obtain ⟨xQ, hxQ, -, -⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
    (top_le_of_mem _ _ pt m₂)
  have hxQW : xQ pt ∈ j ⁻¹ᵁ W := by
    have := hx hpt
    rw [← hxQ] at this
    exact this
  obtain ⟨h, hhW, hhx⟩ := (isAffineOpen_top (pullback g₁ g₂)).exists_basicOpen_le
    (V := j ⁻¹ᵁ W) ⟨xQ pt, hxQW⟩ trivial
  -- the fraction
  set tQ : Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) :=
    (pullback g₁ g₂).presheaf.map (homOfLE hhW).op (j.app W t) with htQ
  obtain ⟨⟨a0, ⟨_, N, rfl⟩⟩, heq⟩ := IsLocalization.surj (Submonoid.powers h) tQ
  have hal : ∀ r : Γ(pullback g₁ g₂, ⊤),
      algebraMap Γ(pullback g₁ g₂, ⊤) Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) r =
        (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op r :=
    fun _ => rfl
  have heq' : tQ * (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op
      (h ^ (N + 1)) = (pullback g₁ g₂).presheaf.map
        (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op (a0 * h) := by
    simp only at heq
    rw [← hal, ← hal, pow_succ, map_mul, map_mul, ← mul_assoc, heq]
  -- sums of products
  have hpo := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g₁ g₂)
  obtain ⟨n₁, α, β, hα⟩ := exists_sum_of_isPushout hpo (a0 * h)
  obtain ⟨n₂, γ, δ, hγ⟩ := exists_sum_of_isPushout hpo (h ^ (N + 1))
  -- evaluation of a sum of products at a lifted point
  have key : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂) {m : ℕ}
      (u : Fin m → Γ(V₁.toScheme, ⊤)) (v : Fin m → Γ(V₂.toScheme, ⊤)),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (secOf V₁ (u k)) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (secOf V₂ (v k))) =
      ev yQ ⊤ (∑ k, (pullback.fst g₁ g₂).appTop (u k) * (pullback.snd g₁ g₂).appTop (v k)) := by
    intro yQ m u v
    rw [ev_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul, ← Category.assoc, ev_secOf, ← Category.assoc, ev_secOf, ev_comp_top,
      ev_comp_top]
  let a : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append (fun k => secOf V₁ (α k)) 0
  let b : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append (fun k => secOf V₂ (β k)) 0
  let c : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append 0 (fun k => secOf V₁ (γ k))
  let d : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append 0 (fun k => secOf V₂ (δ k))
  have hA : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (a k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (b k)) = ev yQ ⊤ (a0 * h) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [key, hα]
  have hH : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (c k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (d k)) = ev yQ ⊤ h ^ (N + 1) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [c, d, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    rw [key, ← hγ, ev_pow yQ ⊤ (fun _ _ => trivial)]
  refine ⟨V₁, V₂, n₁ + n₂, a, c, b, d, top_le_of_mem _ _ pt m₁, top_le_of_mem _ _ pt m₂, ?_, ?_⟩
  · obtain ⟨xQ', hxQ', e1, e2⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
      (top_le_of_mem _ _ pt m₂)
    have hxQ'h : ⊤ ≤ xQ' ⁻¹ᵁ (pullback g₁ g₂).basicOpen h := by
      have hjinj : xQ' = xQ := by
        apply pullback.hom_ext
        · apply (cancel_mono V₁.ι).mp
          rw [Category.assoc, Category.assoc, e1, ← hj1, ← Category.assoc, hxQ,
            pullback.lift_fst]
        · apply (cancel_mono V₂.ι).mp
          rw [Category.assoc, Category.assoc, e2, ← hj2, ← Category.assoc, hxQ,
            pullback.lift_snd]
      rw [hjinj]
      exact top_le_of_mem _ _ pt hhx
    rw [← e1, ← e2, hH]
    exact pow_ne_zero _ (ev_ne_zero_of_mem xQ' h hxQ'h)
  · intro y₁ y₂ hy h1 h2 hne
    obtain ⟨yQ, hyQ, e1, e2⟩ := lift_pt y₁ y₂ hy h1 h2
    subst e1 e2
    rw [hH] at hne ⊢
    rw [hA]
    have hev : ev yQ ⊤ h ≠ 0 := fun h0 => hne (by rw [h0, zero_pow (Nat.succ_ne_zero N)])
    have hmem : ⊤ ≤ yQ ⁻¹ᵁ (pullback g₁ g₂).basicOpen h :=
      mem_basicOpen_of_ev_ne_zero yQ h (fun _ _ => trivial) hev
    have hW : ⊤ ≤ yQ ⁻¹ᵁ (j ⁻¹ᵁ W) := hmem.trans ((TopologicalSpace.Opens.map yQ.base).map
      (homOfLE hhW)).le
    refine ⟨?_, ?_⟩
    · rw [← hyQ]; exact hW
    · rw [← hyQ, ev_comp, ← ev_res yQ (homOfLE hhW) hmem, ← htQ,
        ← ev_pow yQ ⊤ (fun _ _ => trivial),
        ← ev_res yQ (homOfLE ((pullback g₁ g₂).basicOpen_le h)) hmem (h ^ (N + 1)),
        ← ev_mul, heq', ev_res yQ _ hmem]

end Core

end ZInQ.Metrization2
