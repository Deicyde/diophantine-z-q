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
