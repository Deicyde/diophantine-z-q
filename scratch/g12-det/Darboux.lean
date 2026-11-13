import Mathlib

/-! # g12-det: `Darboux` (symplectic bases), proved from Mathlib

`Darboux` is the named linear-algebra Prop of scratch/g12-det/DetTate.lean (copied verbatim).
Proof: induction on `n`; split off a hyperbolic plane `span {e, f}` (`B e f = 1`), whose
orthogonal complement carries a nondegenerate alternating form of dimension `2n`; a family with
Gram matrix `J` is a basis (`J² = −1`, card = finrank). -/

open Module LinearMap LinearMap.BilinForm

namespace G0Galois

/-- **Symplectic (Darboux) bases (GLUE, pure linear algebra; STANDARD: Bourbaki, Algèbre IX §5
no. 1, Artin, *Geometric algebra*, Thm 3.7; numbering UNVERIFIED).** A nondegenerate alternating
bilinear form on a space of dimension `2n` over a field has a basis, indexed by `Fin n ⊕ Fin n`,
in which its Gram matrix is Mathlib's `Matrix.J`. -/
def Darboux : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (n : ℕ), B.Nondegenerate → (∀ x, B x x = 0) →
    Module.finrank F V = 2 * n →
    ∃ b : Module.Basis (Fin n ⊕ Fin n) F V, LinearMap.BilinForm.toMatrix b B = Matrix.J (Fin n) F

section Proof

variable {F : Type} [Field F]

lemma skew_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

lemma isRefl_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) : B.IsRefl := by
  intro x y h
  rw [skew_of_alt B halt x y, h, neg_zero]

/-- A family with Gram matrix `J` is linearly independent. -/
lemma linearIndependent_of_gram {V : Type} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (n : ℕ) (v : Fin n ⊕ Fin n → V)
    (hv : ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j) : LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : Matrix.vecMul g (Matrix.J (Fin n) F) = 0 := by
    funext j
    have := congrArg (fun x => B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := congrArg (fun w => Matrix.vecMul w (Matrix.J (Fin n) F)) h1
  simp only [Matrix.vecMul_vecMul, Matrix.J_squared, Matrix.zero_vecMul] at h2
  intro i
  have := congrFun h2 i
  simpa [Matrix.vecMul_neg] using this

/-- The family version of Darboux, by induction. -/
lemma exists_gram_J : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V), B.Nondegenerate → (∀ x, B x x = 0) → finrank F V = 2 * n →
    ∃ v : Fin n ⊕ Fin n → V, ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B _ _ _
    exact ⟨fun i => by rcases i with i | i <;> exact i.elim0, fun i => by
      rcases i with i | i <;> exact i.elim0⟩
  | succ n ih =>
    intro V _ _ _ B hB halt hdim
    have hrefl := isRefl_of_alt B halt
    have hpos : 0 < finrank F V := by rw [hdim]; omega
    haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have : ∃ y, B e y ≠ 0 := by
      by_contra h
      push Not at h
      exact he (hB.1 e h)
    obtain ⟨y, hy⟩ := this
    set f := (B e y)⁻¹ • y with hfdef
    have hef : B e f = 1 := by
      rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
    have hfe : B f e = -1 := by rw [skew_of_alt B halt, hef]
    have hee : B e e = 0 := halt e
    have hff : B f f = 0 := halt f
    set H : Submodule F V := Submodule.span F {e, f} with hH
    set W : Submodule F V := B.orthogonal H with hW
    -- elements of `H`
    have hmemH : ∀ x ∈ H, ∃ a b : F, a • e + b • f = x := fun x hx =>
      Submodule.mem_span_pair.mp hx
    have heH : e ∈ H := Submodule.subset_span (by simp)
    have hfH : f ∈ H := Submodule.subset_span (by simp)
    -- `H ∩ H^⊥ = 0`
    have hdisj : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro x hx hxW
      obtain ⟨a, b, rfl⟩ := hmemH x hx
      have h1 : B e (a • e + b • f) = 0 := hxW e heH
      have h2 : B f (a • e + b • f) = 0 := hxW f hfH
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff] at h1 h2
      have ha : a = 0 := by linear_combination -h2
      have hb : b = 0 := by linear_combination h1
      simp [ha, hb]
    have hcompl : IsCompl H W :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl
        (B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hdisj)
    -- `finrank H = 2`
    have hli : LinearIndependent F ![e, f] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (B e) hst
      have h2 := congrArg (B f) hst
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff, map_zero] at h1 h2
      constructor
      · linear_combination -h2
      · linear_combination h1
    have hH2 : finrank F H = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
      exact this
    have hW2 : finrank F W = 2 * n := by
      rw [hW, finrank_orthogonal hB, hdim, hH2]; omega
    -- the restriction to `W` is nondegenerate and alternating
    have hBW : (B.restrict W).Nondegenerate := by
      have hsplit : ∀ z : V, ∃ h ∈ H, ∃ w ∈ W, h + w = z := fun z =>
        Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top)
      constructor
      · intro m hm
        apply Subtype.ext
        apply hB.1
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [map_add, hrefl _ _ (m.2 h hh)]
        have := hm ⟨w, hw⟩
        simpa using this
      · intro m hm
        apply Subtype.ext
        apply hB.2
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [LinearMap.map_add₂, m.2 h hh]
        have := hm ⟨w, hw⟩
        simpa using this
    have haltW : ∀ x, B.restrict W x x = 0 := fun x => halt x
    obtain ⟨w, hw⟩ := ih W (B.restrict W) hBW haltW hW2
    have hfw : ∀ x : W, B f x = 0 := fun x => x.2 f hfH
    have hew : ∀ x : W, B e x = 0 := fun x => x.2 e heH
    have hwf : ∀ x : W, B x f = 0 := fun x => hrefl _ _ (hfw x)
    have hwe : ∀ x : W, B x e = 0 := fun x => hrefl _ _ (hew x)
    have hww : ∀ i j, B (w i) (w j) = Matrix.J (Fin n) F i j := hw
    let v : Fin (n + 1) ⊕ Fin (n + 1) → V :=
      Sum.elim (Fin.cons f fun j => (w (Sum.inl j) : V))
        (Fin.cons e fun j => (w (Sum.inr j) : V))
    refine ⟨v, ?_⟩
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [v, Matrix.J, hef, hfe, hee, hff, hfw, hew, hwf, hwe, hww, Matrix.one_apply,
        Fin.succ_ne_zero, Fin.succ_inj]
    all_goals exact (Fin.succ_ne_zero _).symm

/-- **`Darboux`, proved.** -/
theorem darboux : Darboux := by
  intro F V _ _ _ _ B n hB halt hdim
  classical
  obtain ⟨v, hv⟩ := exists_gram_J n V B hB halt hdim
  have hli := linearIndependent_of_gram B n v hv
  have hcard : Fintype.card (Fin n ⊕ Fin n) = finrank F V := by
    rw [Fintype.card_sum, Fintype.card_fin, hdim]; ring
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hcard, ?_⟩
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.BilinForm.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank', hv]

end Proof

end G0Galois

#print axioms G0Galois.darboux
