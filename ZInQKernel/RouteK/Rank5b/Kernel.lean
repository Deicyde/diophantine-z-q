import ZInQKernel.RouteK.Rank5b.Matrices

/-!
# Route K, row 5b: the Selmer group and the kernel of `M₁` (tyz-5b Lemma 4.1)

For a configuration `𝒞` of product class `5` (in particular `natConfig n` for squarefree
`n ≡ 5 (mod 8)`), the solutions of the Selmer system `Σ(𝒞)` split as the torsion part
`{tors e f}` (the classes of `(−1, −n)^e (n, 2)^f`) plus the subspace `H` of solutions with
`b₁ = 0` and `a₀ = λ·u`, and `H ≅ ker M₁` by `σ ↦ (u + v, u)` (`kvec`), with inverse `ofKer`.

**Conventions.** The equations `(E1)`, `(E2)`, `(R)`, `(D)` of tyz-5b §4.1 are literally the rows
`Config.E1`, `Config.E2`, `a₀ = b₀` and `Config.D` of the Lean system: Monsky's matrix is
`(Ku)_x = Σ_{y≠x} [y/x](u_y + u_x)` in both, with `a_xy = [y/x] = bit y x`, and the 2-adic rows
for the class `5` are `twoAdicRows 5 = (a₁ = 0 ∧ b₁ = μ·u ∧ λ·v = λ·u)` (`D_iff_of_five`).
-/

namespace ZInQ.RouteK.Rank5b

open Matrix

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by revert x; decide

namespace Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒞 : RouteK.Config ι)

/-! ### Sums of `λ` and `μ` -/

/-- `y(V) = Σ λ = λ(c(𝒞))`. -/
theorem sum_lam : ∑ x, 𝒞.lam x = lam8 𝒞.prodClass :=
  (lam8_prod Finset.univ 𝒞.cls fun x _ => 𝒞.cls_mem x).symm

theorem sum_mu : ∑ x, 𝒞.mu x = mu8 𝒞.prodClass :=
  (mu8_prod Finset.univ 𝒞.cls fun x _ => 𝒞.cls_mem x).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Reciprocity in the form `[x/y] = [y/x] + λ_x λ_y`. -/
theorem bit_eq_bit_add {x y : ι} (h : x ≠ y) : 𝒞.bit x y = 𝒞.bit y x + 𝒞.lam x * 𝒞.lam y := by
  have := 𝒞.recip' h
  grind

/-! ### `M₁` applied to a vector -/

theorem Lc_mulVec (s : ι → ZMod 2) (x : ι) : (Lc 𝒞 *ᵥ s) x = 𝒞.monsky s x := by
  simp only [mulVec, dotProduct, Config.monsky]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have h1 : ∀ y ∈ Finset.univ.erase x, Lc 𝒞 x y * s y = 𝒞.bit y x * s y := fun y hy => by
    simp only [Lc, (Finset.ne_of_mem_erase hy).symm, ite_false]
  rw [Finset.sum_congr rfl h1]
  simp only [Lc, ite_true, Finset.sum_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem LcT_mulVec (t : ι → ZMod 2) (x : ι) :
    ((Lc 𝒞)ᵀ *ᵥ t) x = 𝒞.monsky t x + 𝒞.lam x * dot 𝒞.lam t + 𝒞.lam x * t x := by
  simp only [mulVec, dotProduct, transpose_apply, Config.monsky, dot]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x),
    ← Finset.add_sum_erase _ (fun y => 𝒞.lam y * t y) (Finset.mem_univ x)]
  have h1 : ∀ y ∈ Finset.univ.erase x, Lc 𝒞 y x * t y =
      𝒞.bit y x * t y + 𝒞.lam x * (𝒞.lam y * t y) := fun y hy => by
    simp only [Lc, Finset.ne_of_mem_erase hy, ite_false]
    rw [bit_eq_bit_add 𝒞 (Finset.ne_of_mem_erase hy).symm]
    ring
  rw [Finset.sum_congr rfl h1]
  simp only [Lc, ite_true, Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  have hsq := zmod2_mul_self (𝒞.lam x)
  generalize ∑ y ∈ Finset.univ.erase x, 𝒞.bit y x * t y = A
  generalize ∑ y ∈ Finset.univ.erase x, 𝒞.bit y x * t x = B
  generalize ∑ y ∈ Finset.univ.erase x, 𝒞.lam y * t y = C
  grind

/-- `M₁ (s, t)` at a top index `x`: `(Kt)_x + λ_x(s_x + t_x) + (λ·s + λ·t)λ_x`. -/
theorem M1c_mulVec_inl (w : ι ⊕ ι → ZMod 2) (x : ι) :
    (M1c 𝒞 *ᵥ w) (Sum.inl x) = 𝒞.monsky (w ∘ Sum.inr) x +
      𝒞.lam x * (w (Sum.inl x) + w (Sum.inr x)) +
      (dot 𝒞.lam (w ∘ Sum.inl) + dot 𝒞.lam (w ∘ Sum.inr)) * 𝒞.lam x := by
  rw [M1c, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, add_mulVec, Pi.add_apply,
    Lc_mulVec, LcT_mulVec, LcT_mulVec]
  simp only [Function.comp_apply]
  grind

/-- `M₁ (s, t)` at a bottom index `x`: `(Ks)_x + μ_x t_x`. -/
theorem M1c_mulVec_inr (w : ι ⊕ ι → ZMod 2) (x : ι) :
    (M1c 𝒞 *ᵥ w) (Sum.inr x) = 𝒞.monsky (w ∘ Sum.inl) x + 𝒞.mu x * w (Sum.inr x) := by
  rw [M1c, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Lc_mulVec, mulVec_diagonal]
  rfl

/-! ### Sums of rows -/

theorem lam_sum_of_five (h5 : 𝒞.prodClass = 5) : ∑ x, 𝒞.lam x = 0 := by
  rw [sum_lam, h5]; decide

theorem mu_sum_of_five (h5 : 𝒞.prodClass = 5) : ∑ x, 𝒞.mu x = 1 := by
  rw [sum_mu, h5]; decide

theorem monsky_add (u u' : ι → ZMod 2) (x : ι) :
    𝒞.monsky (u + u') x = 𝒞.monsky u x + 𝒞.monsky u' x := by
  simp only [RouteK.Config.monsky, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem monsky_const (f : ZMod 2) (x : ι) : 𝒞.monsky (fun _ => f) x = 0 := by
  simp [RouteK.Config.monsky, CharTwo.add_self_eq_zero]

omit [DecidableEq ι] in
theorem dot_add_right (l u u' : ι → ZMod 2) : dot l (u + u') = dot l u + dot l u' := by
  simp [dot, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem dot_const (l : ι → ZMod 2) (f : ZMod 2) : dot l (fun _ => f) = f * ∑ x, l x := by
  simp [dot, Finset.mul_sum, mul_comm]

/-- `Σ_x (Kw)_x = λ·w` when `y(V) = Σ λ = 0` (tyz-5b §4.1). -/
theorem sum_monsky (hl : ∑ x, 𝒞.lam x = 0) (w : ι → ZMod 2) :
    ∑ x, 𝒞.monsky w x = dot 𝒞.lam w := by
  have key : ∀ x, ∑ y, (𝒞.bit x y + 𝒞.bit y x) = 𝒞.lam x := by
    intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), CharTwo.add_self_eq_zero, zero_add,
      Finset.sum_congr rfl fun y hy => 𝒞.recip' (Finset.ne_of_mem_erase hy).symm,
      ← Finset.mul_sum]
    have h := hl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at h
    have h' : ∑ y ∈ Finset.univ.erase x, 𝒞.lam y = 𝒞.lam x := by grind
    rw [h', zmod2_mul_self]
  calc ∑ x, 𝒞.monsky w x = ∑ x, ∑ y, 𝒞.bit y x * (w y + w x) := by
        simp only [𝒞.monsky_eq_sum]
    _ = ∑ x, ∑ y, 𝒞.bit y x * w y + ∑ x, ∑ y, 𝒞.bit y x * w x := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ x, ∑ y, 𝒞.bit x y * w x + ∑ x, ∑ y, 𝒞.bit y x * w x := by
        rw [Finset.sum_comm (f := fun x y => 𝒞.bit y x * w y)]
    _ = ∑ x, w x * ∑ y, (𝒞.bit x y + 𝒞.bit y x) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = dot 𝒞.lam w := by
        simp only [key, dot, mul_comm]

omit [DecidableEq ι] in
/-- The 2-adic rows for the class `5`: `a₁ = 0`, `b₁ = μ·u`, `λ·v = λ·u`. -/
theorem D_iff_of_five (h5 : 𝒞.prodClass = 5) (σ : Unknowns ι) :
    𝒞.D σ ↔ σ.a1 = 0 ∧ σ.b1 = dot 𝒞.mu σ.u ∧ dot 𝒞.lam σ.v = dot 𝒞.lam σ.u := by
  unfold RouteK.Config.D twoAdicRows
  rw [h5]
  simp only [show (5 : ZMod 8) ≠ 1 by decide, show (5 : ZMod 8) ≠ 3 by decide, ite_false,
    ite_true]

end Config

/-! ### Torsion and the subspace `H` -/

/-- The sum of two vectors of unknowns. -/
def uadd {ι : Type*} (σ τ : Unknowns ι) : Unknowns ι :=
  ⟨σ.a0 + τ.a0, σ.a1 + τ.a1, σ.b0 + τ.b0, σ.b1 + τ.b1, σ.u + τ.u, σ.v + τ.v⟩

/-- The torsion classes: `tors e f` stands for `(−1, −n)^e (n, 2)^f`, i.e. `a₀ = b₀ = e`, `a₁ = 0`,
`b₁ = f`, `u = f·𝟏`, `v = e·𝟏`. -/
def tors {ι : Type*} (e f : ZMod 2) : Unknowns ι := ⟨e, 0, e, f, fun _ => f, fun _ => e⟩

theorem uadd_tors_tors {ι : Type*} (σ : Unknowns ι) (e f : ZMod 2) :
    uadd (uadd σ (tors e f)) (tors e f) = σ := by
  ext <;> simp [uadd, tors, add_assoc, CharTwo.add_self_eq_zero]

namespace Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒞 : RouteK.Config ι)

/-- Adding a torsion class preserves solutions (class `5`). -/
theorem isSol_uadd_tors (h5 : 𝒞.prodClass = 5) (σ : Unknowns ι) (e f : ZMod 2) :
    𝒞.IsSol (uadd σ (tors e f)) ↔ 𝒞.IsSol σ := by
  have hl := lam_sum_of_five 𝒞 h5
  have hm := mu_sum_of_five 𝒞 h5
  simp only [RouteK.Config.IsSol, D_iff_of_five 𝒞 h5, RouteK.Config.E1, RouteK.Config.E2, uadd,
    tors, monsky_add, monsky_const, dot_add_right, dot_const, hl, hm, Pi.add_apply]
  refine and_congr (forall_congr' fun x => ?_) (and_congr (forall_congr' fun x => ?_)
    (and_congr ?_ ?_)) <;> grind

/-- The subspace `H`: solutions with `b₁ = 0` and `a₀ = λ·u`. -/
def IsH (σ : Unknowns ι) : Prop := 𝒞.IsSol σ ∧ σ.b1 = 0 ∧ σ.a0 = dot 𝒞.lam σ.u

instance : DecidablePred (IsH 𝒞) := fun σ => by unfold IsH; infer_instance

/-- `k(σ) = (u + v, u)`. -/
def kvec (σ : Unknowns ι) : ι ⊕ ι → ZMod 2 := Sum.elim (σ.u + σ.v) σ.u

/-- The inverse of `kvec`: `(s, t) ↦ (u, v) = (t, s + t)`, `a₀ = b₀ = λ·t`, `a₁ = b₁ = 0`. -/
def ofKer (w : ι ⊕ ι → ZMod 2) : Unknowns ι :=
  ⟨dot 𝒞.lam (w ∘ Sum.inr), 0, dot 𝒞.lam (w ∘ Sum.inr), 0, w ∘ Sum.inr,
    w ∘ Sum.inl + w ∘ Sum.inr⟩

/-- `H` maps into `ker M₁`. -/
theorem M1c_mulVec_kvec (h5 : 𝒞.prodClass = 5) {σ : Unknowns ι} (hσ : IsH 𝒞 σ) :
    M1c 𝒞 *ᵥ kvec σ = 0 := by
  obtain ⟨⟨hE1, hE2, hR, hD⟩, hb1, ha0⟩ := hσ
  rw [D_iff_of_five 𝒞 h5] at hD
  obtain ⟨ha1, -, hlv⟩ := hD
  funext j
  rcases j with x | x
  · rw [M1c_mulVec_inl]
    have h1 := hE1 x
    simp only [RouteK.Config.E1] at h1
    simp only [kvec, Function.comp_def, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    rw [show (fun x => σ.u x + σ.v x) = σ.u + σ.v from rfl, dot_add_right,
      show (fun x => σ.u x) = σ.u from rfl]
    simp only [Pi.zero_apply]
    grind
  · rw [M1c_mulVec_inr]
    have h1 := hE1 x
    have h2 := hE2 x
    simp only [RouteK.Config.E1, RouteK.Config.E2] at h1 h2
    simp only [kvec, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    rw [show (fun x => (σ.u + σ.v) x) = σ.u + σ.v from rfl, monsky_add]
    simp only [Pi.zero_apply]
    grind

/-- `ker M₁` maps into `H`. -/
theorem isH_ofKer (h5 : 𝒞.prodClass = 5) {w : ι ⊕ ι → ZMod 2} (hw : M1c 𝒞 *ᵥ w = 0) :
    IsH 𝒞 (ofKer 𝒞 w) := by
  have hl := lam_sum_of_five 𝒞 h5
  set s := w ∘ Sum.inl with hs
  set t := w ∘ Sum.inr with ht
  have htop : ∀ x, 𝒞.monsky t x + 𝒞.lam x * (s x + t x) + (dot 𝒞.lam s + dot 𝒞.lam t) * 𝒞.lam x
      = 0 := fun x => by
    have h := M1c_mulVec_inl 𝒞 w x
    rw [hw] at h
    exact h.symm
  have hbot : ∀ x, 𝒞.monsky s x + 𝒞.mu x * t x = 0 := fun x => by
    have h := M1c_mulVec_inr 𝒞 w x
    rw [hw] at h
    exact h.symm
  have hst : ∀ f g : ι → ZMod 2, ∑ x, 𝒞.lam x * (f x + g x) = dot 𝒞.lam f + dot 𝒞.lam g :=
    fun f g => by simp [dot, mul_add, Finset.sum_add_distrib]
  have hds : dot 𝒞.lam s = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) fun x _ => htop x
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_monsky 𝒞 hl, hst, ← Finset.mul_sum,
      hl] at h
    grind
  have hmt : dot 𝒞.mu t = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) fun x _ => hbot x
    rw [Finset.sum_add_distrib, sum_monsky 𝒞 hl, hds, zero_add] at h
    exact h
  refine ⟨⟨fun x => ?_, fun x => ?_, rfl, ?_⟩, rfl, rfl⟩
  · simp only [RouteK.Config.E1, ofKer, ← hs, ← ht, Pi.add_apply]
    have := htop x
    grind
  · simp only [RouteK.Config.E2, ofKer, ← hs, ← ht, Pi.add_apply, monsky_add]
    have := htop x
    have := hbot x
    grind
  · rw [D_iff_of_five 𝒞 h5]
    simp only [ofKer, ← hs, ← ht, dot_add_right, hds, hmt, zero_add, and_self]

omit [DecidableEq ι] in
theorem kvec_ofKer (w : ι ⊕ ι → ZMod 2) : kvec (ofKer 𝒞 w) = w := by
  funext j
  rcases j with x | x
  · simp only [kvec, ofKer, Sum.elim_inl, Pi.add_apply, Function.comp_apply]
    grind
  · rfl

theorem ofKer_kvec {σ : Unknowns ι} (hσ : IsH 𝒞 σ) : ofKer 𝒞 (kvec σ) = σ := by
  obtain ⟨hsol, hb1, ha0⟩ := hσ
  have ha1 := RouteK.Config.IsSol.a1_eq_zero 𝒞 hsol
  have hR := hsol.2.2.1
  ext x
  · exact ha0.symm
  · exact ha1.symm
  · exact (hR ▸ ha0).symm
  · exact hb1.symm
  · rfl
  · simp only [ofKer, kvec, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    grind

/-- **Lemma 4.1, the isomorphism** `H ≅ ker M₁`, `σ ↦ (u + v, u)`. -/
def hEquivKer (h5 : 𝒞.prodClass = 5) : {σ // IsH 𝒞 σ} ≃ {w // M1c 𝒞 *ᵥ w = 0} where
  toFun σ := ⟨kvec σ.1, M1c_mulVec_kvec 𝒞 h5 σ.2⟩
  invFun w := ⟨ofKer 𝒞 w.1, isH_ofKer 𝒞 h5 w.2⟩
  left_inv σ := Subtype.ext (ofKer_kvec 𝒞 σ.2)
  right_inv w := Subtype.ext (kvec_ofKer 𝒞 w.1)

/-- The torsion coordinates `(a₀ + λ·u, b₁)` of a vector of unknowns. -/
def torsCoord (σ : Unknowns ι) : ZMod 2 × ZMod 2 := (σ.a0 + dot 𝒞.lam σ.u, σ.b1)

theorem isH_uadd_torsCoord (h5 : 𝒞.prodClass = 5) {σ : Unknowns ι} (hσ : 𝒞.IsSol σ) :
    IsH 𝒞 (uadd σ (tors (torsCoord 𝒞 σ).1 (torsCoord 𝒞 σ).2)) := by
  have hl := lam_sum_of_five 𝒞 h5
  refine ⟨(isSol_uadd_tors 𝒞 h5 _ _ _).2 hσ, ?_, ?_⟩
  · simp only [uadd, tors, torsCoord, CharTwo.add_self_eq_zero]
  · simp only [uadd, tors, torsCoord, dot_add_right, dot_const, hl]
    grind

/-- **Lemma 4.1, the splitting** `Sel₂ = 𝒯 ⊕ H`: every solution is uniquely `h + tors e f` with
`h ∈ H`. -/
def solEquivTorsH (h5 : 𝒞.prodClass = 5) :
    {σ // 𝒞.IsSol σ} ≃ (ZMod 2 × ZMod 2) × {σ // IsH 𝒞 σ} where
  toFun σ := (torsCoord 𝒞 σ.1, ⟨_, isH_uadd_torsCoord 𝒞 h5 σ.2⟩)
  invFun p := ⟨uadd p.2.1 (tors p.1.1 p.1.2), (isSol_uadd_tors 𝒞 h5 _ _ _).2 p.2.2.1⟩
  left_inv σ := Subtype.ext (uadd_tors_tors _ _ _)
  right_inv p := by
    obtain ⟨⟨e, f⟩, h, hh⟩ := p
    have hl := lam_sum_of_five 𝒞 h5
    have hc : torsCoord 𝒞 (uadd h (tors e f)) = (e, f) := by
      have hb := hh.2.1
      simp only [torsCoord, uadd, tors, dot_add_right, dot_const, hl, ← hh.2.2, hb]
      ext <;> simp only <;> grind
    simp only [hc]
    exact Prod.ext rfl (Subtype.ext (uadd_tors_tors _ _ _))

/-- **Lemma 4.1, the count**: `#Σ(𝒞) = 4 · #ker M₁`. -/
theorem card_sols_eq (h5 : 𝒞.prodClass = 5) :
    𝒞.sols.card = 4 * Fintype.card {w // M1c 𝒞 *ᵥ w = 0} := by
  have h1 : 𝒞.sols.card = Fintype.card {σ // 𝒞.IsSol σ} := by
    rw [Fintype.card_subtype]; rfl
  rw [h1, Fintype.card_congr (solEquivTorsH 𝒞 h5), Fintype.card_prod,
    Fintype.card_congr (hEquivKer 𝒞 h5)]
  simp

end Config

end ZInQ.RouteK.Rank5b
