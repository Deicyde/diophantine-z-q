import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: basic tools for the address constructions (App G, tex 10625–10700)

* `lam`: a basis of the dual address space with `λ_i(x_*) = 1` (tex 10657–10661);
* locality of a symbol (graph dependence with the identity map);
* the network operator depends only on the auxiliary-incident bits;
* coefficients of the network operator vanish off the terminal pairs.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

/-! ### The target-adapted dual basis -/

/-- `λ_i`, a basis of the dual address space with `λ_i(x_*) = 1` for all `i` (tex 10657–10661):
one functional taking the value one at `x_*` (`e_{j₀}`, where `x_*(j₀) = 1`), added to a basis of
the functionals vanishing at `x_*`. -/
def lam {b : ℕ} (xs : Fin b → ZMod 2) (j0 i : Fin b) : Fin b → ZMod 2 :=
  if i = j0 then Pi.single j0 1 else Pi.single i 1 + (xs i + 1) • Pi.single j0 1

theorem lam_apply_sum {b : ℕ} (xs : Fin b → ZMod 2) (j0 i : Fin b) (x : Fin b → ZMod 2) :
    (∑ k, lam xs j0 i k * x k) = if i = j0 then x j0 else x i + (xs i + 1) * x j0 := by
  unfold lam
  split_ifs with h
  · simp [Pi.single_apply]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    simp [Pi.single_apply]

/-- `λ_i(x_*) = 1`. -/
theorem lam_target {b : ℕ} {xs : Fin b → ZMod 2} {j0 : Fin b} (h : xs j0 = 1) (i : Fin b) :
    (∑ k, lam xs j0 i k * xs k) = 1 := by
  rw [lam_apply_sum]
  split_ifs
  · exact h
  · rw [h, mul_one, ← add_assoc, zmod2_add_self, zero_add]

theorem lam_ne_zero {b : ℕ} {xs : Fin b → ZMod 2} {j0 : Fin b} (h : xs j0 = 1) (i : Fin b) :
    lam xs j0 i ≠ 0 := by
  intro h0
  have := lam_target h i
  rw [h0] at this
  simp at this

/-- All `λ_i` take the value one only at `x_*`. -/
theorem lam_all_one {b : ℕ} {xs : Fin b → ZMod 2} {j0 : Fin b} (h : xs j0 = 1)
    (x : Fin b → ZMod 2) (hx : ∀ i, (∑ k, lam xs j0 i k * x k) = 1) : x = xs := by
  have h0 : x j0 = 1 := by simpa [lam_apply_sum] using hx j0
  funext i
  by_cases hi : i = j0
  · subst hi; rw [h0, h]
  · have := hx i
    rw [lam_apply_sum, if_neg hi, h0, mul_one] at this
    rcases zmod2_cases (x i) with h1 | h1 <;> rcases zmod2_cases (xs i) with h2 | h2 <;>
      rw [h1, h2] at this ⊢ <;> first | rfl | (exfalso; revert this; decide)

theorem exists_coord_one {b : ℕ} {x : Fin b → ZMod 2} (hx : x ≠ 0) : ∃ j, x j = 1 := by
  by_contra hcon
  push_neg at hcon
  exact hx (funext fun j => (zmod2_cases (x j)).resolve_right (hcon j))

/-! ### Locality of symbols -/

/-- A symbol depends only on the data on the vertex set (graph dependence, identity map). -/
theorem CoefficientRules.congr {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) {Γ Δ : Config L} (hΓ : Γ.Compatible ε) (hV : Γ.V = Δ.V)
    (ht : ∀ v ∈ Γ.V, Γ.t v = Δ.t v)
    (hz : ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → Γ.z v w = Δ.z v w) : A Γ = A Δ := by
  refine hA.graph_dependence Γ Δ hΓ ⟨Equiv.subtypeEquivRight (fun v => by rw [hV]), ?_, ?_⟩
  · intro v; exact (ht v v.2).symm
  · intro v w hvw
    exact (hz v v.2 w w.2 (fun h => hvw (Subtype.ext h))).symm

theorem Config.Compatible.flipBy {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).Compatible ε := by
  intro v hv w hw hvw
  have h := hΓ v hv w hw hvw
  simp only [Config.flipBy]
  have hs : s(w, v) = s(v, w) := Sym2.eq_swap
  by_cases hU : s(v, w) ∈ U
  · rw [if_pos ⟨hvw, hU⟩, if_pos ⟨Ne.symm hvw, hs ▸ hU⟩]
    calc Γ.z v w + 1 + (Γ.z w v + 1) = Γ.z v w + Γ.z w v + (1 + 1) := by ring
      _ = _ := by rw [h, zmod2_add_self, add_zero]
  · rw [if_neg (fun h' => hU h'.2), if_neg (fun h' => hU (hs ▸ h'.2))]
    simpa using h

theorem Config.Compatible.restrict {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    {W : Finset ℕ} (hW : W ⊆ Γ.V) : (Γ.restrict W).Compatible ε :=
  fun v hv w hw hvw => hΓ v (hW hv) w (hW hw) hvw

/-- The flip set only matters on pairs of the vertex set. -/
theorem CoefficientRules.flipBy_inter {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) {Γ : Config L} (hΓ : Γ.Compatible ε) (U : Finset (Sym2 ℕ)) :
    A (Γ.flipBy U) = A (Γ.flipBy (U ∩ pairs Γ.V)) := by
  refine hA.congr (hΓ.flipBy U) rfl (fun _ _ => rfl) ?_
  intro v hv w hw hvw
  have hv' : v ∈ Γ.V := hv
  have hw' : w ∈ Γ.V := hw
  simp only [Config.flipBy]
  congr 1
  have hp : s(v, w) ∈ pairs Γ.V := by
    unfold pairs
    exact Finset.mem_image.mpr ⟨(v, w), by simp [hv', hw', hvw], rfl⟩
  simp [Finset.mem_inter, hp]

/-! ### The network operator depends only on the auxiliary-incident bits -/

theorem netEdges_congr {Γ Δ : Config L} {T X : Finset ℕ}
    (h : ∀ x ∈ X, ∀ u ∈ T ∪ X, Γ.z x u = Δ.z x u) : netEdges Γ T X = netEdges Δ T X := by
  unfold netEdges
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product] at hp
  rw [h p.1 hp.1 p.2 hp.2]

theorem netOp_congr {Γ Δ : Config L} {T X : Finset ℕ}
    (h : ∀ x ∈ X, ∀ u ∈ T ∪ X, Γ.z x u = Δ.z x u) : netOp Γ T X = netOp Δ T X := by
  unfold netOp
  rw [netEdges_congr h]

theorem lap_congr {Γ Δ : Config L} {T X : Finset ℕ}
    (h : ∀ x ∈ X, ∀ u ∈ T ∪ X, Γ.z x u = Δ.z x u) : lap Γ T X = lap Δ T X := by
  funext i j
  unfold lap
  split_ifs with hij
  · exact Finset.sum_congr rfl fun u hu => h i i.2 u (Finset.mem_of_mem_erase hu)
  · exact h i i.2 j (Finset.mem_union_right _ j.2)

/-! ### Coefficients of the network operator off the terminal pairs -/

theorem rep_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (hv : v ∈ V) : rep V S v ∈ V := by
  classical
  unfold rep
  have hne : (V.filter (fun u => conn S u v)).Nonempty :=
    ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.EqvGen.refl v⟩⟩
  rw [dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1

theorem starForest_subset_pairs (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    starForest T S ⊆ pairs T := by
  classical
  intro e he
  unfold starForest at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  rw [Finset.mem_filter] at ha
  unfold pairs
  exact Finset.mem_image.mpr ⟨(rep T S a, a), by simp [rep_mem ha.1, ha.1, ha.2], rfl⟩

theorem prod_X_eq_monomial (F : Finset (Sym2 ℕ)) :
    (∏ e ∈ F, (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2))) =
      MvPolynomial.monomial (∑ e ∈ F, Finsupp.single e 1) 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F haF ih =>
    rw [Finset.prod_insert haF, Finset.sum_insert haF, ih, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

theorem sum_single_eq_single {F : Finset (Sym2 ℕ)} {f : Sym2 ℕ}
    (h : (∑ e ∈ F, Finsupp.single e (1 : ℕ)) = Finsupp.single f 1) : F = {f} := by
  classical
  have hsupp : ∀ g, (∑ e ∈ F, Finsupp.single e (1 : ℕ)) g = if g ∈ F then 1 else 0 := by
    intro g
    rw [Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply]
  ext g
  have := hsupp g
  rw [h, Finsupp.single_apply] at this
  simp only [Finset.mem_singleton]
  constructor
  · intro hg
    rw [if_pos hg] at this
    by_contra hne
    rw [if_neg (Ne.symm hne)] at this
    exact absurd this (by norm_num)
  · intro hgf
    subst hgf
    by_contra hg
    rw [if_neg hg, if_pos rfl] at this
    exact absurd this (by norm_num)

theorem netOp_coeff_single_of_not_mem (Γ : Config L) (T X : Finset ℕ) {f : Sym2 ℕ}
    (hf : f ∉ pairs T) : (netOp Γ T X).coeff (Finsupp.single f 1) = 0 := by
  classical
  unfold netOp
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro S _
  rw [prod_X_eq_monomial, MvPolynomial.coeff_monomial]
  split_ifs with h
  · exfalso
    have hF := sum_single_eq_single h
    apply hf
    exact starForest_subset_pairs T S (hF ▸ Finset.mem_singleton_self f)
  · rfl

end ZInQ.Manuscript.RC.Symbols
