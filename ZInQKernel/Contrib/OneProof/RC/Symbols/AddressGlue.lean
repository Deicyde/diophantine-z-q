import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressBasis
import ZInQKernel.Contrib.OneProof.RC.Symbols.Targets.NetworkMatrices

/-!
# Lane RC2: auxiliary networks glued to a terminal configuration (App G, tex 10657–10720)

* `lap_eq_Qsub`: when the auxiliary bits are the off-diagonal entries of a prescribed matrix `Q`
  and the attachment columns satisfy the row-sum identity, the grounded Laplacian of the active
  network is the principal submatrix `Q_J`, including its diagonal (tex 10669–10675);
* `glue`: adjoin finitely many networks of primary auxiliary vertices, each with its own matrix,
  activations and attachment columns, with no edges between distinct networks (tex 10734).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

/-! ### The grounded Laplacian of an active network is `Q_J` -/

section Identification

variable {b : ℕ} (Γ : Config L) (T X : Finset ℕ) (J : Finset (Fin b))
  (e : X ≃ {q : Phys b // q.1 ∈ J}) (Q : Matrix (Phys b) (Phys b) (ZMod 2))
  (col : ℕ → Phys b → ZMod 2)

/-- The grounded Laplacian of the active network is the prescribed principal matrix `Q_J`,
including its diagonal entries (tex 10669–10675). -/
theorem lap_eq_Qsub (hTX : Disjoint T X)
    (hQ : ∀ i j : X, i ≠ j → Γ.z i j = Q (e i).1 (e j).1)
    (hcol : ∀ i : X, ∀ u ∈ T, Γ.z i u = col u (e i).1)
    (hlap : ∀ q : {q : Phys b // q.1 ∈ J},
      ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 = ∑ u ∈ T, col u q.1) :
    lap Γ T X = (Qsub Q J).submatrix e e := by
  classical
  funext i j
  simp only [Matrix.submatrix_apply, Qsub]
  unfold lap
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hiT : (i : ℕ) ∉ T := fun h => Finset.disjoint_left.mp hTX h i.2
    have hsplit : (T ∪ X).erase i = T ∪ X.erase i := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hu | hu⟩
        · exact Or.inl hu
        · exact Or.inr ⟨hne, hu⟩
      · rintro (hu | ⟨hne, hu⟩)
        · exact ⟨fun h => hiT (h ▸ hu), Or.inl hu⟩
        · exact ⟨hne, Or.inr hu⟩
    have hdisj : Disjoint T (X.erase i) :=
      Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hTX
    rw [hsplit, Finset.sum_union hdisj]
    have h1 : ∑ u ∈ T, Γ.z i u = ∑ u ∈ T, col u (e i).1 :=
      Finset.sum_congr rfl fun u hu => hcol i u hu
    have h2 : ∑ u ∈ X.erase i, Γ.z i u =
        ∑ j ∈ (Finset.univ : Finset X).erase i, Q (e i).1 (e j).1 := by
      rw [Finset.sum_erase_eq_sub i.2, ← Finset.sum_coe_sort X,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
      exact Finset.sum_congr rfl fun j hj => hQ i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have h3 : ∑ q' : {q : Phys b // q.1 ∈ J}, Q (e i).1 q'.1 =
        Q (e i).1 (e i).1 + ∑ j ∈ (Finset.univ : Finset X).erase i, Q (e i).1 (e j).1 := by
      rw [← Equiv.sum_comp e (fun q' => Q (e i).1 q'.1),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [h1, h2, ← hlap (e i), h3, add_assoc, zmod2_add_self, add_zero]
  · rw [if_neg hij]
    exact hQ i j hij

theorem attach_eq_restr (hcol : ∀ i : X, ∀ u ∈ T, Γ.z i u = col u (e i).1) {a : ℕ}
    (ha : a ∈ T) : attach Γ X a = restr J (col a) ∘ e := by
  funext i
  simp only [attach, Function.comp_apply, restr]
  exact hcol i a ha

theorem det_lap_eq (hTX : Disjoint T X)
    (hQ : ∀ i j : X, i ≠ j → Γ.z i j = Q (e i).1 (e j).1)
    (hcol : ∀ i : X, ∀ u ∈ T, Γ.z i u = col u (e i).1)
    (hlap : ∀ q : {q : Phys b // q.1 ∈ J},
      ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 = ∑ u ∈ T, col u q.1) :
    (lap Γ T X).det = (Qsub Q J).det := by
  rw [lap_eq_Qsub Γ T X J e Q col hTX hQ hcol hlap, Matrix.det_submatrix_equiv_self]

theorem attach_adj_eq (hTX : Disjoint T X)
    (hQ : ∀ i j : X, i ≠ j → Γ.z i j = Q (e i).1 (e j).1)
    (hcol : ∀ i : X, ∀ u ∈ T, Γ.z i u = col u (e i).1)
    (hlap : ∀ q : {q : Phys b // q.1 ∈ J},
      ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 = ∑ u ∈ T, col u q.1)
    {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T) :
    attach Γ X a ⬝ᵥ ((lap Γ T X).adjugate *ᵥ attach Γ X c) =
      restr J (col a) ⬝ᵥ ((Qsub Q J).adjugate *ᵥ restr J (col c)) := by
  rw [lap_eq_Qsub Γ T X J e Q col hTX hQ hcol hlap, Matrix.adjugate_submatrix_equiv_self,
    attach_eq_restr Γ T X J e col hcol ha, attach_eq_restr Γ T X J e col hcol hc,
    Matrix.submatrix_mulVec_equiv]
  have hcomp : (restr J (col c) ∘ ⇑e) ∘ ⇑e.symm = restr J (col c) := by
    funext q; simp
  rw [hcomp]
  simp only [dotProduct, Function.comp_apply]
  exact Equiv.sum_comp e (fun q => restr J (col a) q * ((Qsub Q J).adjugate *ᵥ restr J (col c)) q)

end Identification

/-! ### Gluing networks to a terminal configuration -/

section Glue

variable {b : ℕ} {κ : Type*}

/-- The data of one auxiliary network: its prescribed matrix, the activations of its groups and
the attachment columns of the terminals (tex 10661–10683). -/
structure NetSpec (b : ℕ) where
  Q : Matrix (Phys b) (Phys b) (ZMod 2)
  lamv : Fin b → Fin b → ZMod 2
  col : ℕ → Phys b → ZMod 2

open Classical in
/-- Decoding auxiliary vertex names. -/
noncomputable def decode (N : Finset κ) (name : κ → Phys b → ℕ) (u : ℕ) : Option (κ × Phys b) :=
  if h : ∃ pq : κ × Phys b, pq.1 ∈ N ∧ name pq.1 pq.2 = u then some (Classical.choose h) else none

/-- Names are injective on the networks of `N`. -/
def NamesInj (N : Finset κ) (name : κ → Phys b → ℕ) : Prop :=
  ∀ p ∈ N, ∀ p' ∈ N, ∀ q q', name p q = name p' q' → p = p' ∧ q = q'

theorem decode_name {N : Finset κ} {name : κ → Phys b → ℕ} (hinj : NamesInj N name) {p : κ}
    (hp : p ∈ N) (q : Phys b) : decode N name (name p q) = some (p, q) := by
  classical
  have h : ∃ pq : κ × Phys b, pq.1 ∈ N ∧ name pq.1 pq.2 = name p q := ⟨(p, q), hp, rfl⟩
  unfold decode
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  obtain ⟨h1, h2⟩ := hinj _ hs.1 p hp _ q hs.2
  congr 1
  exact Prod.ext h1 h2

theorem decode_eq_none {N : Finset κ} {name : κ → Phys b → ℕ} {u : ℕ}
    (hu : ∀ p ∈ N, ∀ q, name p q ≠ u) : decode N name u = none := by
  classical
  unfold decode
  rw [dif_neg]
  rintro ⟨pq, h1, h2⟩
  exact hu pq.1 h1 pq.2 h2

open Classical in
/-- The glued configuration: the terminal configuration `Γ` and, for each network `p ∈ N`, the
primary auxiliary vertices `name p q`, with auxiliary bits given by the matrix of `p`, attachment
bits by its columns, and no bits between distinct networks. -/
noncomputable def glue (Γ : Config L) (N : Finset κ) (name : κ → Phys b → ℕ)
    (spec : κ → NetSpec b) : Config L where
  V := Γ.V ∪ N.biUnion (fun p => Finset.univ.image (name p))
  t := fun v => if v ∈ Γ.V then Γ.t v else 0
  z := fun u v =>
    if u ∈ Γ.V then
      (if v ∈ Γ.V then Γ.z u v else (decode N name v).elim 0 (fun pq => (spec pq.1).col u pq.2))
    else (decode N name u).elim 0 (fun pq =>
      if v ∈ Γ.V then (spec pq.1).col v pq.2 else
        (decode N name v).elim 0 (fun pq' =>
          if pq.1 = pq'.1 then (spec pq.1).Q pq.2 pq'.2 else 0))

/-- Activations of the glued configuration. -/
noncomputable def glueAct (act' : ℕ → Option (Fin b → ZMod 2)) (N : Finset κ)
    (name : κ → Phys b → ℕ) (spec : κ → NetSpec b) : ℕ → Option (Fin b → ZMod 2) :=
  fun v => (decode N name v).elim (act' v) (fun pq => some ((spec pq.1).lamv pq.2.1))

variable {Γ : Config L} {N : Finset κ} {name : κ → Phys b → ℕ} {spec : κ → NetSpec b}

/-- Fresh names: auxiliary vertices avoid the terminal configuration. -/
def NamesFresh (Γ : Config L) (N : Finset κ) (name : κ → Phys b → ℕ) : Prop :=
  ∀ p ∈ N, ∀ q, name p q ∉ Γ.V

theorem decode_of_mem (hfr : NamesFresh Γ N name) {u : ℕ} (hu : u ∈ Γ.V) :
    decode N name u = none :=
  decode_eq_none fun p hp q h => hfr p hp q (h ▸ hu)

theorem glue_z_tt {u v : ℕ} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) :
    (glue Γ N name spec).z u v = Γ.z u v := by
  simp [glue, hu, hv]

theorem glue_z_at (hinj : NamesInj N name) (hfr : NamesFresh Γ N name) {p : κ} (hp : p ∈ N)
    (q : Phys b) {v : ℕ} (hv : v ∈ Γ.V) :
    (glue Γ N name spec).z (name p q) v = (spec p).col v q := by
  simp [glue, hfr p hp q, hv, decode_name hinj hp q]

theorem glue_z_ta (hinj : NamesInj N name) (hfr : NamesFresh Γ N name) {p : κ} (hp : p ∈ N)
    (q : Phys b) {u : ℕ} (hu : u ∈ Γ.V) :
    (glue Γ N name spec).z u (name p q) = (spec p).col u q := by
  simp [glue, hfr p hp q, hu, decode_name hinj hp q]

open Classical in
theorem glue_z_aa (hinj : NamesInj N name) (hfr : NamesFresh Γ N name) {p p' : κ} (hp : p ∈ N)
    (hp' : p' ∈ N) (q q' : Phys b) :
    (glue Γ N name spec).z (name p q) (name p' q') = if p = p' then (spec p).Q q q' else 0 := by
  simp [glue, hfr p hp q, hfr p' hp' q', decode_name hinj hp q, decode_name hinj hp' q']

theorem glue_t_term {v : ℕ} (hv : v ∈ Γ.V) : (glue Γ N name spec).t v = Γ.t v := by
  simp [glue, hv]

theorem glue_t_aux (hfr : NamesFresh Γ N name) {p : κ} (hp : p ∈ N) (q : Phys b) :
    (glue Γ N name spec).t (name p q) = 0 := by
  simp [glue, hfr p hp q]

theorem glueAct_term (hfr : NamesFresh Γ N name) (act' : ℕ → Option (Fin b → ZMod 2)) {v : ℕ}
    (hv : v ∈ Γ.V) : glueAct act' N name spec v = act' v := by
  simp [glueAct, decode_of_mem hfr hv]

theorem glueAct_aux (hinj : NamesInj N name) (act' : ℕ → Option (Fin b → ZMod 2)) {p : κ}
    (hp : p ∈ N) (q : Phys b) :
    glueAct act' N name spec (name p q) = some ((spec p).lamv q.1) := by
  simp [glueAct, decode_name hinj hp q]

theorem mem_glue_V {v : ℕ} :
    v ∈ (glue Γ N name spec).V ↔ v ∈ Γ.V ∨ ∃ p ∈ N, ∃ q, name p q = v := by
  simp [glue]

/-- The glued configuration is compatible when the terminal configuration is and every network
matrix is symmetric (auxiliary vertices are primary). -/
theorem glue_compatible {ε : L →+ ZMod 2} (hΓ : Γ.Compatible ε) (hinj : NamesInj N name)
    (hfr : NamesFresh Γ N name) (hsym : ∀ p ∈ N, ∀ q q', (spec p).Q q q' = (spec p).Q q' q) :
    (glue Γ N name spec).Compatible ε := by
  intro u hu v hv huv
  rcases mem_glue_V.mp hu with hu' | ⟨p, hp, q, rfl⟩ <;>
    rcases mem_glue_V.mp hv with hv' | ⟨p', hp', q', rfl⟩
  · rw [glue_z_tt hu' hv', glue_z_tt hv' hu', glue_t_term hu', glue_t_term hv']
    exact hΓ u hu' v hv' huv
  · rw [glue_z_ta hinj hfr hp' q' hu', glue_z_at hinj hfr hp' q' hu', glue_t_aux hfr hp' q',
      zmod2_add_self]
    simp
  · rw [glue_z_at hinj hfr hp q hv', glue_z_ta hinj hfr hp q hv', glue_t_aux hfr hp q,
      zmod2_add_self]
    simp
  · rw [glue_z_aa hinj hfr hp hp' q q', glue_z_aa hinj hfr hp' hp q' q, glue_t_aux hfr hp q]
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, if_pos rfl, hsym p hp q q', zmod2_add_self]
      simp
    · rw [if_neg hpp, if_neg (Ne.symm hpp)]
      simp

theorem glue_extends (hfr : NamesFresh Γ N name) : Γ.Extends (glue Γ N name spec) := by
  refine ⟨fun v hv => mem_glue_V.mpr (Or.inl hv), fun v hv => glue_t_term hv, ?_⟩
  intro v hv w hw
  exact glue_z_tt hv hw

end Glue

end ZInQ.Manuscript.RC.Symbols
