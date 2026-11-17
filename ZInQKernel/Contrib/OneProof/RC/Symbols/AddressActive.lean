import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressGlue

/-!
# Lane RC2: active networks at an address (App G, tex 10657–10700)

For a glued configuration, the active configuration at an address consists of the active
terminals and, for each network, the auxiliary vertices of its active groups. The attachment
columns `colOf` (anchor columns `h_i = e_i` and the extra column `c` on a balanced set of
terminals) satisfy the row-sum identity `Σ_active columns = Q_J 1_J` (tex 10669–10683).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

section Active

variable {b : ℕ} {κ : Type*}

/-- The groups active at `x`: `λ_i(x) = 1`. -/
def actGroups (lamv : Fin b → Fin b → ZMod 2) (x : Fin b → ZMod 2) : Finset (Fin b) :=
  Finset.univ.filter (fun i => (∑ k, lamv i k * x k) = 1)

/-- The auxiliary vertices of network `p` active at `x`. -/
def auxAt (name : κ → Phys b → ℕ) (p : κ) (lamv : Fin b → Fin b → ZMod 2)
    (x : Fin b → ZMod 2) : Finset ℕ :=
  (Finset.univ.filter (fun q : Phys b => q.1 ∈ actGroups lamv x)).image (name p)

variable {Γ : Config L} {N : Finset κ} {name : κ → Phys b → ℕ} {spec : κ → NetSpec b}

theorem at_glue_V (hinj : NamesInj N name) (hfr : NamesFresh Γ N name)
    (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) :
    ((glue Γ N name spec).at (glueAct act' N name spec) x).V =
      (Γ.at act' x).V ∪ N.biUnion (fun p => auxAt name p (spec p).lamv x) := by
  classical
  ext v
  simp only [Config.at, Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨hv, hpres⟩
    rcases mem_glue_V.mp hv with hv' | ⟨p, hp, q, rfl⟩
    · left
      refine ⟨hv', ?_⟩
      simpa [present, glueAct_term hfr act' hv'] using hpres
    · right
      refine ⟨p, hp, ?_⟩
      unfold auxAt actGroups
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      simpa [present, glueAct_aux hinj act' hp q] using hpres
  · rintro (⟨hv', hpres⟩ | ⟨p, hp, hvp⟩)
    · refine ⟨mem_glue_V.mpr (Or.inl hv'), ?_⟩
      simpa [present, glueAct_term hfr act' hv'] using hpres
    · unfold auxAt actGroups at hvp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hvp
      refine ⟨mem_glue_V.mpr (Or.inr ⟨p, hp, q, rfl⟩), ?_⟩
      simpa [present, glueAct_aux hinj act' hp q] using hq

theorem auxAt_disjoint_terms (hfr : NamesFresh Γ N name) {p : κ} (hp : p ∈ N)
    (lamv : Fin b → Fin b → ZMod 2) (x : Fin b → ZMod 2) (T : Finset ℕ) (hT : T ⊆ Γ.V) :
    Disjoint T (auxAt name p lamv x) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  unfold auxAt at hu'
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu'
  exact hfr p hp q (hT hu)

theorem auxAt_disjoint (hinj : NamesInj N name) {p p' : κ} (hp : p ∈ N) (hp' : p' ∈ N)
    (hpp : p ≠ p') (lamv lamv' : Fin b → Fin b → ZMod 2) (x : Fin b → ZMod 2) :
    Disjoint (auxAt name p lamv x) (auxAt name p' lamv' x) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  unfold auxAt at hu hu'
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hu'
  exact hpp (hinj p' hp' p hp q' q hq').1.symm

/-- The active auxiliary vertices of one network are indexed by the coordinates of its active
groups. -/
noncomputable def auxEquiv (name : κ → Phys b → ℕ) (p : κ) (lamv : Fin b → Fin b → ZMod 2)
    (x : Fin b → ZMod 2) (hinj : ∀ q q', name p q = name p q' → q = q') :
    (auxAt name p lamv x) ≃ {q : Phys b // q.1 ∈ actGroups lamv x} :=
  (Equiv.ofBijective
    (fun q : {q : Phys b // q.1 ∈ actGroups lamv x} =>
      (⟨name p q.1, Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩,
        rfl⟩⟩ : auxAt name p lamv x))
    ⟨fun q q' h => Subtype.ext (hinj _ _ (congrArg Subtype.val h)), fun u => by
      obtain ⟨q, hq, hu⟩ := Finset.mem_image.mp u.2
      exact ⟨⟨q, (Finset.mem_filter.mp hq).2⟩, Subtype.ext hu⟩⟩).symm

theorem name_auxEquiv (name : κ → Phys b → ℕ) (p : κ) (lamv : Fin b → Fin b → ZMod 2)
    (x : Fin b → ZMod 2) (hinj : ∀ q q', name p q = name p q' → q = q')
    (i : auxAt name p lamv x) : name p (auxEquiv name p lamv x hinj i).1 = i := by
  unfold auxEquiv
  exact congrArg Subtype.val (Equiv.ofBijective_apply_symm_apply _ _ i)

end Active

/-! ### Attachment columns and the row-sum identity -/

section Columns

variable {b : ℕ}

/-- Attachment columns (tex 10670–10683): the anchor `anc g` of group `g` receives the column
`h_g = Q e_g = e_g`; each terminal of the balanced set `R` receives the extra column `c`. -/
def colOf (cv : Phys b → ZMod 2) (anc : Fin b → ℕ) (R : Finset ℕ) : ℕ → Phys b → ZMod 2 :=
  fun u => ∑ g, (if anc g = u then (1 : ZMod 2) else 0) • grp g +
    (if u ∈ R then (1 : ZMod 2) else 0) • cv

theorem sum_grp_apply (J : Finset (Fin b)) (q : Phys b) :
    (∑ g ∈ J, grp g q) = if q.1 ∈ J then 1 else 0 := by
  classical
  simp only [grp]
  rw [Finset.sum_ite_eq]

/-- The row-sum identity: the active attachment columns sum to `Q_J 1_J`, so the prescribed
principal matrix is the grounded Laplacian including its diagonal (tex 10669–10675, 10679–10683).
-/
theorem rowSum_colOf (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (hQ : ∀ g, Q *ᵥ grp g = grp g)
    (cv : Phys b → ZMod 2) (anc : Fin b → ℕ) (R T : Finset ℕ) (J : Finset (Fin b))
    (hanc : ∀ g ∈ J, anc g ∈ T) (hR : Even (R.filter (· ∈ T)).card)
    (q : {q : Phys b // q.1 ∈ J}) :
    ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 = ∑ u ∈ T, colOf cv anc R u q.1 := by
  classical
  have hq := q.2
  have hL : ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 = 1 := by
    have h1 : ∑ q' : {q : Phys b // q.1 ∈ J}, Q q.1 q'.1 =
        ∑ q' : Phys b, Q q.1 q' * (∑ g ∈ J, grp g q') := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun q' : Phys b => q'.1 ∈ J))
        (fun q' => by simp) (fun q' => Q q.1 q'), Finset.sum_filter]
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [sum_grp_apply]
      split_ifs <;> simp
    have h2 : ∑ q' : Phys b, Q q.1 q' * (∑ g ∈ J, grp g q') = ∑ g ∈ J, grp g q.1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      have := congrFun (hQ g) q.1
      simpa [Matrix.mulVec, dotProduct] using this
    rw [h1, h2, sum_grp_apply, if_pos hq]
  have hR' : ∑ u ∈ T, colOf cv anc R u q.1 = 1 := by
    simp only [colOf, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib]
    have hA : ∑ u ∈ T, ∑ g, (if anc g = u then (1 : ZMod 2) else 0) * grp g q.1 = 1 := by
      rw [Finset.sum_comm]
      have hg : ∀ g, ∑ u ∈ T, (if anc g = u then (1 : ZMod 2) else 0) * grp g q.1 =
          if anc g ∈ T then grp g q.1 else 0 := by
        intro g
        rw [← Finset.sum_mul, Finset.sum_ite_eq]
        split_ifs <;> simp
      simp_rw [hg]
      rw [Finset.sum_eq_single q.1.1]
      · rw [if_pos (hanc _ hq)]; simp [grp]
      · intro g _ hg'
        split_ifs <;> simp [grp, Ne.symm hg']
      · simp
    have hB : ∑ u ∈ T, (if u ∈ R then (1 : ZMod 2) else 0) * cv q.1 = 0 := by
      rw [← Finset.sum_mul, Finset.sum_boole]
      have hc : (T.filter (· ∈ R)).card = (R.filter (· ∈ T)).card := by
        rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      rw [hc]
      obtain ⟨k, hk⟩ := hR
      rw [hk]
      push_cast
      rw [zmod2_add_self, zero_mul]
    rw [hA, hB, add_zero]
  rw [hL, hR']

end Columns

end ZInQ.Manuscript.RC.Symbols
