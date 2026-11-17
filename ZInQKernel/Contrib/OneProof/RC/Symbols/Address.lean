import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressSV

/-!
# Lane RC2: the address constructions (`ex:app-simultaneous-address`, tex 10554–10790)

`assemble`: given the program sets chosen by the degree count, install one singular or varying
network per program (tex 10732–10735), glue them, and conclude that all symbols are one at every
nonzero address. `address_general` combines it with (G.1a) (`degree_count`), and
`address_general_one` with its one-symbol specialization (`degree_count_one`).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

/-- Coordinates of the auxiliary groups, coded by natural numbers. -/
def physCode {b : ℕ} (q : Phys b) : ℕ := 3 * q.1.val + q.2.val

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem physCode_injective {b : ℕ} : Function.Injective (physCode (b := b)) := by
  intro q q' h
  unfold physCode at h
  have h1 := q.2.isLt
  have h2 := q'.2.isLt
  have e1 : q.1.val = q'.1.val := by omega
  have e2 : q.2.val = q'.2.val := by omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem glueAct_congr {b : ℕ} {κ : Type*} (act' : ℕ → Option (Fin b → ZMod 2)) (N : Finset κ)
    (name : κ → Phys b → ℕ) {spec spec' : κ → NetSpec b}
    (h : ∀ p, (spec p).lamv = (spec' p).lamv) :
    glueAct act' N name spec = glueAct act' N name spec' := by
  funext v
  unfold glueAct
  cases decode N name v <;> simp [h]

/-- The selection property delivered by the degree count (G.1a). -/
def Selects {Y : Type*} [Fintype Y] (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2)
    (Ns Nv : Finset (Y × Sym2 ℕ)) : Prop :=
  ∀ (Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (Ov : Y × Sym2 ℕ → ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)),
    (∀ p ∈ Ns, IsSingularProgram p.1 p.2 (Os p)) → (∀ p ∈ Nv, IsVaryingProgram p.1 p.2 (Ov p)) →
    ∃ εv : Y × Sym2 ℕ → ZMod 2, ∀ s y,
      act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εv p) y) (P s y) ∅ = 1

/-- The conclusion of the address constructions: finitely many primary auxiliary vertices with
nonzero linear activations, only their incidences chosen, all original data fixed, and every
symbol equal to one at every nonzero address (tex 10568–10573). -/
def AddressConclusion {b : ℕ} (ε : L →+ ZMod 2) (As : Fin 2 → Config L → ZMod 2)
    (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2)) : Prop :=
  ∃ (Γ' : Config L) (act'' : ℕ → Option (Fin b → ZMod 2)),
    Γ'.Compatible ε ∧ Γ.Extends Γ' ∧ (∀ v ∈ Γ.V, act'' v = act' v) ∧
    (∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0 ∧ ∃ w, w ≠ 0 ∧ act'' v = some w) ∧
    ∀ x : Fin b → ZMod 2, x ≠ 0 → ∀ s, As s (Γ'.at act'' x) = 1

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem AddressConclusion.not_present_zero {b : ℕ} {ε : L →+ ZMod 2}
    {As : Fin 2 → Config L → ZMod 2} {Γ : Config L} {act' : ℕ → Option (Fin b → ZMod 2)}
    {Γ' : Config L} {act'' : ℕ → Option (Fin b → ZMod 2)}
    (h : ∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0 ∧ ∃ w, w ≠ 0 ∧ act'' v = some w)
    {v : ℕ} (hv : v ∈ Γ'.V) (hvΓ : v ∉ Γ.V) : v ∉ (Γ'.at act'' 0).V := by
  classical
  obtain ⟨-, w, -, hw⟩ := h v hv hvΓ
  intro hv0
  simp only [Config.at, Finset.mem_filter, present, hw] at hv0
  simp at hv0

/-- **The address assembly** (tex 10732–10790): given program sets selected by the degree count,
install one singular network for each `n_{x,e} = 2` and one varying network for each
`n_{x,e} = 1`, with disjoint auxiliary sets, anchors for every group and a balanced set for the
extra column; at every nonzero address the symbol values are the selected actions of the
products of network operators, hence one. -/
theorem assemble {ε : L →+ ZMod 2} {As : Fin 2 → Config L → ZMod 2}
    (hAs : ∀ s, CoefficientRules ε (As s)) (b : ℕ) (hb : 0 < b) (Γ : Config L)
    (hΓ : Γ.Compatible ε) (act' : ℕ → Option (Fin b → ZMod 2))
    (hanc : ∀ w : Fin b → ZMod 2, w ≠ 0 →
      ∃ u, u ∈ Γ.V ∧ ∀ x, (∑ k, w k * x k) = 1 → u ∈ (Γ.at act' x).V)
    (hbal : ∀ y : Fin b → ZMod 2, y ≠ 0 → ∀ e ∈ pairs (Γ.at act' y).V, ∃ R, R ⊆ Γ.V ∧
      (∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card) ∧
      ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (Ns Nv : Finset ({x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ)) (hdisj : Disjoint Ns Nv)
    (hmem : ∀ p ∈ Ns ∪ Nv, p.2 ∈ pairs (Γ.at act' p.1.1).V)
    (hsel : Selects (fun (s : Fin 2) (y : {x : Fin b → ZMod 2 // x ≠ 0}) U =>
      As s ((Γ.at act' y.1).flipBy U)) Ns Nv) :
    AddressConclusion ε As Γ act' := by
  classical
  set N := Ns ∪ Nv with hN
  -- choices attached to each network
  let j0 : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → Fin b :=
    fun p => Classical.choose (exists_coord_one p.1.2)
  have hj0 : ∀ p : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ, p.1.1 (j0 p) = 1 :=
    fun p => Classical.choose_spec (exists_coord_one p.1.2)
  let lamv : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → Fin b → Fin b → ZMod 2 :=
    fun p => lam p.1.1 (j0 p)
  let anc : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → Fin b → ℕ :=
    fun p g => Classical.choose (hanc (lamv p g) (lam_ne_zero (hj0 p) g))
  have hancp : ∀ (p : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ) (g : Fin b), anc p g ∈ Γ.V ∧
      ∀ x, (∑ k, lamv p g k * x k) = 1 → anc p g ∈ (Γ.at act' x).V :=
    fun p g => Classical.choose_spec (hanc (lamv p g) (lam_ne_zero (hj0 p) g))
  let R : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → Finset ℕ := fun p =>
    if h : p.2 ∈ pairs (Γ.at act' p.1.1).V then Classical.choose (hbal p.1.1 p.1.2 p.2 h)
    else ∅
  have hRp : ∀ p ∈ N, R p ⊆ Γ.V ∧ (∀ x, Even ((R p).filter (· ∈ (Γ.at act' x).V)).card) ∧
      ∀ a ∈ (Γ.at act' p.1.1).V, ∀ c ∈ (Γ.at act' p.1.1).V, a ≠ c →
        (a ∈ R p ∧ c ∈ R p ↔ s(a, c) = p.2) := by
    intro p hp
    have h := hmem p hp
    have hR : R p = Classical.choose (hbal p.1.1 p.1.2 p.2 h) := dif_pos h
    rw [hR]
    exact Classical.choose_spec (hbal p.1.1 p.1.2 p.2 h)
  -- names of the auxiliary vertices
  let B0 := Γ.V.sup id + 1
  let code : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → ℕ :=
    fun p => if h : p ∈ N then (N.equivFin ⟨p, h⟩ : ℕ) else 0
  let name : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → Phys b → ℕ :=
    fun p q => B0 + Nat.pair (code p) (physCode q)
  have hinj : NamesInj N name := by
    intro p hp p' hp' q q' h
    have h2 := Nat.pair_eq_pair.mp (Nat.add_left_cancel h)
    refine ⟨?_, physCode_injective h2.2⟩
    have h3 : code p = code p' := h2.1
    simp only [code, dif_pos hp, dif_pos hp'] at h3
    have := N.equivFin.injective (Fin.ext h3)
    exact congrArg Subtype.val this
  have hfr : NamesFresh Γ N name := by
    intro p _ q hq
    have hle : name p q ≤ Γ.V.sup id := Finset.le_sup (f := id) hq
    have : B0 ≤ name p q := Nat.le_add_right _ _
    omega
  -- network data
  let specF : ({x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → ZMod 2) →
      {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → NetSpec b := fun εv p =>
    if p ∈ Ns then ⟨Qsing b hb, lamv p, colOf (cvec b hb) (anc p) (R p)⟩
    else ⟨Qvar b hb (εv p), lamv p, colOf (cvec b hb) (anc p) (R p)⟩
  have hsymF : ∀ εv, ∀ p ∈ N, ∀ q q', (specF εv p).Q q q' = (specF εv p).Q q' q := by
    intro εv p _ q q'
    by_cases hp : p ∈ Ns
    · simp only [specF, if_pos hp]
      have h := congrFun (congrFun (Qsing_symm b hb) q) q'
      rw [Matrix.transpose_apply] at h
      exact h.symm
    · simp only [specF, if_neg hp]
      have h := congrFun (congrFun (Qvar_symm b hb (εv p)) q) q'
      rw [Matrix.transpose_apply] at h
      exact h.symm
  have hlamF : ∀ εv (p : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ), (specF εv p).lamv = lamv p := by
    intro εv p; by_cases hp : p ∈ Ns <;> simp [specF, hp]
  have hcolF : ∀ εv (p : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ),
      (specF εv p).col = colOf (cvec b hb) (anc p) (R p) := by
    intro εv p; by_cases hp : p ∈ Ns <;> simp [specF, hp]
  -- the network operators
  let O : ({x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → ZMod 2) →
      {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → {x : Fin b → ZMod 2 // x ≠ 0} →
        MvPolynomial (Sym2 ℕ) (ZMod 2) := fun εv p y =>
    netOp ((glue Γ N name (specF εv)).at (glueAct act' N name (specF εv)) y.1)
      (Γ.at act' y.1).V (auxAt name p (lamv p) y.1)
  have hOs : ∀ p ∈ Ns, IsSingularProgram p.1 p.2 (O (fun _ => 0) p) := by
    intro p hp
    have hpN : p ∈ N := Finset.mem_union_left _ hp
    exact singular_program hb hΓ hinj hfr (hsymF _) act' hpN (hj0 p) (anc p) (R p) p.2
      (if_pos hp) (fun g x hx => (hancp p g).2 x hx) (hRp p hpN).2.1
      (hRp p hpN).2.2 (hmem p hpN)
  have hOv : ∀ p ∈ Nv, IsVaryingProgram p.1 p.2 (fun η => O (fun _ => η) p) := by
    intro p hp
    have hpN : p ∈ N := Finset.mem_union_right _ hp
    have hpNs : p ∉ Ns := fun h => Finset.disjoint_left.mp hdisj h hp
    exact varying_program hb hΓ (fun η => specF (fun _ => η)) hinj hfr
      (fun η => hsymF (fun _ => η)) act' hpN (hj0 p) (anc p) (R p) p.2
      (fun η => if_neg hpNs) (fun g x hx => (hancp p g).2 x hx) (hRp p hpN).2.1
      (hRp p hpN).2.2 (hmem p hpN)
  obtain ⟨εv, hεv⟩ := hsel (O (fun _ => 0)) (fun p η => O (fun _ => η) p) hOs hOv
  -- the final configuration
  refine ⟨glue Γ N name (specF εv), glueAct act' N name (specF εv),
    glue_compatible hΓ hinj hfr (hsymF εv), glue_extends hfr,
    fun v hv => glueAct_term hfr act' hv, ?_, ?_⟩
  · intro v hv hvΓ
    rcases mem_glue_V.mp hv with h | ⟨p, hp, q, rfl⟩
    · exact absurd h hvΓ
    · refine ⟨glue_t_aux hfr hp q, (specF εv p).lamv q.1, ?_, glueAct_aux hinj act' hp q⟩
      rw [hlamF]
      exact lam_ne_zero (hj0 p) q.1
  · intro x hx s
    let y : {x : Fin b → ZMod 2 // x ≠ 0} := ⟨x, hx⟩
    set Γx := (glue Γ N name (specF εv)).at (glueAct act' N name (specF εv)) x with hΓxdef
    set T := (Γ.at act' x).V with hTdef
    have hTΓ : T ⊆ Γ.V := Finset.filter_subset _ _
    have hglue := glue_compatible hΓ hinj hfr (hsymF εv)
    have hΓx : Γx.Compatible ε := hglue.restrict (Finset.filter_subset _ _)
    have hV : Γx.V = T ∪ N.biUnion (fun p => auxAt name p (lamv p) x) := by
      rw [hΓxdef, at_glue_V hinj hfr act' x]
      simp only [hlamF, hTdef]
    have hmemX : ∀ p, ∀ v ∈ auxAt name p (lamv p) x, ∃ q, name p q = v := by
      intro p v hv
      unfold auxAt at hv
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨q, rfl⟩
    have hexp := netOp_expansion_multi (hAs s) Γx hΓx T N (fun p => auxAt name p (lamv p) x) hV
      (fun p hp => auxAt_disjoint_terms hfr hp _ x T hTΓ)
      (fun p hp p' hp' hpp => auxAt_disjoint hinj hp hp' hpp _ _ x)
      (fun p hp v hv => by
        obtain ⟨q, rfl⟩ := hmemX p v hv
        show (glue Γ N name (specF εv)).t (name p q) = 0
        exact glue_t_aux hfr hp q)
      (fun p hp p' hp' hpp v hv w hw => by
        obtain ⟨q, rfl⟩ := hmemX p v hv
        obtain ⟨q', rfl⟩ := hmemX p' w hw
        show (glue Γ N name (specF εv)).z _ _ = 0
        rw [glue_z_aa hinj hfr hp hp', if_neg hpp])
    have hTsub : T ⊆ Γx.V := by rw [hV]; exact Finset.subset_union_left
    have hfun : (fun U => As s ((Γx.restrict T).flipBy U)) =
        (fun U => As s ((Γ.at act' y.1).flipBy U)) := by
      funext U
      refine (hAs s).congr ((hΓx.restrict hTsub).flipBy U) rfl ?_ ?_
      · intro v hv
        exact glue_t_term (N := N) (name := name) (spec := specF εv) (hTΓ hv)
      · intro v hv w hw _
        show (glue Γ N name (specF εv)).z v w + _ = Γ.z v w + _
        rw [glue_z_tt (hTΓ hv) (hTΓ hw)]
    have hcongr : ∀ εw : {x : Fin b → ZMod 2 // x ≠ 0} × Sym2 ℕ → ZMod 2, ∀ p ∈ N,
        (specF εv p).Q = (specF εw p).Q →
        netOp Γx T (auxAt name p (lamv p) x) = O εw p y := by
      intro εw p hp hQ
      apply netOp_congr
      intro x' hx' u hu
      obtain ⟨q, rfl⟩ := hmemX p x' hx'
      show (glue Γ N name (specF εv)).z _ _ = (glue Γ N name (specF εw)).z _ _
      rcases Finset.mem_union.mp hu with huT | huX
      · rw [glue_z_at hinj hfr hp q (hTΓ huT), glue_z_at hinj hfr hp q (hTΓ huT), hcolF, hcolF]
      · obtain ⟨q', rfl⟩ := hmemX p u huX
        rw [glue_z_aa hinj hfr hp hp, glue_z_aa hinj hfr hp hp, if_pos rfl, if_pos rfl, hQ]
    have hprod : ∏ p ∈ N, netOp Γx T (auxAt name p (lamv p) x) =
        (∏ p ∈ Ns, O (fun _ => 0) p y) * ∏ p ∈ Nv, O (fun _ => εv p) p y := by
      rw [hN, Finset.prod_union hdisj]
      have h1 : ∏ p ∈ Ns, netOp Γx T (auxAt name p (lamv p) x) = ∏ p ∈ Ns, O (fun _ => 0) p y :=
        Finset.prod_congr rfl fun p hp => hcongr _ p (Finset.mem_union_left _ hp)
          (by simp only [specF, if_pos hp])
      have h2 : ∏ p ∈ Nv, netOp Γx T (auxAt name p (lamv p) x) =
          ∏ p ∈ Nv, O (fun _ => εv p) p y :=
        Finset.prod_congr rfl fun p hp => hcongr _ p (Finset.mem_union_right _ hp) (by
          have hpNs : p ∉ Ns := fun h => Finset.disjoint_left.mp hdisj h hp
          simp only [specF, if_neg hpNs])
      rw [h1, h2]
    rw [hexp, hfun, hprod]
    exact hεv s y

open Classical in
/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem Config.at_compatible {b : ℕ} {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) : (Γ.at act' x).Compatible ε :=
  hΓ.restrict (Finset.filter_subset _ _)

/-- **`ex:app-simultaneous-address`, two symbols** (tex 10554–10768): if every nonzero linear
form has a terminal active whenever it is one (anchors), every active pair has a balanced set for
the extra column, and both terminal polynomials are nonzero at every nonzero address, then
finitely many primary auxiliary vertices make both symbols one at every nonzero address. -/
theorem address_general {ε : L →+ ZMod 2} {A₁ A₂ : Config L → ZMod 2}
    (hA₁ : CoefficientRules ε A₁) (hA₂ : CoefficientRules ε A₂) (b : ℕ) (hb : 0 < b)
    (Γ : Config L) (hΓ : Γ.Compatible ε) (act' : ℕ → Option (Fin b → ZMod 2))
    (hanc : ∀ w : Fin b → ZMod 2, w ≠ 0 →
      ∃ u, u ∈ Γ.V ∧ ∀ x, (∑ k, w k * x k) = 1 → u ∈ (Γ.at act' x).V)
    (hbal : ∀ y : Fin b → ZMod 2, y ≠ 0 → ∀ e ∈ pairs (Γ.at act' y).V, ∃ R, R ⊆ Γ.V ∧
      (∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card) ∧
      ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (hP₁ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A₁ (Γ.at act' x))
    (hP₂ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A₂ (Γ.at act' x)) :
    AddressConclusion ε ![A₁, A₂] Γ act' := by
  classical
  have hAs : ∀ s, CoefficientRules ε (![A₁, A₂] s) := by
    intro s; fin_cases s
    · exact hA₁
    · exact hA₂
  have hE : ∀ (s : Fin 2) (y : {x : Fin b → ZMod 2 // x ≠ 0}) (U : Finset (Sym2 ℕ)),
      ![A₁, A₂] s ((Γ.at act' y.1).flipBy U) =
        ![A₁, A₂] s ((Γ.at act' y.1).flipBy (U ∩ pairs (Γ.at act' y.1).V)) :=
    fun s y U => (hAs s).flipBy_inter (Config.at_compatible hΓ act' y.1) U
  have hP : ∀ (s : Fin 2) (y : {x : Fin b → ZMod 2 // x ≠ 0}),
      ∃ U, ![A₁, A₂] s ((Γ.at act' y.1).flipBy U) = 1 := by
    intro s y; fin_cases s
    · obtain ⟨U, -, hU⟩ := hP₁ y.1 y.2; exact ⟨U, hU⟩
    · obtain ⟨U, -, hU⟩ := hP₂ y.1 y.2; exact ⟨U, hU⟩
  obtain ⟨Ns, Nv, hdisj, hmem, hsel⟩ :=
    degree_count (Y := {x : Fin b → ZMod 2 // x ≠ 0})
      (fun (s : Fin 2) (y : {x : Fin b → ZMod 2 // x ≠ 0}) (U : Finset (Sym2 ℕ)) =>
        ![A₁, A₂] s ((Γ.at act' y.1).flipBy U))
      (fun y : {x : Fin b → ZMod 2 // x ≠ 0} => pairs (Γ.at act' y.1).V) hE hP
  exact assemble hAs b hb Γ hΓ act' hanc hbal Ns Nv hdisj hmem hsel

/-- **`ex:app-simultaneous-address`, one symbol** (tex 10778–10784): a separate singular program
for each variable of a coefficient-one top monomial at each nonzero address. -/
theorem address_general_one {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) (b : ℕ) (hb : 0 < b) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (act' : ℕ → Option (Fin b → ZMod 2))
    (hanc : ∀ w : Fin b → ZMod 2, w ≠ 0 →
      ∃ u, u ∈ Γ.V ∧ ∀ x, (∑ k, w k * x k) = 1 → u ∈ (Γ.at act' x).V)
    (hbal : ∀ y : Fin b → ZMod 2, y ≠ 0 → ∀ e ∈ pairs (Γ.at act' y).V, ∃ R, R ⊆ Γ.V ∧
      (∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card) ∧
      ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (hP : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A (Γ.at act' x)) :
    AddressConclusion ε ![A, A] Γ act' := by
  classical
  have hAs : ∀ s, CoefficientRules ε (![A, A] s) := by
    intro s; fin_cases s <;> exact hA
  have hE : ∀ (y : {x : Fin b → ZMod 2 // x ≠ 0}) (U : Finset (Sym2 ℕ)),
      A ((Γ.at act' y.1).flipBy U) = A ((Γ.at act' y.1).flipBy (U ∩ pairs (Γ.at act' y.1).V)) :=
    fun y U => hA.flipBy_inter (Config.at_compatible hΓ act' y.1) U
  have hP' : ∀ y : {x : Fin b → ZMod 2 // x ≠ 0}, ∃ U, A ((Γ.at act' y.1).flipBy U) = 1 := by
    intro y
    obtain ⟨U, -, hU⟩ := hP y.1 y.2
    exact ⟨U, hU⟩
  obtain ⟨Ns, hmem, hsel⟩ :=
    degree_count_one (Y := {x : Fin b → ZMod 2 // x ≠ 0})
      (fun (y : {x : Fin b → ZMod 2 // x ≠ 0}) (U : Finset (Sym2 ℕ)) =>
        A ((Γ.at act' y.1).flipBy U))
      (fun y : {x : Fin b → ZMod 2 // x ≠ 0} => pairs (Γ.at act' y.1).V) hE hP'
  refine assemble hAs b hb Γ hΓ act' hanc hbal Ns ∅ (Finset.disjoint_empty_right _)
    (fun p hp => hmem p (by simpa using hp)) ?_
  intro Os Ov hOs _
  refine ⟨fun _ => 0, fun s y => ?_⟩
  rw [Finset.prod_empty, mul_one]
  have := hsel Os hOs y
  fin_cases s <;> exact this

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem pair_iff {a c a' c' : ℕ} (hac : a ≠ c) (hac' : a' ≠ c') :
    ((a' = a ∨ a' = c) ∧ (c' = a ∨ c' = c)) ↔ s(a', c') = s(a, c) := by
  rw [Sym2.eq_iff]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩ <;> subst h1 <;> subst h2
    · exact absurd rfl hac'
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hac'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem ite_eq_one_zmod2 (t : ZMod 2) : (if t = 1 then (1 : ZMod 2) else 0) = t := by
  rcases zmod2_cases t with rfl | rfl <;> decide

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem even_card_of_cast {n : ℕ} (h : (n : ZMod 2) = 0) : Even n :=
  (ZMod.natCast_eq_zero_iff_even).mp h

/-- **Lemma `ex:sec7-two-symbol-address`** (tex 2240–2258; proof 2259–2288 and App G
`ex:app-simultaneous-address`). Kind: PROVED from the coefficient rules. Terminals with nonzero
linear activations, a terminal of every nonzero linear form, and at every `x ≠ 0` each symbol's
terminal polynomial separately nonzero: finitely many new primary vertices with nonzero linear
activations, only their incidences chosen, make both symbols one at every `x ≠ 0`; all original
data and the zero address are preserved. (The nonempty-configuration and filter hypotheses of the
text are implied: a terminal of every activation is active at every `x ≠ 0`, and a symbol
vanishing off its filter has a nonzero terminal polynomial only on its filter.) -/
theorem two_symbol_address {ε : L →+ ZMod 2} {A₁ A₂ : Config L → ZMod 2}
    (hA₁ : CoefficientRules ε A₁) (hA₂ : CoefficientRules ε A₂) (b : ℕ) (hb : 1 ≤ b)
    (Γ : Config L) (hΓ : Γ.Compatible ε) (act' : ℕ → Option (Fin b → ZMod 2))
    (hact : ∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w)
    (hall : ∀ w : Fin b → ZMod 2, w ≠ 0 → ∃ v ∈ Γ.V, act' v = some w)
    (hP₁ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A₁ (Γ.at act' x))
    (hP₂ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A₂ (Γ.at act' x)) :
    AddressConclusion ε ![A₁, A₂] Γ act' := by
  classical
  have hpres : ∀ v ∈ Γ.V, ∀ w, act' v = some w → ∀ x,
      (v ∈ (Γ.at act' x).V ↔ (∑ k, w k * x k) = 1) := by
    intro v hv w hw x
    simp [Config.at, present, hv, hw]
  refine address_general hA₁ hA₂ b hb Γ hΓ act' ?_ ?_ hP₁ hP₂
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hall w hw
    exact ⟨v, hv, fun x hx => (hpres v hv w hvw x).mpr hx⟩
  · intro y _ e he
    obtain ⟨a, ha, c, hc, hac, rfl⟩ := mem_pairs he
    have haV : a ∈ Γ.V := Finset.filter_subset _ _ ha
    have hcV : c ∈ Γ.V := Finset.filter_subset _ _ hc
    obtain ⟨α, hα0, hα⟩ := hact a haV
    obtain ⟨β, hβ0, hβ⟩ := hact c hcV
    have haY : (∑ k, α k * y k) = 1 := (hpres a haV α hα y).mp ha
    have hcY : (∑ k, β k * y k) = 1 := (hpres c hcV β hβ y).mp hc
    have hind : ∀ u ∈ Γ.V, ∀ w, act' u = some w → ∀ x,
        (if u ∈ (Γ.at act' x).V then (1 : ZMod 2) else 0) = ∑ k, w k * x k := by
      intro u hu w hw x
      rw [← ite_eq_one_zmod2 (∑ k, w k * x k)]
      exact if_congr (hpres u hu w hw x) rfl rfl
    by_cases hαβ : α = β
    · subst hαβ
      refine ⟨{a, c}, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact haV
        · rw [Finset.mem_singleton.mp hu]; exact hcV
      · intro x
        apply even_card_of_cast
        rw [Finset.natCast_card_filter, Finset.sum_pair hac, hind a haV α hα x,
          hind c hcV α hβ x, zmod2_add_self]
      · intro a' ha' c' hc' hac'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact pair_iff hac hac'
    · have hsum0 : α + β ≠ 0 := by
        intro h
        apply hαβ
        funext k
        have hk := congrFun h k
        simp only [Pi.add_apply, Pi.zero_apply] at hk
        rcases zmod2_cases (α k) with h1 | h1 <;> rcases zmod2_cases (β k) with h2 | h2 <;>
          rw [h1, h2] at hk ⊢ <;> first | rfl | (exfalso; revert hk; decide)
      obtain ⟨d, hdV, hd⟩ := hall (α + β) hsum0
      have hda : d ≠ a := by
        rintro rfl
        rw [hα] at hd
        have := Option.some.inj hd
        apply hβ0
        have h2 : α + β = α + 0 := by rw [add_zero]; exact this.symm
        exact add_left_cancel h2
      have hdc : d ≠ c := by
        rintro rfl
        rw [hβ] at hd
        have := Option.some.inj hd
        apply hα0
        have h2 : α + β = 0 + β := by rw [zero_add]; exact this.symm
        exact add_right_cancel h2
      have hdY : d ∉ (Γ.at act' y).V := by
        intro h
        have := (hpres d hdV (α + β) hd y).mp h
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, haY, hcY] at this
        exact absurd this (by decide)
      refine ⟨{a, c, d}, ?_, ?_, ?_⟩
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact haV
        · exact hcV
        · exact hdV
      · intro x
        apply even_card_of_cast
        have hcd : c ∉ ({d} : Finset ℕ) := by simpa using hdc.symm
        have hacd : a ∉ ({c, d} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hac, hda.symm⟩
        rw [Finset.natCast_card_filter, Finset.sum_insert hacd, Finset.sum_insert hcd,
          Finset.sum_singleton, hind a haV α hα x, hind c hcV β hβ x, hind d hdV (α + β) hd x]
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        rw [← add_assoc, zmod2_add_self]
      · intro a' ha' c' hc' hac'
        have ha'd : a' ≠ d := fun h => hdY (h ▸ ha')
        have hc'd : c' ≠ d := fun h => hdY (h ▸ hc')
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [← pair_iff hac hac']
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1.elim Or.inl (fun h => Or.inr (h.resolve_right ha'd)),
            h2.elim Or.inl (fun h => Or.inr (h.resolve_right hc'd))⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1.elim Or.inl (fun h => Or.inr (Or.inl h)),
            h2.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

/-- Auxiliary result for the App G `ex:app-simultaneous-address`, tex 10554–10790. Kind: PROVED. -/
theorem Config.at_none {b : ℕ} (Γ : Config L) (x : Fin b → ZMod 2) :
    Γ.at (fun _ => (none : Option (Fin b → ZMod 2))) x = Γ := by
  classical
  cases Γ with
  | mk V t z =>
    simp only [Config.at, Config.mk.injEq, and_true]
    exact Finset.filter_true_of_mem (fun v _ => trivial)

/-- **Lemma `ex:sec7-one-symbol-address`** (tex 2222–2238; proof 2259–2288 and App G
`ex:app-simultaneous-address`, stationary one-symbol case 10769–10784). Kind: PROVED from the
coefficient rules. A nonempty stationary terminal list with nonzero terminal polynomial: for
every `b ≥ 1`, finitely many new primary vertices with nonzero linear activations, only their
new incidences chosen, make the symbol one at every `x ≠ 0`; the original vertices and all their
mutual data are unchanged and no new vertex is present at zero (`AddressConclusion`,
`AddressConclusion.not_present_zero`). -/
theorem one_symbol_address {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) (Γ : Config L) (hΓ : Γ.Compatible ε) (hne : Γ.V.Nonempty)
    (hP : TerminalNonzero A Γ) (b : ℕ) (hb : 1 ≤ b) :
    AddressConclusion ε ![A, A] Γ (fun _ => (none : Option (Fin b → ZMod 2))) := by
  classical
  have hat : ∀ x : Fin b → ZMod 2, Γ.at (fun _ => (none : Option (Fin b → ZMod 2))) x = Γ :=
    fun x => Config.at_none Γ x
  refine address_general_one hA b hb Γ hΓ _ ?_ ?_ (fun x _ => by rw [hat]; exact hP)
  · intro w _
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu, fun x _ => by rw [hat]; exact hu⟩
  · intro y _ e he
    rw [hat] at he
    obtain ⟨a, ha, c, hc, hac, rfl⟩ := mem_pairs he
    refine ⟨{a, c}, ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ha
      · rw [Finset.mem_singleton.mp hu]; exact hc
    · intro x
      rw [hat]
      have : ({a, c} : Finset ℕ).filter (· ∈ Γ.V) = {a, c} :=
        Finset.filter_true_of_mem (fun u hu => by
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ha
          · rw [Finset.mem_singleton.mp hu]; exact hc)
      rw [this, Finset.card_pair hac]
      exact even_two
    · intro a' _ c' _ hac'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact pair_iff hac hac'

/-- In the stationary case the cube is based at the original list: at the zero address only the
original vertices are present, with their original data. -/
theorem one_symbol_address_base {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) {b : ℕ} (Γ Γ' : Config L)
    (act'' : ℕ → Option (Fin b → ZMod 2)) (hΓ' : Γ'.Compatible ε) (hext : Γ.Extends Γ')
    (hact : ∀ v ∈ Γ.V, act'' v = none)
    (hnew : ∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0 ∧ ∃ w, w ≠ 0 ∧ act'' v = some w) :
    A (Γ'.at act'' 0) = A Γ := by
  classical
  have hV : (Γ'.at act'' 0).V = Γ.V := by
    ext v
    simp only [Config.at, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hp⟩
      by_contra hvΓ
      obtain ⟨-, w, -, hw⟩ := hnew v hv hvΓ
      simp [present, hw] at hp
    · intro hv
      exact ⟨hext.1 hv, by simp [present, hact v hv]⟩
  refine hA.congr (Config.at_compatible hΓ' act'' 0) hV ?_ ?_
  · intro v hv
    rw [hV] at hv
    exact hext.2.1 v hv
  · intro v hv w hw _
    rw [hV] at hv hw
    exact hext.2.2 v hv w hw

end ZInQ.Manuscript.RC.Symbols
