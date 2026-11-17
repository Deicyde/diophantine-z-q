import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressPrograms
import ZInQKernel.Contrib.OneProof.RC.Symbols.DegreeCount

/-!
# Lane RC2: the singular and varying programs (App G, tex 10685–10720)
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem dot_vecMulVec_mulVec {n : Type*} [Fintype n] (u v w : n → ZMod 2) :
    u ⬝ᵥ (vecMulVec v v *ᵥ w) = (u ⬝ᵥ v) * (v ⬝ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem mem_pairs {V : Finset ℕ} {f : Sym2 ℕ} (hf : f ∈ pairs V) :
    ∃ a ∈ V, ∃ c ∈ V, a ≠ c ∧ f = s(a, c) := by
  unfold pairs at hf
  obtain ⟨⟨a, c⟩, h, rfl⟩ := Finset.mem_image.mp hf
  simp only [Finset.mem_filter, Finset.mem_product] at h
  exact ⟨a, h.1.1, c, h.1.2, h.2, rfl⟩

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem actGroups_lam_eq_univ_iff {b : ℕ} {y : Fin b → ZMod 2} {j0 : Fin b} (hy : y j0 = 1)
    (x : Fin b → ZMod 2) : actGroups (lam y j0) x = Finset.univ ↔ x = y := by
  constructor
  · intro h
    apply lam_all_one hy x
    intro i
    have : i ∈ actGroups (lam y j0) x := h ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  · rintro rfl
    ext i
    simp [actGroups, lam_target hy i]

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem ne_zero_of_coord {b : ℕ} {y : Fin b → ZMod 2} {j0 : Fin b} (hy : y j0 = 1) : y ≠ 0 := by
  rintro rfl
  simp at hy

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem det_Qsub_eq_univ {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b))
    (hJ : J = Finset.univ) : (Qsub Q J).det = Q.det := by
  subst hJ; exact det_Qsub_univ Q

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem restr_adj_eq_univ {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b))
    (hJ : J = Finset.univ) (u v : Phys b → ZMod 2) :
    restr J u ⬝ᵥ ((Qsub Q J).adjugate *ᵥ restr J v) = u ⬝ᵥ (Q.adjugate *ᵥ v) := by
  subst hJ; exact restr_univ_adj Q u v

/-- `network_coeffs` with the active group set named `J`. -/
theorem network_coeffs' {b : ℕ} {κ : Type*} {Γ : Config L} {N : Finset κ}
    {name : κ → Phys b → ℕ} {spec : κ → NetSpec b} {ε : L →+ ZMod 2} (hΓ : Γ.Compatible ε)
    (hinj : NamesInj N name) (hfr : NamesFresh Γ N name)
    (hsym : ∀ p ∈ N, ∀ q q', (spec p).Q q q' = (spec p).Q q' q)
    (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) {p : κ} (hp : p ∈ N)
    (hrow : ∀ q : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x},
      ∑ q' : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x}, (spec p).Q q.1 q'.1 =
        ∑ u ∈ (Γ.at act' x).V, (spec p).col u q.1)
    (J : Finset (Fin b)) (hJ : actGroups (spec p).lamv x = J) :
    MvPolynomial.constantCoeff (netOp ((glue Γ N name spec).at (glueAct act' N name spec) x)
        (Γ.at act' x).V (auxAt name p (spec p).lamv x)) = (Qsub (spec p).Q J).det ∧
    ∀ a ∈ (Γ.at act' x).V, ∀ c ∈ (Γ.at act' x).V, a ≠ c →
      (netOp ((glue Γ N name spec).at (glueAct act' N name spec) x) (Γ.at act' x).V
        (auxAt name p (spec p).lamv x)).coeff (Finsupp.single s(a, c) 1) =
      restr J ((spec p).col a) ⬝ᵥ ((Qsub (spec p).Q J).adjugate *ᵥ restr J ((spec p).col c)) := by
  subst hJ
  exact network_coeffs hΓ hinj hfr hsym act' x hp hrow

section Programs

variable {b : ℕ} (hb : 0 < b) {κ : Type*} {Γ : Config L} {N : Finset κ}
  {name : κ → Phys b → ℕ}

/-- Auxiliary result for the App G singular and varying programs, tex 10685–10720. Kind: PROVED. -/
theorem rowSum_at {spec : κ → NetSpec b} (act' : ℕ → Option (Fin b → ZMod 2))
    {p : κ} {Q : Matrix (Phys b) (Phys b) (ZMod 2)} {y : Fin b → ZMod 2} {j0 : Fin b}
    {anc : Fin b → ℕ} {R : Finset ℕ}
    (hspec : spec p = ⟨Q, lam y j0, colOf (cvec b hb) anc R⟩) (hQ : ∀ g, Q *ᵥ grp g = grp g)
    (hanc : ∀ g x, (∑ k, lam y j0 g k * x k) = 1 → anc g ∈ (Γ.at act' x).V)
    (hReven : ∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card) (x : Fin b → ZMod 2) :
    ∀ q : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x},
      ∑ q' : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x}, (spec p).Q q.1 q'.1 =
        ∑ u ∈ (Γ.at act' x).V, (spec p).col u q.1 := by
  rw [hspec]
  intro q
  exact rowSum_colOf Q hQ (cvec b hb) anc R _ _
    (fun g hg => hanc g x (Finset.mem_filter.mp hg).2) (hReven x) q

/-- **The singular program** (tex 10685–10702): at its target the network operator has zero
constant term and linear part exactly `∂_e`; at every other address constant term one. -/
theorem singular_program {ε : L →+ ZMod 2} (hΓ : Γ.Compatible ε) {spec : κ → NetSpec b}
    (hinj : NamesInj N name) (hfr : NamesFresh Γ N name)
    (hsym : ∀ p ∈ N, ∀ q q', (spec p).Q q q' = (spec p).Q q' q)
    (act' : ℕ → Option (Fin b → ZMod 2)) {p : κ} (hp : p ∈ N)
    {y : Fin b → ZMod 2} {j0 : Fin b} (hy : y j0 = 1) (anc : Fin b → ℕ) (R : Finset ℕ)
    (e : Sym2 ℕ) (hspec : spec p = ⟨Qsing b hb, lam y j0, colOf (cvec b hb) anc R⟩)
    (hanc : ∀ g x, (∑ k, lam y j0 g k * x k) = 1 → anc g ∈ (Γ.at act' x).V)
    (hReven : ∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card)
    (hRe : ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (he : e ∈ pairs (Γ.at act' y).V) :
    IsSingularProgram (⟨y, ne_zero_of_coord hy⟩ : {x : Fin b → ZMod 2 // x ≠ 0}) e
      (fun x : {x : Fin b → ZMod 2 // x ≠ 0} =>
        netOp ((glue Γ N name spec).at (glueAct act' N name spec) x.1) (Γ.at act' x.1).V
          (auxAt name p (lam y j0) x.1)) := by
  classical
  have hQg : ∀ g, Qsing b hb *ᵥ grp g = grp g := fun g => Qmat_mulVec_grp _ _ g
  have hlamv : (spec p).lamv = lam y j0 := by rw [hspec]
  have hQs : (spec p).Q = Qsing b hb := by rw [hspec]
  have hcols : (spec p).col = colOf (cvec b hb) anc R := by rw [hspec]
  have hco := fun x => network_coeffs' hΓ hinj hfr hsym act' x hp
    (rowSum_at hb act' hspec hQg hanc hReven x) (actGroups (lam y j0) x) (by rw [hlamv])
  refine ⟨?_, ?_, ?_⟩
  · -- zero constant term at the target
    obtain ⟨h0, -⟩ := hco y
    simp only [hlamv, hQs] at h0
    rw [h0, det_Qsub_eq_univ _ _ ((actGroups_lam_eq_univ_iff hy y).mpr rfl), Qsing_det]
  · -- linear part `∂_e` at the target
    intro f
    obtain ⟨-, h1⟩ := hco y
    by_cases hf : f ∈ pairs (Γ.at act' y).V
    · obtain ⟨a, ha, c, hc, hac, rfl⟩ := mem_pairs hf
      have h := h1 a ha c hc hac
      simp only [hlamv, hQs, hcols] at h
      rw [h, restr_adj_eq_univ _ _ ((actGroups_lam_eq_univ_iff hy y).mpr rfl), Qsing_adjugate,
        dot_vecMulVec_mulVec, colOf_dot_rvec, dotProduct_comm, colOf_dot_rvec]
      by_cases hR : a ∈ R ∧ c ∈ R
      · rw [if_pos hR.1, if_pos hR.2, if_pos ((hRe a ha c hc hac).mp hR), mul_one]
      · rw [if_neg (fun h' => hR ((hRe a ha c hc hac).mpr h'))]
        by_cases haR : a ∈ R
        · rw [if_pos haR, if_neg (fun hcR => hR ⟨haR, hcR⟩), mul_zero]
        · rw [if_neg haR, zero_mul]
    · rw [if_neg (fun h' : f = e => hf (h' ▸ he))]
      exact netOp_coeff_single_of_not_mem _ _ _ hf
  · -- constant term one away from the target
    intro x hx
    obtain ⟨h0, -⟩ := hco x.1
    simp only [hlamv, hQs] at h0
    rw [h0]
    apply Qsing_det_proper
    intro hJ
    exact hx (Subtype.ext ((actGroups_lam_eq_univ_iff hy x.1).mp hJ))

/-- **The varying program pair** (tex 10704–10720): constant term one everywhere; the sum over
`ε` of the linear parts is `∂_e` at the target and zero elsewhere. -/
theorem varying_program {ε : L →+ ZMod 2} (hΓ : Γ.Compatible ε)
    (specF : ZMod 2 → κ → NetSpec b) (hinj : NamesInj N name) (hfr : NamesFresh Γ N name)
    (hsym : ∀ η, ∀ p ∈ N, ∀ q q', (specF η p).Q q q' = (specF η p).Q q' q)
    (act' : ℕ → Option (Fin b → ZMod 2)) {p : κ} (hp : p ∈ N)
    {y : Fin b → ZMod 2} {j0 : Fin b} (hy : y j0 = 1) (anc : Fin b → ℕ) (R : Finset ℕ)
    (e : Sym2 ℕ) (hspec : ∀ η, specF η p = ⟨Qvar b hb η, lam y j0, colOf (cvec b hb) anc R⟩)
    (hanc : ∀ g x, (∑ k, lam y j0 g k * x k) = 1 → anc g ∈ (Γ.at act' x).V)
    (hReven : ∀ x, Even (R.filter (· ∈ (Γ.at act' x).V)).card)
    (hRe : ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (he : e ∈ pairs (Γ.at act' y).V) :
    IsVaryingProgram (⟨y, ne_zero_of_coord hy⟩ : {x : Fin b → ZMod 2 // x ≠ 0}) e
      (fun η (x : {x : Fin b → ZMod 2 // x ≠ 0}) =>
        netOp ((glue Γ N name (specF η)).at (glueAct act' N name (specF η)) x.1)
          (Γ.at act' x.1).V (auxAt name p (lam y j0) x.1)) := by
  classical
  have hQg : ∀ η g, Qvar b hb η *ᵥ grp g = grp g := fun η g => Qmat_mulVec_grp _ _ g
  have hlamv : ∀ η, (specF η p).lamv = lam y j0 := fun η => by rw [hspec η]
  have hQs : ∀ η, (specF η p).Q = Qvar b hb η := fun η => by rw [hspec η]
  have hcols : ∀ η, (specF η p).col = colOf (cvec b hb) anc R := fun η => by rw [hspec η]
  have hco := fun η x => network_coeffs' hΓ hinj hfr (hsym η) act' x hp
    (rowSum_at hb act' (hspec η) (hQg η) hanc hReven x) (actGroups (lam y j0) x)
    (by rw [hlamv η])
  refine ⟨?_, ?_⟩
  · intro η x
    obtain ⟨h0, -⟩ := hco η x.1
    simp only [hlamv, hQs] at h0
    rw [h0, Qvar_det]
  · intro x f
    by_cases hf : f ∈ pairs (Γ.at act' x.1).V
    · obtain ⟨a, ha, c, hc, hac, rfl⟩ := mem_pairs hf
      have h0 := (hco 0 x.1).2 a ha c hc hac
      have h1 := (hco 1 x.1).2 a ha c hc hac
      simp only [hlamv, hQs, hcols] at h0 h1
      rw [h0, h1, add_comm]
      unfold colOf
      rw [Qvar_change]
      by_cases hxy : x.1 = y
      · have hJ := (actGroups_lam_eq_univ_iff hy x.1).mpr hxy
        rw [if_pos hJ]
        have hxY : x = ⟨y, ne_zero_of_coord hy⟩ := Subtype.ext hxy
        have ha' : a ∈ (Γ.at act' y).V := hxy ▸ ha
        have hc' : c ∈ (Γ.at act' y).V := hxy ▸ hc
        have key := hRe a ha' c hc' hac
        by_cases hR : a ∈ R ∧ c ∈ R
        · have hE : x = ⟨y, ne_zero_of_coord hy⟩ ∧ s(a, c) = e := ⟨hxY, key.mp hR⟩
          rw [if_pos hR.1, if_pos hR.2, mul_one, if_pos hE]
        · have hE : ¬ (x = ⟨y, ne_zero_of_coord hy⟩ ∧ s(a, c) = e) :=
            fun h' => hR (key.mpr h'.2)
          rw [if_neg hE]
          by_cases haR : a ∈ R
          · have hcR : c ∉ R := fun hcR => hR ⟨haR, hcR⟩
            rw [if_pos haR, if_neg hcR, mul_zero]
          · rw [if_neg haR, zero_mul]
      · have hJ : actGroups (lam y j0) x.1 ≠ Finset.univ :=
          fun h' => hxy ((actGroups_lam_eq_univ_iff hy x.1).mp h')
        rw [if_neg hJ, if_neg (fun h' => hxy (congrArg Subtype.val h'.1))]
    · rw [netOp_coeff_single_of_not_mem _ _ _ hf, netOp_coeff_single_of_not_mem _ _ _ hf,
        add_zero, if_neg]
      rintro ⟨hx, rfl⟩
      exact hf (by rw [hx]; exact he)

end Programs

end ZInQ.Manuscript.RC.Symbols
