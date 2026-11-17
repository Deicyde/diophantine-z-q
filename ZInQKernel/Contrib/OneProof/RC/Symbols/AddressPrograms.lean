import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressActive
import ZInQKernel.Contrib.OneProof.RC.Symbols.Network
import ZInQKernel.Contrib.OneProof.RC.Symbols.MatrixTree

/-!
# Lane RC2: the singular and varying programs (App G, tex 10625–10720)

The low-degree coefficients of the network operator of an active network are the rooted-forest
minors `det Q_J` and `c_aᵀ adj(Q_J) c_b` (tex 10641–10650); for the singular and varying
networks this gives the expansions of tex 10696–10701 and 10713–10720, i.e. the program
properties `IsSingularProgram`, `IsVaryingProgram` used by the degree count (G.1a).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Matrix

variable {L : Type*} [AddCommGroup L]

section Coeffs

variable {b : ℕ} {κ : Type*} {Γ : Config L} {N : Finset κ} {name : κ → Phys b → ℕ}
  {spec : κ → NetSpec b}

/-- Auxiliary result for the App G network operators, tex 10641–10650. Kind: PROVED. -/
theorem NamesInj.one {N : Finset κ} {name : κ → Phys b → ℕ} (hinj : NamesInj N name) {p : κ}
    (hp : p ∈ N) : ∀ q q', name p q = name p q' → q = q' :=
  fun q q' h => (hinj p hp p hp q q' h).2

/-- The constant and pair coefficients of the network operator of one active network are
`det Q_J` and `c_aᵀ adj(Q_J) c_b` (tex 10641–10650: rooted-forest minors). -/
theorem network_coeffs {ε : L →+ ZMod 2} (hΓ : Γ.Compatible ε) (hinj : NamesInj N name)
    (hfr : NamesFresh Γ N name) (hsym : ∀ p ∈ N, ∀ q q', (spec p).Q q q' = (spec p).Q q' q)
    (act' : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) {p : κ} (hp : p ∈ N)
    (hrow : ∀ q : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x},
      ∑ q' : {q : Phys b // q.1 ∈ actGroups (spec p).lamv x}, (spec p).Q q.1 q'.1 =
        ∑ u ∈ (Γ.at act' x).V, (spec p).col u q.1) :
    MvPolynomial.constantCoeff (netOp ((glue Γ N name spec).at (glueAct act' N name spec) x)
        (Γ.at act' x).V (auxAt name p (spec p).lamv x)) =
      (Qsub (spec p).Q (actGroups (spec p).lamv x)).det ∧
    ∀ a ∈ (Γ.at act' x).V, ∀ c ∈ (Γ.at act' x).V, a ≠ c →
      (netOp ((glue Γ N name spec).at (glueAct act' N name spec) x) (Γ.at act' x).V
        (auxAt name p (spec p).lamv x)).coeff (Finsupp.single s(a, c) 1) =
      restr (actGroups (spec p).lamv x) ((spec p).col a) ⬝ᵥ
        ((Qsub (spec p).Q (actGroups (spec p).lamv x)).adjugate *ᵥ
          restr (actGroups (spec p).lamv x) ((spec p).col c)) := by
  classical
  set Γx := (glue Γ N name spec).at (glueAct act' N name spec) x with hΓx
  set T := (Γ.at act' x).V with hT
  set X := auxAt name p (spec p).lamv x with hX
  set J := actGroups (spec p).lamv x with hJ
  have hTΓ : T ⊆ Γ.V := Finset.filter_subset _ _
  have hTX : Disjoint T X := auxAt_disjoint_terms hfr hp _ x T hTΓ
  set e := auxEquiv name p (spec p).lamv x (hinj.one hp) with he
  have hname : ∀ i : X, name p (e i).1 = i := name_auxEquiv name p _ x (hinj.one hp)
  have hQ : ∀ i j : X, i ≠ j → Γx.z i j = (spec p).Q (e i).1 (e j).1 := by
    intro i j _
    have h := glue_z_aa (spec := spec) hinj hfr hp hp (e i).1 (e j).1
    rw [hname i, hname j, if_pos rfl] at h
    exact h
  have hcol : ∀ i : X, ∀ u ∈ T, Γx.z i u = (spec p).col u (e i).1 := by
    intro i u hu
    have h := glue_z_at (spec := spec) hinj hfr hp (e i).1 (hTΓ hu)
    rw [hname i] at h
    exact h
  have hsymm : ∀ x' ∈ X, ∀ u ∈ T ∪ X, x' ≠ u → Γx.z x' u = Γx.z u x' := by
    intro x' hx' u hu _
    have hx'' : x' ∈ auxAt name p (spec p).lamv x := hx'
    unfold auxAt at hx''
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx''
    rcases Finset.mem_union.mp hu with huT | huX
    · show (glue Γ N name spec).z _ _ = (glue Γ N name spec).z _ _
      rw [glue_z_at hinj hfr hp q (hTΓ huT), glue_z_ta hinj hfr hp q (hTΓ huT)]
    · have huX' : u ∈ auxAt name p (spec p).lamv x := huX
      unfold auxAt at huX'
      obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp huX'
      show (glue Γ N name spec).z _ _ = (glue Γ N name spec).z _ _
      rw [glue_z_aa hinj hfr hp hp, glue_z_aa hinj hfr hp hp, if_pos rfl, if_pos rfl,
        hsym p hp]
  constructor
  · rw [netOp_constantCoeff, mt0 Γx T X hTX hsymm]
    exact det_lap_eq Γx T X J e (spec p).Q (spec p).col hTX hQ hcol hrow
  · intro a ha c hc hac
    rw [netOp_coeff_X Γx T X ha hc hac, mt1 Γx T X hTX hsymm ha hc hac]
    exact attach_adj_eq Γx T X J e (spec p).Q (spec p).col hTX hQ hcol hrow ha hc

end Coeffs

/-! ### Reindexing over all groups -/

section Univ

variable {b : ℕ}

/-- Auxiliary result for the App G network operators, tex 10641–10650. Kind: PROVED. -/
theorem det_Qsub_univ (Q : Matrix (Phys b) (Phys b) (ZMod 2)) :
    (Qsub Q Finset.univ).det = Q.det := by
  have h : Qsub Q Finset.univ =
      Q.submatrix (Equiv.subtypeUnivEquiv (fun q : Phys b => Finset.mem_univ q.1))
        (Equiv.subtypeUnivEquiv (fun q : Phys b => Finset.mem_univ q.1)) := rfl
  rw [h, Matrix.det_submatrix_equiv_self]

/-- Auxiliary result for the App G network operators, tex 10641–10650. Kind: PROVED. -/
theorem restr_univ_adj (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (u v : Phys b → ZMod 2) :
    restr Finset.univ u ⬝ᵥ ((Qsub Q Finset.univ).adjugate *ᵥ restr Finset.univ v) =
      u ⬝ᵥ (Q.adjugate *ᵥ v) := by
  set e := Equiv.subtypeUnivEquiv (fun q : Phys b => Finset.mem_univ q.1)
  have h : Qsub Q Finset.univ = Q.submatrix e e := rfl
  have hu : restr Finset.univ u = u ∘ e := rfl
  have hv : restr Finset.univ v = v ∘ e := rfl
  rw [h, Matrix.adjugate_submatrix_equiv_self, hu, hv, Matrix.submatrix_mulVec_equiv]
  have hcomp : (v ∘ ⇑e) ∘ ⇑e.symm = v := by funext q; simp
  rw [hcomp]
  simp only [dotProduct, Function.comp_apply]
  exact Equiv.sum_comp e (fun q => u q * (Q.adjugate *ᵥ v) q)

/-- The singular network has `det Q = 0` on all groups (its kernel is the line of `r`). -/
theorem Qsing_det (b : ℕ) (hb : 0 < b) : (Qsing b hb).det = 0 := by
  have hm := Matrix.mul_adjugate (Qsing b hb)
  rw [Qsing_adjugate] at hm
  have h1 := congrArg (fun M => M *ᵥ grp (⟨0, hb⟩ : Fin b)) hm
  rw [← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm, grp_rvec] at h1
  simp only [MulOpposite.op_zero, zero_smul, Matrix.mulVec_zero, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h1
  have h2 := congrFun h1 (⟨0, hb⟩, 0)
  simp [grp] at h2
  exact h2.symm

/-- Auxiliary result for the App G network operators, tex 10641–10650. Kind: PROVED. -/
theorem colOf_dot_rvec (b : ℕ) (hb : 0 < b) (anc : Fin b → ℕ) (R : Finset ℕ) (u : ℕ) :
    colOf (cvec b hb) anc R u ⬝ᵥ rvec b = if u ∈ R then 1 else 0 := by
  classical
  unfold colOf
  rw [add_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, grp_rvec, cvec_rvec, smul_eq_mul, mul_zero, mul_one,
    Finset.sum_const_zero, zero_add]

end Univ

end ZInQ.Manuscript.RC.Symbols
