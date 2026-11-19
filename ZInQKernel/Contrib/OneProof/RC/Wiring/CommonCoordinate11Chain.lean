import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Step

/-!
# One coordinate per support along a chain: the cone basis, up to a sign

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4185–4193):
"In the original integral determinant bases, the support triangle therefore gives (4.7) … retain
the finite mapping-cone bases. Their comparison is a sign".

The relaxed complex of one step is the primitive complex of the next. In the relaxed step its
coordinate is computed in the cone model `relModel` (a `FullPreComplex`: the model of `C_P` plus
the new block); in the next step the primitive model must be a `BlockComplex`. This file re-indexes
the cone model as a block complex and shows that the coordinate is unchanged up to a sign, so
that along a chain of relaxations the coordinate of each support is the same number, up to sign,
in both roles.

* `basedCx_eq`, `fourReindex`, `aug_reindexF`, `kmCoord_reindexF`: relabelling the bases of a
  four-term complex (with the transported orientation) does not change the Knudsen–Mumford
  coordinate (the RC53 group's `torsion_reindex`).
* `kmCoord_orient`: changing the orientation multiplies the coordinate by the sign of a
  permutation.
* `FullPreComplex.toBlock`: the pre-cancellation complex as a block complex (`m₁' = m₁ + |N|`:
  the new summands join `E₁` and `B₂`); `kmCoord_toBlock`: its coordinate is `±` the coordinate
  of the pre-cancellation complex.
* `SupportTriangle.nextModelRetract`: the retract of the relaxed complex onto the re-indexed cone
  model; `SupportTriangle.next`: the next step, whose primitive complex, model and classes are
  this step's relaxed complex, re-indexed cone model and classes; **`next_primCoord`**: its
  primitive coordinate is `±` the relaxed coordinate of this step; `h47_next`: (4.7) along two
  steps, with the sign as part of the unit.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion

/-! ### Relabelling a four-term complex -/

section Reindex

variable {R : Type} [CommRing R]

/-- Two based complexes with the same degrees and differentials are equal (tex 4185–4193).
Kind: PROVED. -/
theorem basedCx_eq {κe κo : Type} [Fintype κe] [Fintype κo] {C C' : BasedCx R κe κo}
    (h1 : C.degE = C'.degE) (h2 : C.degO = C'.degO) (h3 : C.dOE = C'.dOE)
    (h4 : C.dEO = C'.dEO) : C = C' := by
  cases C
  cases C'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

variable {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']

/-- **A four-term complex with relabelled bases** (tex 4185–4193). Kind: definition. -/
def fourReindex (C : FourCx R ι0 ι1 ι2 ι3) (e0 : ι0 ≃ ι0') (e1 : ι1 ≃ ι1') (e2 : ι2 ≃ ι2')
    (e3 : ι3 ≃ ι3') : FourCx R ι0' ι1' ι2' ι3' where
  d0 := C.d0.submatrix e1.symm e0.symm
  d1 := C.d1.submatrix e2.symm e1.symm
  d2 := C.d2.submatrix e3.symm e2.symm
  d10 := by rw [submatrix_mul_equiv, C.d10, submatrix_zero]; rfl
  d21 := by rw [submatrix_mul_equiv, C.d21, submatrix_zero]; rfl

omit [Fintype ι0] [Fintype ι3] [Fintype ι0'] [Fintype ι3'] in
/-- A relabelled cycle is a cycle. (tex 4185–4193) Kind: PROVED. -/
theorem reindexF_cycle (C : FourCx R ι0 ι1 ι2 ι3) (e0 : ι0 ≃ ι0') (e1 : ι1 ≃ ι1')
    (e2 : ι2 ≃ ι2') (e3 : ι3 ≃ ι3') {z : ι1 → R} (hz : C.d1 *ᵥ z = 0) :
    (fourReindex C e0 e1 e2 e3).d1 *ᵥ (z ∘ e1.symm) = 0 := by
  funext i
  change ∑ j, C.d1 (e2.symm i) (e1.symm j) * z (e1.symm j) = 0
  rw [Equiv.sum_comp e1.symm (fun j => C.d1 (e2.symm i) j * z j)]
  exact congrFun hz (e2.symm i)

omit [Fintype ι0] [Fintype ι3] [Fintype ι0'] [Fintype ι3'] in
/-- A relabelled closed functional is closed. (tex 4185–4193) Kind: PROVED. -/
theorem reindexF_closed (C : FourCx R ι0 ι1 ι2 ι3) (e0 : ι0 ≃ ι0') (e1 : ι1 ≃ ι1')
    (e2 : ι2 ≃ ι2') (e3 : ι3 ≃ ι3') {lam : ι2 → R} (hlam : lam ᵥ* C.d1 = 0) :
    (lam ∘ e2.symm) ᵥ* (fourReindex C e0 e1 e2 e3).d1 = 0 := by
  funext j
  change ∑ i, lam (e2.symm i) * C.d1 (e2.symm i) (e1.symm j) = 0
  rw [Equiv.sum_comp e2.symm (fun i => lam i * C.d1 i (e1.symm j))]
  exact congrFun hlam (e1.symm j)

variable [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] [DecidableEq ι0']
  [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- **The augmented complex of the relabelled complex is the relabelled augmented complex**
(tex 4185–4193). Kind: PROVED. -/
theorem aug_reindexF (C : FourCx R ι0 ι1 ι2 ι3) (e0 : ι0 ≃ ι0') (e1 : ι1 ≃ ι1') (e2 : ι2 ≃ ι2')
    (e3 : ι3 ≃ ι3') {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) :
    ((fourReindex C e0 e1 e2 e3).aug (z ∘ e1.symm) (lam ∘ e2.symm) (reindexF_cycle C e0 e1 e2 e3 hz)
        (reindexF_closed C e0 e1 e2 e3 hlam)).toBased =
      (C.aug z lam hz hlam).toBased.reindex
        (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2)
        (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))) := by
  apply basedCx_eq
  · funext x
    rcases x with x | x <;> rfl
  · funext x
    rcases x with x | x <;> rfl
  · ext (i | i) (j | j)
    · rcases j with j | j <;> rfl
    · rfl
    · rfl
    · rcases i with i | i <;> rfl
  · ext (i | i) (j | j) <;> rfl

/-- **Relabelling the bases does not change the coordinate**, with the transported orientation
(tex 4185–4193; the RC53 group's `torsion_reindex`). Kind: PROVED. -/
theorem kmCoord_reindexF [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3) (e0 : ι0 ≃ ι0')
    (e1 : ι1 ≃ ι1') (e2 : ι2 ≃ ι2') (e3 : ι3 ≃ ι3') {z : ι1 → R} {lam : ι2 → R}
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord (fourReindex C e0 e1 e2 e3) (z ∘ e1.symm) (lam ∘ e2.symm)
        (reindexF_cycle C e0 e1 e2 e3 hz) (reindexF_closed C e0 e1 e2 e3 hlam)
        ((Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2).symm.trans
          (σ.trans (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))))) =
      kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [aug_reindexF]
  congr 1
  by_cases hc : Nonempty (Contraction (C.aug z lam hz hlam).toBased)
  · exact torsion_reindex _ hc.some σ _ _
  · have hc' : ¬ Nonempty (Contraction ((C.aug z lam hz hlam).toBased.reindex
        (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2)
        (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))))) := by
      rintro ⟨h⟩
      apply hc
      have h2 := h.reindex (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2).symm
        (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))).symm
      refine ⟨?_⟩
      have heq : ((C.aug z lam hz hlam).toBased.reindex
          (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2)
          (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit)))).reindex
          (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2).symm
          (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))).symm =
          (C.aug z lam hz hlam).toBased := by
        apply basedCx_eq
        · funext x
          change (C.aug z lam hz hlam).toBased.degE _ = _
          rw [Equiv.symm_symm, Equiv.symm_apply_apply]
        · funext x
          change (C.aug z lam hz hlam).toBased.degO _ = _
          rw [Equiv.symm_symm, Equiv.symm_apply_apply]
        · ext i j
          change (C.aug z lam hz hlam).toBased.dOE _ _ = _
          rw [Equiv.symm_symm, Equiv.symm_symm, Equiv.symm_apply_apply,
            Equiv.symm_apply_apply]
        · ext i j
          change (C.aug z lam hz hlam).toBased.dEO _ _ = _
          rw [Equiv.symm_symm, Equiv.symm_symm, Equiv.symm_apply_apply,
            Equiv.symm_apply_apply]
      exact heq ▸ h2
    unfold torsion
    rw [dite_eq_right hc, dite_eq_right hc']

/-- **Changing the orientation multiplies the coordinate by a sign** (tex 4185–4193: "their
comparison is a sign"). Kind: PROVED. -/
theorem kmCoord_orient [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3) {z : ι1 → R} {lam : ι2 → R}
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (σ₁ σ₂ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ₂ =
      ((Equiv.Perm.sign (σ₂.trans σ₁.symm) : ℤ) : R) * kmCoord C z lam hz hlam σ₁ := by
  unfold kmCoord torsion
  by_cases hc : Nonempty (Contraction (C.aug z lam hz hlam).toBased)
  · rw [dite_eq_left hc, dite_eq_left hc]
    unfold tau
    have e : ((C.aug z lam hz hlam).toBased.dOE + hc.some.hOE).submatrix σ₂ id =
        (((C.aug z lam hz hlam).toBased.dOE + hc.some.hOE).submatrix σ₁ id).submatrix
          (σ₂.trans σ₁.symm) id := by
      ext i j
      simp
    rw [e, det_permute]
    ring
  · rw [dite_eq_right hc, dite_eq_right hc]
    ring

end Reindex

/-! ### The pre-cancellation complex as a block complex -/

section ToBlock

variable {K : Type} [Field K] (C : FullPreComplex K)

/-- The new summands join the old ones: `Fin m₁ ⊕ N ≃ Fin (m₁ + |N|)` (tex 4185–4193).
Kind: definition. -/
def joinN : Fin C.m1 ⊕ C.N ≃ Fin (C.m1 + Fintype.card C.N) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin C.N)).trans finSumFinEquiv

/-- Degree one: `(B₁ ⊕ H₁ ⊕ E₁) ⊕ N ≃ B₁ ⊕ H₁ ⊕ (E₁ ⊕ N)` (tex 4185–4193). Kind: definition. -/
def toBlockE1 :
    C.D1 ⊕ C.N ≃ Fin C.m0 ⊕ Unit ⊕ Fin (C.m1 + Fintype.card C.N) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (joinN C))))

/-- Degree two: `(B₂ ⊕ H₂ ⊕ E₂) ⊕ N ≃ (B₂ ⊕ N) ⊕ H₂ ⊕ E₂` (tex 4185–4193). Kind: definition. -/
def toBlockE2 :
    C.D2 ⊕ C.N ≃ Fin (C.m1 + Fintype.card C.N) ⊕ Unit ⊕ Fin C.m2 :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
    ((Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr (joinN C) (Equiv.refl _))))

/-- **The pre-cancellation complex as a block complex** (tex 4185–4193): the same matrices,
re-indexed, with `m₁' = m₁ + |N|`. Kind: definition. -/
def FullPreComplex.toBlock : BlockComplex K where
  m0 := C.m0
  m1 := C.m1 + Fintype.card C.N
  m2 := C.m2
  d0 := C.toFour.d0.submatrix (toBlockE1 C).symm id
  d1 := C.toFour.d1.submatrix (toBlockE2 C).symm (toBlockE1 C).symm
  d2 := C.toFour.d2.submatrix id (toBlockE2 C).symm
  d1_d0 := by rw [submatrix_mul_equiv, C.toFour.d10, submatrix_zero]; rfl
  d2_d1 := by rw [submatrix_mul_equiv, C.toFour.d21, submatrix_zero]; rfl

/-- The block complex is the relabelled four-term complex (tex 4185–4193).
Kind: PROVED (definitional). -/
theorem toBlock_toFour :
    (FullPreComplex.toBlock C).toFour =
      fourReindex C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C) (Equiv.refl _) :=
  rfl

/-- **The coordinate of the block re-indexing is `±` the coordinate of the pre-cancellation
complex** (tex 4185–4193: "their comparison is a sign"). Kind: PROVED. -/
theorem kmCoord_toBlock {z : C.D1 ⊕ C.N → K} {lam : C.D2 ⊕ C.N → K}
    (hz : C.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.toFour.d1 = 0) :
    ∃ ε : ℤˣ, kmCoord (FullPreComplex.toBlock C).toFour (z ∘ (toBlockE1 C).symm)
        (lam ∘ (toBlockE2 C).symm)
        (reindexF_cycle C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C) (Equiv.refl _) hz)
        (reindexF_closed C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C) (Equiv.refl _) hlam)
        (σBlock C.m0 (C.m1 + Fintype.card C.N) C.m2) =
      (ε : K) * kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) := by
  set σ' := (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl (Fin C.m0)) (Equiv.refl Unit))
    (toBlockE2 C)).symm.trans ((σFull C.m0 C.m1 C.m2 C.N).trans (Equiv.sumCongr (toBlockE1 C)
      (Equiv.sumCongr (Equiv.refl (Fin C.m2)) (Equiv.refl Unit)))) with hσ'
  have h1 := kmCoord_orient (FullPreComplex.toBlock C).toFour
    (reindexF_cycle C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C) (Equiv.refl _) hz)
    (reindexF_closed C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C) (Equiv.refl _) hlam)
    σ' (σBlock C.m0 (C.m1 + Fintype.card C.N) C.m2)
  have h2 := kmCoord_reindexF C.toFour (Equiv.refl _) (toBlockE1 C) (toBlockE2 C)
    (Equiv.refl _) hz hlam (σFull C.m0 C.m1 C.m2 C.N)
  refine ⟨Equiv.Perm.sign ((σBlock C.m0 (C.m1 + Fintype.card C.N) C.m2).trans σ'.symm), ?_⟩
  refine h1.trans ?_
  exact congrArg (fun t => ((Equiv.Perm.sign ((σBlock C.m0 (C.m1 + Fintype.card C.N)
    C.m2).trans σ'.symm) : ℤ) : K) * t) h2

/-! ### The degreewise identification and the retract onto the block re-indexing -/

omit [Field K] in
/-- Re-indexed matrix–vector products (tex 4185–4193). Kind: PROVED. -/
theorem mulVec_submatrix_apply_equiv [CommRing K] {α β α' β' : Type} [Fintype β] [Fintype β']
    (M : Matrix α β K) (e : α ≃ α') (f : β ≃ β') (y : β' → K) (x : α) :
    (M.submatrix e.symm f.symm *ᵥ y) (e x) = (M *ᵥ (y ∘ f)) x := by
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply]

/-- **The block re-indexing is degreewise isomorphic to the pre-cancellation complex**
(tex 4185–4193): `v ↦ v ∘ e` in degrees one and two, the identity elsewhere.
Kind: definition. -/
def toBlockEquiv : (n : ℤ) → (FullPreComplex.toBlock C).toGCx.X n ≃ₗ[K] C.toGCx.X n
  | 0 => LinearEquiv.refl K (Fin C.m0 → K)
  | 1 => LinearEquiv.funCongrLeft K K (toBlockE1 C)
  | 2 => LinearEquiv.funCongrLeft K K (toBlockE2 C)
  | 3 => LinearEquiv.refl K (Fin C.m2 → K)
  | Int.ofNat (_ + 4) => LinearEquiv.refl K (Empty → K)
  | Int.negSucc _ => LinearEquiv.refl K (Empty → K)

/-- The identification commutes with the differentials (tex 4185–4193). Kind: PROVED. -/
theorem toBlockEquiv_comm (a b : ℤ) (h : a + 1 = b)
    (y : (FullPreComplex.toBlock C).toGCx.X a) :
    C.toGCx.d a b h (toBlockEquiv C a y) =
      toBlockEquiv C b ((FullPreComplex.toBlock C).toGCx.d a b h y) := by
  subst h
  match a with
  | 0 =>
    funext x
    exact (mulVec_submatrix_apply_equiv C.toFour.d0 (toBlockE1 C) (Equiv.refl _)
      (y : Fin C.m0 → K) x).symm
  | 1 =>
    funext x
    exact (mulVec_submatrix_apply_equiv C.toFour.d1 (toBlockE2 C) (toBlockE1 C)
      (y : Fin C.m0 ⊕ Unit ⊕ Fin (C.m1 + Fintype.card C.N) → K) x).symm
  | 2 =>
    funext x
    exact (mulVec_submatrix_apply_equiv C.toFour.d2 (Equiv.refl _) (toBlockE2 C)
      (y : Fin (C.m1 + Fintype.card C.N) ⊕ Unit ⊕ Fin C.m2 → K) x).symm
  | 3 =>
    change (0 : Empty → K) = (0 : Empty → K)
    rfl
  | Int.ofNat (n + 4) =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → K) _ _
    simp only [map_zero]
  | Int.negSucc n =>
    obtain rfl : y = 0 := Subsingleton.elim (α := Empty → K) _ _
    simp only [map_zero]

end ToBlock

/-! ### The next step of a chain of relaxations -/

/-- A basis vector composed with an equivalence is a basis vector (tex 4185–4193).
Kind: PROVED. -/
theorem single_comp_equiv' {F : Type} [Field F] {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (k : κ) : (Pi.single k (1 : F) : κ → F) ∘ e = Pi.single (e.symm k) 1 := by
  funext x
  by_cases h : e x = k
  · have h' : x = e.symm k := by rw [← h, Equiv.symm_apply_apply]
    subst h'
    simp
  · have h' : x ≠ e.symm k := fun hx => h (by rw [hx, Equiv.apply_symm_apply])
    simp [Function.comp_apply, h, h']

/-- **The coordinate vector of a functional composed with a re-indexing** (tex 4185–4193):
`funVec (φ ∘ (· ∘ e)) = funVec φ ∘ e⁻¹`. Kind: PROVED. -/
theorem funVec_comp_funCongrLeft {F : Type} [Field F] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (φ : (ι → F) →ₗ[F] F) (e : ι ≃ κ) :
    funVec (φ ∘ₗ (LinearEquiv.funCongrLeft F F e).toLinearMap) = funVec φ ∘ e.symm := by
  funext k
  change φ ((Pi.single k (1 : F) : κ → F) ∘ e) = φ (Pi.single (e.symm k) 1)
  rw [single_comp_equiv']

section Chain

variable {F : Type} [Field F] (S : SupportTriangle F)

/-- **The retract of the relaxed complex onto the block re-indexing of its cone model**
(tex 4185–4193): the next step's primitive model. Kind: definition. -/
def SupportTriangle.nextModelRetract :
    GRetract S.CR (FullPreComplex.toBlock S.model).toGCx :=
  retractOfModelEquiv S.retract (toBlockEquiv S.model) (toBlockEquiv_comm S.model)

/-- **The next step of a chain of relaxations** (tex 4185–4193): the relaxed complex of this step
is the primitive complex of the next, with the block re-indexing of this step's cone model as
primitive model and this step's relaxed cycle and functional as primitive cycle and functional;
the next relaxed complex, its inclusion, quotient model and classes are inputs.
Kind: definition. -/
def SupportTriangle.next {CR' : GCx F} (E' : SplitInclusion S.CR CR') {Q'' : GCx F}
    (RQ' : GRetract E'.quotientCx Q'') (hQ'' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q''.X n))
    {N' : Type} [Fintype N'] [DecidableEq N'] (b1' : Module.Basis N' F (Q''.X 1))
    (b2' : Module.Basis N' F (Q''.X 2)) (zR' : CR'.X 1) (hzR' : CR'.d 1 2 rfl zR' = 0)
    (lamR' : CR'.X 2 →ₗ[F] F) (hlamR' : lamR' ∘ₗ CR'.d 1 2 rfl = 0) : SupportTriangle F where
  CP := S.CR
  CR := CR'
  E := E'
  D := FullPreComplex.toBlock S.model
  R := S.nextModelRetract
  Q' := Q''
  RQ := RQ'
  hQ' := hQ''
  N := N'
  b1 := b1'
  b2 := b2'
  zR := zR'
  hzR := hzR'
  zP := S.zR
  hzP := S.hzR
  lamR := lamR'
  hlamR := hlamR'
  lamP := S.lamR
  hlamP := S.hlamR

variable {CR' : GCx F} (E' : SplitInclusion S.CR CR') {Q'' : GCx F}
  (RQ' : GRetract E'.quotientCx Q'') (hQ'' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q''.X n))
  {N' : Type} [Fintype N'] [DecidableEq N'] (b1' : Module.Basis N' F (Q''.X 1))
  (b2' : Module.Basis N' F (Q''.X 2)) (zR' : CR'.X 1) (hzR' : CR'.d 1 2 rfl zR' = 0)
  (lamR' : CR'.X 2 →ₗ[F] F) (hlamR' : lamR' ∘ₗ CR'.d 1 2 rfl = 0)

/-- **The next primitive cycle is this relaxed cycle, re-indexed** (tex 4185–4193).
Kind: PROVED (definitional). -/
theorem next_zPv :
    (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').zPv = S.zRv ∘ (toBlockE1 S.model).symm :=
  rfl

/-- **The next primitive functional is this relaxed functional, re-indexed** (tex 4185–4193).
Kind: PROVED. -/
theorem next_lamPv :
    (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').lamPv =
      S.lamRv ∘ (toBlockE2 S.model).symm :=
  funVec_comp_funCongrLeft (ι := S.model.D2 ⊕ S.model.N)
    (κ := Fin (S.model.m1 + Fintype.card S.model.N) ⊕ Unit ⊕ Fin S.model.m2)
    (S.lamR ∘ₗ S.retract.i.f 2 2 rfl) (toBlockE2 S.model)

/-- **One coordinate per support along a chain, up to a sign** (tex 4185–4193: "in the original
integral determinant bases … their comparison is a sign"): the primitive coordinate of the next
step is `±` the relaxed coordinate of this step. Kind: PROVED. -/
theorem next_primCoord :
    ∃ ε : ℤˣ, (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').primCoord =
      (ε : F) * S.relCoord := by
  obtain ⟨ε, hε⟩ := kmCoord_toBlock S.model S.zRv_cycle S.lamRv_closed
  refine ⟨ε, Eq.trans ?_ hε⟩
  exact kmCoord_congr _ _ _ _ _ (next_zPv S E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR')
    (next_lamPv S E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR') _

/-- **(4.7) along two steps of a chain** (tex 4166–4193): if this step and the next are
torsion-level steps at primes with Frobenius data `(Fr₁, q₁, a₁, z₁)` and `(Fr₂, q₂, a₂, z₂)`,
then `l₁ l₂ u_rel' = ε e₁² q₁⁻⁴ e₂² q₂⁻⁴ u_prim` with a sign `ε`, where `u_rel'` is the relaxed
coordinate of the next step and `u_prim` the primitive coordinate of this one: the sign is the
unit of the comparison of the cone bases. Kind: PROVED. -/
theorem h47_next {Fr₁ Fr₂ : Matrix (Fin 2) (Fin 2) F} {q₁ qi₁ a₁ z₁ zi₁ q₂ qi₂ a₂ z₂ zi₂ : F}
    (hq₁ : q₁ * qi₁ = 1) (ha₁ : Fr₁.trace = a₁) (hd₁ : Fr₁.det = q₁) (hq₂ : q₂ * qi₂ = 1)
    (ha₂ : Fr₂.trace = a₂) (hd₂ : Fr₂.det = q₂)
    (h₁ : KmStep Fr₁ q₁ a₁ z₁ zi₁ S.relCoord S.primCoord)
    (h₂ : KmStep Fr₂ q₂ a₂ z₂ zi₂ (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').relCoord
      (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').primCoord) :
    ∃ ε : ℤˣ, ZInQ.Manuscript.RC.Central.quotientFactor Fr₁ qi₁ z₁ zi₁ *
        ZInQ.Manuscript.RC.Central.quotientFactor Fr₂ qi₂ z₂ zi₂ *
        (S.next E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR').relCoord =
      (ε : F) * (ZInQ.Manuscript.RC.Central.pointFactor a₁ z₁ zi₁ ^ 2 * qi₁ ^ 4) *
        (ZInQ.Manuscript.RC.Central.pointFactor a₂ z₂ zi₂ ^ 2 * qi₂ ^ 4) * S.primCoord := by
  obtain ⟨ε, hε⟩ := next_primCoord S E' RQ' hQ'' b1' b2' zR' hzR' lamR' hlamR'
  refine ⟨ε, ?_⟩
  have e₁ := h₁.h47 hq₁ ha₁ hd₁
  have e₂ := h₂.h47 hq₂ ha₂ hd₂
  rw [hε] at e₂
  linear_combination (ZInQ.Manuscript.RC.Central.quotientFactor Fr₁ qi₁ z₁ zi₁) * e₂ +
    ((ZInQ.Manuscript.RC.Central.pointFactor a₂ z₂ zi₂) ^ 2 * qi₂ ^ 4 * (ε : F)) * e₁

end Chain


end ZInQ.Manuscript.RC.Wiring
