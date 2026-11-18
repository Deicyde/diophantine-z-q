import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerDisks
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.NonVacuity
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# Torsion, part 7: the Kummer-model identification as one input against `SelData`

The remaining model input of the Kummer coordinate (tex L4051–4064): **the ordinary Kummer
complex is `kummerModel` in the retained bases, with class `a · z₀` and functional `b · λ₀`.**
It is stated here as ONE structure, `KummerModelIdentification D`, over the Selmer data
`D : SelData S` (whose Selmer complex `selCx D` is the Kummer complex), so that it can be
discharged by instantiating `D` with the genuine cochain-level Selmer complexes:

* `BasedCx.toGCx`: a based complex as a `GCx` (degree `k` = vectors supported on the basis
  vectors of degree `k`, differential the total matrix `d`).
* `KummerModelIdentification D`: the core `[S^n --D_c--> S^n]` with acyclic augmentation and RC15
  coordinate `z₀ ⊗ λ₀ = u₀ adj D_c`; the class `z = a z₀` and functional `λ = b λ₀`; torsion disks
  `δ₁, δ₂, δ₃`; a quasi-isomorphism `φ` from `kummerModel` to `selCx D` (the retained bases are the
  model's standard bases) carrying the model class to the Selmer class `zSel` and pulling the Selmer
  functional `λSel` back to `λ`.
* `KummerModelIdentification.coord`: the Kummer coordinate (the Knudsen–Mumford coordinate of the
  model in the retained bases); `coord_eq`: `u_K = a b u₀ · δ₁ δ₂⁻¹ δ₃`;
  `hK_of_identification`: Bookkeeping's input `hK` in its exact type, from the identification and
  the valuations of `a, b, u₀, δ_i`; `hvprim_of_identification`: RC0's `hvprim`.
* `modelSel`, `identification_example` (**LESSON 2 consistency instance**): for the Selmer data
  whose global complex is the model itself (zero local conditions), the identity-like map is a
  quasi-isomorphism (an isomorphism of complexes) and every field holds (`D_c = (0)`,
  `z₀ = λ₀ = u₀ = a = b = 1`, unit disks).

**Classification.** GLUE input (the identification), with PROVED consequences.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {S : Type} [CommRing S]

/-! ### Based complexes as `GCx` -/

section ToGCx

variable {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]

/-- The total degree function. -/
def BasedCx.deg (C : BasedCx S κe κo) : κe ⊕ κo → ℤ := Sum.elim C.degE C.degO

/-- The total differential. -/
def BasedCx.dTot (C : BasedCx S κe κo) : Matrix (κe ⊕ κo) (κe ⊕ κo) S :=
  fromBlocks 0 C.dEO C.dOE 0

omit [DecidableEq κe] [DecidableEq κo] in
theorem BasedCx.hasDeg_dTot (C : BasedCx S κe κo) : HasDeg C.dTot C.deg C.deg 1 := by
  rintro (i | i) (j | j) h
  · exact absurd rfl h
  · exact C.deg_dEO i j h
  · exact C.deg_dOE i j h
  · exact absurd rfl h

theorem BasedCx.dTot_mul_self (C : BasedCx S κe κo) : C.dTot * C.dTot = 0 := by
  rw [BasedCx.dTot, fromBlocks_multiply]; simp [C.dd_E, C.dd_O]

/-- Vectors supported in degree `k`. -/
def BasedCx.degSub (C : BasedCx S κe κo) (k : ℤ) : Submodule S (κe ⊕ κo → S) where
  carrier := {v | ∀ x, C.deg x ≠ k → v x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' _ _ := rfl
  smul_mem' c v hv x hx := by simp [hv x hx]

omit [DecidableEq κe] [DecidableEq κo] in
theorem BasedCx.dTot_mem (C : BasedCx S κe κo) {i j : ℤ} (h : i + 1 = j) {v : κe ⊕ κo → S}
    (hv : v ∈ C.degSub i) : C.dTot *ᵥ v ∈ C.degSub j := by
  intro x hx
  refine Finset.sum_eq_zero fun y _ => ?_
  change C.dTot x y * v y = 0
  by_cases hd : C.dTot x y = 0
  · rw [hd, zero_mul]
  · have := C.hasDeg_dTot x y hd
    rw [hv y (by omega), mul_zero]

/-- **A based complex as a `GCx`**: degree `k` is the span of the basis vectors of degree `k`. -/
def BasedCx.toGCx (C : BasedCx S κe κo) : GCx S where
  X k := ModuleCat.of S (C.degSub k)
  d i j h := ((Matrix.mulVecLin C.dTot).domRestrict (C.degSub i)).codRestrict (C.degSub j)
    (fun v => C.dTot_mem h v.2)
  d_d i j k hij hjk x := by
    apply Subtype.ext
    change C.dTot *ᵥ (C.dTot *ᵥ (x : κe ⊕ κo → S)) = 0
    rw [mulVec_mulVec, C.dTot_mul_self, zero_mulVec]

end ToGCx

/-! ### Degree-one and degree-two vectors of a four-term complex -/

section FourVec

variable {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- A vector of `C¹`. -/
def vec1 (y : ι1 → S) : (ι0 ⊕ ι2) ⊕ (ι1 ⊕ ι3) → S := Sum.elim 0 (Sum.elim y 0)

/-- A vector of `C²`. -/
def vec2 (y : ι2 → S) : (ι0 ⊕ ι2) ⊕ (ι1 ⊕ ι3) → S := Sum.elim (Sum.elim 0 y) 0

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
theorem vec1_mem (C : FourCx S ι0 ι1 ι2 ι3) (y : ι1 → S) :
    (vec1 (ι0 := ι0) (ι2 := ι2) (ι3 := ι3) y) ∈ C.toBased.degSub 1 := by
  rintro ((x | x) | (x | x)) hx
  · rfl
  · rfl
  · exact absurd rfl hx
  · rfl

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
theorem vec2_mem (C : FourCx S ι0 ι1 ι2 ι3) (y : ι2 → S) :
    (vec2 (ι0 := ι0) (ι1 := ι1) (ι3 := ι3) y) ∈ C.toBased.degSub 2 := by
  rintro ((x | x) | (x | x)) hx
  · rfl
  · exact absurd rfl hx
  · rfl
  · rfl

end FourVec

/-! ### The identification -/

/-- **The Kummer-model identification** (GLUE input, tex L4051–4064): the Selmer complex of `D`
(the ordinary Kummer complex) is quasi-isomorphic, by `φ`, to `kummerModel D_c δ₁ δ₂ δ₃` in its
standard bases (the retained bases), with the Selmer class `zSel` the image of the model class
`a z₀` and the Selmer functional `λSel` restricting to the model functional `b λ₀`. -/
structure KummerModelIdentification [IsDomain S] (D : SelData S) where
  n : ℕ
  Dc : Matrix (Fin n) (Fin n) S
  δ₁ : Sˣ
  δ₂ : Sˣ
  δ₃ : Sˣ
  z₀ : Fin n → S
  w₀ : Fin n → S
  u₀ : S
  a : S
  b : S
  z : Fin n → S
  w : Fin n → S
  hzdef : z = a • z₀
  hwdef : w = b • w₀
  hz : (twoTerm Dc).d1 *ᵥ z = 0
  hw : w ᵥ* (twoTerm Dc).d1 = 0
  /-- The augmented core is acyclic (`[z]` generates `H¹`, `λ` is an isomorphism on `H²`). -/
  hcore : Contraction ((twoTerm Dc).aug z w hz hw).toBased
  /-- RC15's coordinate of the primitive class and functional. -/
  hu₀ : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord Dc z₀ w₀ u₀
  /-- The comparison map from the model to the Selmer complex. -/
  φ : GHom (kummerModel Dc (δ₁ : S) δ₂ δ₃).toBased.toGCx (selCx D)
  qis : QuasiIso (GHom.toCC φ)
  /-- The Selmer (Kummer) class. -/
  zSel : (selCx D).X 1
  /-- The Selmer (Kummer) functional. -/
  lamSel : (selCx D).X 2 →ₗ[S] S
  hclass : φ.f 1 1 rfl ⟨vec1 (kz z), vec1_mem _ _⟩ = zSel
  hfun : ∀ y, lamSel (φ.f 2 2 rfl ⟨vec2 y, vec2_mem _ _⟩) = kw w ⬝ᵥ y

namespace KummerModelIdentification

variable [IsDomain S] {D : SelData S}

/-- **The Kummer coordinate** in the retained bases: the Knudsen–Mumford coordinate of the model. -/
noncomputable def coord (I : KummerModelIdentification D) : S :=
  kmCoord (kummerModel I.Dc (I.δ₁ : S) I.δ₂ I.δ₃) (kz I.z) (kw I.w)
    (kummerModel_hz I.Dc _ _ _ I.hz) (kummerModel_hw I.Dc _ _ _ I.hw) (σK I.n)

theorem hu (I : KummerModelIdentification D) :
    ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord I.Dc I.z I.w (I.a * I.b * I.u₀) := by
  rw [I.hzdef, I.hwdef]; exact isClassFunctionalCoord_smul I.Dc I.a I.b I.hu₀

/-- **`u_K = a b u₀ · δ₁ δ₂⁻¹ δ₃`.** -/
theorem coord_eq (I : KummerModelIdentification D) :
    I.coord = I.a * I.b * I.u₀ * I.δ₁ * ((I.δ₂⁻¹ : Sˣ) : S) * I.δ₃ :=
  kmCoord_kummerModel I.Dc I.z I.w _ I.hz I.hw I.hcore I.hu I.δ₁ I.δ₂ I.δ₃

end KummerModelIdentification

section Valuation

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.Calibration

/-- **Bookkeeping's input `hK` from the identification** (tex L4051–4064): with the class and
functional valuations `v₂ a(0) = v₂ b(0) = j + v₂L + v₂m`, `v₂ u₀(0) = 0`, and disk lengths
`g_A, s_A, g_A`. -/
theorem hK_of_identification {D : SelData (PowerSeries ℚ_[2])}
    (I : KummerModelIdentification D) (j vL vm gA sA : ℤ) (hu₀v : v2 (central I.u₀) = 0)
    (ha : v2 (central I.a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central I.b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central I.δ₁) = gA) (h₂ : v2 (central I.δ₂) = sA) (h₃ : v2 (central I.δ₃) = gA) :
    v2 (central I.coord) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ) := by
  have hc : v2 (central (I.a * I.b * I.u₀)) =
      (((j + vL + vm) + (j + vL + vm) : ℤ) : WithTop ℤ) := by
    simp only [central_mul, v2_mul, ha, hb, hu₀v, add_zero]
    norm_cast
  exact v2_kmCoord_kummerModel I.Dc I.z I.w _ I.hz I.hw I.hcore I.hu I.δ₁ I.δ₂ I.δ₃ hc h₁ h₂ h₃

/-- **RC0's `hvprim` from the identification**, the support triangle and the quotient length. -/
theorem hvprim_of_identification {D : SelData (PowerSeries ℚ_[2])}
    (I : KummerModelIdentification D) (j vL vm gA sA vN ω : ℤ) (hu₀v : v2 (central I.u₀) = 0)
    (ha : v2 (central I.a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central I.b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central I.δ₁) = gA) (h₂ : v2 (central I.δ₂) = sA) (h₃ : v2 (central I.δ₃) = gA)
    {uprim δW : PowerSeries ℚ_[2]} (htri : δW * uprim = I.coord)
    (hδ : v2 (central δW) = ((2 * vN + 4 * ω : ℤ) : WithTop ℤ)) :
    v2 (central uprim) = ((primValuation j vL vm gA sA vN ω : ℤ) : WithTop ℤ) :=
  hvprim_of_support_triangle j vL vm gA sA vN ω
    (hK_of_identification I j vL vm gA sA hu₀v ha hb h₁ h₂ h₃) htri hδ

end Valuation

/-! ### LESSON 2: a consistency instance -/

section Example

/-- Selmer data whose global complex is a given complex and whose local conditions are zero. -/
def modelSel (G : GCx S) : SelData S :=
  ⟨G, zeroCx S, zeroCx S, zeroHom S _ _, zeroHom S _ _⟩

/-- The inclusion `G → selCx (modelSel G)`, `a ↦ (a, 0, 0)`. -/
def modelIncl (G : GCx S) : GHom G (selCx (modelSel G)) where
  f i j h := h ▸ (LinearMap.id.prod (0 : G.X i →ₗ[S] (PUnit.{1} × PUnit.{1})))
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- The projection `selCx (modelSel G) → G`. -/
def modelProj (G : GCx S) : GHom (selCx (modelSel G)) G where
  f i j h := h ▸ (LinearMap.fst S (G.X i) (PUnit.{1} × PUnit.{1}))
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

instance (G : GCx S) : IsIso (GHom.toCC (modelIncl G)) := by
  refine ⟨⟨GHom.toCC (modelProj G), ?_, ?_⟩⟩
  · rw [GHom.toCC_comp, ← toCC_idGHom]
    exact GHom.toCC_ext fun i x => rfl
  · rw [GHom.toCC_comp, ← toCC_idGHom]
    exact GHom.toCC_ext fun i x => Prod.ext rfl (Prod.ext rfl rfl)

theorem quasiIso_modelIncl (G : GCx S) : QuasiIso (GHom.toCC (modelIncl G)) := inferInstance

/-- The model of the example: `D_c = (0)`, unit disks. -/
abbrev exModel [IsDomain S] (δ₁ δ₂ δ₃ : Sˣ) :=
  (kummerModel (0 : Matrix (Fin 1) (Fin 1) S) (δ₁ : S) δ₂ δ₃).toBased.toGCx

/-- The weight vector of the example functional. -/
def exW : ((((Empty ⊕ Unit) ⊕ Empty) ⊕ Empty) ⊕ (((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit)) ⊕
      ((((Fin 1 ⊕ Unit) ⊕ Unit) ⊕ Empty) ⊕ (((Empty ⊕ Empty) ⊕ Empty) ⊕ Unit)) → S :=
  vec2 (kw (1 : Fin 1 → S))

/-- The example functional: the `λ`-weighted degree-two coordinates. -/
def exLam [IsDomain S] (δ₁ δ₂ δ₃ : Sˣ) :
    (selCx (modelSel (exModel δ₁ δ₂ δ₃))).X 2 →ₗ[S] S where
  toFun c := exW ⬝ᵥ ((show ((kummerModel (0 : Matrix (Fin 1) (Fin 1) S) (δ₁ : S) δ₂
    δ₃).toBased.degSub 2) from c.1) : _ → S)
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' r _ := dotProduct_smul r _ _

/-- **LESSON 2: the identification is consistent** — an instance for the Selmer data whose global
complex is the model (`D_c = (0)`, `z₀ = λ₀ = u₀ = a = b = 1`, arbitrary unit disks). -/
def identification_example [IsDomain S] (δ₁ δ₂ δ₃ : Sˣ) :
    KummerModelIdentification (modelSel (exModel δ₁ δ₂ δ₃)) where
  n := 1
  Dc := 0
  δ₁ := δ₁
  δ₂ := δ₂
  δ₃ := δ₃
  z₀ := 1
  w₀ := 1
  u₀ := 1
  a := 1
  b := 1
  z := 1
  w := 1
  hzdef := by simp
  hwdef := by simp
  hz := twoTerm_zero_hz
  hw := twoTerm_zero_hw
  hcore := twoTermContraction_example
  hu₀ := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]
  φ := modelIncl _
  qis := quasiIso_modelIncl _
  zSel := (modelIncl _).f 1 1 rfl ⟨vec1 (kz 1), vec1_mem _ _⟩
  lamSel := exLam δ₁ δ₂ δ₃
  hclass := rfl
  hfun y := by
    change exW ⬝ᵥ vec2 y = _
    simp [exW, vec2, kw, dotProduct, Fintype.sum_sum_type]

end Example

end ZInQ.Contrib.CloudB3RC53.Torsion
