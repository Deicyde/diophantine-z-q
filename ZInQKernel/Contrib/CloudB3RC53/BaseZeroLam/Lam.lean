import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Bridges
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerPairing

/-!
# The base-zero leaf: `lam`, `hlam` from Proposition `ex:arith-paired-functional`

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-paired-functional` (tex L3704–3880) and
Definition `ex:arith-coordinate` (tex L3877–3892), as used by Lemma `ex:arith-base-zero` (tex
4330–4376).

Lane RC25's base-zero leaf (`RC/BaseZeroAssembly/Assembly.lean`, `BaseZeroCore`) has the fields

* `lam : CU.X 2 →ₗ[Λ_(t)] Λ_(t)` ("the paired functional"),
* `hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0` ("it is closed"),
* `hu : ∀ w, w ᵥ* Dm = 0 → (∀ y, lam (e2.symm y) = w ⬝ᵥ y) → IsClassFunctionalCoord … uprim`.

This file builds `lam`, `hlam` from the paired-functional results of `PairedFunctional/` and
reduces `hu` to one coordinate statement:

* `baseLam pd2 ψ cz` is the paired functional `λ(w) = PD(w, ψ(c z))` (`pairedFunctional`), and
  `baseLam_closed`: it satisfies `hlam` for every chain map `ψ`, by the Leibniz identity of the
  pairing (`pairedFunctional_closed`).
* `exists_baseLam` (PROVED, `pairedFunctionalIntegral_proof` over `Λ_(t)`): under the hypotheses of
  `PairedFunctionalIntegral` (the cone of `j : C_{U⊥} → τ^*C_U` is a sum of tame local models with
  unit hypotheses), `ψ = j⁻¹` exists and `λ_z` is closed and integral over `Λ_(t)`.
* `exists_baseLam_selmer` (PROVED): the same when the pairing is the trace of a Selmer cup
  product, `pd = tr(· ∪ ·)` for `SelPairData` (`CU = C_U`, `C' = C_{U⊥}` the Selmer complexes).
  The Leibniz hypotheses are then discharged by `selmerDualityComponents_proof`. Lane RC26's
  `τ≥2` data (`genuinePairDataTrunc …`.`toSelPairData`, with the trace `trT`) are of this form.
* `rowOf lam e2`, `rowOf_closed`, `rowOf_unique`: in the coordinates `e2`, a closed `lam` is the
  row `w_λ = (λ(e2⁻¹ eᵢ))ᵢ` with `w_λ Dm = 0`, and it is the only row representing `lam`.
* **`BaseZeroCore.ofClosed` (PROVED)**: a `BaseZeroCore` from the other fields, any closed `lam`,
  and the coordinate statement for the single row `w_λ`. The field `hu` is derived.
* **`BaseZeroCore.ofPaired` (PROVED)**: the same with `lam := PD(·, ψ(c z))` for any chain map
  `ψ` (`ofPaired_lam`: the field is this functional, by definition).
* **`nonempty_baseZeroCore_of_paired` (PROVED)**: with `ψ = j⁻¹` produced from the
  paired-functional hypotheses (the cone of `j` is a sum of tame local models).
* Non-vacuity: `exLam_coord` — on the rank-one model (`m = 0`, `Dm = 0`, `z = 1`) with the
  multiplication pairing, `ψ = 𝟙` and `c z = 1`, the paired functional is closed, its row is
  `w_λ = 1`, and `u_prim = 1` is its coordinate (`IsClassFunctionalCoord` holds); the central rank
  condition `rank(Dm mod t) = m` holds too.

What remains of the leaf is unchanged: `boundary` ((4.5) at the base) and `hprimId`; and the
identification of `CU` with the genuine primitive Selmer complex at the base (no genuine
two-term model over `Λ_(t)` is constructed in the project).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.BaseZeroLam

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.BaseZeroAssembly

/-- The ring `A = Λ_(t)` of the base-zero model. -/
abbrev A : Type := Rings.LambdaT

variable {CU C' C : CochainComplex (ModuleCat.{0} A) ℤ}

/-- **The paired functional at the base** `λ(w) = PD(w, ψ(c z))` (tex L3745–3747, L3846–3847). -/
def baseLam (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A) (ψ : C ⟶ C') (cz : C.X 1) :
    CU.X 2 →ₗ[A] A :=
  pairedFunctional pd2 ψ cz

/-- **`hlam`: the paired functional is closed** (tex L3856–3860), for every chain map `ψ` and
cocycle `c z`. PROVED. -/
theorem baseLam_closed (pd1 : CU.X 1 →ₗ[A] C'.X 2 →ₗ[A] A) (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A)
    (ε : A) (hL : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') {cz : C.X 1} (hz : (C.d 1 2).hom cz = 0) :
    ∀ y : CU.X 1, baseLam pd2 ψ cz ((CU.d 1 2).hom y) = 0 :=
  pairedFunctional_closed pd1 pd2 ε hL ψ hz

/-- **The integral closed paired functional at the base** (Proposition
`ex:arith-paired-functional` over `Λ_(t)`; exponent `a = 0`, tex L3864–3869). PROVED. -/
theorem exists_baseLam (Z : CochainComplex (ModuleCat.{0} A) ℤ) (j : C' ⟶ C) (c : Z ⟶ C)
    (z : Z.X 1) (pd1 : CU.X 1 →ₗ[A] C'.X 2 →ₗ[A] A) (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A)
    (pd3 : CU.X 3 →ₗ[A] C'.X 0 →ₗ[A] A) (ε ε' : A)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module A (M v)]
    (Aq Cin Dq : ∀ v, Module.End A (M v)) (hDC : ∀ v, Dq v * Cin v = Cin v * Aq v) (n : ι → ℤ)
    (hunit : ∀ v, (IsUnit (Aq v) ∧ IsUnit (Dq v)) ∨ IsUnit (Cin v))
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (tameComplex (Aq v) (Cin v) (Dq v) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (hL2 : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) :
    ∃ e : HomotopyEquiv C' C, e.hom = j ∧
      ∀ y : CU.X 1, baseLam pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom y) = 0 :=
  exists_closed_pairedFunctional A CU C' C Z j c z pd1 pd2 pd3 ε ε' ι M Aq Cin Dq hDC n hunit
    hcone hz hL1 hL2

/-- **The paired functional of a Selmer cup product at the base** (tex L3826–3849): for Selmer
pairing data `Q` over `Λ_(t)` with a trace killing coboundaries, `CU = C_U`, `C' = C_{U⊥}` and
`pd = tr(· ∪ ·)`, the Leibniz hypotheses hold (`selmerDualityComponents_proof`), so the cone
hypothesis gives a closed integral `λ_z`. PROVED. -/
theorem exists_baseLam_selmer {D D' : SelData A} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[A] A) (htr : ∀ x, tr ((coneCx Q.resE).d 2 3 rfl x) = 0)
    {C Z : CochainComplex (ModuleCat.{0} A) ℤ} (j : (selCx D').toCC ⟶ C) (c : Z ⟶ C)
    (z : Z.X 1) (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)]
    [∀ v, Module A (M v)] (Aq Cin Dq : ∀ v, Module.End A (M v))
    (hDC : ∀ v, Dq v * Cin v = Cin v * Aq v) (n : ι → ℤ)
    (hunit : ∀ v, (IsUnit (Aq v) ∧ IsUnit (Dq v)) ∨ IsUnit (Cin v))
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (tameComplex (Aq v) (Cin v) (Dq v) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0) :
    ∃ e : HomotopyEquiv (selCx D').toCC C, e.hom = j ∧
      ∀ y : (selCx D).toCC.X 1,
        baseLam (traceComp (selPair Q) tr 2 1 rfl) e.inv ((c.f 1).hom z)
          (((selCx D).toCC.d 1 2).hom y) = 0 := by
  obtain ⟨hL1, hL2⟩ := selmerDualityComponents_proof A D D' Q tr htr
  exact exists_baseLam Z j c z _ _ _ 1 (-1) ι M Aq Cin Dq hDC n hunit hcone hz hL1 hL2

/-! ### The row of a closed functional and the field `hu` -/

variable {m : ℕ}

/-- The row `w_λ = (λ(e2⁻¹ eᵢ))ᵢ` of a functional in the coordinates `e2`. -/
def rowOf (lam : CU.X 2 →ₗ[A] A) (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) : Fin (m + 1) → A :=
  fun i => lam (e2.symm (Pi.single i 1))

/-- The row represents the functional: `λ(e2⁻¹ y) = w_λ · y`. PROVED. -/
theorem rowOf_spec (lam : CU.X 2 →ₗ[A] A) (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A))
    (y : Fin (m + 1) → A) : lam (e2.symm y) = rowOf lam e2 ⬝ᵥ y := by
  have hy : y = ∑ i, y i • Pi.single i (1 : A) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul, smul_eq_mul, rowOf, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The row is unique: any `w` with `λ(e2⁻¹ y) = w · y` is `w_λ`. PROVED. -/
theorem rowOf_unique (lam : CU.X 2 →ₗ[A] A) (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A))
    (w : Fin (m + 1) → A) (hw : ∀ y, lam (e2.symm y) = w ⬝ᵥ y) : w = rowOf lam e2 := by
  funext i
  rw [rowOf, hw, dotProduct_single, mul_one]

/-- The row of a closed functional is closed: `w_λ Dm = 0`. PROVED. -/
theorem rowOf_closed (lam : CU.X 2 →ₗ[A] A) (e1 : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0) : rowOf lam e2 ᵥ* Dm = 0 := by
  obtain ⟨w, hw, hrep⟩ := twoTermClosedRow_proof A CU m Dm e1 e2 hd lam hlam
  rw [← rowOf_unique lam e2 w hrep]
  exact hw

/-- **The base-zero core from a closed functional** (tex L3877–3892, 4330–4376): the fields of
`BaseZeroCore` other than `lam`, `hlam`, `hu`, a closed `lam`, and the coordinate statement for its
row `w_λ` give a `BaseZeroCore` (the field `hu` is derived from the uniqueness of the row).
PROVED. -/
def BaseZeroCore.ofClosed {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) (m : ℕ) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hcentral : (Dm.map Rings.rhoT).rank = m) (z : Fin (m + 1) → A) (hz : Dm *ᵥ z = 0)
    (CU : CochainComplex (ModuleCat.{0} A) ℤ) (e1 : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (lam : CU.X 2 →ₗ[A] A) (hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0)
    (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap A (FractionRing Uniform.Lambda)))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (z i))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (rowOf lam e2 i)) uprim)
    (boundary : Boundary45Base P (m + 1) (fun i => Rings.rhoT (z i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) : BaseZeroCore D Fam P where
  m := m
  Dm := Dm
  hcentral := hcentral
  z := z
  hz := hz
  CU := CU
  e1 := e1
  e2 := e2
  hd := hd
  lam := lam
  hlam := hlam
  uprim := uprim
  hu := fun w _ hrep => by
    rw [rowOf_unique lam e2 w hrep]
    exact hu
  boundary := boundary
  hprimId := hprimId

/-- **The base-zero core with `lam := PD(·, ψ(c z))`** (tex L3745–3747, L3846–3860): for any chain
map `ψ : C → C'` (in the proposition, a homotopy inverse of `j`), a cocycle `c z` and the Leibniz
identity of the pairing, the paired functional is the field `lam` (closed by `baseLam_closed`), and
`hu` is the coordinate statement for its row. PROVED. -/
def BaseZeroCore.ofPaired {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) (m : ℕ) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hcentral : (Dm.map Rings.rhoT).rank = m) (zm : Fin (m + 1) → A) (hzm : Dm *ᵥ zm = 0)
    (CU C' C : CochainComplex (ModuleCat.{0} A) ℤ) (e1 : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (pd1 : CU.X 1 →ₗ[A] C'.X 2 →ₗ[A] A) (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A) (ε : A)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') (cz : C.X 1) (hcz : (C.d 1 2).hom cz = 0)
    (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap A (FractionRing Uniform.Lambda)))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (zm i))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (rowOf (baseLam pd2 ψ cz) e2 i)) uprim)
    (boundary : Boundary45Base P (m + 1) (fun i => Rings.rhoT (zm i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) : BaseZeroCore D Fam P :=
  BaseZeroCore.ofClosed D Fam P m Dm hcentral zm hzm CU e1 e2 hd (baseLam pd2 ψ cz)
    (baseLam_closed pd1 pd2 ε hL1 ψ hcz) uprim hu boundary hprimId

theorem BaseZeroCore.ofPaired_lam {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type}
    [AddCommGroup G] (P : G) (m : ℕ) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hcentral : (Dm.map Rings.rhoT).rank = m) (zm : Fin (m + 1) → A) (hzm : Dm *ᵥ zm = 0)
    (CU C' C : CochainComplex (ModuleCat.{0} A) ℤ) (e1 : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (pd1 : CU.X 1 →ₗ[A] C'.X 2 →ₗ[A] A) (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A) (ε : A)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') (cz : C.X 1) (hcz : (C.d 1 2).hom cz = 0)
    (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap A (FractionRing Uniform.Lambda)))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (zm i))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (rowOf (baseLam pd2 ψ cz) e2 i)) uprim)
    (boundary : Boundary45Base P (m + 1) (fun i => Rings.rhoT (zm i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) :
    (BaseZeroCore.ofPaired D Fam P m Dm hcentral zm hzm CU C' C e1 e2 hd pd1 pd2 ε hL1 ψ cz hcz
      uprim hu boundary hprimId).lam = baseLam pd2 ψ cz :=
  rfl

/-- **The base-zero core with `lam := λ_z`** (Proposition `ex:arith-paired-functional` at the
base): under the cone hypothesis, `j` has a homotopy inverse `e.inv`, and the core with
`lam = λ_z = PD(·, e.inv (c z))` exists as soon as `u_prim` is the coordinate of the row of `λ_z`.
PROVED. -/
theorem nonempty_baseZeroCore_of_paired {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type}
    [AddCommGroup G] (P : G) (m : ℕ) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hcentral : (Dm.map Rings.rhoT).rank = m) (zm : Fin (m + 1) → A) (hzm : Dm *ᵥ zm = 0)
    (CU C' C Z : CochainComplex (ModuleCat.{0} A) ℤ) (e1 : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)) (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (j : C' ⟶ C) (c : Z ⟶ C) (z : Z.X 1) (pd1 : CU.X 1 →ₗ[A] C'.X 2 →ₗ[A] A)
    (pd2 : CU.X 2 →ₗ[A] C'.X 1 →ₗ[A] A) (pd3 : CU.X 3 →ₗ[A] C'.X 0 →ₗ[A] A) (ε ε' : A)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module A (M v)]
    (Aq Cin Dq : ∀ v, Module.End A (M v)) (hDC : ∀ v, Dq v * Cin v = Cin v * Aq v) (n : ι → ℤ)
    (hunit : ∀ v, (IsUnit (Aq v) ∧ IsUnit (Dq v)) ∨ IsUnit (Cin v))
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (tameComplex (Aq v) (Cin v) (Dq v) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (hL2 : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y)
    (uprim : FractionRing Uniform.Lambda)
    (hu : ∀ e : HomotopyEquiv C' C, e.hom = j → Central.IsClassFunctionalCoord
      (Dm.map (algebraMap A (FractionRing Uniform.Lambda)))
      (fun i => algebraMap A (FractionRing Uniform.Lambda) (zm i))
      (fun i => algebraMap A (FractionRing Uniform.Lambda)
        (rowOf (baseLam pd2 e.inv ((c.f 1).hom z)) e2 i)) uprim)
    (boundary : Boundary45Base P (m + 1) (fun i => Rings.rhoT (zm i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) :
    ∃ e : HomotopyEquiv C' C, e.hom = j ∧ Nonempty (BaseZeroCore D Fam P) := by
  obtain ⟨e, he, -⟩ := exists_baseLam Z j c z pd1 pd2 pd3 ε ε' ι M Aq Cin Dq hDC n hunit hcone
    hz hL1 hL2
  have hcz : (C.d 1 2).hom ((c.f 1).hom z) = 0 := by
    have h' := congrArg (fun f => ModuleCat.Hom.hom f z) (c.comm 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
    rw [h', hz, map_zero]
  exact ⟨e, he, ⟨BaseZeroCore.ofPaired D Fam P m Dm hcentral zm hzm CU C' C e1 e2 hd pd1 pd2 ε
    hL1 e.inv _ hcz uprim (hu e he) boundary hprimId⟩⟩

/-! ### Non-vacuity: the rank-one model -/

/-- The complex with `Λ_(t)` in every degree and zero differentials. -/
def exCU : CochainComplex (ModuleCat.{0} A) ℤ where
  X _ := ModuleCat.of A A
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- The coordinates `A ≃ A¹`. -/
instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

def exE (n : ℤ) : exCU.X n ≃ₗ[A] (Fin (0 + 1) → A) := (LinearEquiv.funUnique (Fin (0 + 1)) A A).symm

/-- The multiplication pairing. -/
def exPd (i k : ℤ) : exCU.X i →ₗ[A] exCU.X k →ₗ[A] A := LinearMap.mul A A

theorem exCU_d (i k : ℤ) (y : exCU.X i) : (exCU.d i k).hom y = 0 := rfl

theorem exHd : ∀ y, exE 2 ((exCU.d 1 2).hom y) = (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A) *ᵥ
    exE 1 y := fun y => by rw [exCU_d, map_zero, zero_mulVec]

theorem exHL1 :
    ∀ w y, exPd 2 1 ((exCU.d 1 2).hom w) y = (1 : A) * exPd 1 2 w ((exCU.d 1 2).hom y) :=
  fun w y => by rw [exCU_d, exCU_d, map_zero, map_zero, LinearMap.zero_apply, mul_zero]

theorem exCz : (exCU.d 1 2).hom (1 : A) = 0 := rfl

/-- The row of the paired functional of the rank-one model is `1`. -/
theorem exRow : rowOf (baseLam (exPd 2 1) (𝟙 exCU) (1 : A)) (exE 2) = fun _ => 1 := by
  funext i
  obtain rfl : i = default := Subsingleton.elim i default
  change (Pi.single (M := fun _ : Fin (0 + 1) => A) default 1 default) * (1 : A) = 1
  rw [Pi.single_eq_same, mul_one]

/-- **Non-vacuity**: on the rank-one model (`m = 0`, `Dm = 0`, `z = 1`), the paired functional of
the multiplication pairing is closed, its row is `1`, and `u_prim = 1` is its class-functional
coordinate: the hypotheses of `BaseZeroCore.ofPaired` on `lam` and `hu` hold non-degenerately. -/
theorem exLam_coord :
    (∀ y : exCU.X 1, baseLam (exPd 2 1) (𝟙 exCU) (1 : A) ((exCU.d 1 2).hom y) = 0) ∧
    ((0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A).map Rings.rhoT).rank = 0 ∧
    Central.IsClassFunctionalCoord
      ((0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A).map (algebraMap A (FractionRing Uniform.Lambda)))
      (fun _ => algebraMap A (FractionRing Uniform.Lambda) 1)
      (fun i => algebraMap A (FractionRing Uniform.Lambda)
        (rowOf (baseLam (exPd 2 1) (𝟙 exCU) (1 : A)) (exE 2) i)) 1 := by
  refine ⟨baseLam_closed (exPd 1 2) (exPd 2 1) 1 exHL1 (𝟙 exCU) exCz, ?_, ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.rank_zero]
  · rw [exRow]
    unfold Central.IsClassFunctionalCoord
    ext i k
    obtain rfl : i = k := Subsingleton.elim i k
    simp [vecMulVec_apply, adjugate_fin_one]

end ZInQ.Contrib.CloudB3RC53.BaseZeroLam
