import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Retention
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate3

/-!
# Common coordinate, part 8: (4.7) from retained naturality, with no assumed `w_R = e_q w_P`

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex L4159–4193). Repair of
CommonCoordinate review items 4 and 8 (and v2 item 4): `ActualStep` (`Unit.lean`) assumed the
functional relation `w_R|old = e_q w_P` of the triangular model directly. Here it is constructed:

* `SelmerFunctionals wR wP e_K`: the triangular-basis functionals are the paired functionals
  `λ_R = tr(z_S ∪ ·)`, `λ_P = tr(z_{P⊥} ∪ ·)` of retained Selmer data — a
  `PlaceRetention` (`Retention.lean`: every old condition and homotopy retained, place by place;
  its new place is an `UnramifiedNewPlace`, not instantiable by genuine continuous cochains, and
  re-pointing to the genuine Galois support data is pending),
  a trace killing coboundaries, the paired strict lift `j z_S = e z_{P⊥} + d b`, and model bases
  `φ_P` (cocycles of `C_P`) and `φ_R` of `C_R` whose old part is `i ∘ φ_P` — read in the coordinate
  ring through `ψ`, with `ψ(e) = e_q`.
* `SelmerFunctionals.restrict`: `w_R|old = e_q w_P`, PROVED from `pairedFunctional_natural` and
  `PlaceRetention.toRetainedPairing`.
* `NaturalStep`: `ActualStep` with the field `w_R|old = e_q w_P` replaced by `SelmerFunctionals`;
  `NaturalStep.toActualStep` (PROVED).
* `commonCoordinate_h47_of_natural`: RC0's field `h47` (tex L4166–4193, the multi-prime (4.7)),
  `commonCoordinateModel_of_natural_models` and `commonCoordinateInputs_of_natural` (RC0's
  `CommonCoordinateInputs`), from retained naturality, support-change retention and the triangular
  models. PROVED.
* Non-vacuity (LESSON 2): `naturalStep_example`, the step of `actualStep_example` with its
  functionals produced by `examplePlaceRetention`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix CategoryTheory ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- **The triangular-basis functionals are paired functionals of retained Selmer data**
(tex L4159–4177). `wR`, `wP` are the functionals of the relaxed and primitive triangular models and
`eK` the point factor `e_q` in the coordinate ring. -/
def SelmerFunctionals {K : Type} [CommRing K] {n : ℕ} {κ : Type} (wR : Fin n ⊕ κ → K)
    (wP : Fin n → K) (eK : K) : Prop :=
  ∃ (S : CommRingCat.{0}) (DR DPp : SelData S) (UP US : GCx S) (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) (R : PlaceRetention DR DPp fP fS)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (_ : ∀ z, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl z) = 0)
    (zS : (selCx (restrictData DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (_ : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (φP : Fin n → (selCx (restrictData DR fP)).X 2)
    (_ : ∀ i, (selCx (restrictData DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : Fin n ⊕ κ → (selCx DR).X 2)
    (_ : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i))
    (ψ : S →+* K),
    ψ e = eK ∧
      (∀ j, wR j = ψ (pairedFun R.toRetainedPairing.QR
        (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS (φR j))) ∧
      (∀ i, wP i = ψ (pairedFun R.toRetainedPairing.QP tr zP (φP i)))

/-- **`w_R|old = e_q w_P`** (tex L4170–4177), PROVED from the naturality of the cup pairing
(`pairedFunctional_natural`) for the retained pairing of the place-by-place retention data. -/
theorem SelmerFunctionals.restrict {K : Type} [CommRing K] {n : ℕ} {κ : Type}
    {wR : Fin n ⊕ κ → K} {wP : Fin n → K} {eK : K} (h : SelmerFunctionals wR wP eK) (i : Fin n) :
    wR (Sum.inl i) = eK * wP i := by
  obtain ⟨S, DR, DPp, UP, US, fP, fS, R, tr, htr, zS, zP, e, b, hlift, φP, hφP, φR, hφR, ψ,
    he, hwR, hwP⟩ := h
  rw [hwR, hwP, hφR, pairedFunctional_natural R.toRetainedPairing tr htr zS zP e b hlift (φP i)
    (hφP i), map_mul, he]

/-- **One relaxation step from retained naturality** (tex L4159–4193): `ActualStep` with the field
`w_R|old = e_q w_P` replaced by `SelmerFunctionals` (the functionals come from retained Selmer
data). -/
def NaturalStep {K : Type} [CommRing K] (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (uprim urel ε : K) (unitR unitP : K → Prop) : Prop :=
  ∃ (n : ℕ) (DPa PP QP : Matrix (Fin n) (Fin n) K)
    (DRa PR QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (zPa wPa : Fin n → K)
    (zRa wRa : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K),
    IsUnit PP.det ∧ IsUnit QP.det ∧ IsUnit PR.det ∧ IsUnit QR.det ∧
    PR * DRa * QR = fromBlocks (PP * DPa * QP) X 0 (twoPlaceBlock F q z zi) ∧
    (∀ i, (QR⁻¹ *ᵥ zRa) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zPa) i) ∧
    SelmerFunctionals (wRa ᵥ* PR⁻¹) (wPa ᵥ* PP⁻¹) (pointFactor a z zi) ∧
    IsCoordOn DRa zRa wRa urel ∧ IsClassFunctionalCoord DPa zPa wPa uprim ∧
    (PP * DPa * QP).adjugate ≠ 0 ∧
    unitR (PR.det * QR.det) ∧ unitP (PP.det * QP.det) ∧
    ε = qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)

/-- `NaturalStep` gives `ActualStep`: the functional relation is PROVED by
`SelmerFunctionals.restrict`. -/
theorem NaturalStep.toActualStep {K : Type} [CommRing K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop}
    (h : NaturalStep F q qi a z zi uprim urel ε unitR unitP) :
    ActualStep F q qi a z zi uprim urel ε unitR unitP := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS, h8, h9,
    h10, h11, h12, h13⟩ := h
  exact ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS.restrict,
    h8, h9, h10, h11, h12, h13⟩

/-- **RC0's field `h47` from retained naturality** (tex L4166–4193):
`(∏_U l_q) u_rel = (∏_U e_q² ε_q) u_prim` when each relaxation step is a `NaturalStep`, with no
assumed functional relation. PROVED. -/
theorem commonCoordinate_h47_of_natural {R : Type*} [CommRing R]
    (chi : R →+* PowerSeries ℚ_[2]) (U : Finset ℕ) (l e : ℕ → R) (urel uprim : PowerSeries ℚ_[2])
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2]))
    (q qi a z zi eps : ℕ → PowerSeries ℚ_[2]) (u : Finset ℕ → PowerSeries ℚ_[2])
    (hl : ∀ p ∈ U, chi (l p) = quotientFactor (F p) (qi p) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (hrel : u U = urel) (hprim : u ∅ = uprim)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      NaturalStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T) (u (insert p T)) (eps p)
        LamUnit LamUnit) :
    (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * eps q) * uprim :=
  commonCoordinate_h47_of_models_full chi U l e urel uprim F q qi a z zi eps u hl he hrel hprim hq
    ha hd fun T hT p hp hpT => (hstep T hT p hp hpT).toActualStep

/-- **A `CommonCoordinateModel` from retained naturality** (tex L4142–4328): as
`commonCoordinateModel_of_actual_models`, each relaxation step a `NaturalStep`. -/
noncomputable def commonCoordinateModel_of_natural_models {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (R : Type) [CommRing R] (chi : R →+* PowerSeries ℚ_[2]) (Q : Finset ℕ)
    (v g l e ei : ℕ → R)
    (hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1)
    (hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q))
    (hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1) (urel : PowerSeries ℚ_[2]) (U : Finset ℕ)
    (hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1))
    (hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel)
    (qn : ℕ → ℕ) (hodd : ∀ p ∈ U, Odd (qn p))
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (a z zi eps : ℕ → PowerSeries ℚ_[2])
    (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = PowerSeries.C (qn p : ℚ_[2]))
    (hl : ∀ p ∈ U, chi (l p) =
      quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (u : Finset ℕ → PowerSeries ℚ_[2]) (hrel : u U = urel) (hprim : u ∅ = D.uPrim Fam x)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      NaturalStep (F p) (PowerSeries.C (qn p : ℚ_[2])) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (a p)
        (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit) :
    CommonCoordinateModel D Fam x :=
  commonCoordinateModel_of_actual_models D Fam x R chi Q v g l e ei hsign hratio hinv urel U hU
    hutilde qn hodd F a z zi eps ha hd hl he u hrel hprim fun T hT p hp hpT =>
      (hstep T hT p hp hpT).toActualStep

/-- **The support-triangle data at one address with retained naturality** (tex 4142–4328): RC0's
`CommonCoordinateTriangles` with each step a `NaturalStep` instead of an `ActualStep`. -/
structure CommonCoordinateTrianglesN {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type 1 where
  R : Type
  [commR : CommRing R]
  chi : R →+* PowerSeries ℚ_[2]
  Q : Finset ℕ
  v : ℕ → R
  g : ℕ → R
  l : ℕ → R
  e : ℕ → R
  ei : ℕ → R
  hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1
  hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q)
  hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1
  urel : PowerSeries ℚ_[2]
  U : Finset ℕ
  hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1)
  hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel
  qn : ℕ → ℕ
  hodd : ∀ p ∈ U, Odd (qn p)
  F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  a : ℕ → PowerSeries ℚ_[2]
  z : ℕ → PowerSeries ℚ_[2]
  zi : ℕ → PowerSeries ℚ_[2]
  ha : ∀ p ∈ U, (F p).trace = a p
  hd : ∀ p ∈ U, (F p).det = PowerSeries.C (qn p : ℚ_[2])
  hl : ∀ p ∈ U, chi (l p) =
    quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p)
  he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p)
  u : Finset ℕ → PowerSeries ℚ_[2]
  hrel : u U = urel
  hprim : u ∅ = D.uPrim Fam x
  eps : ℕ → PowerSeries ℚ_[2]
  hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
    NaturalStep (F p) (PowerSeries.C (qn p : ℚ_[2])) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (a p)
      (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit

attribute [instance] CommonCoordinateTrianglesN.commR

/-- RC0's `CommonCoordinateTriangles` from the naturality data (PROVED). -/
def CommonCoordinateTrianglesN.toTriangles {ℓ : ℕ} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} (M : CommonCoordinateTrianglesN D Fam x) : CommonCoordinateTriangles D Fam x where
  R := M.R
  chi := M.chi
  Q := M.Q
  v := M.v
  g := M.g
  l := M.l
  e := M.e
  ei := M.ei
  hsign := M.hsign
  hratio := M.hratio
  hinv := M.hinv
  urel := M.urel
  U := M.U
  hU := M.hU
  hutilde := M.hutilde
  qn := M.qn
  hodd := M.hodd
  F := M.F
  a := M.a
  z := M.z
  zi := M.zi
  ha := M.ha
  hd := M.hd
  hl := M.hl
  he := M.he
  u := M.u
  hrel := M.hrel
  hprim := M.hprim
  eps := M.eps
  hstep T hT p hp hpT := (M.hstep T hT p hp hpT).toActualStep

/-- **The inputs of (4.7) with retained naturality** (tex 4142–4328): at every address of a final
family, one `CommonCoordinateTrianglesN`. -/
def CommonCoordinateInputsN {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateTrianglesN D F x)

/-- **RC0's `CommonCoordinateInputs` (hence `h47` at every address) from retained naturality,
support-change retention and the triangular models**, with no assumed `w_R = e_q w_P`. PROVED. -/
theorem commonCoordinateInputs_of_natural {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsN D) : CommonCoordinateInputs D :=
  commonCoordinateInputs_of_triangles fun Co Ce F hF x => by
    obtain ⟨M⟩ := h Co Ce F hF x
    exact ⟨M.toTriangles⟩

/-! ### Non-vacuity -/

/-- **The functionals of `actualStep_example` are paired functionals of retained Selmer data**:
over `ℚ₂[[t]]`, the place-by-place retention `examplePlaceRetention` (relaxed data with `ι_R = id`),
the trace `fst` (it kills coboundaries of `Cone(E → E_L)[−1]`), the strict class `z_S = (−2, 0, 0)`,
the orthogonal class `z_{P⊥} = (1, 0, 0)`, `e = −2`, and the cocycle `φ_P = (1, 1, 0)`;
`λ_P(φ_P) = 1` and `λ_R(i φ_P) = −2`. -/
theorem selmerFunctionals_example :
    SelmerFunctionals (κ := Fin 2 ⊕ Fin 2) (Sum.elim (fun _ => (-2 : KPS)) (fun _ => 0))
      (fun _ : Fin 1 => (1 : KPS)) (pointFactor 2 2 2) := by
  refine ⟨CommRingCat.of KPS, relSel KPS, constSel KPS, constCx KPS, constCx KPS, constId KPS,
    constId KPS, examplePlaceRetention KPS,
    LinearMap.fst KPS ((constCx KPS).X 3) ((constCx KPS).X (3 - 1)), fun _ => rfl,
    (show selT _ 1 from ((-2 : KPS), (0 : KPS), (0 : KPS))),
    (show selT _ 1 from ((1 : KPS), (0 : KPS), (0 : KPS))), (-2 : KPS),
    (show selT _ 0 from ((0 : KPS), (0 : KPS), (0 : KPS))), ?_,
    fun _ => (show selT _ 2 from ((1 : KPS), (1 : KPS), (0 : KPS))), ?_,
    Sum.elim (fun _ => (changeMap (relSel KPS) (constId KPS)).f 2 2 rfl
      (show selT _ 2 from ((1 : KPS), (1 : KPS), (0 : KPS)))) (fun _ => 0), fun _ => rfl,
    RingHom.id KPS, ?_, ?_, ?_⟩
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change (-2 : KPS) = (-2) * 1 + 0
      ring
    · change (0 : KPS) = (-2) * 0 + 0
      ring
    · change (0 : KPS) = (-2) * 0 + (0 - 0 - 0)
      ring
  · intro i
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · rfl
    · change (1 : KPS) - 1 - 0 = 0
      ring
  · simp [pointFactor]
  · rintro (j | j)
    · change (-2 : KPS) = (-2) * 1
      ring
    · change (0 : KPS) = (-2) * 0
      ring
  · intro i
    change (1 : KPS) = 1 * 1
    ring

/-- **Non-vacuity of `NaturalStep`** with `Λ`-unit basis comparisons, over `ℚ₂[[t]]`: the step of
`actualStep_example`, its functional relation now produced by retained Selmer data. -/
theorem naturalStep_example :
    NaturalStep (1 : Matrix (Fin 2) (Fin 2) KPS) 1 1 2 2 2 1 4 1 LamUnit LamUnit := by
  refine ⟨1, 0, 1, 1, Matrix.diagonal exDiag, 1, 1, 0, fun _ => 1, fun _ => 1,
    Sum.elim (fun _ => -2) (fun _ => 0), Sum.elim (fun _ => -2) (fun _ => 0),
    by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, ← relaxed_example]
  · intro i
    simp [pointFactor]
  · rw [inv_one, inv_one, vecMul_one, vecMul_one]
    exact selmerFunctionals_example
  · -- the relaxed coordinate: `adj diag(0,1,1,1,1) = diag(1,0,0,0,0)`
    unfold IsCoordOn
    rw [adjugate_diagonal]
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x; fin_cases y
      simp only [vecMulVec_apply, Sum.elim_inl, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
      rw [Finset.prod_eq_one]
      · norm_num
      · intro j hj
        rcases j with j | j
        · fin_cases j; exact absurd rfl (Finset.ne_of_mem_erase hj)
        · rfl
    · simp [vecMulVec_apply, diagonal_apply_ne]
    · simp [vecMulVec_apply, diagonal_apply_ne]
    · simp only [vecMulVec_apply, Sum.elim_inr, mul_zero, Matrix.smul_apply, smul_eq_mul]
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq, Finset.prod_eq_zero (i := Sum.inl 0)]
        · simp
        · simp
        · rfl
      · rw [diagonal_apply_ne _ (fun h => hxy (Sum.inr_injective h)), mul_zero]
  · unfold IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]
  · rw [Matrix.one_mul, Matrix.mul_one, adjugate_fin_one]
    exact one_ne_zero
  · simpa using ZInQ.Manuscript.RC.Wiring.lamUnit_one
  · simpa using ZInQ.Manuscript.RC.Wiring.lamUnit_one
  · simp

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
