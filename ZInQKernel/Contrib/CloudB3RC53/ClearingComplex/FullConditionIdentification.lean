import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionOld
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionSelmer
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.GenuineIdentification

/-!
# The identification with the full-condition triangle (5.6)

Manuscript `diophantine_zq.tex`, the triangle (5.6) (tex 5234–5238), its graded model
(tex 5398–5403), the new-local cancellation (tex 5394–5454), the local blocks (tex 5455–5463) and
the support comparisons (tex 3470–3499).

`Identification3 K S S' hS b dK hK cE tK` replaces `Identification2G` (whose pre-cancellation new
blocks sit in degrees two and three and whose augmented model is compared with the unramified
support data). Its differences:

* the pre-cancellation family model is a `FullPreComplex`: the new singular summands `N` sit in
  **degrees one and two** (`C¹ = D¹ ⊕ N`, `C² = D² ⊕ N`, `d¹ = (P Q; T B)`), so the surviving
  Schur differential is `d¹ = P − QB⁻¹T` and `d⁰ = c⁰`, `d² = U` are unchanged (`poles1`);
* the family local conditions `Δf` are **full at the new places** (`hfull`: the condition map is
  an isomorphism in every degree there; satisfied by the relaxed conditions, `hfull_relaxed`);
* there is **no nonemptiness hypothesis** on the new places: `S' = S` (`Q = ∅`) is admitted;
* the augmented model modulo `ρ` is compared with the genuine **full-condition** Selmer complex
  `selCx (galoisFullData K hS R₀ M₀ Δ₀)` (`ψ0`), its old part with the genuine unramified
  support complex, the first term of the genuine sequence `galoisFullSES` (`ψold`; that term is
  `selCx (galoisSupportData …).Dp` by `galoisFullSES_X₁`), and the square commutes with the
  inclusion `C(ur) → C(full)` (`square`);
* PROVED, not assumed: the induced map from the model quotient `N --B--> N` (degrees one and two)
  to the genuine singular quotients `⊕_q C^•_cont(G_{K_q}, M₀) / C^•_cont(G_q/I_q, M₀)` exists
  (`quotMap`, the cokernel property of the model sequence) and is a **quasi-isomorphism**
  (`quotMap_quasiIso`, the five lemma on the two short exact sequences of (5.6)). In particular
  `B` need not be invertible modulo `ρ`, and the old inclusion is not claimed to be a
  quasi-isomorphism.

The cancellation fields (the local blocks `A_q` with `det A_q = X^{d_q} v_q + 2 w_q`, the family
model, `T₀ = Y₀ = 0`, the central Smith form, the budget) form the parent structure `FullCore Qn`
(indexed by an arbitrary finite type `Qn`, here the new places); the remaining fields (the genuine
family model, Nekovář's finite setting, the tame models) are those of `Identification2G`. Derived
as there: `FullCore.toIdentification` (poles in degree one),
`toSelmerIdentification`, `support_qis` (from the PRINT `NekovarProp788ii`) and
`clearingInputsCx_of_km3` (the body of RC0's `ClearingInputsCx`).

Kinds: `Identification3` is ELLIOT for the inherited `FullCore` fields (the lifted family model,
`B₀ = diag(A_q)`, `T₀ = 0`, the central Smith form, the budget (5.7); tex 5394–5430, 5522–5543)
and GLUE for the Galois comparisons. The family clause (`Mf`, `Δf`, `hfull`, `ψf`) is met by
every model once `S ≠ ∅` (zero coefficients, the model as the local condition at one old place).
`clearingTarget_of_G3` consumes only `FullCore` and the family clause (through
`toSelmerIdentification`), not `ψ0`, `ψold`, `square`, `tame`. All other declarations are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData aug sgnChar
  genuinePole)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData galoisSupportData NewPlaces
  GaloisLocalConditions locMap urRes inflMap Gloc NekovarProp788ii NekovarFiniteSetting
  supportChange_of_print selmerIdentificationOfGenuine urCond contCochains ResMod natCx natHom
  locMap_compat)

variable {b : ℕ}

/-- **The new local block of a full-condition model is invertible over `𝒪[G]`** (PROVED; as
`isUnit_B_of`). -/
theorem isUnit_B_full {Qn ιn : Type} [Fintype Qn] [DecidableEq Qn] [Fintype ιn] [DecidableEq ιn]
    (A : Qn → Matrix ιn ιn Lam) (dq : Qn → ℕ) (hd : ∀ q, dq q ≤ 4) (v : Qn → Lamˣ) (w : Qn → Lam)
    (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q)
    (C : FullPreComplex (MonoidAlgebra Lam (SignGroup b))) (eN : C.N ≃ ιn × Qn)
    (hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A) :
    IsUnit (C.map (φO b)).B.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Determinant.matrix_isUnit_of_isUnit_aug Determinant.isUnit_one_add_two_mul_OO
    Determinant.signGroup_mul_self _ ?_
  change IsUnit ((C.B.map (φO b)).map aug).det
  have h0 := (Determinant.newLocal_family_pole_genuine A dq hd v w hdet
    (C.B.submatrix eN.symm eN.symm) hB0 (sgnChar 0) 0).1
  have e : ((C.B.submatrix eN.symm eN.symm).map (Determinant.signEval (sgnChar 0))).map
      (algebraMap Lam OO) = ((C.B.map (φO b)).map aug).submatrix eN.symm eN.symm := by
    refine Matrix.ext fun i j => ?_
    change algebraMap Lam OO (Determinant.signEval (sgnChar 0) (C.B _ _)) = aug (φO b (C.B _ _))
    rw [Determinant.signEval_sgnChar_zero, aug_φO]
  rw [e, Matrix.det_submatrix_equiv_self] at h0
  exact h0

/-- **The cancellation core of the full-condition model** (the new local blocks indexed by `Qn`,
possibly empty; the family model with the new summands in degrees one and two; `T₀ = Y₀ = 0`; the
central Smith form; the budget). -/
structure FullCore (Qn : Type) [Fintype Qn] [DecidableEq Qn] (b : ℕ) (dK hK cE tK : ℕ) where
  /-- the index of a local block -/
  ιn : Type
  [fι : Fintype ιn]
  [dι : DecidableEq ιn]
  /-- the new local blocks over `Λ`, one per new place -/
  A : Qn → Matrix ιn ιn Lam
  dq : Qn → ℕ
  hd : ∀ q, dq q ≤ 4
  v : Qn → Lamˣ
  w : Qn → Lam
  hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q
  /-- the pre-cancellation family model over `Λ[G]`, new summands in degrees one and two -/
  C : FullPreComplex (MonoidAlgebra Lam (SignGroup b))
  eN : C.N ≃ ιn × Qn
  hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A
  hT0 : C.T.map (augR b) = 0
  hY0 : C.Y.map (augR b) = 0
  s : (i : ℕ) → Fin (((C.map (augR b)).old hY0 hT0).mi i) → ℤ_[2]
  s_ne : ∀ i j, s i j ≠ 0
  central_full :
    ((C.map (augR b)).old hY0 hT0).d0.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d0 ∧
      ((C.map (augR b)).old hY0 hT0).d1.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d1 ∧
      ((C.map (augR b)).old hY0 hT0).d2.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d2
  budget : BudgetInputsAt (((C.map (φO b)).cancel (isUnit_B_full A dq hd v w hdet C eN hB0)).toSmithBlocks
    (O := OO) ((C.map (augR b)).old hY0 hT0).Ai s s_ne (central_of_full _ s central_full))
    fr₀ dK hK cE tK

namespace FullCore

attribute [instance] fι dι

variable {Qn : Type} [Fintype Qn] [DecidableEq Qn] {dK hK cE tK : ℕ}
  (M : FullCore Qn b dK hK cE tK)

theorem isUnit_B : IsUnit (M.C.map (φO b)).B.det :=
  isUnit_B_full M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0

/-- **The remaining complex**: the cancellation of the new singular summands over `𝒪[G]`. -/
def D : BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  (M.C.map (φO b)).cancel M.isUnit_B

/-- The augmented old part over `Λ`. -/
abbrev oldC : BlockComplex Lam := (M.C.map (augR b)).old M.hY0 M.hT0

/-- The new local block as a family over `ι × Q`. -/
abbrev Bsub : Matrix (M.ιn × Qn) (M.ιn × Qn)
    (MonoidAlgebra Lam (SignGroup b)) :=
  M.C.B.submatrix M.eN.symm M.eN.symm

theorem d1_map_aug : M.D.d1.map (augS b) = (M.C.P.map (augR b)).map (algebraMap Lam OO) := by
  change (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
    M.C.T.map (φO b)).map (augS b) = _
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_φO_aug, map_φO_aug M.C.T,
    M.hT0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, sub_zero]

theorem aug_eq (i : ℕ) :
    (M.D.Ai i).map aug = (M.oldC.Ai i).map (algebraMap Lam OO) := by
  match i with
  | 0 => exact Matrix.ext fun j k => aug_φO (M.C.c0 (Sum.inl j) k)
  | 1 =>
    exact Matrix.ext fun j k =>
      congrArg (fun N : Matrix _ _ OO => N (Sum.inl j) (Sum.inr (Sum.inr k))) M.d1_map_aug
  | 2 => exact Matrix.ext fun j k => aug_φO (M.C.U j (Sum.inr (Sum.inr k)))
  | _ + 3 => exact Matrix.ext fun j => j.elim0

/-- **The sign-evaluated surviving differential `d¹ = P − QB⁻¹T` is the Schur complement of the
new-local family** (PROVED; one cancellation, in degree one). -/
theorem poles1 : IsNewLocalSchur (b := b) fun x => M.D.d1.map (Determinant.signEval (sgnChar x)) := by
  refine ⟨Qn, M.ιn, inferInstance, inferInstance, inferInstance, inferInstance, M.A,
    M.dq, M.hd, M.v, M.w, M.hdet, M.Bsub, M.hB0, Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2,
    Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1, inferInstance, inferInstance, M.C.P,
    M.C.Q.submatrix id M.eN.symm, M.C.T.submatrix M.eN.symm id, 1, 1, fun x => ?_⟩
  set f := (Determinant.signEval (O := OO) (sgnChar x)).toRingHom
  have hB : IsUnit (M.C.B.map (φO b)).det := M.isUnit_B
  have h1 : M.D.d1.map (Determinant.signEval (sgnChar x)) =
      (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
        M.C.T.map (φO b)).map f := rfl
  set Px := (M.C.P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Qx := (M.C.Q.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Bx := (M.C.B.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Tx := (M.C.T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  have hL : M.D.d1.map (Determinant.signEval (sgnChar x)) = Px - Qx * Bx⁻¹ * Tx := by
    rw [h1, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      map_inv_of_isUnit f _ hB]
    change (M.C.P.map (φO b)).map (Determinant.signEval (sgnChar x)) -
        (M.C.Q.map (φO b)).map (Determinant.signEval (sgnChar x)) *
          ((M.C.B.map (φO b)).map (Determinant.signEval (sgnChar x)))⁻¹ *
          (M.C.T.map (φO b)).map (Determinant.signEval (sgnChar x)) = _
    rw [map_φO_signEval, map_φO_signEval, map_φO_signEval, map_φO_signEval]
  have hR : (1 : Matrix (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) Lam).map
        (algebraMap Lam OO) *
      (Px - (Qx.submatrix id M.eN.symm) * (Bx.submatrix M.eN.symm M.eN.symm)⁻¹ *
        (Tx.submatrix M.eN.symm id)) *
      (1 : Matrix (Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) (Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) Lam).map
        (algebraMap Lam OO) = Px - Qx * Bx⁻¹ * Tx := by
    rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  exact hL.trans hR.symm

/-- **The identification, derived** (PROVED): `poles0 = c⁰`, `poles1` the Schur complement,
`poles2 = U`. -/
def toIdentification : Identification b dK hK cE tK where
  D := M.D
  A0 := M.oldC.Ai
  s := M.s
  s_ne := M.s_ne
  central := central_of_full _ M.s M.central_full
  aug_eq := M.aug_eq
  poles0 := Identification2.isNewLocalSchur_lam M.C.c0
  poles1 := M.poles1
  poles2 := Identification2.isNewLocalSchur_lam M.C.U
  budget := budgetInputs_of_at M.budget

end FullCore


variable (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
  (hS : S ⊆ S')

/-- **The identification with the full-condition triangle (5.6)** (ELLIOT for the inherited
`FullCore` fields: the lifted family model, `B₀ = diag(A_q)`, `T₀ = 0`, the central Smith form, the
budget (5.7), tex 5394–5430, 5522–5543; GLUE for the Galois comparisons; the family clause is met
by every model once `S ≠ ∅`; `clearingTarget_of_G3` consumes only `FullCore` and the family
clause; see the module docstring). The new places may be empty. -/
structure Identification3 [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    (b : ℕ) (dK hK cE tK : ℕ) extends FullCore (NewPlaces K S S') b dK hK cE tK where
  /-- the family coefficient module (a topological `𝒪[G][G_{K,S'}]`-module) -/
  Mf : Type
  [Mf_acg : AddCommGroup Mf]
  [Mf_mod : Module (MonoidAlgebra OO (SignGroup b)) Mf]
  [Mf_act : DistribMulAction (GKS K S') Mf]
  [Mf_comm : SMulCommClass (GKS K S') (MonoidAlgebra OO (SignGroup b)) Mf]
  [Mf_top : TopologicalSpace Mf]
  [Mf_cadd : ContinuousAdd Mf]
  [Mf_csmul : ContinuousConstSMul (MonoidAlgebra OO (SignGroup b)) Mf]
  [Mf_cact : ContinuousSMul (GKS K S') Mf]
  /-- the family local conditions -/
  Δf : GaloisLocalConditions K S' (MonoidAlgebra OO (SignGroup b)) Mf
  /-- the family local conditions are FULL at the new places: there the condition map
  `U_v → C^•_cont(G_{K_v}, M_f)` is an isomorphism in every degree (the complex `C_b` of (5.6)) -/
  hfull : ∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places K S', v.1 ∉ S →
    ∀ n : ℤ, Function.Bijective ((Δf.i v).f n n rfl)
  /-- `C ⊗ 𝒪[G]` is a model of the genuine family Selmer complex -/
  ψf : (C.map (φO b)).toGCx.toCC ⟶ (selCx (galoisSelData K S' _ Mf Δf)).toCC
  qisf : QuasiIso ψf
  /-- the finite coefficient ring of the comparison, a quotient of `Λ` -/
  R₀ : Type
  [R₀_ring : CommRing R₀]
  [R₀_local : IsLocalRing R₀]
  ρ : Lam →+* R₀
  p : ℕ
  hset : NekovarFiniteSetting K S p R₀
  hS' : S'.Finite
  /-- the coefficient module at augmentation (finite discrete `R₀[G_{K,S}]`-module) -/
  M₀ : Type
  [M₀_acg : AddCommGroup M₀]
  [M₀_mod : Module R₀ M₀]
  [M₀_act : DistribMulAction (GKS K S) M₀]
  [M₀_comm : SMulCommClass (GKS K S) R₀ M₀]
  [M₀_top : TopologicalSpace M₀]
  [M₀_disc : DiscreteTopology M₀]
  [M₀_cact : ContinuousSMul (GKS K S) M₀]
  [M₀_fin : Finite M₀]
  /-- the unramified factorizations at the new places -/
  ψur : ∀ q : NewPlaces K S S', ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1 →ₜ* GKS K S
  hψur : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψur q (urRes K q.1 g)
  /-- the old local conditions -/
  Δ₀ : GaloisLocalConditions K S R₀ M₀
  /-- the augmented family model modulo `ρ` models the genuine FULL-condition Selmer complex
  `(C_b)₀` of (5.6) -/
  ψ0 : ((C.map (augR b)).map ρ).toGCx.toCC ⟶ (selCx (galoisFullData K hS R₀ M₀ Δ₀)).toCC
  qis0 : QuasiIso ψ0
  /-- the augmented old part modulo `ρ` models the genuine unramified support complex (the first
  term of the genuine sequence of (5.6), `selCx (galoisSupportData …).Dp`) -/
  ψold : (((C.map (augR b)).map ρ).old (FullPreComplex.map_Y_zero _ ρ hY0)
      (FullPreComplex.map_T_zero _ ρ hT0)).toGCx.toCC ⟶
    (galoisFullSES K hS R₀ M₀ ψur hψur Δ₀).X₁
  qisOld : QuasiIso ψold
  /-- compatibility with the inclusion `C(ur) → C(full)` -/
  square : ψold ≫ (galoisFullSES K hS R₀ M₀ ψur hψur Δ₀).f =
    SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (FullPreComplex.map_Y_zero _ ρ hY0)
      (FullPreComplex.map_T_zero _ ρ hT0)) ≫ ψ0
  /-- the Frobenius of the new place `q` on `M₀`, and its residue cardinality -/
  Φq : NewPlaces K S S' → (M₀ →ₗ[R₀] M₀)
  qq : NewPlaces K S S' → ℕ
  qq_odd : ∀ q, Odd (qq q)
  /-- bases of `M₀` indexed by the local block index -/
  bas : NewPlaces K S S' → Module.Basis ιn R₀ M₀
  /-- the local block reduces to the actual tame differential `Φ_q − q` (tex 5455–5463) -/
  hA : ∀ q, (A q).map ρ =
    LinearMap.toMatrix (bas q) (bas q) (Φq q - ((qq q : ℕ) : R₀) • LinearMap.id)
  /-- the tame model is a quasi-isomorphic model of the genuine local complex and the genuine
  unramified condition at `q` (named input) -/
  tame : ∀ q : NewPlaces K S S', TameModelQIso M₀ (Φq q) (qq q)
    (natCx (contCochains R₀ (Gloc K q.1) (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) M₀))))
    (natCx (contCochains R₀ (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
      (ResMod (ψur q) M₀)))
    (natHom (urCond (k := R₀) (GS := GKS K S) (GS' := GKS K S') (M := M₀) (infl := inflMap K hS)
      (Gq := fun q : NewPlaces K S S' => Gloc K q.1) (locq := fun q => locMap K S' q.1)
      (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
      (π := fun q => urRes K q.1) (ψ := ψur)
      (fun q g => (locMap_compat K hS q.1 g).trans (hψur q g)) q))

namespace Identification3
attribute [instance] Mf_acg Mf_mod Mf_act Mf_comm Mf_top Mf_cadd Mf_csmul Mf_cact
  R₀_ring R₀_local M₀_acg M₀_mod M₀_act M₀_comm M₀_top M₀_disc M₀_cact M₀_fin

variable {K S S' hS} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {dK hK cE tK : ℕ} (M : Identification3 K S S' hS b dK hK cE tK)

theorem comp_qis :
    QuasiIso (SelmerDuality.GHom.toCC (FullPreComplex.incl M.isUnit_B) ≫ M.ψf) := by
  have := FullPreComplex.incl_quasiIso M.isUnit_B
  have := M.qisf
  infer_instance

/-- **The Selmer-phrased identification with the genuine family Selmer data** (PROVED). -/
def toSelmerIdentification : SelmerIdentification b dK hK cE tK :=
  selmerIdentificationOfGenuine K S' M.toIdentification M.Mf M.Δf
    (SelmerDuality.GHom.toCC (FullPreComplex.incl M.isUnit_B) ≫ M.ψf) M.comp_qis

/-- **The genuine unramified support comparison is a quasi-isomorphism** (PROVED from the PRINT
`NekovarProp788ii`, Nekovář 7.8.8(ii)). -/
theorem support_qis (h : NekovarProp788ii K) :
    QuasiIso (SelmerDuality.GHom.toCC
      (SelmerDuality.supportMap (galoisSupportData K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀))) :=
  supportChange_of_print K h hS M.p M.hset M.hS' M.ψur M.hψur M.Δ₀

/-! ### The quotient comparison of (5.6), derived -/

/-- The augmented model modulo `ρ`. -/
abbrev Cρ : FullPreComplex M.R₀ := (M.C.map (augR b)).map M.ρ

theorem hYρ : M.Cρ.Y = 0 := FullPreComplex.map_Y_zero _ M.ρ M.hY0

theorem hTρ : M.Cρ.T = 0 := FullPreComplex.map_T_zero _ M.ρ M.hT0

/-- The model sequence `C_old → C → (N --B--> N)` modulo `ρ` is short exact. -/
theorem model_shortExact : (FullPreComplex.oldSES M.hYρ M.hTρ).ShortExact :=
  FullPreComplex.oldSES_shortExact M.hYρ M.hTρ

/-- The genuine sequence `C(ur) → C(full) → ⊕_q Q_q` is short exact. -/
theorem genuine_shortExact : (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).ShortExact :=
  galoisFullSES_shortExact K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀

theorem square_g : (FullPreComplex.oldSES M.hYρ M.hTρ).f ≫ M.ψ0 ≫
    (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).g = 0 := by
  have h1 : (FullPreComplex.oldSES M.hYρ M.hTρ).f ≫ M.ψ0 =
      M.ψold ≫ (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).f := M.square.symm
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [h1]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (M.ψold ≫ ·) (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).zero).trans
    Limits.comp_zero

/-- **The induced map on the quotients of (5.6)**: from the model `N --B--> N` (degrees one and
two) to the genuine singular quotients `⊕_q C^•_cont(G_{K_q}, M₀) / C^•_cont(G_q/I_q, M₀)`
(the cokernel property of the model sequence). -/
def quotMap : (FullPreComplex.oldSES M.hYρ M.hTρ).X₃ ⟶
    (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).X₃ :=
  haveI := M.model_shortExact.epi_g
  M.model_shortExact.exact.desc (M.ψ0 ≫ (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).g)
    M.square_g

theorem quotMap_fac : (FullPreComplex.oldSES M.hYρ M.hTρ).g ≫ M.quotMap =
    M.ψ0 ≫ (galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀).g := by
  have := M.model_shortExact.epi_g
  exact M.model_shortExact.exact.g_desc _ _

/-- The morphism of the two short exact sequences of (5.6): `(ψold, ψ0, quotMap)`. -/
def sesHom : FullPreComplex.oldSES M.hYρ M.hTρ ⟶ galoisFullSES K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀ where
  τ₁ := M.ψold
  τ₂ := M.ψ0
  τ₃ := M.quotMap
  comm₁₂ := M.square
  comm₂₃ := M.quotMap_fac.symm

/-- **The quotient comparison of (5.6) is a quasi-isomorphism** (PROVED; the five lemma): the model
`N --B--> N` in degrees one and two computes the genuine singular quotients
`⊕_q C^•_cont(G_{K_q}, M₀) / C^•_cont(G_q/I_q, M₀)`. -/
theorem quotMap_quasiIso : QuasiIso M.quotMap := by
  have h₁ : QuasiIso M.sesHom.τ₁ := M.qisOld
  have h₂ : QuasiIso M.sesHom.τ₂ := M.qis0
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ M.sesHom M.model_shortExact
    M.genuine_shortExact h₁ h₂

end Identification3

/-- **The full condition satisfies `hfull`**: the relaxed (full) conditions everywhere have the
identity as condition map. -/
theorem hfull_relaxed {K : Type} [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
    (k : Type) [CommRing k] (Mf : Type) [AddCommGroup Mf] [Module k Mf]
    [DistribMulAction (GKS K S') Mf] [SMulCommClass (GKS K S') k Mf] [TopologicalSpace Mf]
    [ContinuousAdd Mf] [ContinuousConstSMul k Mf] [ContinuousSMul (GKS K S') Mf] :
    ∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places K S', v.1 ∉ S → ∀ n : ℤ,
      Function.Bijective
        (((ZInQ.Manuscript.RC.SelmerComplex.relaxedConditions k _ _ _ Mf :
          GaloisLocalConditions K S' k Mf).i v).f n n rfl) :=
  fun _ _ _ => Function.bijective_id

/-- **The inputs of RC0's `clearingTarget_of_complex`** (the body of `ClearingInputsCx`) from the
full-condition identification, transported cycles and functionals, and E1a (PROVED; `c := kmCoord`,
E1b `coordComputation_km`). -/
theorem clearingInputsCx_of_km3 {ℓ : ℕ} (Dd : RCData ℓ) (K : Type) [Field K] [NumberField K]
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification3 K S S' hS F.b dK hK cE tK)
        (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
        (μ : Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2 → MonoidAlgebra OO (SignGroup F.b))
        (hz : M.D.d1 *ᵥ z = 0) (hμ : μ ᵥ* M.D.d1 = 0) (κ η : MonoidAlgebra OO (SignGroup F.b)),
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink M.toIdentification.B κ η 0 e g (cOf M.D z μ hz hμ)) :
    ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
        CoordComputation I.B sd ε c I.D.RankOnePattern I.D.AcyclicPattern ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink I.B κ η 0 e g c := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  refine ⟨dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, M, z, μ, hz, hμ, κ, η, hlink⟩ := hF Co Ce F hFam
  exact ⟨M.toSelmerIdentification, sdOf M.D z μ M.oldC.Ai M.s M.s_ne
      (central_of_full _ M.s M.central_full), κ, -1, η, cOf M.D z μ hz hμ,
    coordComputation_km M.D z μ hz hμ M.oldC.Ai M.s M.s_ne (central_of_full _ M.s M.central_full),
    hlink⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
