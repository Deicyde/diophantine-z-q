import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.CoordE1b
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalConsistency
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances

/-!
# The identification over the genuine Selmer complexes

Manuscript `diophantine_zq.tex`, tex L5394–5425 (the new-local cancellation), L5486–5535 (the
remaining complex), L3470–3499 (the support change). Lane RC26 (`RC/SelmerComplex/`) built the
genuine continuous-cochain Selmer complexes `galoisSelData` over `G_{K,S}` and the genuine support
change `galoisSupportData` (Nekovář 7.8.8(ii), whose quasi-isomorphy is the PRINT
`NekovarProp788ii`). Their caveat: the abstract `UnramifiedNewPlace` / `SupportChangeUnramified`
(term isomorphisms with the three-term tame model) never hold for genuine continuous cochains,
whose terms are infinite. `Identification2` (`NewLocalModel.lean`) uses them; this file re-points
the identification to the genuine objects, keeping `Identification2` unchanged.

* `TameModelQIso` (the one named input "the tame model as a quasi-isomorphic model", on lane RC26's
  gap list): quasi-isomorphisms from the tame model `M --(Φ−1, 0)--> M² --(0, Φ−q)--> M` and the
  unramified condition `[Φ − 1]` (`tL`, `tU` of `NewLocalConsistency.lean`) to a full local complex
  and an unramified condition, compatible with the inclusions.
* `Identification2G K S S' hS b dK hK cE tK` (GLUE): the cancellation data of `Identification2`
  (a nonempty family of new local blocks indexed by the NEW PLACES `S' − S`, the pre-cancellation
  family model, `T₀ = Y₀ = 0`, the central Smith form, the budget), and on the Selmer side:
  - the family Selmer complex is genuine: `galoisSelData K S' 𝒪[G] M Δ`, quasi-isomorphic to the
    family model `C ⊗ 𝒪[G]`;
  - the support change is genuine: `galoisSupportData K hS R₀ M₀ ψ hψ Δ₀` over a finite coefficient
    ring `R₀` (a quotient of `Λ` via `ρ`) in Nekovář's finite setting, with the augmented family
    model and its old part quasi-isomorphic to the new- and old-support Selmer complexes,
    compatibly with the support comparison;
  - at every new place `q` the tame model of the actual Frobenius `Φ_q` on `M₀` is a
    quasi-isomorphic model of the genuine local complex `C^•_cont(G_{K_q}, M₀)` and the genuine
    unramified condition `C^•_cont(G_q/I_q, M₀)` (`TameModelQIso`), and the reduction of the local
    block `A_q` is the matrix of `Φ_q − q` (tex 5455–5463).
* PROVED: `toIdentification`, `toSelmerIdentification` (`selmerIdentificationOfGenuine`),
  `support_qis` (from the PRINT `NekovarProp788ii`), and `clearingInputsCx_of_kmG` (the body of
  RC0's `ClearingInputsCx` from `Identification2G`, transported cycle and functional, and E1a, with
  `c := kmCoord` and E1b `coordComputation_km`).

LESSON 2 (recorded, see notes): an instance with a nonempty set of new places needs genuine
continuous cochains of `G_{K_q}` quasi-isomorphic to a nonzero tame model (local Galois
cohomology) and a factorization `ψ_q` (lane RC26's GLUE `UnramifiedAtFactorization`); neither is
available, so no unconditional witness is given here. The cancellation part is witnessed by
`identification2_example` (`PlaceSupport.lean`).
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

/-! ### The tame model as a quasi-isomorphic model -/

/-- **The tame model is a quasi-isomorphic model** of a full local complex `L` and an unramified
condition `U` with inclusion `ι` (named input): quasi-isomorphisms from `tL M Φ q`, `tU M Φ`,
commuting with the inclusions. -/
structure TameModelQIso {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (Φ : M →ₗ[R] M) (q : ℕ) (L U : GCx R) (ι : GHom U L) where
  fL : (tL M Φ q).toCC ⟶ L.toCC
  fU : (tU M Φ).toCC ⟶ U.toCC
  qisL : QuasiIso fL
  qisU : QuasiIso fU
  comm : SelmerDuality.GHom.toCC (tιH M Φ q) ≫ fL = fU ≫ SelmerDuality.GHom.toCC ι

/-! ### Coefficient change of an upper triangular pre-cancellation complex -/

theorem PreComplex.map_Y_zero {S S' : Type} [CommRing S] [CommRing S'] (C : PreComplex S)
    (f : S →+* S') (h : C.Y = 0) : (C.map f).Y = 0 := by
  change C.Y.map f = 0
  rw [h, Matrix.map_zero _ (map_zero f)]

theorem PreComplex.map_T_zero {S S' : Type} [CommRing S] [CommRing S'] (C : PreComplex S)
    (f : S →+* S') (h : C.T = 0) : (C.map f).T = 0 := by
  change C.T.map f = 0
  rw [h, Matrix.map_zero _ (map_zero f)]

/-! ### The identification over the genuine Selmer complexes -/

variable (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
  (hS : S ⊆ S')

set_option maxHeartbeats 1000000 in
/-- **The identification of the remaining complex over the genuine Selmer complexes** (GLUE; see
the module docstring). -/
structure Identification2G [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    (b : ℕ) (dK hK cE tK : ℕ) where
  /-- the new places are the active primes: there is at least one -/
  [nQ : Nonempty (NewPlaces K S S')]
  /-- the index of a local block -/
  ιn : Type
  [fι : Fintype ιn]
  [dι : DecidableEq ιn]
  [nι : Nonempty ιn]
  /-- the new local blocks over `Λ`, one per new place -/
  A : NewPlaces K S S' → Matrix ιn ιn Lam
  dq : NewPlaces K S S' → ℕ
  hd : ∀ q, dq q ≤ 4
  v : NewPlaces K S S' → Lamˣ
  w : NewPlaces K S S' → Lam
  hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q
  /-- the pre-cancellation finite free family model over `Λ[G]` -/
  C : PreComplex (MonoidAlgebra Lam (SignGroup b))
  eN : C.N ≃ ιn × NewPlaces K S S'
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
  budget : BudgetInputsAt ((remOf A dq hd v w hdet C eN hB0).toSmithBlocks (O := OO)
    ((C.map (augR b)).old hY0 hT0).Ai s s_ne
      (central_of_full _ s central_full)) fr₀ dK hK cE tK
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
  /-- `C ⊗ 𝒪[G]` is a model of the GENUINE family Selmer complex -/
  ψf : (C.map (φO b)).toGCx.toCC ⟶ (selCx (galoisSelData K S' _ Mf Δf)).toCC
  qisf : QuasiIso ψf
  /-- the finite coefficient ring of the support comparison, a quotient of `Λ` -/
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
  /-- the augmented family model modulo `ρ` models the GENUINE new-support Selmer complex -/
  ψ0 : ((C.map (augR b)).map ρ).toGCx.toCC ⟶
    (selCx (galoisSupportData K hS R₀ M₀ ψur hψur Δ₀).Dp).toCC
  qis0 : QuasiIso ψ0
  /-- the augmented old part modulo `ρ` models the GENUINE old-support Selmer complex -/
  ψold : (((C.map (augR b)).map ρ).old (PreComplex.map_Y_zero _ ρ hY0)
      (PreComplex.map_T_zero _ ρ hT0)).toGCx.toCC ⟶
    (selCx (galoisSupportData K hS R₀ M₀ ψur hψur Δ₀).D).toCC
  qisOld : QuasiIso ψold
  /-- compatibility with the genuine support comparison -/
  square : ψold ≫ SelmerDuality.GHom.toCC
      (SelmerDuality.supportMap (galoisSupportData K hS R₀ M₀ ψur hψur Δ₀)) =
    SelmerDuality.GHom.toCC (((C.map (augR b)).map ρ).oldIncl (PreComplex.map_Y_zero _ ρ hY0)
      (PreComplex.map_T_zero _ ρ hT0)) ≫ ψ0
  /-- the Frobenius of the new place `q` on `M₀`, and its residue cardinality -/
  Φq : NewPlaces K S S' → (M₀ →ₗ[R₀] M₀)
  qq : NewPlaces K S S' → ℕ
  qq_odd : ∀ q, Odd (qq q)
  /-- bases of `M₀` indexed by the local block index -/
  bas : NewPlaces K S S' → Module.Basis ιn R₀ M₀
  /-- the local block reduces to the actual tame differential `Φ_q − q` (tex 5455–5463) -/
  hA : ∀ q, (A q).map ρ =
    LinearMap.toMatrix (bas q) (bas q) (Φq q - ((qq q : ℕ) : R₀) • LinearMap.id)
  /-- **the tame model is a quasi-isomorphic model** of the genuine local complex and the genuine
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

namespace Identification2G

attribute [instance] fι dι nι Mf_acg Mf_mod Mf_act Mf_comm Mf_top Mf_cadd Mf_csmul Mf_cact
  R₀_ring R₀_local M₀_acg M₀_mod M₀_act M₀_comm M₀_top M₀_disc M₀_cact M₀_fin

variable {K S S' hS} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {b : ℕ}
  {dK hK cE tK : ℕ} (M : Identification2G K S S' hS b dK hK cE tK)

/-- The new local block as a family over `ι × Q`. -/
abbrev Bsub : Matrix (M.ιn × NewPlaces K S S') (M.ιn × NewPlaces K S S')
    (MonoidAlgebra Lam (SignGroup b)) :=
  M.C.B.submatrix M.eN.symm M.eN.symm

theorem isUnit_B : IsUnit (M.C.map (φO b)).B.det :=
  isUnit_B_of M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0

/-- **The remaining complex**: the cancellation of the new local block over `𝒪[G]`. -/
def D : BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  remOf M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0

/-- The augmented old part over `Λ`. -/
abbrev oldC : BlockComplex Lam := (M.C.map (augR b)).old M.hY0 M.hT0

theorem d2_map_aug : M.D.d2.map (augS b) = (M.C.P.map (augR b)).map (algebraMap Lam OO) := by
  change (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
    M.C.T.map (φO b)).map (augS b) = _
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_φO_aug, map_φO_aug M.C.T,
    M.hT0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, sub_zero]

/-- **Full augmentation compatibility** (PROVED from `T₀ = 0`). -/
theorem aug_full : M.D.d0.map (augS b) = M.oldC.d0.map (algebraMap Lam OO) ∧
    M.D.d1.map (augS b) = M.oldC.d1.map (algebraMap Lam OO) ∧
    M.D.d2.map (augS b) = M.oldC.d2.map (algebraMap Lam OO) :=
  ⟨map_φO_aug M.C.c0, map_φO_aug M.C.X, M.d2_map_aug⟩

theorem aug_eq (i : ℕ) :
    (M.D.Ai i).map aug = (M.oldC.Ai i).map (algebraMap Lam OO) := by
  match i with
  | 0 => exact Matrix.ext fun j k => aug_φO (M.C.c0 (Sum.inl j) k)
  | 1 => exact Matrix.ext fun j k => aug_φO (M.C.X (Sum.inl j) (Sum.inr (Sum.inr k)))
  | 2 => exact Matrix.ext fun j k => congrArg (fun N => N j (Sum.inr (Sum.inr k))) M.d2_map_aug
  | _ + 3 => exact Matrix.ext fun j => j.elim0

/-- **The sign-evaluated surviving differential is the Schur complement of the new-local family**
(PROVED; one cancellation). -/
theorem poles2 : IsNewLocalSchur (b := b) fun x => M.D.d2.map (Determinant.signEval (sgnChar x)) := by
  refine ⟨NewPlaces K S S', M.ιn, inferInstance, inferInstance, inferInstance, inferInstance, M.A,
    M.dq, M.hd, M.v, M.w, M.hdet, M.Bsub, M.hB0, Fin M.D.m2, Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2,
    inferInstance, inferInstance, M.C.P, M.C.Q.submatrix id M.eN.symm,
    M.C.T.submatrix M.eN.symm id, 1, 1, fun x => ?_⟩
  set f := (Determinant.signEval (O := OO) (sgnChar x)).toRingHom
  have hB : IsUnit (M.C.B.map (φO b)).det := M.isUnit_B
  have h1 : M.D.d2.map (Determinant.signEval (sgnChar x)) =
      (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
        M.C.T.map (φO b)).map f := rfl
  set Px := (M.C.P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Qx := (M.C.Q.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Bx := (M.C.B.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Tx := (M.C.T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  have hL : M.D.d2.map (Determinant.signEval (sgnChar x)) = Px - Qx * Bx⁻¹ * Tx := by
    rw [h1, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      map_inv_of_isUnit f _ hB]
    change (M.C.P.map (φO b)).map (Determinant.signEval (sgnChar x)) -
        (M.C.Q.map (φO b)).map (Determinant.signEval (sgnChar x)) *
          ((M.C.B.map (φO b)).map (Determinant.signEval (sgnChar x)))⁻¹ *
          (M.C.T.map (φO b)).map (Determinant.signEval (sgnChar x)) = _
    rw [map_φO_signEval, map_φO_signEval, map_φO_signEval, map_φO_signEval]
  have hR : (1 : Matrix (Fin M.C.m2) (Fin M.C.m2) Lam).map (algebraMap Lam OO) *
      (Px - (Qx.submatrix id M.eN.symm) * (Bx.submatrix M.eN.symm M.eN.symm)⁻¹ *
        (Tx.submatrix M.eN.symm id)) *
      (1 : Matrix (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) Lam).map
        (algebraMap Lam OO) = Px - Qx * Bx⁻¹ * Tx := by
    rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  exact hL.trans hR.symm

/-- **The identification, derived** (PROVED). -/
def toIdentification : Identification b dK hK cE tK where
  D := M.D
  A0 := M.oldC.Ai
  s := M.s
  s_ne := M.s_ne
  central := central_of_full _ M.s M.central_full
  aug_eq := M.aug_eq
  poles0 := Identification2.isNewLocalSchur_lam M.C.c0
  poles1 := Identification2.isNewLocalSchur_lam M.C.X
  poles2 := M.poles2
  budget := budgetInputs_of_at M.budget

theorem comp_qis : QuasiIso (SelmerDuality.GHom.toCC (PreComplex.incl M.isUnit_B) ≫ M.ψf) := by
  have := PreComplex.incl_quasiIso M.isUnit_B
  have := M.qisf
  infer_instance

/-- **The Selmer-phrased identification with the GENUINE family Selmer data** (PROVED; lane RC26's
`selmerIdentificationOfGenuine`, `sel := galoisSelData K S' 𝒪[G] M Δ`). -/
def toSelmerIdentification : SelmerIdentification b dK hK cE tK :=
  selmerIdentificationOfGenuine K S' M.toIdentification M.Mf M.Δf
    (SelmerDuality.GHom.toCC (PreComplex.incl M.isUnit_B) ≫ M.ψf) M.comp_qis

/-- **The genuine support comparison is a quasi-isomorphism** (PROVED from the PRINT
`NekovarProp788ii`, Nekovář 7.8.8(ii), in the finite setting carried by the identification). -/
theorem support_qis (h : NekovarProp788ii K) :
    QuasiIso (SelmerDuality.GHom.toCC
      (SelmerDuality.supportMap (galoisSupportData K hS M.R₀ M.M₀ M.ψur M.hψur M.Δ₀))) :=
  supportChange_of_print K h hS M.p M.hset M.hS' M.ψur M.hψur M.Δ₀

end Identification2G

/-- **The inputs of RC0's `clearingTarget_of_complex`** (the body of `ClearingInputsCx`) from the
identification over the GENUINE Selmer complexes, transported cycles and functionals, and E1a
(PROVED; `c := kmCoord`, E1b `coordComputation_km`). -/
theorem clearingInputsCx_of_kmG {ℓ : ℕ} (Dd : RCData ℓ) (K : Type) [Field K] [NumberField K]
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification2G K S S' hS F.b dK hK cE tK)
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
