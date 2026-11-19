import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Frob
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresStage
import ZInQKernel.Contrib.RC53Assist.FrobeniusMatch.Arithmetic

/-!
# The stage Frobenius identifications at the leaf

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): at an unused
good split prime `q` with places `w`, `w' = κ(w)`, the quotient blocks carry `z Fr_q` and
`z⁻¹ Fr_q` (tex 4178–4182), `z` the scalar Frobenius value (tex 4144–4145, 4286–4292), and
"Conjugation sends `z` to `z⁻¹`" (tex 4171); with `M_i = (T₂E ⊗ A_i)(χ_h Ψ_i)` (tex 2724–2727),
the prescription `ξ_i(Fr_q) = 1` (tex 2731–2736) and `α_i^τ = α_i⁻¹` (tex 2778–2796), at a stage
of the inner limit (tex 4385–4451). Lane RC32's round twelve states the arithmetic inputs as named
Props; here they are closed at the leaf's values `leafFrobΛ C Fam x ps`.

* (1) `stageBasis`, `stageBasis_baseChangeAct`: the stage basis of `A_s ⊗ E(K_S)[2^s]` induced by
  a basis of lane RC28's `T₂E`, in which `id ⊗ σ` has the stage image of the matrix of `σ`;
  `frobMatrixAt_frobMatStage`, `urFrobElt_conj_of_above`, **`exists_frobMatrixAt_frobMatStage`**:
  `FrobMatrixAt` with the matrix `frobMatStage C q s` of the leaf, from `FrobQFixes` and the data
  `SplitPlacesAt`.
* (2) `quadChar_gksOfQ_frobQ`, `quadChar_urFrobElt_split`, **`charValueAt_alphaStage_of_quad`**,
  `stageMk_zAt`: `CharValueAt` for lane E2's `alphaStage` with the leaf's `zAt`, from
  `MovingValueAt`; `alphaChar_eq_alphaStage`, `movingValueAt_of_xi` for lane RC28's `alphaChar`.
* (3) **`frobConjugatePlaces_proved`**: the round-twelve input `FrobConjugatePlaces` holds.
* (4) **`stageCoefEquiv`**, `stageCoefEquiv_smul`, `stageInflEquiv`, `mcoefModuleK_stage_eq`,
  **`stageChainFrobE2`**: lane E2's module over the stage ring (its `mcoefModuleK`) is the actual
  module over the stage ring, equivariantly, and carries the Frobenius fields.
* (5) **`nonempty_stageChainFrob_leaf`**, **`nonempty_stageChainFrob_leaf_E2`**: the `D` of
  `GenuineStageSteps.ofFrob` at the leaf's values, from `LeafStepInputs` at each step.

Remaining inputs: `FrobQFixes` (GLUE; PROVED for `K = ℚ(√k)`, `(k/q) = 1` by
`frobQFixes_of_sqrt`), `MovingValueAt` and `MovingAnticyclotomic` (GLUE: the prescribed value and
the anticyclotomy of the moving character, tex 2731–2736, 2781–2788), and the data
`SplitPlacesAt`.

Kinds: definitions, PROVED, and GLUE (the input statements).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Limits (stageIdeal stageEquiv stageMap)
open ZInQ.Manuscript.RC.Uniform (Lambda)

section StageBasis

/-- **The reduction `ℤ₂ → Λ → Λ ⧸ stageIdeal s`** to the coefficient stage (tex 4385–4451,
4444–4448). Kind: definition. -/
abbrev stageC (s : ℕ) : ℤ_[2] →+* StageRing s := (stageMk s).comp PowerSeries.C

/-- `2^s ↦ 0` in the stage ring (tex 4385–4451: `2^s ∈ stageIdeal s`). Kind: PROVED. -/
theorem stageC_two_pow (s : ℕ) : stageC s ((2 : ℤ_[2]) ^ s) = 0 := by
  show stageMk s (PowerSeries.C ((2 : ℤ_[2]) ^ s)) = 0
  rw [map_pow, map_ofNat]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

/-- The stage image of `c ∈ ℤ₂` is that of its residue `c mod 2^s` (tex 4385–4451).
Kind: PROVED. -/
theorem stageC_eq_resN (s : ℕ) (c : ℤ_[2]) : stageC s c = (resN s c : StageRing s) := by
  have hker : c - (resN s c : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ s} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, resN,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hker
  have h0 : stageC s c - stageC s (resN s c : ℤ_[2]) = 0 := by
    rw [← map_sub, ← hd, map_mul, Nat.cast_ofNat, stageC_two_pow, mul_zero]
  rw [sub_eq_zero.mp h0, map_natCast]

/-- The `A_s`-linear extension `a ⊗ m ↦ a • f m` of an additive map into `A_s²` (tex
2724–2727). Kind: definition. -/
def stageVecLift (s : ℕ) {M : Type} [AddCommGroup M] (f : M →+ (Fin 2 → StageRing s)) :
    StageRing s ⊗[ℤ] M →ₗ[StageRing s] (Fin 2 → StageRing s) :=
  @LinearMap.liftBaseChange ℤ M (Fin 2 → StageRing s) (StageRing s) _ _ _ _ _ _ _ _
    AddCommGroup.intIsScalarTower f.toIntLinearMap

/-- `stageVecLift` on pure tensors (tex 2724–2727). Kind: PROVED. -/
theorem stageVecLift_tmul (s : ℕ) {M : Type} [AddCommGroup M] (f : M →+ (Fin 2 → StageRing s))
    (a : StageRing s) (m : M) : stageVecLift s f (a ⊗ₜ[ℤ] m) = a • f m :=
  @LinearMap.liftBaseChange_tmul ℤ M (Fin 2 → StageRing s) (StageRing s) _ _ _ _ _ _ _ _
    AddCommGroup.intIsScalarTower f.toIntLinearMap a m

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- The projection `T₂E → E(K_S)[2^s]` turns `ℤ₂`-scalars into their residues (tex
2836–2838). Kind: PROVED. -/
theorem projLev_padicSmul (s : ℕ) (c : ℤ_[2]) (P : TateS K S W) :
    projLev s (c • P) = resN s c • projLev s P := rfl

variable (b : Module.Basis (Fin 2) ℤ_[2] (TateS K S W)) (s : ℕ)

/-- The stage coordinates of a point of `T₂E` in the basis `b` (tex 2836–2838, 4385–4451).
Kind: definition. -/
def tateStageCoord : TateS K S W →+ (Fin 2 → StageRing s) where
  toFun P i := stageC s (b.repr P i)
  map_zero' := by
    funext i
    simp
  map_add' P Q := by
    funext i
    simp

/-- The stage coordinates, entrywise (tex 2836–2838). Kind: PROVED. -/
theorem tateStageCoord_apply (P : TateS K S W) (i : Fin 2) :
    tateStageCoord b s P i = stageC s (b.repr P i) := rfl

/-- The stage coordinates of a basis vector are a standard vector (tex 2836–2838).
Kind: PROVED. -/
theorem tateStageCoord_basis (i : Fin 2) : tateStageCoord b s (b i) = Pi.single i 1 := by
  funext j
  rw [tateStageCoord_apply, Module.Basis.repr_self]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- The stage coordinates vanish on `2^s T₂E`, the kernel of the projection to
`E(K_S)[2^s]` (tex 2836–2838, 4385–4451). Kind: PROVED. -/
theorem ker_projLev_le_tateStageCoord :
    (projLev (K := K) (S := S) (W := W) s).ker ≤ (tateStageCoord b s).ker := by
  intro P hP
  obtain ⟨Q, rfl⟩ := (mem_ker_projLev_iff s P).mp (congrArg Subtype.val hP)
  rw [AddMonoidHom.mem_ker]
  funext i
  rw [tateStageCoord_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, stageC_two_pow,
    zero_mul]
  rfl

/-- The matrix of `σ ∈ G_{K,S}` on `T₂E` in the basis `b` (tex 2836–2838). Kind: definition. -/
abbrev tateMat (σ : GKS K S) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  LinearMap.toMatrix b b (DistribSMul.toLinearMap ℤ_[2] (TateS K S W) σ)

/-- **The stage coordinates of `σ P`**: the stage image of the matrix of `σ` in `b`, applied to
the stage coordinates of `P` (tex 2836–2838, 4176–4184). Kind: PROVED. -/
theorem tateStageCoord_smul (σ : GKS K S) (P : TateS K S W) :
    tateStageCoord b s (σ • P) =
      Matrix.toLin' ((tateMat b σ).map (stageC s)) (tateStageCoord b s P) := by
  funext i
  rw [Matrix.toLin'_apply, tateStageCoord_apply]
  have h := congrFun (LinearMap.toMatrix_mulVec_repr b b
    (DistribSMul.toLinearMap ℤ_[2] (TateS K S W) σ) P) i
  rw [DistribSMul.toLinearMap_apply] at h
  rw [← h, RingHom.map_mulVec]
  rfl

variable [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The stage coordinates of a point of `E(K_S)[2^s]`: those of any lift to `T₂E`
(tex 2836–2838, 4385–4451). Kind: definition. -/
def levStageCoord : Lev K S W s →+ (Fin 2 → StageRing s) :=
  (QuotientAddGroup.lift _ (tateStageCoord b s) (ker_projLev_le_tateStageCoord b s)).comp
    (LambdaCoef.tateQuotEquiv (K := K) (S := S) (W := W) s).symm.toAddMonoidHom

/-- The stage coordinates of a projected point are those of the point (tex 2836–2838).
Kind: PROVED. -/
theorem levStageCoord_projLev (P : TateS K S W) :
    levStageCoord b s (projLev s P) = tateStageCoord b s P := by
  rw [levStageCoord, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ← LambdaCoef.tateQuotEquiv_mk, AddEquiv.symm_apply_apply]
  rfl

/-- Natural scalars move across `⊗[ℤ]` (tex 2724–2727). Kind: PROVED. -/
theorem nsmul_tmul_eq {A M : Type} [CommRing A] [AddCommGroup M] (n : ℕ) (a : A) (m : M) :
    (n • a) ⊗ₜ[ℤ] m = a ⊗ₜ[ℤ] (n • m) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, TensorProduct.tmul_add, ih]

/-- **The stage basis of `A_s ⊗ E(K_S)[2^s]` induced by a Tate basis** (tex 2724–2727,
2836–2838, 4385–4451). Kind: definition. -/
def stageBasis : StageRing s ⊗[ℤ] Lev K S W s ≃ₗ[StageRing s] (Fin 2 → StageRing s) :=
  LinearEquiv.ofLinearMap
    (stageVecLift s (levStageCoord b s))
    ((Pi.basisFun (StageRing s) (Fin 2)).constr (StageRing s)
      fun i => (1 : StageRing s) ⊗ₜ[ℤ] projLev s (b i))
    (by
      apply (Pi.basisFun (StageRing s) (Fin 2)).ext
      intro i
      rw [LinearMap.comp_apply, Module.Basis.constr_basis, stageVecLift_tmul,
        one_smul, Pi.basisFun_apply, LinearMap.id_apply]
      exact (levStageCoord_projLev b s (b i)).trans (tateStageCoord_basis b s i))
    (by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul a P =>
        obtain ⟨P', rfl⟩ := projLev_surjective (K := K) (S := S) (W := W) s P
        rw [LinearMap.comp_apply, stageVecLift_tmul, LinearMap.id_apply,
          Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun]
        change ∑ i, (a • levStageCoord b s (projLev s P')) i • ((1 : StageRing s) ⊗ₜ[ℤ]
          projLev s (b i)) = a ⊗ₜ[ℤ] projLev s P'
        conv_rhs => rw [← b.sum_repr P', map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [levStageCoord_projLev, Pi.smul_apply, tateStageCoord_apply, stageC_eq_resN,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul, mul_comm,
          ← nsmul_eq_mul, nsmul_tmul_eq, projLev_padicSmul]
      | add x y hx hy => rw [map_add, hx, hy, map_add])

/-- The stage basis on pure tensors (tex 2724–2727, 2836–2838). Kind: PROVED. -/
theorem stageBasis_tmul (a : StageRing s) (P : TateS K S W) :
    stageBasis b s (a ⊗ₜ[ℤ] projLev s P) = a • tateStageCoord b s P := by
  rw [stageBasis, LinearEquiv.coe_ofLinearMap, stageVecLift_tmul]
  exact congrArg (a • ·) (levStageCoord_projLev b s P)

/-- **The matrix of `id ⊗ σ` in the stage basis** is the stage image of the matrix of `σ` on
`T₂E` in `b` (tex 2724–2727, 2836–2838, 4176–4184, 4385–4451). Kind: PROVED. -/
theorem stageBasis_baseChangeAct (σ : GKS K S) (x : StageRing s ⊗[ℤ] Lev K S W s) :
    stageBasis b s (baseChangeAct (StageRing s) (Lev K S W s) σ x) =
      Matrix.toLin' ((tateMat b σ).map (stageC s)) (stageBasis b s x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a P =>
    obtain ⟨P', rfl⟩ := projLev_surjective (K := K) (S := S) (W := W) s P
    rw [baseChangeAct_tmul, ← projLev_smul, stageBasis_tmul, stageBasis_tmul,
      tateStageCoord_smul, LinearMap.map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end StageBasis


/-! ### The leaf's Frobenius matrix in a stage basis -/

section LeafMatrix

open ZInQ.Contrib.RC53Assist.InnerLimitArith (basisK gksOfQ)

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/-- **The stage image of the leaf's Frobenius matrix** `frobMat C q` (tex 4176–4184,
4385–4451): the matrix `Fr` of `leafFrobΛ` reduced to the stage (`StageFrobAt`).
Kind: definition. -/
abbrev frobMatStage (C : TateCoef E) (q s : ℕ) : Matrix (Fin 2) (Fin 2) (StageRing s) :=
  ((frobMat C q).map PowerSeries.C).map (stageMk s)

/-- **The stage basis of lane RC28's `tateBasis`, transported along `γ ∈ G_{K,S}`**
(tex 2836–2838, 4176–4184): `stageBasis tateBasis ∘ (id ⊗ γ⁻¹)`. Kind: definition. -/
def tateStageBasis (C : TateCoef E) (s : ℕ) (γ : GKS C.K C.S) :
    StageRing s ⊗[ℤ] Lev C.K C.S (E.baseChange C.K) s ≃ₗ[StageRing s] (Fin 2 → StageRing s) :=
  (LinearEquiv.baseChange ℤ (StageRing s) _ _
    (DistribMulAction.toAddEquiv (Lev C.K C.S (E.baseChange C.K) s) γ⁻¹).toIntLinearEquiv).trans
    (stageBasis (basisK C.S E) s)

/-- **The leaf's Frobenius matrix in the stage basis** (tex 4144–4145, 4176–4184,
4209–4213): if `Fr_q` fixes `K` and `Frob_w = γ Fr_q|_{K_S} γ⁻¹`, then `id ⊗ Frob_w` has the
matrix `frobMatStage C q s` in `tateStageBasis C s γ` (`frobMat_eq_native`). Kind: PROVED. -/
theorem frobMatrixAt_frobMatStage (C : TateCoef E) {q : ℕ}
    (hfix : ∀ x : C.K, frobQ q (C.e (algebraMap C.K (AlgebraicClosure C.K) x)) =
      C.e (algebraMap C.K (AlgebraicClosure C.K) x))
    {S : Set (HeightOneSpectrum (𝓞 C.K))} (w : NewPlaces C.K C.S S) (s : ℕ) {γ : GKS C.K C.S}
    (hγ : urFrobElt C.K w = γ * gksOfQ C.S C.e (frobQ q) hfix * γ⁻¹) :
    FrobMatrixAt (tateStageBasis C s γ) w (frobMatStage C q s) := by
  intro x
  have hF : ∀ y, stageBasis (basisK C.S E) s
      (baseChangeAct (StageRing s) _ (gksOfQ C.S C.e (frobQ q) hfix) y) =
        Matrix.toLin' (frobMatStage C q s) (stageBasis (basisK C.S E) s y) := by
    intro y
    rw [stageBasis_baseChangeAct, tateMat, ← frobMat_eq_native]
    rfl
  refine toLin'_transport (stageBasis (basisK C.S E) s) (gksOfQ C.S C.e (frobQ q) hfix)
    (urFrobElt C.K w) (DistribMulAction.toAddEquiv _ γ⁻¹) (fun t => ?_) _ hF x
  change γ⁻¹ • urFrobElt C.K w • t = gksOfQ C.S C.e (frobQ q) hfix • γ⁻¹ • t
  rw [hγ, smul_smul, smul_smul, mul_assoc γ, inv_mul_cancel_left]

end LeafMatrix

/-! ### The Frobenius at a place and the rational Frobenius -/

section FrobConj

open ZInQ.Contrib.RC53Assist.InnerLimitArith (gksOfQ galKOfQ galKOfQ_apply MovingLabel)
open ZInQ.Contrib.RC53Assist.FrobeniusMatch (integersEquiv rational_isArithFrobAt
  label_frobenius_conjugate localPrime localPrime_under decompMap_isArithFrobAt)
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (frobElt eUr frobElt_eUr)

variable {K : Type} [Field K] [NumberField K]

/-- **A rational Frobenius fixing `K` is an arithmetic Frobenius over `K`** at the compatible
prime, when the prime of `K` below it has `p` elements (tex 4144–4145, 4209–4213).
Kind: PROVED. -/
theorem galKOfQ_isArithFrobAt (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (g : GalQ) (p : ℕ)
    [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime] (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hF : ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P)
    (hgK : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x))
    (v : HeightOneSpectrum (𝓞 K)) (hPv : (P.comap (integersEquiv e)).under (𝓞 K) = v.asIdeal)
    (hcard : Nat.card (𝓞 K ⧸ v.asIdeal) = p) :
    IsArithFrobAt (𝓞 K) (galKOfQ e g hgK) (P.comap (integersEquiv e)) := by
  have hF' := rational_isArithFrobAt g p P hP hF
  intro x
  change galKOfQ e g hgK • x - x ^ Nat.card (𝓞 K ⧸ (P.comap (integersEquiv e)).under (𝓞 K)) ∈
    P.comap (integersEquiv e)
  rw [hPv, hcard, Ideal.mem_comap, map_sub, map_pow]
  have he : integersEquiv e (galKOfQ e g hgK • x) = g • integersEquiv e x := by
    apply RingOfIntegers.ext
    change e (galKOfQ e g hgK (x : AlgebraicClosure K)) = g (e (x : AlgebraicClosure K))
    rw [galKOfQ_apply, AlgEquiv.apply_symm_apply]
  rw [he]
  have h2 : g • integersEquiv e x - integersEquiv e x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P :=
    hF' (integersEquiv e x)
  rwa [hP, ZInQ.Contrib.ChebFD.C10.card_quot] at h2

variable {S₀ S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The Frobenius at `w` is conjugate to a rational Frobenius at a prime above `w`**
(tex 3478–3487, 4144–4145): the arithmetic-label files' `label_frobenius_conjugate` (local
Frobenius lift, decomposition embedding, prime transitivity, unramified uniqueness).
Kind: PROVED. -/
theorem urFrobElt_conj_of_above (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (g : GalQ) (p : ℕ)
    [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime] (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hF : ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P)
    (hgK : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x))
    (w : NewPlaces K S₀ S) (hPw : (P.comap (integersEquiv e)).under (𝓞 K) = w.1.asIdeal)
    (hcard : Nat.card (𝓞 K ⧸ w.1.asIdeal) = p) :
    ∃ γ : GKS K S₀, urFrobElt K w = γ * gksOfQ S₀ e g hgK * γ⁻¹ :=
  label_frobenius_conjugate S₀ (MovingLabel.ofPrimes (fun _ => w.1) (fun _ => w.2.2)) 0
    (P.comap (integersEquiv e)) hPw (galKOfQ e g hgK)
    (galKOfQ_isArithFrobAt e g p P hP hF hgK w.1 hPw hcard)

/-- `κ² = 1` for the restriction `κ = τ|_K` of an actual complex conjugation (tex 2778).
Kind: PROVED. -/
theorem actualConj_kappa_kappa (C : ActualConj K S₀) (x : K) : C.κ (C.κ x) = x := by
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← C.hτ, ← C.hτ, C.hinv]

/-- The Frobenius at a new place is the restriction of the decomposition image of a local
Frobenius lift (tex 3478–3487). Kind: PROVED. -/
theorem urFrobElt_eq_resAbsCont (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : urRes K w.1 φ = frobElt (eUr K w.1)) :
    urFrobElt K w = resAbsCont K S₀ (decompMap K w.1 φ) := by
  change urFactor K w (frobElt (eUr K w.1)) = locMap K S₀ w.1 φ
  rw [urFactor_spec K w φ, hφ]

/-- **(3) The round-twelve input `FrobConjugatePlaces` holds** (tex 2778–2796, 4171,
4176–4184): `τ σ τ⁻¹` is an arithmetic Frobenius at `τ 𝔓` above `κ(w)` when `σ` is one at
`𝔓` above `w` (`decompMap_isArithFrobAt`, `resAbs_conjAbs`), and the label comparison at
`κ(w)` gives the conjugator. Kind: PROVED. -/
theorem frobConjugatePlaces_proved (S : Set (HeightOneSpectrum (𝓞 K))) (C : ActualConj K S₀) :
    FrobConjugatePlaces S C := by
  intro w w' hw'
  obtain ⟨φ, hφ⟩ := urRes_surjective K w.1 (frobElt (eUr K w.1))
  have hφ' : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ := by
    change urRes K w.1 φ = _
    rw [hφ, frobElt_eUr]
  have hP := decompMap_isArithFrobAt w.1 φ hφ'
  set σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w.1 φ) with hσ
  let τO : 𝓞 (AlgebraicClosure K) ≃+* 𝓞 (AlgebraicClosure K) := RingOfIntegers.mapRingEquiv C.τ
  let Q : Ideal (𝓞 (AlgebraicClosure K)) := (localPrime w.1).comap τO.symm
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQu : Q.under (𝓞 K) = w'.1.asIdeal := by
    rw [hw']
    ext x
    have h1 : x ∈ (conjPlace C.κ w.1).asIdeal ↔
        (RingOfIntegers.mapRingEquiv C.κ).symm x ∈ w.1.asIdeal := by
      change x ∈ w.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) ↔ _
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
    have hcomp : τO.symm (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure K)) x) =
        algebraMap (𝓞 K) (𝓞 (AlgebraicClosure K)) ((RingOfIntegers.mapRingEquiv C.κ).symm x) := by
      apply τO.injective
      rw [RingEquiv.apply_symm_apply]
      apply RingOfIntegers.ext
      change algebraMap K (AlgebraicClosure K) (x : K) =
        C.τ (algebraMap K (AlgebraicClosure K)
          (((RingOfIntegers.mapRingEquiv C.κ).symm x : 𝓞 K) : K))
      rw [C.hτ]
      congr 1
      exact (congrArg Subtype.val (RingEquiv.apply_symm_apply
        (RingOfIntegers.mapRingEquiv C.κ) x)).symm
    rw [Ideal.mem_under, Ideal.mem_comap, h1, hcomp, ← localPrime_under w.1]
    exact Iff.rfl
  have hcard : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) =
      Nat.card (𝓞 K ⧸ (localPrime w.1).under (𝓞 K)) := by
    rw [hQu, localPrime_under, hw']
    exact Nat.card_congr (Ideal.quotientEquiv w.1.asIdeal (conjPlace C.κ w.1).asIdeal
      (RingOfIntegers.mapRingEquiv C.κ) rfl).toEquiv.symm
  have hQ : IsArithFrobAt (𝓞 K) (conjAbs K C.κ C.τ C.hτ σ) Q := by
    intro x
    change conjAbs K C.κ C.τ C.hτ σ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [hcard, Ideal.mem_comap]
    have hx : τO.symm (conjAbs K C.κ C.τ C.hτ σ • x) = σ • τO.symm x := by
      apply RingOfIntegers.ext
      change C.τ.symm (C.τ (σ (C.τ.symm (x : AlgebraicClosure K)))) =
        σ (C.τ.symm (x : AlgebraicClosure K))
      rw [RingEquiv.symm_apply_apply]
    change τO.symm (conjAbs K C.κ C.τ C.hτ σ • x -
      x ^ Nat.card (𝓞 K ⧸ (localPrime w.1).under (𝓞 K))) ∈ localPrime w.1
    rw [map_sub, map_pow, hx]
    exact hP (τO.symm x)
  obtain ⟨g, hg⟩ := label_frobenius_conjugate S₀
    (MovingLabel.ofPrimes (fun _ => w'.1) (fun _ => w'.2.2)) 0 Q hQu _ hQ
  refine ⟨g, ?_⟩
  change (MovingLabel.ofPrimes (fun _ => w'.1) (fun _ => w'.2.2)).frob 0 = _
  rw [hg, urFrobElt_eq_resAbsCont w φ hφ, ActualConj.conj_apply]
  exact congrArg (fun z => g * z * g⁻¹) (resAbs_conjAbs K C.κ C.τ C.hτ S₀ C.hS σ)

end FrobConj

/-! ### (1) The leaf's matrix at both places of a split prime -/

section LeafPlaces

open ZInQ.Contrib.RC53Assist.InnerLimitArith (gksOfQ)
open ZInQ.Contrib.RC53Assist.FrobeniusMatch (integersEquiv)
open ZInQ.Contrib.ChebFD.C10 (Zbar)

variable {E : WeierstrassCurve ℚ}

/-- **GLUE input: the chosen rational Frobenius `frobQ q` acts trivially on `K`** (tex
2720–2722: active primes split in `K`; a Frobenius at an unramified prime of residue degree one
has trivial decomposition image: Neukirch, Algebraic Number Theory, Ch. I §9). PROVED for
`K = ℚ(√k)` and `(k/q) = 1` by `frobQFixes_of_sqrt`. Kind: GLUE. -/
def FrobQFixes (C : TateCoef E) (q : ℕ) : Prop :=
  ∀ x : C.K, frobQ q (C.e (algebraMap C.K (AlgebraicClosure C.K) x)) =
    C.e (algebraMap C.K (AlgebraicClosure C.K) x)

/-- **The two places of the leaf above a split prime** (tex 2720–2722, 4142–4145): `w' = κ(w)`,
the primes of `𝒪_K` containing `q` are `w`, `w'`, both of residue cardinality `q` (data
conditions on the chain's places). Kind: definition. -/
structure SplitPlacesAt (C : TateCoef E) (Cc : ActualConj C.K C.S) (q : ℕ)
    {S : Set (HeightOneSpectrum (𝓞 C.K))} (w w' : NewPlaces C.K C.S S) : Prop where
  /-- the second place is the conjugate of the first -/
  conj : w'.1 = conjPlace Cc.κ w.1
  /-- the primes of `𝒪_K` containing `q` are the two places -/
  above : ∀ I : Ideal (𝓞 C.K), I.IsPrime → (q : 𝓞 C.K) ∈ I → I = w.1.asIdeal ∨ I = w'.1.asIdeal
  /-- the first place has residue cardinality `q` -/
  card : Nat.card (𝓞 C.K ⧸ w.1.asIdeal) = q
  /-- the second place has residue cardinality `q` -/
  card' : Nat.card (𝓞 C.K ⧸ w'.1.asIdeal) = q

/-- The data conditions are symmetric in the two places (tex 4171). Kind: PROVED. -/
theorem SplitPlacesAt.symm {C : TateCoef E} {Cc : ActualConj C.K C.S} {q : ℕ}
    {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K C.S S}
    (h : SplitPlacesAt C Cc q w w') : SplitPlacesAt C Cc q w' w where
  conj := by rw [h.conj, conjPlace_conjPlace _ (actualConj_kappa_kappa Cc)]
  above I hI hq := (h.above I hI hq).symm
  card := h.card'
  card' := h.card

variable [E.IsElliptic]

/-- **(1) The leaf's Frobenius matrix in a stage basis at a place of a split prime**
(tex 4144–4145, 4176–4184, 4209–4213): `FrobMatrixAt eT w (frobMatStage C q s)` for a stage
basis `eT` induced by `tateBasis`, from `FrobQFixes` and `SplitPlacesAt` (the prime of `ℤ̄`
defining `frobQ q` lies above `w` or `w'`; in the second case (3) transports). Kind: PROVED. -/
theorem exists_frobMatrixAt_frobMatStage (C : TateCoef E) (Cc : ActualConj C.K C.S) {q : ℕ}
    (hq : q.Prime) (hfix : FrobQFixes C q) {S : Set (HeightOneSpectrum (𝓞 C.K))}
    {w w' : NewPlaces C.K C.S S} (hpl : SplitPlacesAt C Cc q w w') (s : ℕ) :
    ∃ eT : StageRing s ⊗[ℤ] Lev C.K C.S (E.baseChange C.K) s ≃ₗ[StageRing s]
      (Fin 2 → StageRing s), FrobMatrixAt eT w (frobMatStage C q s) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPp, hPZ, hF⟩ := isFrobAtC10_frobQ hq
  have := hPp
  have hIp : ((P.comap (integersEquiv C.e)).under (𝓞 C.K)).IsPrime := Ideal.IsPrime.under _ _
  have hqI : (q : 𝓞 C.K) ∈ (P.comap (integersEquiv C.e)).under (𝓞 C.K) := by
    have hpP : ((q : ℕ) : Zbar) ∈ P := ZInQ.Contrib.ChebFD.HSyn.natCast_mem P q hPZ
    change integersEquiv C.e (algebraMap (𝓞 C.K) (𝓞 (AlgebraicClosure C.K)) (q : 𝓞 C.K)) ∈ P
    simpa only [map_natCast] using hpP
  rcases hpl.above _ hIp hqI with h | h
  · obtain ⟨γ, hγ⟩ := urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w h hpl.card
    exact ⟨_, frobMatrixAt_frobMatStage C hfix w s hγ⟩
  · obtain ⟨γ, hγ⟩ := urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w' h hpl.card'
    obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w' w hpl.symm.conj
    exact ⟨_, frobMatrixAt_conj Cc (E.baseChange C.K)
      (ZInQ.Manuscript.RC.KummerMaps.tate_baseChange_map_kappa E Cc) _ hg
      (frobMatrixAt_frobMatStage C hfix w' s hγ)⟩

end LeafPlaces

/-! ### (2) The character value at the Frobenius -/

section CharValue

open ZInQ.Contrib.RC53Assist.InnerLimitArith (gksOfQ galKOfQ galKOfQ_apply gksOfQ_lift)
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (sqrtQbar sqrtQbar_sq sqrtChar_apply sqrtChar_of_isFrobAt)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}

/-- The quadratic character of `√n` (`n ∈ ℤ`) at the restriction of `σ ∈ G_ℚ` fixing `K`
is trivial iff `σ` fixes `√n` in `ℚ̄` (tex 2724–2727, 2790–2791). Kind: PROVED. -/
theorem quadChar_gksOfQ_eq_one_iff (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0) {n : ℤ} (hn : h = (n : K))
    (σ : GalQ) (hσ : ∀ x : K, σ (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    quadChar sh hs hs0 (gksOfQ S₀ e σ hσ) = 1 ↔ σ (sqrtQbar n) = sqrtQbar n := by
  have hq1 : quadChar sh hs hs0 (gksOfQ S₀ e σ hσ) = 1 ↔
      galS K S₀ (gksOfQ S₀ e σ hσ) sh = sh := by
    unfold quadChar
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs with h1
    · exact ⟨fun _ => h1, fun _ => rfl⟩
    · exact ⟨fun h2 => absurd h2 (by decide), fun h2 => absurd h2 h1⟩
  have hlift := gksOfQ_lift S₀ e σ hσ sh
  rw [galKOfQ_apply] at hlift
  have hr2 : e (inclS K S₀ sh) ^ 2 = (n : Qbar) := by
    rw [← map_pow, ← map_pow, hs, AlgHom.commutes, hn, map_intCast, map_intCast]
  have hkey : galS K S₀ (gksOfQ S₀ e σ hσ) sh = sh ↔
      σ (e (inclS K S₀ sh)) = e (inclS K S₀ sh) := by
    constructor
    · intro h1
      rw [h1] at hlift
      exact e.symm_apply_eq.mp hlift
    · intro h1
      have h3 : inclS K S₀ (galS K S₀ (gksOfQ S₀ e σ hσ) sh) = inclS K S₀ sh := by
        rw [← hlift, h1, AlgEquiv.symm_apply_apply]
      exact (inclS K S₀).toRingHom.injective h3
  rw [hq1, hkey]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hr2.trans (sqrtQbar_sq n).symm) with h2 | h2
  · rw [h2]
  · rw [h2, map_neg, neg_inj]

/-- The quadratic character at the restricted rational Frobenius is the Legendre symbol
`(n/q)` (tex 4286–4292; lane RC24's `sqrtChar_of_isFrobAt`). Kind: PROVED. -/
theorem quadChar_gksOfQ_frobQ (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0) {n : ℤ} (hn : h = (n : K)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqn : ¬ (q : ℤ) ∣ n)
    (hσ : ∀ x : K, frobQ q (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    ((quadChar sh hs hs0 (gksOfQ S₀ e (frobQ q) hσ) : ℤˣ) : ℤ) = jacobiSym n q := by
  have : Fact q.Prime := ⟨hq⟩
  have hsc := sqrtChar_of_isFrobAt hq hq2 hqn (isFrobAt_frobQ hq)
  rw [sqrtChar_apply] at hsc
  have hiff := quadChar_gksOfQ_eq_one_iff e sh hs hs0 hn (frobQ q) hσ
  have hnz : (n : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hqn
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  by_cases hfix : frobQ q (sqrtQbar n) = sqrtQbar n
  · rw [ite_eq_left hfix] at hsc
    have hsq : IsSquare (n : ZMod q) := by
      by_contra hns
      rw [ZInQ.Manuscript.RC.Symbols.legBit, ite_eq_right hns] at hsc
      exact absurd hsc (by decide)
    rw [hiff.mpr hfix, Units.val_one, (legendreSym.eq_one_iff q hnz).mpr hsq]
  · rw [ite_eq_right hfix] at hsc
    have hns : ¬ IsSquare (n : ZMod q) := by
      intro hsq
      rw [ZInQ.Manuscript.RC.Symbols.legBit, ite_eq_left hsq] at hsc
      exact absurd hsc (by decide)
    have hm1 : quadChar sh hs hs0 (gksOfQ S₀ e (frobQ q) hσ) = -1 :=
      (Int.units_eq_one_or _).resolve_left fun h1 => hfix (hiff.mp h1)
    rw [hm1, Units.val_neg, Units.val_one, (legendreSym.eq_neg_one_iff q).mpr hns]

/-- `t ↦ t` under `Λ → A_s` (tex 2725, 4385–4451). Kind: PROVED. -/
theorem stageMap_X (s : ℕ) :
    stageMap s PowerSeries.X = ZInQ.Manuscript.RC.HeegnerAlgebra.tA s := by
  show Ideal.Quotient.mk _ (PowerSeries.trunc s (PowerSeries.map (PadicInt.toZModPow s)
    PowerSeries.X)) = Ideal.Quotient.mk _ Polynomial.X
  rw [PowerSeries.map_X, Ideal.Quotient.eq]
  have h := ZInQ.Manuscript.RC.Limits.X_pow_dvd_sub_trunc s
    (Polynomial.X : Polynomial (ZMod (2 ^ s)))
  rw [Polynomial.coe_X] at h
  rw [← neg_sub, Ideal.neg_mem_iff]
  exact Ideal.mem_span_singleton.mpr h

/-- **GLUE input: the moving part of the stage character at the Frobenius of `w`** (tex
2731–2736: "prescribing `ξ_i(Fr_q) = 1` at each finite stage", `Ψ_i = (1 + t)^{ξ_i}`,
tex 2783): `ψ(π(Frob_w)) = 1 + t`; for lane RC28's `alphaChar` it follows from `ξ(Frob_w) = 1`
(`movingValueAt_of_xi`). Kind: GLUE. -/
def MovingValueAt {Δ : Type} [CommGroup Δ] (s : ℕ) (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef s)ˣ)
    (w : NewPlaces K S₀ S) : Prop :=
  ψ (π (urFrobElt K w)) = ZInQ.Manuscript.RC.CoefModules.onePlusT s

/-- **GLUE input: the moving part of the stage character is anticyclotomic** (tex 2781–2788:
"Conjugation acts on this ring-class group by inversion", `Ψ_i(τgτ⁻¹) = Ψ_i(g)⁻¹`).
Kind: GLUE. -/
def MovingAnticyclotomic (Cc : ActualConj K S₀) {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ)
    {s : ℕ} (ψ : Δ →* (Acoef s)ˣ) : Prop :=
  ∀ σ, ψ (π (Cc.conj σ)) = (ψ (π σ))⁻¹

/-- **Lane RC28's `α_s = χ_h (1 + t)^ξ` is lane E2's `alphaStage`** with `π = ξ` and
`ψ = (1 + t)^{(·)}` (tex 2781–2791). Kind: PROVED. -/
theorem alphaChar_eq_alphaStage (s : ℕ) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0)
    (ξ : GKS K S₀ →* Multiplicative (ZMod (2 ^ (2 * s)))) :
    alphaChar s (quadChar sh hs hs0) ξ = alphaStage s sh hs hs0 ξ
      (ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * s)
        (ZInQ.Manuscript.RC.CoefModules.onePlusT s) (onePlusT_pow s)) := rfl

/-- **The prescription `ξ(Frob_w) = 1` gives `MovingValueAt`** for lane RC28's moving character
(tex 2731–2736, 2783). Kind: PROVED. -/
theorem movingValueAt_of_xi {s : ℕ} (hs1 : 0 < s)
    (ξ : GKS K S₀ →* Multiplicative (ZMod (2 ^ (2 * s)))) (w : NewPlaces K S₀ S)
    (hξ : ξ (urFrobElt K w) = Multiplicative.ofAdd 1) :
    MovingValueAt s ξ (ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * s)
      (ZInQ.Manuscript.RC.CoefModules.onePlusT s) (onePlusT_pow s)) w := by
  have : Fact (1 < 2 ^ (2 * s)) := ⟨Nat.one_lt_two_pow (by omega)⟩
  unfold MovingValueAt
  rw [hξ, ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]

/-- **The anticyclotomy of lane RC28's moving character** from `ξ ∘ c = ξ⁻¹` (tex 2786–2788).
Kind: PROVED. -/
theorem movingAnticyclotomic_of_xi (Cc : ActualConj K S₀) {s : ℕ}
    (ξ : GKS K S₀ →* Multiplicative (ZMod (2 ^ (2 * s))))
    (hξ : ∀ σ, ξ (Cc.conj σ) = (ξ σ)⁻¹) :
    MovingAnticyclotomic Cc ξ (ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * s)
      (ZInQ.Manuscript.RC.CoefModules.onePlusT s) (onePlusT_pow s)) := fun σ => by
  rw [hξ, map_inv]

/-- **(2) The value of lane E2's stage character at the Frobenius, from the quadratic value**
(tex 4144–4145, 4286–4292): `α(Frob_w) = c (1 + t)` at the stage. Kind: PROVED. -/
theorem charValueAt_alphaStage_of_quad (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0) {Δ : Type} [CommGroup Δ]
    (π : GKS K S₀ →* Δ) (s : ℕ) (ψ : Δ →* (Acoef s)ˣ) (w : NewPlaces K S₀ S) {c : ℤ}
    (hχ : ((quadChar sh hs hs0 (urFrobElt K w) : ℤˣ) : ℤ) = c) (hmov : MovingValueAt s π ψ w) :
    CharValueAt (stageRingChar s (alphaStage s sh hs hs0 π ψ)) w
      (stageMk s ((c : LamI) * (1 + PowerSeries.X))) := by
  have hα : ((alphaStage s sh hs hs0 π ψ (urFrobElt K w) : (Acoef s)ˣ) : Acoef s) =
      (c : Acoef s) * (1 + ZInQ.Manuscript.RC.HeegnerAlgebra.tA s) := by
    change (((intUnitsTo (Acoef s) (quadChar sh hs hs0 (urFrobElt K w))) *
      ψ (π (urFrobElt K w)) : (Acoef s)ˣ) : Acoef s) = _
    rw [hmov, Units.val_mul]
    congr 1
    change (((quadChar sh hs hs0 (urFrobElt K w) : ℤˣ) : ℤ) : Acoef s) = _
    rw [hχ]
  unfold CharValueAt
  change (stageEquiv s).symm
    ((alphaStage s sh hs hs0 π ψ (urFrobElt K w) : (Acoef s)ˣ) : Acoef s) = _
  rw [hα, RingEquiv.symm_apply_eq, ZInQ.Manuscript.RC.Limits.stageEquiv_mk, map_mul, map_add,
    map_one, map_intCast, stageMap_X]

/-- **(2) The value of lane E2's stage character at the Frobenius** when
`Frob_w = γ Fr_q|_{K_S} γ⁻¹` (tex 4144–4145, 4286–4292): `(n/q)(1 + t)`. Kind: PROVED. -/
theorem charValueAt_alphaStage (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0) {n : ℤ} (hn : h = (n : K))
    {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (s : ℕ) (ψ : Δ →* (Acoef s)ˣ)
    (w : NewPlaces K S₀ S) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : ¬ (q : ℤ) ∣ n)
    (hσ : ∀ x : K, frobQ q (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) {γ : GKS K S₀}
    (hγ : urFrobElt K w = γ * gksOfQ S₀ e (frobQ q) hσ * γ⁻¹) (hmov : MovingValueAt s π ψ w) :
    CharValueAt (stageRingChar s (alphaStage s sh hs hs0 π ψ)) w
      (stageMk s (((jacobiSym n q : ℤ) : LamI) * (1 + PowerSeries.X))) :=
  charValueAt_alphaStage_of_quad sh hs hs0 π s ψ w (by
    rw [hγ, map_mul, map_mul, map_inv, mul_inv_cancel_comm,
      quadChar_gksOfQ_frobQ e sh hs hs0 hn hq hq2 hqn hσ]) hmov

end CharValue

/-! ### (4) Lane E2's coefficient module over the stage ring of the chain -/

section E2Module

open ZInQ.Contrib.CloudB3E2.NormCochain (StageIsoA stageIsoA mcoefModuleK alphaStage)

variable {K : Type} [Field K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}

/-- **`(A_s ⊗ T)(α)` over the stage ring of the chain through `stageEquiv s`** (tex 2724–2727,
4385–4451): lane E2's `mcoefModuleK` with `stageIsoA s` (`mcoefModuleK_stage_eq`).
Kind: definition. -/
abbrev stageCompModule (s : ℕ) (α : GKS K S₀ →* (Acoef s)ˣ) (T : Type) [AddCommGroup T] :
    Module (StageRing s) (CoefMod (Acoef s) α T) :=
  Module.compHom _ (stageEquiv s).toRingHom

/-- **Lane E2's `mcoefModuleK` at the stages of the chain is `stageCompModule`** (tex
4385–4451). Kind: PROVED. -/
theorem mcoefModuleK_stage_eq [NumberField K] (W : WeierstrassCurve K) (s : ℕ) (sh : KS K S₀)
    {h : K} (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0) {Δ : Type} [CommGroup Δ]
    (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef s)ˣ) :
    @mcoefModuleK K _ _ S₀ W s sh h hs hs0 Δ _ π ψ (StageRing s) _ (stageIsoA s) =
      stageCompModule s (alphaStage s sh hs hs0 π ψ) (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ)) :=
  rfl

/-- The Galois action commutes with the stage ring on `stageCompModule` (tex 2724–2727).
Kind: PROVED. -/
theorem stageComp_smulCommClass (s : ℕ) (α : GKS K S₀ →* (Acoef s)ˣ) (T : Type) [AddCommGroup T]
    [DistribMulAction (GKS K S₀) T] :
    letI := stageCompModule s α T
    SMulCommClass (GKS K S₀) (StageRing s) (CoefMod (Acoef s) α T) :=
  letI := stageCompModule s α T
  ⟨fun g c m => smul_comm g (stageEquiv s c) m⟩

variable (s : ℕ) (T : Type) [AddCommGroup T]

/-- `stageEquiv⁻¹ ⊗ id : A_s ⊗ T ≃ (Λ ⧸ stageIdeal s) ⊗ T` (tex 2724–2727, 4385–4451).
Kind: definition. -/
abbrev stageTensorCongr : Acoef s ⊗[ℤ] T ≃ₗ[ℤ] StageRing s ⊗[ℤ] T :=
  TensorProduct.congr (stageEquiv s).symm.toAddEquiv.toIntLinearEquiv (LinearEquiv.refl ℤ T)

/-- `stageTensorCongr` on pure tensors (tex 2724–2727). Kind: PROVED. -/
theorem stageTensorCongr_tmul (a : Acoef s) (t : T) :
    stageTensorCongr s T (a ⊗ₜ[ℤ] t) = (stageEquiv s).symm a ⊗ₜ[ℤ] t := rfl

/-- `stageTensorCongr` is linear for the stage ring acting through `stageEquiv s`
(tex 2724–2727, 4385–4451). Kind: PROVED. -/
theorem stageTensorCongr_smul (c : StageRing s) (x : Acoef s ⊗[ℤ] T) :
    stageTensorCongr s T (stageEquiv s c • x) = c • stageTensorCongr s T x := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [TensorProduct.smul_tmul', stageTensorCongr_tmul, stageTensorCongr_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable (α : GKS K S₀ →* (Acoef s)ˣ)

/-- **(4) The coefficient module of lane E2 is the actual module over the stage ring**
(tex 2724–2727, 4385–4451): `(A_s ⊗ T)(α) ≃ (Λ ⧸ stageIdeal s ⊗ T)(α ∘ stageEquiv⁻¹)`,
linear for lane E2's `mcoefModuleK`. Kind: definition. -/
def stageCoefEquiv :
    letI := stageCompModule s α T
    CoefMod (Acoef s) α T ≃ₗ[StageRing s] CoefMod (StageRing s) (stageRingChar s α) T :=
  letI := stageCompModule s α T
  { toFun := fun x => stageTensorCongr s T x
    invFun := fun y => (stageTensorCongr s T).symm y
    map_add' := fun x y => map_add (stageTensorCongr s T) x y
    map_smul' := fun c x => stageTensorCongr_smul s T c x
    left_inv := fun x => (stageTensorCongr s T).symm_apply_apply x
    right_inv := fun y => (stageTensorCongr s T).apply_symm_apply y }

/-- `stageCoefEquiv` is `stageEquiv⁻¹ ⊗ id` (tex 2724–2727). Kind: PROVED. -/
theorem stageCoefEquiv_apply (x : Acoef s ⊗[ℤ] T) :
    stageCoefEquiv s T α x = stageTensorCongr s T x := rfl

variable {T} [DistribMulAction (GKS K S₀) T]

/-- `stageEquiv⁻¹ ⊗ id` commutes with `id ⊗ g` (tex 2724–2727). Kind: PROVED. -/
theorem stageTensorCongr_baseChangeAct (g : GKS K S₀) (x : Acoef s ⊗[ℤ] T) :
    stageTensorCongr s T (baseChangeAct (Acoef s) T g x) =
      baseChangeAct (StageRing s) T g (stageTensorCongr s T x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a t => rw [baseChangeAct_tmul, stageTensorCongr_tmul, stageTensorCongr_tmul,
      baseChangeAct_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (T)

/-- **(4) `stageCoefEquiv` is `G_{K,S₀}`-equivariant** (tex 2724–2727). Kind: PROVED. -/
theorem stageCoefEquiv_smul (g : GKS K S₀) (x : CoefMod (Acoef s) α T) :
    stageCoefEquiv s T α (g • x) = g • stageCoefEquiv s T α x := by
  rw [CoefMod.smul_def, CoefMod.act_apply, CoefMod.smul_def, CoefMod.act_apply]
  change stageTensorCongr s T (((α g : (Acoef s)ˣ) : Acoef s) • baseChangeAct (Acoef s) T g x) =
    (((stageRingChar s α g : (StageRing s)ˣ)) : StageRing s) •
      baseChangeAct (StageRing s) T g (stageTensorCongr s T x)
  have he : ((α g : (Acoef s)ˣ) : Acoef s) =
      stageEquiv s (((stageRingChar s α g : (StageRing s)ˣ)) : StageRing s) :=
    (RingEquiv.apply_symm_apply (stageEquiv s) _).symm
  rw [he, stageTensorCongr_smul]
  exact congrArg (_ • ·) (stageTensorCongr_baseChangeAct s g (show Acoef s ⊗[ℤ] T from x))

omit [DistribMulAction (GKS K S₀) T] in
/-- **(4) `stageCoefEquiv` is `stageEquiv⁻¹`-semilinear for the `A_s`-module structure**
(tex 2724–2727, 4385–4451). Kind: PROVED. -/
theorem stageCoefEquiv_smul_coef (a : Acoef s) (x : CoefMod (Acoef s) α T) :
    stageCoefEquiv s T α (a • x) = (stageEquiv s).symm a • stageCoefEquiv s T α x := by
  change stageTensorCongr s T (a • (show Acoef s ⊗[ℤ] T from x)) =
    (stageEquiv s).symm a • stageTensorCongr s T x
  conv_lhs => rw [← RingEquiv.apply_symm_apply (stageEquiv s) a]
  exact stageTensorCongr_smul s T _ _

/-- **(4) The inflated modules**: lane E2's `MinS` (`M₀ = (A_s ⊗ T)(α)`, inflated to `S`) and
the inflated actual module over the stage ring (tex 2724–2727, 3470–3498). Kind: definition. -/
def stageInflEquiv [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) :
    letI := stageCompModule s α T
    InflMod hS (CoefMod (Acoef s) α T) ≃ₗ[StageRing s]
      InflMod hS (CoefMod (StageRing s) (stageRingChar s α) T) :=
  letI := stageCompModule s α T
  stageCoefEquiv s T α

/-- **(4) `stageInflEquiv` is `G_{K,S}`-equivariant** (tex 3470–3498). Kind: PROVED. -/
theorem stageInflEquiv_smul [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (g : GKS K S) (x : InflMod hS (CoefMod (Acoef s) α T)) :
    stageInflEquiv s T α hS (g • x) = g • stageInflEquiv s T α hS x :=
  stageCoefEquiv_smul s T α (inflMap K hS g) x

end E2Module

/-! ### (4) The Frobenius fields on lane E2's module -/

section E2Frob

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) {ι : Type} (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  (W : WeierstrassCurve K) [W.IsElliptic] (s : ℕ) [TopologicalSpace (StageRing s)]
  [DiscreteTopology (StageRing s)] (α : GKS K S₀ →* (Acoef s)ˣ) [IsOpenKer α]

/-- **(4) The Frobenius fields of a chain on lane E2's module** (tex 3470–3498, 4176–4184):
`MinS` with `mcoefModuleK`, `X j = urRep (Mcoef …)`, `f j = urId` (lane E2's objects), bases
`e ∘ stageCoefEquiv` from `StageFrobInput` on the actual module. Kind: definition. -/
def stageChainFrobE2 (pidx : ℕ → ι) (n : ℕ) (Fr : ℕ → Matrix (Fin 2) (Fin 2) (StageRing s))
    (z zi : ℕ → StageRing s)
    (e₁ e₂ : ℕ → StageRing s ⊗[ℤ] TorsS K S₀ W ((2 ^ s : ℕ) : ℤ) ≃ₗ[StageRing s]
      (Fin 2 → StageRing s))
    (h₁ : ∀ i < n, StageFrobInput (e₁ i) (stageRingChar s α)
      (newPlace (place (pidx i, false)) (hw (pidx i, false))) (Fr i) (z i))
    (h₂ : ∀ i < n, StageFrobInput (e₂ i) (stageRingChar s α)
      (newPlace (place (pidx i, true)) (hw (pidx i, true))) (Fr i) (zi i)) :
    letI := stageCompModule s α (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))
    haveI := stageComp_smulCommClass s α (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))
    StageChainFrob (StageRing s) (MinS hS W s α) place
      (urChainRep place hw (Mcoef K S₀ W s α)) pidx n Fr z zi :=
  letI := stageCompModule s α (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))
  haveI := stageComp_smulCommClass s α (TorsS K S₀ W ((2 ^ s : ℕ) : ℤ))
  { f := fun j => urId hS (StageRing s) (Mcoef K S₀ W s α) (newPlace (place j) (hw j))
    hf := fun j => urId_compat hS (StageRing s) (Mcoef K S₀ W s α) (place j) (hw j)
    hbij := fun j => urId_bijective (StageRing s) (Mcoef K S₀ W s α) hS
      (newPlace (place j) (hw j))
    b₁ := fun i => (stageCoefEquiv s _ α).trans (e₁ i)
    hb₁ := fun i hi v => by
      change (e₁ i) (stageCoefEquiv s _ α
        (urFrobElt K (newPlace (place (pidx i, false)) (hw (pidx i, false))) •
          (show Mcoef K S₀ W s α from v))) =
        Matrix.toLin' (z i • Fr i) ((e₁ i) (stageCoefEquiv s _ α v))
      rw [stageCoefEquiv_smul, coefMod_smul_toLin' (stageRingChar s α) (e₁ i) _ (Fr i)
        (h₁ i hi).frobMatrix, (h₁ i hi).charValue]
    b₂ := fun i => (stageCoefEquiv s _ α).trans (e₂ i)
    hb₂ := fun i hi v => by
      change (e₂ i) (stageCoefEquiv s _ α
        (urFrobElt K (newPlace (place (pidx i, true)) (hw (pidx i, true))) •
          (show Mcoef K S₀ W s α from v))) =
        Matrix.toLin' (zi i • Fr i) ((e₂ i) (stageCoefEquiv s _ α v))
      rw [stageCoefEquiv_smul, coefMod_smul_toLin' (stageRingChar s α) (e₂ i) _ (Fr i)
        (h₂ i hi).frobMatrix, (h₂ i hi).charValue] }

end E2Frob

/-! ### (5) The Frobenius fields of the genuine stage chain at the leaf's values -/

section LeafAssembly

open ZInQ.Contrib.RC53Assist.InnerLimitArith (gksOfQ basisK)
open ZInQ.Contrib.RC53Assist.FrobeniusMatch (integersEquiv)
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage)

variable {E : WeierstrassCurve ℚ}

/-- **The Frobenius at one of the two places is conjugate to `Fr_q`** (tex 4144–4145).
Kind: PROVED. -/
theorem frobQ_conj_split (C : TateCoef E) (Cc : ActualConj C.K C.S) {q : ℕ} (hq : q.Prime)
    (hfix : FrobQFixes C q) {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K C.S S}
    (hpl : SplitPlacesAt C Cc q w w') :
    (∃ γ : GKS C.K C.S, urFrobElt C.K w = γ * gksOfQ C.S C.e (frobQ q) hfix * γ⁻¹) ∨
      ∃ γ : GKS C.K C.S, urFrobElt C.K w' = γ * gksOfQ C.S C.e (frobQ q) hfix * γ⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPp, hPZ, hF⟩ := isFrobAtC10_frobQ hq
  have := hPp
  have hIp : ((P.comap (integersEquiv C.e)).under (𝓞 C.K)).IsPrime := Ideal.IsPrime.under _ _
  have hqI : (q : 𝓞 C.K) ∈ (P.comap (integersEquiv C.e)).under (𝓞 C.K) := by
    have hpP : ((q : ℕ) : Zbar) ∈ P := ZInQ.Contrib.ChebFD.HSyn.natCast_mem P q hPZ
    change integersEquiv C.e (algebraMap (𝓞 C.K) (𝓞 (AlgebraicClosure C.K)) (q : 𝓞 C.K)) ∈ P
    simpa only [map_natCast] using hpP
  rcases hpl.above _ hIp hqI with h | h
  · exact Or.inl (urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w h hpl.card)
  · exact Or.inr (urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w' h hpl.card')

/-- **The quadratic character at the Frobenius of a place of a split prime** is `(n/q)`
(tex 2790–2795, 4286–4292). Kind: PROVED. -/
theorem quadChar_urFrobElt_split (C : TateCoef E) (Cc : ActualConj C.K C.S) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hfix : FrobQFixes C q) {S : Set (HeightOneSpectrum (𝓞 C.K))}
    {w w' : NewPlaces C.K C.S S} (hpl : SplitPlacesAt C Cc q w w') (sh : KS C.K C.S) {h : C.K}
    (hs : sh ^ 2 = algebraMap C.K (KS C.K C.S) h) (hs0 : sh ≠ 0) {n : ℤ} (hn : h = (n : C.K))
    (hqn : ¬ (q : ℤ) ∣ n) :
    ((quadChar sh hs hs0 (urFrobElt C.K w) : ℤˣ) : ℤ) = jacobiSym n q := by
  have hval := quadChar_gksOfQ_frobQ C.e sh hs hs0 hn hq hq2 hqn hfix
  rcases frobQ_conj_split C Cc hq hfix hpl with ⟨γ, hγ⟩ | ⟨γ, hγ⟩
  · rw [hγ, map_mul, map_mul, map_inv, mul_inv_cancel_comm, hval]
  · obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w' w hpl.symm.conj
    have hκh : Cc.κ h = h := by rw [hn, map_intCast]
    rw [hg, map_mul, map_mul, map_inv, mul_inv_cancel_comm, quadChar_conj Cc sh hs hs0 hκh, hγ,
      map_mul, map_mul, map_inv, mul_inv_cancel_comm, hval]

/-- The leaf's point at the stage is `(h_x/q)(1 + t)` at an unused `q` (tex 4286–4292).
Kind: PROVED. -/
theorem stageMk_zAt (Fam : Family) (hQ : ∀ q ∈ Fam.Q, q.Prime) {x : Addr Fam.b} {q : ℕ}
    (hq : q ∈ Fam.Q) (hx : Fam.lam q x = 0) (s : ℕ) :
    stageMk s (zAt Fam x q : Lambda) =
      stageMk s (((jacobiSym (Fam.h x) q : ℤ) : LamI) * (1 + PowerSeries.X)) := by
  rw [← sgnChar_frobLift_of_unused Fam hQ hq hx 0]
  rfl

/-- An unused graph prime does not divide `h_x` (tex 4288–4292). Kind: PROVED. -/
theorem not_dvd_h_of_unused (Fam : Family) (hQ : ∀ q ∈ Fam.Q, q.Prime) {x : Addr Fam.b}
    {q : ℕ} (hq : q ∈ Fam.Q) (hx : Fam.lam q x = 0) : ¬ (q : ℤ) ∣ Fam.h x := by
  intro hd
  have : Fact q.Prime := ⟨hQ q hq⟩
  have h0 : jacobiSym (Fam.h x) q = 0 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  rw [← sgnChar_frobLift_of_unused Fam hQ hq hx 0] at h0
  exact Units.ne_zero _ h0

/-- **Lane E2's stage character is anticyclotomic** (tex 2786–2795: `α_i^τ = α_i^{-1}`).
Kind: PROVED. -/
theorem alphaStage_conj {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
    (Cc : ActualConj K S₀) (sh : KS K S₀) {h : K} (hs : sh ^ 2 = algebraMap K (KS K S₀) h)
    (hs0 : sh ≠ 0) (hκh : Cc.κ h = h) {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (s : ℕ)
    (ψ : Δ →* (Acoef s)ˣ) (hξ : MovingAnticyclotomic Cc π ψ) (σ : GKS K S₀) :
    alphaStage s sh hs hs0 π ψ (Cc.conj σ) = (alphaStage s sh hs hs0 π ψ σ)⁻¹ := by
  have hq : (quadChar sh hs hs0 σ)⁻¹ = quadChar sh hs hs0 σ := by
    rcases Int.units_eq_one_or (quadChar sh hs hs0 σ) with h1 | h1 <;> rw [h1] <;> rfl
  have ha : (intUnitsTo (Acoef s) (quadChar sh hs hs0 σ))⁻¹ =
      intUnitsTo (Acoef s) (quadChar sh hs hs0 σ) := by
    rw [← map_inv, hq]
  simp only [alphaStage, charMul_apply, MonoidHom.comp_apply]
  rw [quadChar_conj Cc sh hs hs0 hκh, hξ σ]
  calc intUnitsTo (Acoef s) (quadChar sh hs hs0 σ) * (ψ (π σ))⁻¹
      = (intUnitsTo (Acoef s) (quadChar sh hs hs0 σ))⁻¹ * (ψ (π σ))⁻¹ := by rw [ha]
    _ = (intUnitsTo (Acoef s) (quadChar sh hs hs0 σ) * ψ (π σ))⁻¹ := by
      rw [mul_inv_rev]
      exact mul_comm (G := (Acoef s)ˣ) _ _

/-- The stage character over the stage ring is anticyclotomic when `α` is (tex 2795).
Kind: PROVED. -/
theorem stageRingChar_conj {K : Type} [Field K] [NumberField K]
    {S₀ : Set (HeightOneSpectrum (𝓞 K))} (s : ℕ) (Cc : ActualConj K S₀)
    (α : GKS K S₀ →* (Acoef s)ˣ) (hα : ∀ σ, α (Cc.conj σ) = (α σ)⁻¹) (σ : GKS K S₀) :
    stageRingChar s α (Cc.conj σ) = (stageRingChar s α σ)⁻¹ := by
  rw [stageRingChar, MonoidHom.comp_apply, MonoidHom.comp_apply, hα, map_inv]

/-- **The arithmetic inputs of the leaf at one step** (tex 2720–2736, 4142–4145): the data of
the unused split prime and its places, and the GLUE inputs `FrobQFixes`, `MovingValueAt`.
Kind: definition. -/
structure LeafStepInputs (C : TateCoef E) (Cc : ActualConj C.K C.S) (Fam : Family)
    (x : Addr Fam.b) (s : ℕ) {Δ : Type} [CommGroup Δ] (π : GKS C.K C.S →* Δ)
    (ψ : Δ →* (Acoef s)ˣ) (q : ℕ) {S : Set (HeightOneSpectrum (𝓞 C.K))}
    (w w' : NewPlaces C.K C.S S) : Prop where
  /-- `q` is prime -/
  prime : q.Prime
  /-- `q` is odd -/
  ne_two : q ≠ 2
  /-- `q` is a graph prime -/
  mem : q ∈ Fam.Q
  /-- `q` is unused at the character -/
  unused : Fam.lam q x = 0
  /-- GLUE: `Fr_q` acts trivially on `K` -/
  fixes : FrobQFixes C q
  /-- the two places above `q` -/
  places : SplitPlacesAt C Cc q w w'
  /-- GLUE: the moving character at the Frobenius of the first place -/
  moving : MovingValueAt s π ψ w

variable [E.IsElliptic]

/-- **(5) The stage Frobenius inputs at both places of one step, at the leaf's values**
(tex 4171, 4176–4184): `StageFrobInput` at `w` with `(frobMatStage, z)` and at `w'` with
`(frobMatStage, z⁻¹)`. Kind: PROVED. -/
theorem exists_stageFrobInput_leaf (C : TateCoef E) (Cc : ActualConj C.K C.S) (Fam : Family)
    (hQ : ∀ q ∈ Fam.Q, q.Prime) (x : Addr Fam.b) (s : ℕ) (sh : KS C.K C.S) {h : C.K}
    (hs : sh ^ 2 = algebraMap C.K (KS C.K C.S) h) (hs0 : sh ≠ 0)
    (hn : h = ((Fam.h x : ℤ) : C.K)) {Δ : Type} [CommGroup Δ] (π : GKS C.K C.S →* Δ)
    (ψ : Δ →* (Acoef s)ˣ) (hξ : MovingAnticyclotomic Cc π ψ) {q : ℕ}
    {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K C.S S}
    (hI : LeafStepInputs C Cc Fam x s π ψ q w w') :
    (∃ eT : StageRing s ⊗[ℤ] Lev C.K C.S (E.baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          w (frobMatStage C q s) (stageMk s (zAt Fam x q : Lambda))) ∧
      ∃ eT : StageRing s ⊗[ℤ] Lev C.K C.S (E.baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          w' (frobMatStage C q s) (stageMk s (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda)) := by
  have hqn := not_dvd_h_of_unused Fam hQ hI.mem hI.unused
  have hχ := quadChar_urFrobElt_split C Cc hI.prime hI.ne_two hI.fixes hI.places sh hs hs0 hn hqn
  have hz : CharValueAt (stageRingChar s (alphaStage s sh hs hs0 π ψ)) w
      (stageMk s (zAt Fam x q : Lambda)) := by
    rw [stageMk_zAt Fam hQ hI.mem hI.unused s]
    exact charValueAt_alphaStage_of_quad sh hs hs0 π s ψ w hχ hI.moving
  obtain ⟨e₁, he₁⟩ := exists_frobMatrixAt_frobMatStage C Cc hI.prime hI.fixes hI.places s
  obtain ⟨e₂, he₂⟩ := exists_frobMatrixAt_frobMatStage C Cc hI.prime hI.fixes hI.places.symm s
  obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w w' hI.places.conj
  have hκh : Cc.κ h = h := by rw [hn, map_intCast]
  have hα := stageRingChar_conj s Cc _ (alphaStage_conj Cc sh hs hs0 hκh π s ψ hξ)
  have hzi : stageMk s (zAt Fam x q : Lambda) *
      stageMk s (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact ⟨⟨e₁, he₁, hz⟩, ⟨e₂, he₂,
    charValueAt_of_anticyclotomic hz hzi (anticyclotomicAt_of_conj Cc hα hg)⟩⟩

end LeafAssembly

/-! ### (5) The leaf: bases at all steps and the chain data -/

section LeafChain

open ZInQ.Contrib.RC53Assist.InnerLimitArith (basisK)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Cc : ActualConj C.K C.S)
  (Fam : Family) (hQ : ∀ q ∈ Fam.Q, q.Prime) (x : Addr Fam.b) (ps : List ℕ)
  {S : Set (HeightOneSpectrum (𝓞 C.K))} {ι : Type} (place : ι × Bool → Places C.K S)
  (hw : ∀ j, (place j).1 ∉ C.S) (pidx : ℕ → ι) (n s : ℕ) (sh : KS C.K C.S) {h : C.K}
  (hs : sh ^ 2 = algebraMap C.K (KS C.K C.S) h) (hs0 : sh ≠ 0)
  (hn : h = ((Fam.h x : ℤ) : C.K)) {Δ : Type} [CommGroup Δ] (π : GKS C.K C.S →* Δ)
  (ψ : Δ →* (Acoef s)ˣ) (hξ : MovingAnticyclotomic Cc π ψ)

include hQ hn hξ in
/-- **(5) Stage bases at the two places of every step, at the leaf's values** (tex 4176–4184,
4385–4451). Kind: PROVED. -/
theorem exists_leaf_stageBases
    (hstep : ∀ i < n, LeafStepInputs C Cc Fam x s π ψ (ps.getD i 1)
      (newPlace (place (pidx i, false)) (hw (pidx i, false)))
      (newPlace (place (pidx i, true)) (hw (pidx i, true)))) :
    ∃ e₁ e₂ : ℕ → StageRing s ⊗[ℤ] Lev C.K C.S ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), ∀ i < n,
      StageFrobInput (e₁ i) (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          (newPlace (place (pidx i, false)) (hw (pidx i, false)))
          (((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x ps).map (stageMk s)).z i) ∧
        StageFrobInput (e₂ i) (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          (newPlace (place (pidx i, true)) (hw (pidx i, true)))
          (((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x ps).map (stageMk s)).zi i) := by
  have hex : ∀ i, ∃ e₁ e₂ : StageRing s ⊗[ℤ] Lev C.K C.S ((Ecurve ℓ).baseChange C.K) s ≃ₗ[
      StageRing s] (Fin 2 → StageRing s), i < n →
      StageFrobInput e₁ (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          (newPlace (place (pidx i, false)) (hw (pidx i, false)))
          (((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x ps).map (stageMk s)).z i) ∧
        StageFrobInput e₂ (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          (newPlace (place (pidx i, true)) (hw (pidx i, true)))
          (((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x ps).map (stageMk s)).zi i) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ :=
        exists_stageFrobInput_leaf C Cc Fam hQ x s sh hs hs0 hn π ψ hξ (hstep i hi)
      exact ⟨e₁, e₂, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨stageBasis (basisK C.S (Ecurve ℓ)) s, stageBasis (basisK C.S (Ecurve ℓ)) s,
        fun h' => absurd h' hi⟩
  choose e₁ e₂ he using hex
  exact ⟨e₁, e₂, fun i hi => he i hi⟩

include hQ hn hξ in
/-- **(5) The Frobenius fields of the genuine stage chain at the leaf's values, on the actual
module over the stage ring** (tex 4142–4194, 4176–4184, 4385–4451): the input `D` of
`GenuineStageSteps.ofFrob` with `Fr`, `z`, `zi` those of `leafFrobΛ` at the stage.
Kind: PROVED. -/
theorem nonempty_stageChainFrob_leaf (hS : C.S ⊆ S) [TopologicalSpace (StageRing s)]
    [DiscreteTopology (StageRing s)] [IsOpenKer (alphaStage s sh hs hs0 π ψ)]
    (hstep : ∀ i < n, LeafStepInputs C Cc Fam x s π ψ (ps.getD i 1)
      (newPlace (place (pidx i, false)) (hw (pidx i, false)))
      (newPlace (place (pidx i, true)) (hw (pidx i, true)))) :
    Nonempty (StageChainFrob (StageRing s)
      (InflMod hS (stageActualMod s ((Ecurve ℓ).baseChange C.K) (alphaStage s sh hs hs0 π ψ)))
      place (urChainRep place hw
        (stageActualMod s ((Ecurve ℓ).baseChange C.K) (alphaStage s sh hs hs0 π ψ))) pidx n
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).z i)
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).zi i)) := by
  obtain ⟨e₁, e₂, he⟩ :=
    exists_leaf_stageBases C Cc Fam hQ x ps place hw pidx n s sh hs hs0 hn π ψ hξ hstep
  exact nonempty_stageChainFrob_stage hS place hw ((Ecurve ℓ).baseChange C.K) s
    (alphaStage s sh hs hs0 π ψ) pidx n _ _ _ e₁ e₂ (fun i hi => (he i hi).1)
    (fun i hi => (he i hi).2)

include hQ hn hξ in
/-- **(4)+(5) The Frobenius fields of the genuine stage chain at the leaf's values, on lane E2's
module** `MinS` with `mcoefModuleK` (tex 4142–4194, 4385–4451). Kind: PROVED. -/
theorem nonempty_stageChainFrob_leaf_E2 (hS : C.S ⊆ S) [TopologicalSpace (StageRing s)]
    [DiscreteTopology (StageRing s)] [IsOpenKer (alphaStage s sh hs hs0 π ψ)]
    (hstep : ∀ i < n, LeafStepInputs C Cc Fam x s π ψ (ps.getD i 1)
      (newPlace (place (pidx i, false)) (hw (pidx i, false)))
      (newPlace (place (pidx i, true)) (hw (pidx i, true)))) :
    letI := stageCompModule s (alphaStage s sh hs hs0 π ψ)
      (TorsS C.K C.S ((Ecurve ℓ).baseChange C.K) ((2 ^ s : ℕ) : ℤ))
    haveI := stageComp_smulCommClass s (alphaStage s sh hs hs0 π ψ)
      (TorsS C.K C.S ((Ecurve ℓ).baseChange C.K) ((2 ^ s : ℕ) : ℤ))
    Nonempty (StageChainFrob (StageRing s)
      (MinS hS ((Ecurve ℓ).baseChange C.K) s (alphaStage s sh hs hs0 π ψ)) place
      (urChainRep place hw (Mcoef C.K C.S ((Ecurve ℓ).baseChange C.K) s
        (alphaStage s sh hs hs0 π ψ))) pidx n
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).Fr i)
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).z i)
      (fun i => ((leafFrobΛ C Fam x ps).map (stageMk s)).zi i)) := by
  obtain ⟨e₁, e₂, he⟩ :=
    exists_leaf_stageBases C Cc Fam hQ x ps place hw pidx n s sh hs hs0 hn π ψ hξ hstep
  exact ⟨stageChainFrobE2 hS place hw ((Ecurve ℓ).baseChange C.K) s
    (alphaStage s sh hs hs0 π ψ) pidx n _ _ _ e₁ e₂ (fun i hi => (he i hi).1)
    (fun i hi => (he i hi).2)⟩

end LeafChain

/-! ### `FrobQFixes` from the splitting of `q` -/

section Fixes

open ZInQ.Manuscript.RC.PrintsArith (Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (sqrtQbar sqrtQbar_sq sqrtChar_apply sqrtChar_of_isFrobAt)

variable {E : WeierstrassCurve ℚ}

/-- **`FrobQFixes` from the splitting of `q` in `K = ℚ(√k)`** (tex 2720–2722): `(k/q) = 1`
and Euler's criterion (lane RC24's `sqrtChar_of_isFrobAt`). Kind: PROVED. -/
theorem frobQFixes_of_sqrt (C : TateCoef E) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {k : ℤ}
    (hqk : ¬ (q : ℤ) ∣ k) (hsq : IsSquare ((k : ℤ) : ZMod q)) (r : C.K)
    (hr : r ^ 2 = (k : C.K)) (hgen : Algebra.adjoin ℚ {r} = ⊤) : FrobQFixes C q := by
  have hsc := sqrtChar_of_isFrobAt hq hq2 hqk (isFrobAt_frobQ hq)
  rw [sqrtChar_apply, ZInQ.Manuscript.RC.Symbols.legBit, ite_eq_left hsq] at hsc
  have hfs : frobQ q (sqrtQbar k) = sqrtQbar k := by
    by_contra hne
    rw [ite_eq_right hne] at hsc
    exact absurd hsc (by decide)
  let ρ : C.K →+* Qbar :=
    (C.e : AlgebraicClosure C.K →+* Qbar).comp (algebraMap C.K (AlgebraicClosure C.K))
  have hρr : frobQ q (ρ r) = ρ r := by
    have hr2 : ρ r ^ 2 = (k : Qbar) := by rw [← map_pow, hr, map_intCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hr2.trans (sqrtQbar_sq k).symm) with h | h
    · rw [h, hfs]
    · rw [h, map_neg, hfs]
  intro x
  have hx : x ∈ Algebra.adjoin ℚ {r} := hgen ▸ Algebra.mem_top
  change frobQ q (ρ x) = ρ x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    exact hρr
  | algebraMap a => rw [eq_ratCast (algebraMap ℚ C.K) a, map_ratCast, map_ratCast]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

end Fixes

end ZInQ.Manuscript.RC.Wiring
