import ZInQKernel.Contrib.RC53Assist.Calibration.GenuineLocalBlocks
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.TateCoef
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerAnnActual
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.NatHomology
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidual

/-!
The degree-zero calculation for the central local blocks (tex 4032–4036, 4066–4080).
All actions are on the actual torsion in the support field, localized by `locMap`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open NumberField IsDedekindDomain CategoryTheory Matrix TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs_apply_coe)
open ZInQ.Contrib.CloudB3RC53.GenuineInst (natH0Iso smul_torsTwo_cubicCurve)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}

/-- Local inertia is trivial on the actual untwisted torsion at every precision. -/
def LocalUnramifiedTorsion (W : WeierstrassCurve K) (v : Places K S) : Prop :=
  ∀ (σ : Gloc K v.1), urRes K v.1 σ = 1 →
    ∀ (i : ℕ) (P : TorsS K S W ((2 ^ i : ℕ) : ℤ)), locMap K S v.1 σ • P = P

/-- At an active place a genuine inertia element fixes the untwisted torsion and negates the
quadratic square root. -/
def ActiveLocalAction (W : WeierstrassCurve K) (s : KS K S)
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : Places K S) : Prop :=
  ∃ σ : Gloc K v.1, urRes K v.1 σ = 1 ∧ quadChar s hs hs0 (locMap K S v.1 σ) = -1 ∧
    ∀ (i : ℕ) (P : TorsS K S W ((2 ^ i : ℕ) : ℤ)), locMap K S v.1 σ • P = P

/-- The matrix on the global Tate module of the actual local element, along the same restriction
that gives the action on the coefficient module. -/
def localTateMatrix (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : Places K S)
    (φ : Gloc K v.1) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  tateMatrix E (tateGalToQ (tateAlgEquiv K) (decompMap K v.1 φ))

/-- At a moving place both factors of the central action are unramified. An arithmetic
Frobenius lift acts with the specified trace, determinant and quadratic sign. -/
structure MovingLocalAction (E : WeierstrassCurve ℚ) [E.IsElliptic] (s : KS K S)
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : Places K S)
    (r : ℕ) (a χ : ℤ) : Type where
  frob : Gloc K v.1
  frob_ur : urRes K v.1 frob = frobElt (eUr K v.1)
  unramifiedTorsion : LocalUnramifiedTorsion (E.baseChange K) v
  unramifiedSign : ∀ σ : Gloc K v.1, urRes K v.1 σ = 1 →
    quadChar s hs hs0 (locMap K S v.1 σ) = 1
  trace : (localTateMatrix E v frob).trace = (a : ℤ_[2])
  det : (localTateMatrix E v frob).det = (r : ℤ_[2])
  sign : (quadChar s hs hs0 (locMap K S v.1 frob) : ℤ) = χ

/-- Degree-zero local cohomology is the invariant subgroup of the actual module. -/
def locH0EquivFixed (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (v : Places K S) :
    locH W i α v 0 ≃ {x : Mcoef K S W i α // ∀ σ : Gloc K v.1, locMap K S v.1 σ • x = x} := by
  let T := ResMod (locMap K S v.1) (Mcoef K S W i α)
  exact (natH0Iso (contCochains (Acoef i) (Gloc K v.1) T)).toLinearEquiv.toEquiv.trans
    (contH0AddEquiv (Acoef i) (Gloc K v.1) T).toEquiv

private theorem centralChar_coe (i : ℕ) (g : GKS K S) :
    (centralChar i s hs hs0 g : Acoef i) = (((quadChar s hs hs0 g : ℤˣ) : ℤ) : Acoef i) := by
  have h1 : movingCharS i (1 : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) g = 1 := by
    rw [movingCharS, ZInQ.Manuscript.RC.HeegnerAlgebra.movingChar, MonoidHom.comp_apply,
      MonoidHom.one_apply, map_one]
  rw [centralChar, alphaChar, charMul_apply, h1, mul_one, MonoidHom.comp_apply]
  rfl

private theorem central_tmul_smul {W : WeierstrassCurve K} (i : ℕ) (g : GKS K S)
    (b : Acoef i) (P : TorsS K S W ((2 ^ i : ℕ) : ℤ)) :
    g • (CoefMod.equiv (Acoef i) (centralChar i s hs hs0) _ (b ⊗ₜ[ℤ] P)) =
      ((quadChar s hs hs0 g : ℤˣ) : ℤ) •
        (CoefMod.equiv (Acoef i) (centralChar i s hs hs0) _ (b ⊗ₜ[ℤ] (g • P))) := by
  rw [CoefMod.smul_tmul, centralChar_coe, ← zsmul_eq_mul, ← TensorProduct.smul_tmul', map_zsmul]

private theorem central_smul_of_torsion_fixed {W : WeierstrassCurve K} (i : ℕ) (g : GKS K S)
    (hg : ∀ P : TorsS K S W ((2 ^ i : ℕ) : ℤ), g • P = P)
    (x : Mcoef K S W i (centralChar i s hs hs0)) :
    g • x = ((quadChar s hs hs0 g : ℤˣ) : ℤ) • x := by
  let f := CoefMod.equiv (Acoef i) (centralChar i s hs hs0) (TorsS K S W ((2 ^ i : ℕ) : ℤ))
  obtain ⟨y, rfl⟩ := f.surjective x
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, smul_add, smul_add, hx, hy]
  | tmul b P => rw [central_tmul_smul, hg]

omit [NumberField K] in
private theorem torsionFixed_of_two_smul {W : WeierstrassCurve K}
    (hRat : ∀ (g : GKS K S) (P : TorsS K S W (2 : ℤ)), g • P = P)
    (i : ℕ) (g : GKS K S) (P : TorsS K S W ((2 ^ i : ℕ) : ℤ)) (hP : (2 : ℕ) • P = 0) :
    g • P = P := by
  let Q : TorsS K S W (2 : ℤ) :=
    ⟨P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val hP)⟩
  exact Subtype.ext (congrArg (fun t : TorsS K S W (2 : ℤ) => t.val) (hRat g Q))

/-- For the manuscript's curve, the ordinary two-torsion is fixed over every support. -/
theorem ecurve_torsTwo_fixed {ℓ : ℕ} (g : GKS K S)
    : ∀ P : TorsS K S ((Ecurve ℓ).baseChange K) (2 : ℤ), g • P = P := by
  rw [tate_ecurve_baseChange]
  exact smul_torsTwo_cubicCurve 0 (ℓ : K) (-3 * (ℓ : K)) g

/-- At an active place the actual central invariants are exactly the subgroup killed by two. -/
theorem active_fixed_iff_two_smul {W : WeierstrassCurve K} [W.IsElliptic] (v : Places K S)
    (hv : ActiveLocalAction W s hs hs0 v)
    (hRat : ∀ (g : GKS K S) (P : TorsS K S W (2 : ℤ)), g • P = P)
    (i : ℕ) (x : Mcoef K S W i (centralChar i s hs hs0)) :
    (∀ σ : Gloc K v.1, locMap K S v.1 σ • x = x) ↔ (2 : ℕ) • x = 0 := by
  constructor
  · intro hx
    obtain ⟨σ, _, hσ, ht⟩ := hv
    have hn := central_smul_of_torsion_fixed (s := s) (hs := hs) (hs0 := hs0) i _ (ht i) x
    rw [hσ, Units.val_neg, Units.val_one, neg_one_zsmul, hx σ] at hn
    rwa [two_nsmul, add_eq_zero_iff_eq_neg]
  · intro hx σ
    let f := CoefMod.equiv (Acoef i) (centralChar i s hs hs0) (TorsS K S W ((2 ^ i : ℕ) : ℤ))
    let b := (kannPB i).basis
    let c (k : Fin (kannPB i).dim) := kannCoordTens (kann_torsS_nsmul (S₀ := S) W i)
      (b.coord k).toAddMonoidHom (AddMonoidHom.id _)
    let y := f.symm x
    have hy : (2 : ℕ) • y = 0 := by
      simpa only [y, map_nsmul, map_zero] using congrArg f.symm hx
    have hcy (k) : (2 : ℕ) • c k y = 0 := by rw [← map_nsmul, hy, map_zero]
    have hrec : x = ∑ k, f (b k ⊗ₜ[ℤ] c k y) := by
      have hr := kannCoordTens_recon b (kann_torsS_nsmul (S₀ := S) W i) y
      refine (f.apply_symm_apply x).symm.trans ((congrArg f hr.symm).trans ?_)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hrec, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [central_tmul_smul, torsionFixed_of_two_smul hRat i _ _ (hcy k)]
    rcases Int.units_eq_one_or (quadChar s hs hs0 (locMap K S v.1 σ)) with hsign | hsign
    · rw [hsign, Units.val_one, one_zsmul]
    · rw [hsign, Units.val_neg, Units.val_one, neg_one_zsmul, neg_eq_iff_add_eq_zero, ← two_nsmul]
      have ht := congrArg (fun t => f (b k ⊗ₜ[ℤ] t)) (hcy k)
      simpa only [← TensorProduct.mk_apply, map_nsmul, map_zero] using ht

/-- Coordinates on the actual finite coefficient module from the Tate basis. -/
def centralCoordinates (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : ℕ)
    (hFull : FullTorsion K S (E.baseChange K) (2 ^ i)) :
    Mcoef K S (E.baseChange K) i (centralChar i s hs hs0) ≃ₗ[Acoef i] (Fin 2 → Acoef i) :=
  (tateCoefModBasis S E (tateAlgEquiv K) i (Acoef i) (centralChar i s hs hs0) hFull).equivFun

private theorem centralCoordinates_smul (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : ℕ)
    (hFull : FullTorsion K S (E.baseChange K) (2 ^ i))
    (v : Places K S) (φ : Gloc K v.1)
    (x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0)) :
    centralCoordinates E i hFull (locMap K S v.1 φ • x) =
      ((quadChar s hs hs0 (locMap K S v.1 φ) : ℤˣ) : ℤ) •
        ((localTateMatrix E v φ).map (constRed i)).mulVecLin (centralCoordinates E i hFull x) := by
  let b := tateCoefModBasis S E (tateAlgEquiv K) i (Acoef i) (centralChar i s hs hs0) hFull
  let f := (CoefMod.act (Acoef i) (centralChar i s hs hs0)
    (TorsS K S (E.baseChange K) ((2 ^ i : ℕ) : ℤ)) (locMap K S v.1 φ))
  let B := (localTateMatrix E v φ).map (constRed i)
  let L : (Fin 2 → Acoef i) →ₗ[Acoef i] (Fin 2 → Acoef i) :=
    (b.equivFun : _ →ₗ[Acoef i] _) ∘ₗ f ∘ₗ (b.equivFun.symm : _ →ₗ[Acoef i] _)
  let c : Acoef i := ((quadChar s hs hs0 (locMap K S v.1 φ) : ℤˣ) : ℤ)
  have hl : L = c • B.mulVecLin := by
    apply (Pi.basisFun (Acoef i) (Fin 2)).ext
    intro j
    have hb : b.equivFun.symm (Pi.basisFun (Acoef i) (Fin 2) j) = b j := by simp
    change b.equivFun (f (b.equivFun.symm (Pi.basisFun (Acoef i) (Fin 2) j))) = _
    rw [hb]
    change b.equivFun (locMap K S v.1 φ • b j) = _
    have hh := tateMcoefBasis_smul S E (tateAlgEquiv K) i (centralChar i s hs hs0) hFull
      (locMap K S v.1 φ) (decompMap K v.1 φ) (fun z => (resAbs_apply_coe K S (decompMap K v.1 φ) z).symm) j
    change locMap K S v.1 φ • b j = _ at hh
    rw [hh, map_sum]
    ext k
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, b, Module.Basis.equivFun_self,
      LinearMap.smul_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_apply]
    simp [centralChar_coe, c, B, localTateMatrix, constRed,
      ZInQ.Manuscript.RC.LambdaCoef.lamToAcoef_C, smul_eq_mul]
    rfl
  have he := congrArg (fun F : (Fin 2 → Acoef i) →ₗ[Acoef i] (Fin 2 → Acoef i) =>
    F (b.equivFun x)) hl
  change b.equivFun (f (b.equivFun.symm (b.equivFun x))) = c • B.mulVecLin (b.equivFun x) at he
  rw [LinearEquiv.symm_apply_apply] at he
  simpa only [centralCoordinates, CoefMod.smul_def, c, Int.cast_smul_eq_zsmul] using he

private theorem fixed_iff_frobenius {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ) (i : ℕ)
    (x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0)) :
    (∀ σ : Gloc K v.1, locMap K S v.1 σ • x = x) ↔ locMap K S v.1 H.frob • x = x := by
  refine ⟨fun hx => hx H.frob, fun hx => ?_⟩
  have hker σ (hσ : urRes K v.1 σ = 1) :
      ∀ y : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0), locMap K S v.1 σ • y = y := by
    intro y
    rw [central_smul_of_torsion_fixed i _ (H.unramifiedTorsion σ hσ i),
      H.unramifiedSign σ hσ, Units.val_one, one_zsmul]
  let π := urRes K v.1
  let _ : T2Space (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K v.1) := krullTopology_t2
  have hπ : Function.Surjective π := ZInQ.Manuscript.RC.SelmerComplex.urRes_surjective K v.1
  have hQ : Topology.IsQuotientMap π := π.continuous.isClosedMap.isQuotientMap π.continuous hπ
  let F : _ → Mcoef K S (E.baseChange K) i (centralChar i s hs hs0) :=
    fun g => locMap K S v.1 (Classical.choose (hπ g)) • x
  have hF (σ : Gloc K v.1) : F (π σ) = locMap K S v.1 σ • x := by
    let τ := Classical.choose (hπ (π σ))
    have hτ : π τ = π σ := Classical.choose_spec (hπ (π σ))
    have h0 : π (τ * σ⁻¹) = 1 := by rw [map_mul, map_inv, hτ, mul_inv_cancel]
    change locMap K S v.1 τ • x = _
    have he := hker (τ * σ⁻¹) h0 (locMap K S v.1 σ • x)
    rw [← mul_smul, ← map_mul, inv_mul_cancel_right] at he
    exact he
  have hFc : Continuous F := hQ.continuous_iff.mpr <| by
    change Continuous (fun σ => F (π σ))
    simp only [hF]
    exact ((locMap K S v.1).continuous.smul continuous_const)
  have hpow (n : ℤ) : locMap K S v.1 (H.frob ^ n) • x = x := by
    rw [map_zpow]
    exact (MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (GKS K S) x).zpow_mem (MulAction.mem_stabilizer_iff.mpr hx) n))
  have hall : F = fun _ => x := eq_of_eq_zpow (eUr K v.1) hFc continuous_const (fun n => by
    rw [← H.frob_ur, ← map_zpow, hF, hpow])
  intro σ
  rw [← hF, hall]

/-- Rank-two determinant identity used at the moving places. -/
theorem det_signed_frobenius_sub_one (F : Matrix (Fin 2) (Fin 2) ℤ_[2]) {r : ℕ} {a χ : ℤ}
    (htr : F.trace = (a : ℤ_[2])) (hdet : F.det = (r : ℤ_[2]))
    (hχ : χ = 1 ∨ χ = -1) :
    ((χ : ℤ_[2]) • F - 1).det = (((r : ℤ) + 1 - χ * a : ℤ) : ℤ_[2]) := by
  have hsq : (χ : ℤ_[2]) * (χ : ℤ_[2]) = 1 := by rcases hχ with h | h <;> norm_num [h]
  push_cast
  rw [← htr, ← hdet]
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, smul_eq_mul]
  linear_combination (F 0 0 * F 1 1 - F 0 1 * F 1 0) * hsq

/-- The moving-place invariant count, from the signed Frobenius matrix and Smith form. -/
theorem card_locH0_moving {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ)
    (hχ : χ = 1 ∨ χ = -1) (hN : (r : ℤ) + 1 - χ * a ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv : padicValInt 2 ((r : ℤ) + 1 - χ * a) ≤ i)
    (hFull : FullTorsion K S (E.baseChange K) (2 ^ i)) :
    Nat.card (locH (E.baseChange K) i (centralChar i s hs hs0) v 0) =
      2 ^ (padicValInt 2 ((r : ℤ) + 1 - χ * a) * i) := by
  let e := centralCoordinates (s := s) (hs := hs) (hs0 := hs0) E i hFull
  let B := (χ : ℤ_[2]) • localTateMatrix E v H.frob - 1
  have hdet : B.det = (((r : ℤ) + 1 - χ * a : ℤ) : ℤ_[2]) :=
    det_signed_frobenius_sub_one _ H.trace H.det hχ
  have hn : B.det ≠ 0 := by rw [hdet]; exact_mod_cast hN
  have hval : B.det.valuation = padicValInt 2 ((r : ℤ) + 1 - χ * a) := by
    rw [hdet, GenuineLocalBlockModel.valuation_intCast_padicInt]
  have hB : (B.map (constRed i)).mulVecLin =
      (χ : Acoef i) • ((localTateMatrix E v H.frob).map (constRed i)).mulVecLin - LinearMap.id := by
    rw [show B.map (constRed i) = (χ : Acoef i) •
        (localTateMatrix E v H.frob).map (constRed i) - 1 by
      ext j k
      simp [B, Matrix.one_apply]]
    apply LinearMap.ext
    intro x
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  let ef : {x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0) //
      ∀ σ : Gloc K v.1, locMap K S v.1 σ • x = x} ≃
      LinearMap.ker (B.map (constRed i)).mulVecLin := e.toEquiv.subtypeEquiv (fun x => by
    rw [fixed_iff_frobenius H i x, ← e.injective.eq_iff, LinearMap.mem_ker, hB,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have ht := centralCoordinates_smul (s := s) (hs := hs) (hs0 := hs0) E i hFull v H.frob x
    rw [H.sign, ← Int.cast_smul_eq_zsmul (Acoef i)] at ht
    change e (locMap K S v.1 H.frob • x) = _ at ht
    rw [ht]
    rfl)
  rw [Nat.card_congr ((locH0EquivFixed _ i _ v).trans ef), card_ker_eq_card_coker,
    card_coker_acoef B hn i hi (hval.symm ▸ hv), hval]

/-- The active-place invariant count. The scalar (2) on a rank-two free coefficient module
has a kernel of order (2^{2i}). -/
theorem card_locH0_active {E : WeierstrassCurve ℚ} [E.IsElliptic] (v : Places K S)
    (H : ActiveLocalAction (E.baseChange K) s hs hs0 v)
    (hRat : ∀ (g : GKS K S) (P : TorsS K S (E.baseChange K) (2 : ℤ)), g • P = P)
    (i : ℕ) (hi : i ≠ 0) (hFull : FullTorsion K S (E.baseChange K) (2 ^ i)) :
    Nat.card (locH (E.baseChange K) i (centralChar i s hs hs0) v 0) = 2 ^ (2 * i) := by
  let e := centralCoordinates (s := s) (hs := hs) (hs0 := hs0) E i hFull
  let B : Matrix (Fin 2) (Fin 2) ℤ_[2] := (2 : ℤ_[2]) • 1
  have hB : (B.map (constRed i)).mulVecLin =
      (2 : Acoef i) • (LinearMap.id : (Fin 2 → Acoef i) →ₗ[Acoef i] _) := by
    rw [show B.map (constRed i) = (2 : Acoef i) • (1 : Matrix (Fin 2) (Fin 2) (Acoef i)) by
      ext j k
      have hc : constRed i (2 : ℤ_[2]) = (2 : Acoef i) := map_ofNat (constRed i) 2
      by_cases h : j = k
      · simpa [B, h] using hc
      · simp [B, h]]
    apply LinearMap.ext
    intro x
    simp only [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hdet : B.det = 2 ^ 2 := by
    change ((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det = _
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hn : B.det ≠ 0 := hdet.symm ▸ pow_ne_zero 2 two_ne_zero
  have hval : B.det.valuation = 2 := by
    rw [hdet, PadicInt.valuation_pow, valuation_two_padicInt', mul_one]
  let ef : {x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0) //
      ∀ σ : Gloc K v.1, locMap K S v.1 σ • x = x} ≃
      LinearMap.ker (B.map (constRed i)).mulVecLin := e.toEquiv.subtypeEquiv (fun x => by
    rw [active_fixed_iff_two_smul v H hRat, LinearMap.mem_ker, hB,
      LinearMap.smul_apply, LinearMap.id_apply]
    change (2 : ℕ) • x = 0 ↔ (2 : Acoef i) • e x = 0
    rw [← Nat.cast_ofNat (R := Acoef i), Nat.cast_smul_eq_nsmul, ← map_nsmul e]
    exact (map_eq_zero_iff e e.injective).symm)
  rw [Nat.card_congr ((locH0EquivFixed _ i _ v).trans ef)]
  by_cases hi2 : 2 ≤ i
  · rw [card_ker_eq_card_coker, card_coker_acoef B hn i hi (hval.symm ▸ hi2), hval]
  · have hi1 : i = 1 := by omega
    subst i
    have h0 : (2 : Acoef 1) = 0 := by simpa using acoef_two_pow_eq_zero 1
    have hk : LinearMap.ker (B.map (constRed 1)).mulVecLin = ⊤ := by
      apply Submodule.eq_top_iff'.2
      intro x
      rw [LinearMap.mem_ker, hB, LinearMap.smul_apply, LinearMap.id_apply, h0]
      exact zero_smul (Acoef 1) x
    rw [hk, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_fun, card_acoef 1 one_ne_zero]
    simp

end ZInQ.Contrib.RC53Assist.Calibration
