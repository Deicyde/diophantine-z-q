import ZInQKernel.Contrib.OneProof.RC.CalPres.Presentations

/-! The finite coefficient actions used by the two local models. -/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open NumberField IsDedekindDomain CategoryTheory Matrix TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs_apply_coe)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}

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

/-- The finite Tate coordinates transport the actual action of a local element to its integral
Tate matrix with the central quadratic sign, reduced to the stage ring.
This is the linear transport underlying the invariant count in `CalLocalLengths.LocalOrders`. -/
theorem centralSignedTateAction (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : ℕ)
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

/-- Both factors of the moving central coefficient are unramified, so inertia acts trivially. -/
theorem movingInertiaAction {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ) (i : ℕ)
    (σ : Gloc K v.1) (hσ : urRes K v.1 σ = 1)
    (x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0)) :
    locMap K S v.1 σ • x = x := by
  rw [central_smul_of_torsion_fixed i _ (H.unramifiedTorsion σ hσ i),
    H.unramifiedSign σ hσ, Units.val_one, one_zsmul]

/-- At an active place the stipulated inertia element acts as minus the identity on the actual
finite central coefficient at every precision. -/
theorem activeInertiaAction {W : WeierstrassCurve K} [W.IsElliptic] {v : Places K S}
    (H : ActiveLocalAction W s hs hs0 v) :
    ∃ σ : Gloc K v.1, urRes K v.1 σ = 1 ∧
      ∀ (i : ℕ) (x : Mcoef K S W i (centralChar i s hs hs0)), locMap K S v.1 σ • x = -x := by
  obtain ⟨σ, hσ, hc, ht⟩ := H
  refine ⟨σ, hσ, fun i x => ?_⟩
  rw [central_smul_of_torsion_fixed i _ (ht i), hc, Units.val_neg, Units.val_one, neg_one_zsmul]

/-- In finite Tate coordinates, a signed integral Tate matrix minus a scalar acts by the
actual local element minus that scalar. -/
theorem signedReduced_subScalar {E : WeierstrassCurve ℚ} [E.IsElliptic] (v : Places K S)
    (φ : Gloc K v.1) {χ : ℤ} (hχ : (quadChar s hs hs0 (locMap K S v.1 φ) : ℤ) = χ)
    (i q : ℕ) (hFull : FullTorsion K S (E.baseChange K) (2 ^ i))
    (x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0)) :
    reduceLocalBlock i ((χ : ℤ_[2]) • localTateMatrix E v φ - (q : ℤ_[2]) • 1)
        (centralCoordinates E i hFull x) =
      centralCoordinates E i hFull (locMap K S v.1 φ • x) -
        (q : Acoef i) • centralCoordinates E i hFull x := by
  have hm : (((χ : ℤ_[2]) • localTateMatrix E v φ - (q : ℤ_[2]) • 1).map (constRed i)) =
      (χ : Acoef i) • (localTateMatrix E v φ).map (constRed i) - (q : Acoef i) • 1 := by
    ext j k
    by_cases hjk : j = k <;> simp [hjk]
  have ht := centralSignedTateAction (s := s) (hs := hs) (hs0 := hs0) E i hFull v φ x
  rw [hχ, ← Int.cast_smul_eq_zsmul (Acoef i)] at ht
  rw [reduceLocalBlock, hm, ht]
  simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The instances `q = 1` and `q = r` of the moving action are the ordinary and singular
differentials of the tame model, respectively. -/
theorem movingReduced_subScalar {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ) (i q : ℕ)
    (hFull : FullTorsion K S (E.baseChange K) (2 ^ i))
    (x : Mcoef K S (E.baseChange K) i (centralChar i s hs hs0)) :
    reduceLocalBlock i ((χ : ℤ_[2]) • localTateMatrix E v H.frob - (q : ℤ_[2]) • 1)
        (centralCoordinates E i hFull x) =
      centralCoordinates E i hFull (locMap K S v.1 H.frob • x) -
        (q : Acoef i) • centralCoordinates E i hFull x :=
  signedReduced_subScalar v H.frob H.sign i q hFull x

/-- At an active place, the signed integral Tate action of any Frobenius lift minus one
is twice an integral matrix, because the actual action at precision one is trivial. -/
theorem activeSignedTate_subOne_even {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    (H : ActiveLocalAction (E.baseChange K) s hs hs0 v)
    (hRat : ∀ (g : GKS K S) (P : TorsS K S (E.baseChange K) (2 : ℤ)), g • P = P)
    (hFull : FullTorsion K S (E.baseChange K) (2 ^ 1)) (φ : Gloc K v.1) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℤ_[2],
      (((quadChar s hs hs0 (locMap K S v.1 φ) : ℤ) : ℤ_[2]) • localTateMatrix E v φ - 1) =
        (2 : ℤ_[2]) • T := by
  let χ : ℤ := quadChar s hs hs0 (locMap K S v.1 φ)
  let B := (χ : ℤ_[2]) • localTateMatrix E v φ - 1
  let e := centralCoordinates (s := s) (hs := hs) (hs0 := hs0) E 1 hFull
  have h2 : (2 : Acoef 1) = 0 := by simpa using acoef_two_pow_eq_zero 1
  have hkill (x : Mcoef K S (E.baseChange K) 1 (centralChar 1 s hs hs0)) :
      (2 : ℕ) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (Acoef 1), Nat.cast_ofNat, h2]
    exact zero_smul (Acoef 1) x
  have hzero (y : Fin 2 → Acoef 1) : reduceLocalBlock 1 B y = 0 := by
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx := (active_fixed_iff_two_smul v H hRat 1 x).2 (hkill x) φ
    have ha := signedReduced_subScalar v φ (show _ = χ from rfl) 1 1 hFull x
    simpa only [Nat.cast_one, one_smul, hx, sub_self, B, e] using ha
  have hred (j k : Fin 2) : constRed 1 (B j k) = 0 := by
    have he := congrFun (hzero (Pi.single k 1)) j
    simpa only [reduceLocalBlock, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.map_apply, Pi.zero_apply] using he
  have hdvd (j k : Fin 2) : (2 : ℤ_[2]) ∣ B j k := by
    have hz := congrArg (acoefResidue 1 one_ne_zero) (hred j k)
    have hp : PadicInt.toZModPow 1 (B j k) = 0 := by
      simpa only [constRed, RingHom.comp_apply, ZInQ.Manuscript.RC.LambdaCoef.lamToAcoef_C,
        acoefResidue_mk, Polynomial.coeff_C_zero, ZMod.cast_id, map_zero] using hz
    have hm : B j k ∈ RingHom.ker (PadicInt.toZModPow 1) := RingHom.mem_ker.mpr hp
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hm
    exact hm
  choose T hT using hdvd
  refine ⟨T, ?_⟩
  apply Matrix.ext
  intro j k
  change B j k = (2 : ℤ_[2]) * T j k
  exact hT j k

/-- At finite precision the active integral differential acts as multiplication by two. -/
theorem activeReduced_apply (i : ℕ) (x : Fin 2 → Acoef i) :
    reduceLocalBlock i activeBlock x = (2 : Acoef i) • x := by
  simp only [reduceLocalBlock, activeBlock, PresentsLocalQuotient.map_two_smul_one, Matrix.mulVecLin_apply,
    Matrix.smul_mulVec, Matrix.one_mulVec]


end ZInQ.Contrib.RC53Assist.Calibration
