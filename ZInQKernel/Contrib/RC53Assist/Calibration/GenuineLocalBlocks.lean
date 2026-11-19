import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerImage
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.FiniteLevel
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf3

/-!
# The local blocks of the calibration over the genuine Kummer images

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 4000–4080), with Lemma
`ex:arith-local-kummer` (tex 3413–3456) and the coefficient conventions of tex 2720–2760.

The calibration leaf `CalibrationModelH` models the central full/Kummer quotient block `D_W` at
the moving and active places by existential matrices: `D_W = P_W · diag(twoPlaceBlock Fr r z z',
B_act) · Q_W` with unit changes of basis, `tr Fr(0) = a_r`, `det Fr(0) = r`, `z(0) = z'(0) = χ`,
`B_act(0) = 2 · 1`. None of these matrices is tied to the Kummer local conditions whose
quotients they model, so the block structure carries no information beyond its valuation formula.
This file restates the local blocks over the genuine Kummer images: the central integral local
blocks are required to present, at every precision `i`, the genuine central full/Kummer quotients
at the places where they sit, for the actual Kummer condition of the local Kummer maps (genuine
coefficient map through the quadratic-twist identification, `H¹`-image the span of the actual
local Kummer map).

Mathematical content (all objects at precision `i`, coefficient ring `A_i = (ℤ/2^i)[t]/t^i`):

* `centralChar i s`: the coefficient character `χ_h` with trivial moving character (the centre
  `t = 0` kills the moving character, tex 4066–4080); it equals `χ_h` on every decomposition group
  (`isLocallyQuadAt_centralChar`), so the actual Kummer condition exists at every place, including
  the two places above the moving prime and the active places.
* For `M_i = (E[2^i] ⊗ A_i)(χ_h)` and a place `v`: `locH v n = Hⁿ(K_v, M_i)`; `kummerImageH1`,
  the image of `H¹` of the actual Kummer condition at `v`, **is the `A_i`-span of the image of the
  actual local Kummer map `E^{(h)}(K_v) → H¹(K_v, M_i)`** (`kummerImageH1_eq_span`); `H⁰` of the
  condition is all of `H⁰(K_v, M_i)` and its `H¹` injects (`kummerCondition_isIso_H0`,
  `kummerCondition_mono_H1`); the condition is that of the actual local twist, the base change of
  the global twist (`kummerTwist_eq_baseChange`), with coefficient map `t ↦ 1 ⊗ j⁻¹(φ_q t)` through
  the twist identification `φ_q` (`kummerCoefficientMap_apply`), injective for `i ≠ 0`
  (`kummerCoefficientMap_injective`). Since the condition is concentrated in degrees zero and one,
  the full/Kummer quotient at `v` has `H¹ = H¹(K_v, M_i)/(Kummer image)` (`quotH1`) and
  `H² = H²(K_v, M_i)`.
* `PresentsLocalQuotient … v B`: the integral matrix `B ∈ M_m(ℤ₂)`, reduced to `A_i`, is a
  two-term model of that quotient in degrees one and two: `ker B̄ ≅ H¹(K_v, M_i)/(Kummer image)`
  and `coker B̄ ≅ H²(K_v, M_i)` as `A_i`-modules.
* Consequences for the genuine groups (PROVED): `card_quotH1_eq_card_locH2` — the quotient of
  `H¹(K_v, M_i)` by the genuine Kummer image has the order of `H²(K_v, M_i)`;
  `det_smul_quotH1`, `det_smul_locH2` — both are killed by `det B`; `two_smul_quotH1`,
  `two_smul_locH2` — at a place presented by the minimal model `2 · 1` both are killed by `2`.
* Orders over `A_i` (PROVED): `card_acoef_quot` (`|A_i/(2^v)| = 2^{vi}` for `v ≤ i`),
  `smith_matrix` (Smith normal form over `ℤ₂` in matrix form) and `card_coker_acoef`: for
  `B ∈ M_m(ℤ₂)` with `det B ≠ 0` and `v₂ det B ≤ i`, the cokernel of `B̄` over `A_i` has
  `2^{i · v₂ det B}` elements. Hence `card_locH2_eq`, `card_quotH1_eq`: at a place presented by
  `B`, `|H²(K_v, M_i)| = |H¹(K_v, M_i)/(Kummer image)| = 2^{i · v₂ det B}`; and
  `valuation_det_eq`: the genuine order determines `v₂ det B`.
* `GenuineLocalBlockModel`: the local-block fields of `CalibrationModelH`, the integral central
  Frobenius (`Fr(0) = Fr_ℤ`), two distinct places above the moving prime, `2ω(h)` distinct places
  above primes dividing `h`, and the presentations at every precision: by the central moving block
  `χ Fr_ℤ − r` at the two places above `r`, by `2 · 1₂` at each active place.
  `central_moving_blocks`, `central_active_block`: the presented blocks are the central values of
  the model's blocks. `hδ`: the quotient length `v₂ det D_W(0) = 2 v₂ N + 4ω`.
  `trace_FrZ`, `det_FrZ`, `det_moving` (`det(χ Fr_ℤ − r) = r N`), `moving_killed`,
  `two_smul_active`: `r N`, resp. `2`, kills the genuine quotient. **`length_moving`: the central
  full/Kummer quotient at the places above the moving prime has degree-two length `v₂ N`**
  (`|H²(K_w, M_i)| = 2^{i v₂N}` for `i ≥ v₂N`, tex 4066–4072); **`length_active`: at each active
  place it has length two** (`|H²(K_v, M_i)| = 2^{2i}` for `i ≥ 2`, tex 4076–4078); both for the
  quotient of `H¹` by the genuine Kummer image as well.
* `CalibrationModelHG`: `CalibrationModelH` with its local-block fields replaced by one
  `GenuineLocalBlockModel` over the leaf's field `K`, the fixed curve and the twist `h_x`;
  `CalibrationModelHG.toModelH`, `CalibrationModelHG.nonempty_modelP`, `calibrationInputsH_of_HG`,
  `calibrationTarget_of_HG` (PROVED).
* `GenuineLengthBlockModel`: the converse direction, without the Frobenius trace and determinant,
  the central moving scalars and the central active block: the central quotient block is a block
  sum of integral local blocks, each presenting the genuine central full/Kummer quotient at its
  place, and the genuine quotients have the lengths of the text (`v₂ N` above the moving prime, two
  at the active places). `det_ne_zero_of_length` (the local blocks are rationally invertible: a
  singular block would have a cokernel as large as `A_i`, `card_coker_ge_of_det_eq_zero`),
  `valuation_of_length`, **`GenuineLengthBlockModel.hδ`: `v₂ det D_W(0) = 2 ℓ_mov + 4ω`, derived
  from the genuine lengths.**
* `MilneLocalDualityOrder` (PRINT, Milne ADT I.2.3, the local finite duality cited at tex
  3442–3445, as one separate leaf): `|H²(K_v, M_i)| = |H⁰(K_v, M_i)|` for a self-dual coefficient
  character. `centralChar_mul_self`, `length_H2_of_H0`: the degree-two length inputs of
  `GenuineLengthBlockModel` follow from degree-zero lengths, i.e. from the orders of
  `H⁰(K_v, M_i) = E^{(h)}(K_v)[2^i] ⊗ A_i` (the local points).
* `CalibrationModelHL`: `CalibrationModelH` with its local-block fields replaced by one
  `GenuineLengthBlockModel`; `CalibrationModelHL.nonempty_modelP` (to `CalibrationModelP`),
  `calibrationInputsP_of_HL`, `calibrationTarget_of_HL` (PROVED).

**Status.** The presentations genuinely constrain the matrices. The length inputs `lenMov`,
`lenMov'`, `lenAct` of `GenuineLengthBlockModel` are exactly the local determinant valuations of
the presenting blocks (`Recorded.genuine_length_iff_local_det`): they are explicit arithmetic
suppliers, not derived here. `GenuineLengthBlockModel` does not require its moving number to be
prime, nor tie `a_r`, `χ` to the curve (`Recorded.compositeMovingNumber`); the ties are
`MovingPrimeData`, a field of the leaf `CalibrationModelHKL2`.

Kinds: definitions and PROVED theorems, and one PRINT leaf (`MilneLocalDualityOrder`, used only
in `length_H2_of_H0`). The inputs are the presentations (each identifies a local quotient of the
actual Kummer condition with its two-term model, tex 4066–4080), for `GenuineLengthBlockModel`
the genuine lengths, and the fields kept from `CalibrationModelH`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open NumberField IsDedekindDomain CategoryTheory Matrix
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.TwistDictionary (twistK)

/-! ### The central coefficient character -/

section CentralCharacter

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The central coefficient character** `χ_h` at precision `i`: the coefficient character
`α_i = χ_h Ψ_i` with the moving character `Ψ_i` replaced by its central value `1`. -/
abbrev centralChar (i : ℕ) (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h)
    (hs0 : s ≠ 0) : GKS K S →* (Acoef i)ˣ :=
  alphaChar i (quadChar s hs hs0) 1

/-- The central character has open kernel. PROVED. -/
instance centralChar_isOpenKer (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) : IsOpenKer (centralChar i s hs hs0) :=
  alphaChar_isOpenKer i _ _ (by
    have : ((1 : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))).ker : Set (GKS K S)) =
        Set.univ := by
      ext g; simp
    rw [this]; exact isOpen_univ)

/-- **The central character is `χ_h` on every decomposition group** (the moving character is
trivial at the centre). PROVED. -/
theorem isLocallyQuadAt_centralChar (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyQuadAt i (centralChar i s hs hs0) (quadChar s hs hs0) v :=
  isLocallyQuadAt_alphaChar i _ 1 v fun _ => rfl

end CentralCharacter

/-! ### The genuine local Kummer image and the full/Kummer quotient at one place -/

section Local

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (v : Places K S)

/-- `Hⁿ(K_v, M_i)`, the cohomology of the continuous local cochains of `M_i`. -/
abbrev locH (n : ℤ) : ModuleCat (Acoef i) :=
  (locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.homology n

variable (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S W (2 ^ i)) (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1)

/-- **The Kummer image at `v`**: the image of `H¹` of the actual Kummer condition in
`H¹(K_v, M_i)`. -/
def kummerImageH1 : Submodule (Acoef i) (locH W i α v 1) :=
  LinearMap.range (HomologicalComplex.homologyMap
    (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1).hom

/-- **The Kummer image is the `A_i`-span of the image of the actual local Kummer map**
`E^{(h)}(K_v) → H¹(K_v, M_i)` (tex 3415–3418, 3430–3432). PROVED (the local Kummer maps'
`actualKummerAt_range_eq_span`). -/
theorem kummerImageH1_eq_span :
    kummerImageH1 W i α v s hs hs0 hFull hα =
      Submodule.span (Acoef i) (Set.range (actualKummerMap W i s hs hs0 α hFull v hα)) :=
  actualKummerAt_range_eq_span W i s hs hs0 α hFull v hα

/-- `H⁰` of the actual Kummer condition is all of `H⁰(K_v, M_i)` (tex 3415–3417). PROVED. -/
theorem kummerCondition_isIso_H0 :
    IsIso (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 0) :=
  actualKummerAt_isIso_H0 W i s hs hs0 α hFull v hα

/-- `H¹` of the actual Kummer condition injects into `H¹(K_v, M_i)` (tex 3415–3418). PROVED. -/
theorem kummerCondition_mono_H1 :
    Mono (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1) :=
  actualKummerAt_mono_H1 W i s hs hs0 α hFull v hα

omit [W.IsElliptic] [IsOpenKer α] in
/-- **The Kummer condition is that of the actual local twist `E^{(h)}` over `K_v`, the base change
of the global twist** (tex 3413–3416). PROVED. -/
theorem kummerTwist_eq_baseChange :
    localTwist W h v.1 = (twistK W h).baseChange (v.1.adicCompletion K) :=
  localTwist_eq_baseChange W h v.1

omit [IsOpenKer α] in
/-- **The coefficient map of the Kummer condition** is `t ↦ 1 ⊗ j⁻¹(φ_q t)`: the
quadratic-twist identification `φ_q : E^{(h)}[2^i] ≅ E[2^i]` at the local square root
`q = j(s)`, the comparison `j` along the fixed embedding, and `t ↦ 1 ⊗ t` into `M_i`
(tex 3413–3438). PROVED (definitional). -/
theorem kummerCoefficientMap_apply
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kummerIota W i s hs hs0 α hFull v.1 t =
      toResModAdd (locMap K S v.1) (Mcoef K S W i α)
        (oneTmul (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))
          ((compTorsEquiv W (2 ^ i) hFull v.1).symm
            (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) h)
              two_ne_zero (localSqrt_ne_zero s hs0 v.1) (localSqrt_sq s hs v.1) (2 ^ i) t))) :=
  rfl

omit [IsOpenKer α] in
/-- The coefficient map of the Kummer condition is injective for `i ≠ 0`. PROVED. -/
theorem kummerCoefficientMap_injective (hi : i ≠ 0) :
    Function.Injective (kummerIota W i s hs hs0 α hFull v.1) :=
  kummerIotaBase_injective W i s hs hs0 α hFull v.1 hi

/-- **`H¹` of the central full/Kummer quotient at `v`**: `H¹(K_v, M_i)` modulo the Kummer image. -/
abbrev quotH1 : Type := (locH W i α v 1) ⧸ kummerImageH1 W i α v s hs hs0 hFull hα

end Local

/-! ### Orders of cokernels over `A_i` (Smith normal form over `ℤ₂`) -/

section Orders

open Polynomial

/-- `|ℤ/2^i ⧸ (2^v)| = 2^v` for `v ≤ i`. PROVED. -/
theorem card_zmod_quot (i v : ℕ) (hv : v ≤ i) :
    Nat.card (ZMod (2 ^ i) ⧸ Ideal.span {(2 : ZMod (2 ^ i)) ^ v}) = 2 ^ v := by
  have hdvd : 2 ^ v ∣ 2 ^ i := pow_dvd_pow 2 hv
  let f : ZMod (2 ^ i) →+* ZMod (2 ^ v) := ZMod.castHom hdvd (ZMod (2 ^ v))
  have hsurj : Function.Surjective f := ZMod.ringHom_surjective f
  have hker : RingHom.ker f = Ideal.span {(2 : ZMod (2 ^ i)) ^ v} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective x
      have : ((y : ℕ) : ZMod (2 ^ v)) = 0 := by
        simpa [f, map_natCast] using hx
      rw [ZMod.natCast_eq_zero_iff] at this
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, by push_cast; ring⟩
    · rintro ⟨c, rfl⟩
      rw [map_mul, map_pow, map_ofNat]
      have : (2 : ZMod (2 ^ v)) ^ v = 0 := by
        rw [show (2 : ZMod (2 ^ v)) ^ v = ((2 ^ v : ℕ) : ZMod (2 ^ v)) by push_cast; ring]
        exact ZMod.natCast_self _
      rw [this, zero_mul]
  rw [← hker, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv]
  exact Nat.card_zmod _

/-- `|A_i ⧸ (2^v)| = 2^{v i}` for `v ≤ i` (`A_i` is free of rank `i` over `ℤ/2^i`). PROVED. -/
theorem card_acoef_quot (i v : ℕ) (hi : i ≠ 0) (hv : v ≤ i) :
    Nat.card (Acoef i ⧸ Ideal.span {(2 : Acoef i) ^ v}) = 2 ^ (v * i) := by
  classical
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  set R := ZMod (2 ^ i)
  set c : R := (2 : R) ^ v with hc
  let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := R) i)
  have hdim : pb.dim = i := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]
  let e : Acoef i ≃ₗ[R] (Fin pb.dim → R) := pb.basis.equivFun
  set J : Ideal (Acoef i) := Ideal.span {(2 : Acoef i) ^ v}
  have h2 : (2 : Acoef i) ^ v = algebraMap R (Acoef i) c := by
    rw [hc, map_pow, map_ofNat]
  have hJ : ∀ x : Acoef i, x ∈ J ↔ ∃ y : Acoef i, x = c • y := by
    intro x
    rw [Ideal.mem_span_singleton', h2]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, by rw [mul_comm]; exact (Algebra.smul_def c b).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [mul_comm]; exact (Algebra.smul_def c y).symm⟩
  let Q : Submodule R (Fin pb.dim → R) :=
    Submodule.pi Set.univ (fun _ => (Ideal.span {c} : Submodule R R))
  have hmap : (J.restrictScalars R).map (e : Acoef i →ₗ[R] (Fin pb.dim → R)) = Q := by
    ext x
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, LinearEquiv.coe_coe, Q,
      Submodule.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨a, ha, rfl⟩ j
      obtain ⟨y, rfl⟩ := (hJ a).1 ha
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
    · intro hx
      choose b hb using fun j => Ideal.mem_span_singleton'.1 (hx j)
      refine ⟨c • e.symm b, (hJ _).2 ⟨_, rfl⟩, ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      ext j
      rw [Pi.smul_apply, smul_eq_mul, ← hb j, mul_comm]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv R J).toEquiv
  have e2 := (Submodule.Quotient.equiv (J.restrictScalars R) Q e hmap).toEquiv
  have e3 := (Submodule.quotientPi (fun _ : Fin pb.dim => (Ideal.span {c} : Submodule R R))).toEquiv
  rw [← Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr e3, Nat.card_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdim]
  rw [show (Ideal.span {c} : Submodule R R) = Ideal.span {(2 : ZMod (2 ^ i)) ^ v} from rfl]
  rw [card_zmod_quot i v hv, ← pow_mul]


section Smith

open Matrix

variable {m : ℕ}

/-- A square matrix over `ℤ₂` with nonzero determinant is injective. PROVED. -/
theorem mulVecLin_injective_of_det_ne_zero (B : Matrix (Fin m) (Fin m) ℤ_[2]) (h : B.det ≠ 0) :
    Function.Injective B.mulVecLin := by
  intro x y hxy
  have h1 := congrArg (fun z => B.adjugate *ᵥ z) hxy
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  funext j
  have h2 := congrFun h1 j
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ h h2

/-- **Smith normal form over `ℤ₂` in matrix form**: `B = P · diag(a) · C` and `P · diag(a) = B · X`
with `P` invertible, `a_j ≠ 0`, and `det B` associated to `∏ a_j`. PROVED. -/
theorem smith_matrix (B : Matrix (Fin m) (Fin m) ℤ_[2]) (h : B.det ≠ 0) :
    ∃ (P Q C X : Matrix (Fin m) (Fin m) ℤ_[2]) (a : Fin m → ℤ_[2]),
      P * Q = 1 ∧ Q * P = 1 ∧ B = P * diagonal a * C ∧ P * diagonal a = B * X ∧
      (∀ j, a j ≠ 0) ∧ Associated B.det (∏ j, a j) := by
  classical
  set f := B.mulVecLin with hf
  have hinj := mulVecLin_injective_of_det_ne_zero B h
  set N := LinearMap.range f
  let e : (Fin m → ℤ_[2]) ≃ₗ[ℤ_[2]] N := LinearEquiv.ofInjective f hinj
  have hrank : Module.finrank ℤ_[2] N = Module.finrank ℤ_[2] (Fin m → ℤ_[2]) :=
    (LinearEquiv.finrank_eq e).symm
  let b := Pi.basisFun ℤ_[2] (Fin m)
  let b' := N.smithNormalFormTopBasis b hrank
  let a := N.smithNormalFormCoeffs b hrank
  let ab := N.smithNormalFormBotBasis b hrank
  have hab : ∀ j, (ab j : Fin m → ℤ_[2]) = a j • b' j := N.smithNormalFormBotBasis_def b hrank
  let P : Matrix (Fin m) (Fin m) ℤ_[2] := b.toMatrix b'
  let Q : Matrix (Fin m) (Fin m) ℤ_[2] := b'.toMatrix b
  have hPcol : ∀ j k, P k j = b' j k := fun j k => by
    simp [P, Module.Basis.toMatrix_apply, b]
  -- preimages of the Smith generators
  have hpre : ∀ j, ∃ x, B *ᵥ x = a j • b' j := by
    intro j
    obtain ⟨x, hx⟩ := (ab j).2
    exact ⟨x, by rw [← hab j, ← hx]; rfl⟩
  choose xs hxs using hpre
  -- coordinates of the columns of `B`
  let C : Matrix (Fin m) (Fin m) ℤ_[2] :=
    Matrix.of fun j k => ab.repr ⟨B *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ j
  let X : Matrix (Fin m) (Fin m) ℤ_[2] := Matrix.of fun k j => xs j k
  have hcol : ∀ k, B *ᵥ Pi.single k 1 = ∑ j, C j k • a j • b' j := by
    intro k
    have h2 := congrArg Subtype.val (ab.sum_repr ⟨B *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hab] at h2
    exact h2.symm
  refine ⟨P, Q, C, X, a, b.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip b, ?_, ?_,
    N.smithNormalFormCoeffs_ne_zero b hrank, ?_⟩
  · refine Matrix.ext fun r k => ?_
    have h1 := congrFun (hcol k) r
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [h1, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hPcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Matrix.ext fun r j => ?_
    have h1 := congrFun (hxs j) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, hPcol, Matrix.mul_apply]
    simp only [X, Matrix.of_apply]
    rw [h1]
    ring
  · -- determinants
    let e' : (Fin m → ℤ_[2]) ≃ₗ[ℤ_[2]] N := b'.equiv ab (Equiv.refl _)
    have h1 : LinearMap.det (N.subtype ∘ₗ (e : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] N)) = B.det := by
      have : N.subtype ∘ₗ (e : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] N) = Matrix.toLin' B := by
        refine LinearMap.ext fun y => ?_
        rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
          LinearEquiv.ofInjective_apply, Matrix.toLin'_apply]
        rfl
      rw [this, LinearMap.det_toLin']
    have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] N)) = ∏ j, a j := by
      rw [← LinearMap.det_toMatrix b']
      have : LinearMap.toMatrix b' b' (N.subtype ∘ₗ (e' : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] N)) =
          Matrix.diagonal a := by
        ext r j
        rw [LinearMap.toMatrix_apply]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, e',
          Module.Basis.equiv_apply, Equiv.refl_apply, hab, map_smul, Module.Basis.repr_self,
          Finsupp.smul_single, smul_eq_mul, mul_one]
        by_cases hrj : r = j
        · subst hrj; simp
        · simp [Ne.symm hrj, Matrix.diagonal_apply_ne _ hrj]
      rw [this, Matrix.det_diagonal]
    have := LinearMap.associated_det_comp_equiv N.subtype e e'
    rwa [h1, h2] at this

/-- A unit of `ℤ₂` has valuation zero. PROVED. -/
theorem valuation_unit_padicInt (u : ℤ_[2]ˣ) : (u : ℤ_[2]).valuation = 0 := by
  have h := congrArg PadicInt.valuation u.mul_inv
  rw [PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹), PadicInt.valuation_one] at h
  omega

/-- Associated elements of `ℤ₂` have the same valuation. PROVED. -/
theorem valuation_eq_of_associated {x y : ℤ_[2]} (h : Associated x y) :
    x.valuation = y.valuation := by
  obtain ⟨u, rfl⟩ := h
  by_cases hx : x = 0
  · simp [hx]
  · rw [PadicInt.valuation_mul hx (Units.ne_zero u), valuation_unit_padicInt, add_zero]

/-- The valuation of a product of nonzero elements of `ℤ₂` is the sum of the valuations. PROVED. -/
theorem valuation_prod_padicInt {ι : Type*} (s : Finset ι) (f : ι → ℤ_[2])
    (hf : ∀ j ∈ s, f j ≠ 0) : (∏ j ∈ s, f j).valuation = ∑ j ∈ s, (f j).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      PadicInt.valuation_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- The reduction `ℤ₂ → A_i` of constants (the reduction `Λ → A_i` on constant power series). -/
abbrev constRed (i : ℕ) : ℤ_[2] →+* Acoef i :=
  (ZInQ.Manuscript.RC.LambdaCoef.lamToAcoef i).comp PowerSeries.C

/-- **The order of the cokernel of a reduced integral matrix**: for `B ∈ M_m(ℤ₂)` with
`det B ≠ 0` and `v₂ det B ≤ i`, the cokernel of its reduction to `A_i` has `2^{i · v₂ det B}`
elements. PROVED (Smith normal form over `ℤ₂`). -/
theorem card_coker_acoef (B : Matrix (Fin m) (Fin m) ℤ_[2]) (h : B.det ≠ 0) (i : ℕ) (hi : i ≠ 0)
    (hv : (B.det).valuation ≤ i) :
    Nat.card ((Fin m → Acoef i) ⧸ LinearMap.range (Matrix.mulVecLin (B.map (constRed i)))) =
      2 ^ ((B.det).valuation * i) := by
  classical
  obtain ⟨P, Q, C, X, a, hPQ, hQP, hB, hPD, ha0, hassoc⟩ := smith_matrix B h
  set φ := constRed i with hφ
  have hval : (B.det).valuation = ∑ j, (a j).valuation := by
    rw [valuation_eq_of_associated hassoc, valuation_prod_padicInt _ _ (fun j _ => ha0 j)]
  set D : Matrix (Fin m) (Fin m) (Acoef i) := diagonal (fun j => φ (a j)) with hDdef
  have hdiag : (diagonal a).map φ = D := by
    rw [hDdef, Matrix.diagonal_map (map_zero φ)]
  have hPD' : (P.map φ) * D = (B.map φ) * (X.map φ) := by
    have := congrArg (fun M => M.map φ) hPD
    simp only [Matrix.map_mul, hdiag] at this
    exact this
  have hB' : B.map φ = (P.map φ) * D * (C.map φ) := by
    have := congrArg (fun M => M.map φ) hB
    simp only [Matrix.map_mul, hdiag] at this
    exact this
  have hrange : LinearMap.range (B.map φ).mulVecLin =
      (LinearMap.range D.mulVecLin).map (P.map φ).mulVecLin := by
    rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
    apply le_antisymm
    · rw [hB', Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · rw [hPD', Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
  have hPQ' : (P.map φ) * (Q.map φ) = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQP' : (Q.map φ) * (P.map φ) = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero φ) (map_one φ)]
  let Ψ : (Fin m → Acoef i) ≃ₗ[Acoef i] (Fin m → Acoef i) :=
    LinearEquiv.ofLinearMap (P.map φ).mulVecLin (Q.map φ).mulVecLin
      (by rw [← Matrix.mulVecLin_mul, hPQ', Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hQP', Matrix.mulVecLin_one])
  have hD : LinearMap.range D.mulVecLin = Submodule.pi Set.univ
      (fun j => (Ideal.span {φ (a j)} : Submodule (Acoef i) (Acoef i))) := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
      forall_const, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩ j
      exact ⟨y j, by rw [hDdef, Matrix.mulVec_diagonal, mul_comm]⟩
    · intro hx
      choose y hy using hx
      refine ⟨y, funext fun j => ?_⟩
      rw [hDdef, Matrix.mulVec_diagonal, ← hy j, mul_comm]
  have e1 := (Submodule.Quotient.equiv (LinearMap.range D.mulVecLin)
    (LinearMap.range (B.map φ).mulVecLin) Ψ hrange.symm).toEquiv
  have e2 := (Submodule.quotientPi
    (fun j => (Ideal.span {φ (a j)} : Submodule (Acoef i) (Acoef i)))).toEquiv
  rw [← Nat.card_congr e1, hD, Nat.card_congr e2, Nat.card_pi]
  have hj : ∀ j, Nat.card (Acoef i ⧸ (Ideal.span {φ (a j)} : Submodule (Acoef i) (Acoef i))) =
      2 ^ ((a j).valuation * i) := by
    intro j
    have hspan : (Ideal.span {φ (a j)} : Ideal (Acoef i)) =
        Ideal.span {(2 : Acoef i) ^ (a j).valuation} := by
      conv_lhs => rw [PadicInt.unitCoeff_spec (ha0 j)]
      rw [map_mul, map_pow, map_natCast, Nat.cast_ofNat]
      exact Ideal.span_singleton_mul_left_unit ((PadicInt.unitCoeff (ha0 j)).isUnit.map φ) _
    have hle : (a j).valuation ≤ i := by
      calc (a j).valuation ≤ ∑ k, (a k).valuation :=
            Finset.single_le_sum (f := fun k => (a k).valuation) (fun k _ => Nat.zero_le _)
              (Finset.mem_univ j)
        _ = (B.det).valuation := hval.symm
        _ ≤ i := hv
    change Nat.card (Acoef i ⧸ (Ideal.span {φ (a j)} : Ideal (Acoef i))) = _
    rw [hspan, card_acoef_quot i _ hi hle]
  simp only [hj]
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, hval]

end Smith

/-- **A singular matrix over `ℤ₂` has a left kernel vector with a coordinate equal to `1`.**
PROVED. -/
theorem exists_left_kernel_one (B : Matrix (Fin m) (Fin m) ℤ_[2]) (h : B.det = 0) :
    ∃ (c : Fin m → ℤ_[2]) (j₀ : Fin m), c j₀ = 1 ∧ c ᵥ* B = 0 := by
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  have hne : (Finset.univ.filter fun j => v j ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext j
    by_contra hj
    exact hcon ⟨j, by simpa using hj⟩
  obtain ⟨j₀, hj₀mem, hj₀min⟩ := Finset.exists_min_image _ (fun j => (v j).valuation) hne
  have hj₀ : v j₀ ≠ 0 := (Finset.mem_filter.mp hj₀mem).2
  set u₀ := PadicInt.unitCoeff hj₀ with hu₀
  have e₀ : v j₀ = (u₀ : ℤ_[2]) * ((2 : ℕ) : ℤ_[2]) ^ (v j₀).valuation :=
    PadicInt.unitCoeff_spec hj₀
  let c : Fin m → ℤ_[2] := fun j => if hj : v j = 0 then 0 else
    ((u₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (PadicInt.unitCoeff hj : ℤ_[2]) *
      ((2 : ℕ) : ℤ_[2]) ^ ((v j).valuation - (v j₀).valuation)
  have hvc : ∀ j, v j = v j₀ * c j := by
    intro j
    by_cases hj : v j = 0
    · simp [c, hj]
    · have hle : (v j₀).valuation ≤ (v j).valuation :=
        hj₀min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      have ej : v j = (PadicInt.unitCoeff hj : ℤ_[2]) * ((2 : ℕ) : ℤ_[2]) ^ (v j).valuation :=
        PadicInt.unitCoeff_spec hj
      have hpow : ((2 : ℕ) : ℤ_[2]) ^ (v j).valuation = ((2 : ℕ) : ℤ_[2]) ^ (v j₀).valuation *
          ((2 : ℕ) : ℤ_[2]) ^ ((v j).valuation - (v j₀).valuation) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      have hu : (u₀ : ℤ_[2]) * ((u₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := Units.mul_inv u₀
      simp only [c, hj, dite_false]
      calc v j = (PadicInt.unitCoeff hj : ℤ_[2]) * ((2 : ℕ) : ℤ_[2]) ^ (v j).valuation := ej
        _ = ((u₀ : ℤ_[2]) * ((u₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * (PadicInt.unitCoeff hj : ℤ_[2]) *
            (((2 : ℕ) : ℤ_[2]) ^ (v j₀).valuation *
              ((2 : ℕ) : ℤ_[2]) ^ ((v j).valuation - (v j₀).valuation)) := by
          rw [hu, one_mul, hpow]
        _ = ((u₀ : ℤ_[2]) * ((2 : ℕ) : ℤ_[2]) ^ (v j₀).valuation) *
            (((u₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (PadicInt.unitCoeff hj : ℤ_[2]) *
              ((2 : ℕ) : ℤ_[2]) ^ ((v j).valuation - (v j₀).valuation)) := by ring
        _ = _ := by rw [← e₀]
  have hc1 : c j₀ = 1 := by
    simp only [c, hj₀, dite_false, Nat.sub_self, pow_zero, mul_one]
    rw [← hu₀]
    exact Units.inv_mul u₀
  refine ⟨c, j₀, hc1, ?_⟩
  have hvsm : v = v j₀ • c := funext fun j => by rw [Pi.smul_apply, smul_eq_mul, ← hvc j]
  rw [hvsm, Matrix.smul_vecMul] at hv
  funext k
  have := congrFun hv k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hj₀

/-- `|A_i| = 2^{i i}`. PROVED. -/
theorem card_acoef (i : ℕ) (hi : i ≠ 0) : Nat.card (Acoef i) = 2 ^ (i * i) := by
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := ZMod (2 ^ i)) i)
  have hdim : pb.dim = i := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]
  change Nat.card (AdjoinRoot (X ^ i : (ZMod (2 ^ i))[X])) = _
  rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, hdim, ← pow_mul, mul_comm]

/-- **A singular reduced block has a cokernel at least as large as `A_i`.** PROVED. -/
theorem card_coker_ge_of_det_eq_zero (B : Matrix (Fin m) (Fin m) ℤ_[2]) (h : B.det = 0) (i : ℕ)
    (hi : i ≠ 0) :
    2 ^ (i * i) ≤
      Nat.card ((Fin m → Acoef i) ⧸ LinearMap.range (Matrix.mulVecLin (B.map (constRed i)))) := by
  classical
  obtain ⟨c, j₀, hc1, hcB⟩ := exists_left_kernel_one B h
  set φ := constRed i
  let f : (Fin m → Acoef i) →ₗ[Acoef i] Acoef i :=
    { toFun := fun x => (fun j => φ (c j)) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun r x => by simp [dotProduct_smul] }
  have hcB' : (fun j => φ (c j)) ᵥ* (B.map φ) = 0 := by
    funext k
    have := congrArg φ (congrFun hcB k)
    simp only [Pi.zero_apply, map_zero] at this
    rw [Pi.zero_apply, show ((fun j => φ (c j)) ᵥ* B.map φ) k = φ ((c ᵥ* B) k) from
      (RingHom.map_vecMul φ B c k).symm]
    exact this
  have hle : LinearMap.range (Matrix.mulVecLin (B.map φ)) ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change (fun j => φ (c j)) ⬝ᵥ ((B.map φ) *ᵥ x) = 0
    rw [Matrix.dotProduct_mulVec, hcB', zero_dotProduct]
  let g := (LinearMap.range (Matrix.mulVecLin (B.map φ))).liftQ f hle
  have hg : Function.Surjective g := by
    intro y
    refine ⟨Submodule.Quotient.mk (Pi.single j₀ y), ?_⟩
    change (fun j => φ (c j)) ⬝ᵥ Pi.single j₀ y = y
    rw [dotProduct_single, hc1, map_one, one_mul]
  have : Finite ((Fin m → Acoef i) ⧸ LinearMap.range (Matrix.mulVecLin (B.map φ))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [← card_acoef i hi]
  exact Nat.card_le_card_of_surjective g hg

/-- `v₂(2) = 1` in `ℤ₂`. PROVED. -/
theorem valuation_two_padicInt' : (2 : ℤ_[2]).valuation = 1 := by
  simpa using PadicInt.valuation_p (p := 2)

end Orders

/-! ### Two-term presentations of the local quotients -/

section Presentation

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (v : Places K S) (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S W (2 ^ i)) (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1)

/-- **An integral matrix presents the central full/Kummer quotient at `v` at precision `i`**
(tex 4066–4080): the reduction `B̄` of `B ∈ M_m(ℤ₂)` to `A_i`, as the two-term complex
`[A_i^m --B̄--> A_i^m]` in degrees one and two, has the cohomology of the quotient of the full
local complex by the actual Kummer condition: `ker B̄ ≅ H¹(K_v, M_i)/(Kummer image)` and
`coker B̄ ≅ H²(K_v, M_i)`. -/
structure PresentsLocalQuotient {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2]) : Type where
  /-- `H¹` of the model is `H¹` of the quotient -/
  eH1 : LinearMap.ker (Matrix.mulVecLin (B.map (constRed i))) ≃ₗ[Acoef i]
    quotH1 W i α v s hs hs0 hFull hα
  /-- `H²` of the model is `H²` of the quotient -/
  eH2 : ((Fin m → Acoef i) ⧸ LinearMap.range (Matrix.mulVecLin (B.map (constRed i)))) ≃ₗ[Acoef i]
    locH W i α v 2

/-- **An endomorphism of a finite module has kernel and cokernel of the same order.** PROVED. -/
theorem card_ker_eq_card_coker {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    (f : M →ₗ[R] M) : Nat.card (LinearMap.ker f) = Nat.card (M ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at h1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have h3 : Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) =
      Nat.card (LinearMap.range f) * Nat.card (M ⧸ LinearMap.range f) := by
    rw [mul_comm (Nat.card (LinearMap.range f)) (Nat.card (LinearMap.ker f)), ← h1, h2]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

/-- `det B̄ · x` lies in the image of `B̄` (`B̄ adj B̄ = det B̄ · 1`). PROVED. -/
theorem det_smul_mem_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2]) (x : Fin m → Acoef i) :
    (constRed i B.det) • x ∈ LinearMap.range (Matrix.mulVecLin (B.map (constRed i))) := by
  refine ⟨(B.map (constRed i)).adjugate *ᵥ x, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, RingHom.map_det, RingHom.mapMatrix_apply]

/-- `det B̄` kills the kernel of `B̄` (`adj B̄ B̄ = det B̄ · 1`). PROVED. -/
theorem det_smul_of_mulVec_eq_zero {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2])
    (x : Fin m → Acoef i) (hx : (B.map (constRed i)) *ᵥ x = 0) : (constRed i B.det) • x = 0 := by
  have h := congrArg (fun y => (B.map (constRed i)).adjugate *ᵥ y) hx
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  rwa [RingHom.map_det, RingHom.mapMatrix_apply]

namespace PresentsLocalQuotient

variable {W i α v s hs hs0 hFull hα}

/-- **The quotient of `H¹(K_v, M_i)` by the genuine Kummer image has the order of
`H²(K_v, M_i)`** at a place presented by a square model. PROVED. -/
theorem card_quotH1_eq_card_locH2 {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B) :
    Nat.card (quotH1 W i α v s hs hs0 hFull hα) = Nat.card (locH W i α v 2) := by
  rw [← Nat.card_congr P.eH1.toEquiv, ← Nat.card_congr P.eH2.toEquiv]
  exact card_ker_eq_card_coker _

/-- **The determinant of a presenting block kills the genuine quotient of `H¹(K_v, M_i)` by the
Kummer image.** PROVED. -/
theorem det_smul_quotH1 {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B)
    (y : quotH1 W i α v s hs hs0 hFull hα) : (constRed i B.det) • y = 0 := by
  obtain ⟨x, rfl⟩ := P.eH1.surjective y
  have hx : (constRed i B.det) • x = 0 :=
    Subtype.ext (det_smul_of_mulVec_eq_zero i B (x : Fin m → Acoef i) x.2)
  rw [← P.eH1.map_smul, hx, P.eH1.map_zero]

/-- **The determinant of a presenting block kills `H²(K_v, M_i)`.** PROVED. -/
theorem det_smul_locH2 {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B)
    (y : locH W i α v 2) : (constRed i B.det) • y = 0 := by
  obtain ⟨q, rfl⟩ := P.eH2.surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← P.eH2.map_smul, ← Submodule.Quotient.mk_smul,
    (Submodule.Quotient.mk_eq_zero _).2 (det_smul_mem_range i B x), P.eH2.map_zero]

/-- **The order of `H²` of the genuine local quotient** at a place presented by `B` with
`det B ≠ 0`: `|H²(K_v, M_i)| = 2^{i · v₂ det B}` once `v₂ det B ≤ i`. PROVED. -/
theorem card_locH2_eq {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B) (hdet : B.det ≠ 0) (hi : i ≠ 0)
    (hv : (B.det).valuation ≤ i) :
    Nat.card (locH W i α v 2) = 2 ^ ((B.det).valuation * i) := by
  rw [← Nat.card_congr P.eH2.toEquiv]
  exact card_coker_acoef B hdet i hi hv

/-- **The order of the quotient of `H¹(K_v, M_i)` by the genuine Kummer image** at a place
presented by `B` with `det B ≠ 0`: `2^{i · v₂ det B}` once `v₂ det B ≤ i`. PROVED. -/
theorem card_quotH1_eq {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B) (hdet : B.det ≠ 0) (hi : i ≠ 0)
    (hv : (B.det).valuation ≤ i) :
    Nat.card (quotH1 W i α v s hs hs0 hFull hα) = 2 ^ ((B.det).valuation * i) := by
  rw [P.card_quotH1_eq_card_locH2]
  exact P.card_locH2_eq hdet hi hv

/-- **The genuine length determines the valuation of the presenting block**: if
`|H²(K_v, M_i)| = 2^{ℓ i}` at a precision `i ≥ v₂ det B`, `i ≠ 0`, then `v₂ det B = ℓ`.
PROVED. -/
theorem valuation_det_eq {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B) (hdet : B.det ≠ 0) (hi : i ≠ 0)
    (hv : (B.det).valuation ≤ i) {ℓ : ℕ} (hcard : Nat.card (locH W i α v 2) = 2 ^ (ℓ * i)) :
    (B.det).valuation = ℓ := by
  have h := P.card_locH2_eq hdet hi hv
  rw [hcard] at h
  have h' := Nat.pow_right_injective (le_refl 2) h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h').symm

/-- **A block presenting a genuine quotient of finite length is rationally invertible**: if
`|H²(K_v, M_i)| = 2^{ℓ i}` at a precision `i > ℓ`, then `det B ≠ 0` (a singular block has a
cokernel at least as large as `A_i`). PROVED. -/
theorem det_ne_zero_of_card {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ_[2]}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα B) (hi : i ≠ 0) {ℓ : ℕ} (hℓ : ℓ < i)
    (hcard : Nat.card (locH W i α v 2) = 2 ^ (ℓ * i)) : B.det ≠ 0 := by
  intro h0
  have h1 := card_coker_ge_of_det_eq_zero B h0 i hi
  rw [Nat.card_congr P.eH2.toEquiv, hcard] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h3 := Nat.le_of_mul_le_mul_right h2 (Nat.pos_of_ne_zero hi)
  omega

/-- The reduction of `2 · 1` is `2 · 1`. PROVED. -/
theorem map_two_smul_one (m : ℕ) :
    ((2 : ℤ_[2]) • (1 : Matrix (Fin m) (Fin m) ℤ_[2])).map (constRed i) =
      (2 : Acoef i) • (1 : Matrix (Fin m) (Fin m) (Acoef i)) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

/-- The kernel of `2 · 1` is killed by `2`. PROVED. -/
theorem two_smul_of_mulVec {m : ℕ} (y : Fin m → Acoef i)
    (hy : (((2 : ℤ_[2]) • (1 : Matrix (Fin m) (Fin m) ℤ_[2])).map (constRed i)) *ᵥ y = 0) :
    (2 : Acoef i) • y = 0 := by
  rwa [map_two_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at hy

/-- **At a place presented by the minimal model `2 · 1`, the quotient of `H¹(K_v, M_i)` by the
genuine Kummer image is killed by `2`.** PROVED. -/
theorem two_smul_quotH1 {m : ℕ}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα ((2 : ℤ_[2]) • (1 : Matrix (Fin m) (Fin m) ℤ_[2])))
    (y : quotH1 W i α v s hs hs0 hFull hα) : (2 : Acoef i) • y = 0 := by
  obtain ⟨x, rfl⟩ := P.eH1.surjective y
  have hx : (2 : Acoef i) • x = 0 := Subtype.ext (two_smul_of_mulVec (x : Fin m → Acoef i) x.2)
  rw [← P.eH1.map_smul, hx, P.eH1.map_zero]

/-- **At a place presented by the minimal model `2 · 1`, `H²(K_v, M_i)` is killed by `2`.**
PROVED. -/
theorem two_smul_locH2 {m : ℕ}
    (P : PresentsLocalQuotient W i α v s hs hs0 hFull hα ((2 : ℤ_[2]) • (1 : Matrix (Fin m) (Fin m) ℤ_[2])))
    (y : locH W i α v 2) : (2 : Acoef i) • y = 0 := by
  obtain ⟨q, rfl⟩ := P.eH2.surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : (2 : Acoef i) • x ∈ LinearMap.range
      (Matrix.mulVecLin (((2 : ℤ_[2]) • (1 : Matrix (Fin m) (Fin m) ℤ_[2])).map (constRed i))) := by
    refine ⟨x, ?_⟩
    rw [Matrix.mulVecLin_apply, map_two_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← P.eH2.map_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2 hx,
    P.eH2.map_zero]

end PresentsLocalQuotient

end Presentation

/-! ### The local-block model over the genuine Kummer images -/

section Model

open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)

/-- **The local-block model of the central quotient block, over the genuine Kummer images**
(tex 4066–4080, 3413–3456), for the quotient block `D_W` of the leaf, the moving prime `r` with
trace `a_r` and quadratic sign `χ = χ_h(r)`, and `ω = ω(h)`.

| field | content | tex | kind |
|---|---|---|---|
| `S`, `W`, `hW`, `s`, `hs`, `hs0`, `hFull` | the Selmer support, the curve `E_K`, a square root of `h` in `K_S`, `E[2^i] ⊂ E(K_S)` at every precision | 2720–2760, 3413–3438 | definition |
| `wmov`, `wmov'`, `act`, `hwmov`, `hwmov'`, `hwne`, `hact_inj`, `hact_above` | the two distinct places above the split moving prime and `2ω` distinct places above primes dividing `h` (the active places) | 4066–4080 | definition |
| `Fr` … `hact` | the block structure of `CalibrationModelH` (same names and types) | 4066–4080 | as in `CalibrationModelH` |
| `FrZ`, `hFrZ` | the central Frobenius is integral | 4066–4071 | definition |
| `presMov`, `presMov'` | at every precision the central moving block `χ Fr_ℤ − r` presents the central full/Kummer quotient at each place above the moving prime, for the actual Kummer condition | 4066–4075 | ELLIOT (the local quotient and its two-term model) |
| `presAct` | at every precision the minimal model `2 · 1₂` presents the central full/Kummer quotient at each active place | 4076–4078 | ELLIOT (the local quotient and its two-term model) |
-/
structure GenuineLocalBlockModel (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {κ : Type} [Fintype κ] [DecidableEq κ] (DW : Matrix κ κ (PowerSeries ℚ_[2]))
    (rmov : ℕ) (amov chimov : ℤ) (ω : ℕ) : Type 1 where
  /-- the finite set of places of the Selmer complexes -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- the curve `E` over `K` -/
  W : WeierstrassCurve K
  [ellW : W.IsElliptic]
  /-- it is the base change of the fixed curve -/
  hW : W = E₀.baseChange K
  /-- a square root of `h` in `K_S` (it defines `χ_h`) -/
  s : KS K S
  /-- `s² = h` -/
  hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)
  /-- `s ≠ 0` -/
  hs0 : s ≠ 0
  /-- `E[2^i] ⊂ E(K_S)` at every precision -/
  hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)
  /-- the first place above the moving prime -/
  wmov : Places K S
  /-- the second place above the moving prime -/
  wmov' : Places K S
  /-- the places above the active primes -/
  act : Fin (2 * ω) → Places K S
  /-- the first place lies above the moving prime -/
  hwmov : (rmov : 𝓞 K) ∈ wmov.1.asIdeal
  /-- the second place lies above the moving prime -/
  hwmov' : (rmov : 𝓞 K) ∈ wmov'.1.asIdeal
  /-- the two places above the split moving prime are distinct -/
  hwne : wmov ≠ wmov'
  /-- the active places are distinct -/
  hact_inj : Function.Injective act
  /-- every active place lies above a prime dividing `h` -/
  hact_above : ∀ a, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ hZ ∧ (p : 𝓞 K) ∈ (act a).1.asIdeal
  /-- the Frobenius at the moving prime, over `ℚ₂[[t]]` -/
  Fr : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- its central value has trace `a_r` -/
  hFtr : (Fr.map central).trace = (amov : ℚ_[2])
  /-- its central value has determinant `r` -/
  hFdet : (Fr.map central).det = (rmov : ℚ_[2])
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the moving and active places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * ω)
  /-- the moving scalar at the first place above `r` -/
  zmov : PowerSeries ℚ_[2]
  /-- the moving scalar at the second place above `r` -/
  zmov' : PowerSeries ℚ_[2]
  /-- the block at the active places -/
  Bact : Matrix (Fin (4 * ω)) (Fin (4 * ω)) (PowerSeries ℚ_[2])
  /-- the quotient block is the direct sum of the local blocks, up to the changes of basis -/
  hDW : DW = PW * (fromBlocks (twoPlaceBlock Fr (rmov : PowerSeries ℚ_[2]) zmov zmov') 0 0
    Bact).submatrix eW eW * QW
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the first moving scalar is `χ` at the centre -/
  hzmov : central zmov = chimov
  /-- the second moving scalar is `χ` at the centre -/
  hzmov' : central zmov' = chimov
  /-- the active block is `2 · 1` at the centre -/
  hact : Bact.map central = (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2])
  /-- the integral central Frobenius -/
  FrZ : Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- the central Frobenius is integral -/
  hFrZ : Fr.map central = FrZ.map PadicInt.Coe.ringHom
  /-- the central moving block presents the quotient at the first place above `r` -/
  presMov : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov.1) (chimov • FrZ - (rmov : ℤ_[2]) • 1)
  /-- the central moving block presents the quotient at the second place above `r` -/
  presMov' : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov' s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov'.1) (chimov • FrZ - (rmov : ℤ_[2]) • 1)
  /-- the minimal model `2 · 1₂` presents the quotient at every active place -/
  presAct : ∀ (i : ℕ) (a : Fin (2 * ω)), PresentsLocalQuotient W i (centralChar i s hs hs0) (act a)
    s hs hs0 (hFull i) (isLocallyQuadAt_centralChar i s hs hs0 (act a).1)
    ((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]))

attribute [instance] GenuineLocalBlockModel.ellW

namespace GenuineLocalBlockModel

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {κ : Type}
  [Fintype κ] [DecidableEq κ] {DW : Matrix κ κ (PowerSeries ℚ_[2])} {rmov : ℕ} {amov chimov : ℤ}
  {ω : ℕ}

/-- **The presented moving blocks are the central values of the model's moving blocks**: the
central value of `twoPlaceBlock Fr r z z'` is `diag(χ Fr_ℤ − r, χ Fr_ℤ − r)`. PROVED. -/
theorem central_moving_blocks (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) :
    (twoPlaceBlock G.Fr (rmov : PowerSeries ℚ_[2]) G.zmov G.zmov').map central =
      fromBlocks ((chimov • G.FrZ - (rmov : ℤ_[2]) • 1).map PadicInt.Coe.ringHom) 0 0
        ((chimov • G.FrZ - (rmov : ℤ_[2]) • 1).map PadicInt.Coe.ringHom) := by
  rw [ZInQ.Contrib.CloudB3RC53.Calibration.central_twoPlaceBlock, G.hFrZ, G.hzmov, G.hzmov']
  have hr : central (rmov : PowerSeries ℚ_[2]) = (rmov : ℚ_[2]) := by simp [central]
  rw [hr]
  have e : ((chimov : ℚ_[2]) • G.FrZ.map PadicInt.Coe.ringHom - (rmov : ℚ_[2]) • 1) =
      (chimov • G.FrZ - (rmov : ℤ_[2]) • 1).map PadicInt.Coe.ringHom := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]
    by_cases hab : a = b
    · subst hab; simp [zsmul_eq_mul]
    · simp [Matrix.one_apply_ne hab, zsmul_eq_mul]
  simp only [twoPlaceBlock, e]

/-- **The presented active blocks are the central value of the model's active block**: each
`2 · 1₂` is a diagonal block of `B_act(0) = 2 · 1`. PROVED. -/
theorem central_active_block (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) :
    G.Bact.map central = (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2]) ∧
      ((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).map PadicInt.Coe.ringHom =
        (2 : ℚ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  refine ⟨G.hact, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_cast
  · simp [Matrix.one_apply_ne hab]

/-- **The quotient length** `v₂ det D_W(0) = 2 v₂N + 4ω`, `N = r + 1 − χ a_r` (tex 4066–4080),
from the block structure (the local blocks' `hδ_of_local_blocks`). PROVED. -/
theorem hδ (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) (hr : Odd rmov)
    (hχ : chimov = 1 ∨ chimov = -1) (hN : (rmov : ℤ) + 1 - chimov * amov ≠ 0) :
    v2 (central DW.det) =
      ((2 * ((padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov) : ℕ) : ℤ) + 4 * (ω : ℤ) : ℤ) :
        WithTop ℤ) :=
  ZInQ.Contrib.CloudB3RC53.Calibration.hδ_of_local_blocks ω DW G.PW G.QW G.eW G.Fr rmov G.zmov
    G.zmov' G.Bact G.hDW G.hPW G.hQW (G.Fr.map central) hr amov chimov hχ G.hFtr G.hFdet hN rfl
    G.hzmov G.hzmov' G.hact

/-- **At the moving places the genuine quotient of `H¹` by the Kummer image has the order of
`H²`**, at every precision. PROVED. -/
theorem card_moving (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) (i : ℕ) :
    Nat.card (quotH1 G.W i (centralChar i G.s G.hs G.hs0) G.wmov G.s G.hs G.hs0 (G.hFull i)
        (isLocallyQuadAt_centralChar i G.s G.hs G.hs0 G.wmov.1)) =
      Nat.card (locH G.W i (centralChar i G.s G.hs G.hs0) G.wmov 2) :=
  (G.presMov i).card_quotH1_eq_card_locH2

/-- **At every active place the genuine quotient of `H¹` by the Kummer image and `H²` are
killed by `2`**, at every precision. PROVED. -/
theorem two_smul_active (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) (i : ℕ)
    (a : Fin (2 * ω)) :
    (∀ y : quotH1 G.W i (centralChar i G.s G.hs G.hs0) (G.act a) G.s G.hs G.hs0 (G.hFull i)
        (isLocallyQuadAt_centralChar i G.s G.hs G.hs0 (G.act a).1), (2 : Acoef i) • y = 0) ∧
      (∀ y : locH G.W i (centralChar i G.s G.hs G.hs0) (G.act a) 2, (2 : Acoef i) • y = 0) :=
  ⟨(G.presAct i a).two_smul_quotH1, (G.presAct i a).two_smul_locH2⟩

/-- The integral central Frobenius has trace `a_r`. PROVED. -/
theorem trace_FrZ (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) :
    G.FrZ.trace = (amov : ℤ_[2]) := by
  apply Subtype.coe_injective
  have h := G.hFtr
  rw [G.hFrZ, ← AddMonoidHom.map_trace] at h
  exact h.trans (PadicInt.coe_intCast amov).symm

/-- The integral central Frobenius has determinant `r`. PROVED. -/
theorem det_FrZ (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) :
    G.FrZ.det = (rmov : ℤ_[2]) := by
  apply Subtype.coe_injective
  have h := G.hFdet
  rw [G.hFrZ, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact h.trans (PadicInt.coe_natCast rmov).symm

/-- **The presented moving block has determinant `r N`**, `N = r + 1 − χ a_r` (tex 4066–4071).
PROVED. -/
theorem det_moving (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω)
    (hχ : chimov = 1 ∨ chimov = -1) :
    (chimov • G.FrZ - (rmov : ℤ_[2]) • 1).det =
      (rmov : ℤ_[2]) * ((rmov : ℤ_[2]) + 1 - (chimov : ℤ_[2]) * (amov : ℤ_[2])) := by
  have hχ2 : (chimov : ℤ_[2]) ^ 2 = 1 := by rcases hχ with rfl | rfl <;> norm_num
  rw [← Int.cast_smul_eq_zsmul ℤ_[2] chimov G.FrZ]
  exact ZInQ.Contrib.CloudB3RC53.Calibration.det_moving_block G.FrZ _ _ _ hχ2 G.trace_FrZ
    G.det_FrZ

/-- **`r N` kills the genuine central full/Kummer quotient at the places above the moving prime**,
at every precision: both the quotient of `H¹(K_w, M_i)` by the actual Kummer image and
`H²(K_w, M_i)` (tex 4066–4072: "the central full/Kummer quotient has degree-two length
`v₂(N_i)`"). PROVED. -/
theorem moving_killed (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω)
    (hχ : chimov = 1 ∨ chimov = -1) (i : ℕ) :
    (∀ y : quotH1 G.W i (centralChar i G.s G.hs G.hs0) G.wmov G.s G.hs G.hs0 (G.hFull i)
        (isLocallyQuadAt_centralChar i G.s G.hs G.hs0 G.wmov.1),
        (constRed i ((rmov : ℤ_[2]) * ((rmov : ℤ_[2]) + 1 - (chimov : ℤ_[2]) * (amov : ℤ_[2])))) •
          y = 0) ∧
      (∀ y : locH G.W i (centralChar i G.s G.hs G.hs0) G.wmov 2,
        (constRed i ((rmov : ℤ_[2]) * ((rmov : ℤ_[2]) + 1 - (chimov : ℤ_[2]) * (amov : ℤ_[2])))) •
          y = 0) := by
  rw [← G.det_moving hχ]
  exact ⟨(G.presMov i).det_smul_quotH1, (G.presMov i).det_smul_locH2⟩

/-- An odd natural number is a unit of `ℤ₂`: valuation zero. PROVED. -/
theorem valuation_natCast_odd {r : ℕ} (hr : Odd r) : ((r : ℤ_[2])).valuation = 0 := by
  have h : ((r : ℤ_[2]) : ℚ_[2]).valuation = 0 := by
    rw [PadicInt.coe_natCast, Padic.valuation_natCast]
    have : padicValNat 2 r = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h2 =>
        (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h2)
    rw [this]; rfl
  rw [PadicInt.valuation_coe] at h
  exact_mod_cast h

/-- The valuation of an integer in `ℤ₂`. PROVED. -/
theorem valuation_intCast_padicInt (n : ℤ) : ((n : ℤ_[2])).valuation = padicValInt 2 n := by
  have h : ((n : ℤ_[2]) : ℚ_[2]).valuation = padicValInt 2 n := by
    rw [PadicInt.coe_intCast, Padic.valuation_intCast]
  rw [PadicInt.valuation_coe] at h
  exact_mod_cast h

/-- The determinant of the presented moving block, as an integer: `r N`. PROVED. -/
theorem det_moving_intCast (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω)
    (hχ : chimov = 1 ∨ chimov = -1) :
    (chimov • G.FrZ - (rmov : ℤ_[2]) • 1).det =
      (((rmov : ℤ) * ((rmov : ℤ) + 1 - chimov * amov) : ℤ) : ℤ_[2]) := by
  rw [G.det_moving hχ]
  push_cast
  ring

/-- The valuation of the presented moving block is `v₂ N`. PROVED. -/
theorem valuation_det_moving (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω)
    (hχ : chimov = 1 ∨ chimov = -1) (hr : Odd rmov) (hN : (rmov : ℤ) + 1 - chimov * amov ≠ 0) :
    ((chimov • G.FrZ - (rmov : ℤ_[2]) • 1).det).valuation =
      padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov) := by
  rw [G.det_moving hχ]
  have hr0 : (rmov : ℤ_[2]) ≠ 0 := by
    exact_mod_cast hr.pos.ne'
  have hN' : ((rmov : ℤ_[2]) + 1 - (chimov : ℤ_[2]) * (amov : ℤ_[2])) =
      (((rmov : ℤ) + 1 - chimov * amov : ℤ) : ℤ_[2]) := by push_cast; ring
  have hN0 : (((rmov : ℤ) + 1 - chimov * amov : ℤ) : ℤ_[2]) ≠ 0 := by exact_mod_cast hN
  rw [hN', PadicInt.valuation_mul hr0 hN0, valuation_natCast_odd hr, zero_add,
    valuation_intCast_padicInt]

/-- **The central full/Kummer quotient at the places above the moving prime has degree-two length
`v₂ N`** (tex 4066–4072), at every precision `i ≥ v₂ N`, `i ≠ 0`: `|H²(K_w, M_i)| = 2^{i v₂N}`
and the quotient of `H¹(K_w, M_i)` by the genuine Kummer image has the same order. PROVED. -/
theorem length_moving (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω)
    (hχ : chimov = 1 ∨ chimov = -1) (hr : Odd rmov) (hN : (rmov : ℤ) + 1 - chimov * amov ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv : padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov) ≤ i) :
    Nat.card (locH G.W i (centralChar i G.s G.hs G.hs0) G.wmov 2) =
        2 ^ (padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov) * i) ∧
      Nat.card (quotH1 G.W i (centralChar i G.s G.hs G.hs0) G.wmov G.s G.hs G.hs0 (G.hFull i)
        (isLocallyQuadAt_centralChar i G.s G.hs G.hs0 G.wmov.1)) =
        2 ^ (padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov) * i) := by
  have hdet : (chimov • G.FrZ - (rmov : ℤ_[2]) • 1).det ≠ 0 := by
    rw [G.det_moving_intCast hχ]
    have : (rmov : ℤ) * ((rmov : ℤ) + 1 - chimov * amov) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.pos.ne') hN
    exact_mod_cast this
  have hval := G.valuation_det_moving hχ hr hN
  rw [← hval] at hv ⊢
  exact ⟨(G.presMov i).card_locH2_eq hdet hi hv, (G.presMov i).card_quotH1_eq hdet hi hv⟩

/-- **At each active place the central full/Kummer quotient has length two** (tex 4076–4078): at
every precision `i ≥ 2`, `|H²(K_v, M_i)| = 2^{2i}` and the quotient of `H¹(K_v, M_i)` by the
genuine Kummer image has the same order. PROVED. -/
theorem length_active (G : GenuineLocalBlockModel K E₀ hZ DW rmov amov chimov ω) (i : ℕ)
    (hi : 2 ≤ i) (a : Fin (2 * ω)) :
    Nat.card (locH G.W i (centralChar i G.s G.hs G.hs0) (G.act a) 2) = 2 ^ (2 * i) ∧
      Nat.card (quotH1 G.W i (centralChar i G.s G.hs G.hs0) (G.act a) G.s G.hs G.hs0 (G.hFull i)
        (isLocallyQuadAt_centralChar i G.s G.hs G.hs0 (G.act a).1)) = 2 ^ (2 * i) := by
  have hdet4 : ((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det = 2 ^ 2 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hval : (((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det).valuation = 2 := by
    rw [hdet4, PadicInt.valuation_pow, valuation_two_padicInt', mul_one]
  have hdet : ((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det ≠ 0 := by
    rw [hdet4]; exact pow_ne_zero _ two_ne_zero
  have hv : (((2 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det).valuation ≤ i := by
    rw [hval]; exact hi
  have hi0 : i ≠ 0 := by omega
  have h1 := (G.presAct i a).card_locH2_eq hdet hi0 hv
  have h2 := (G.presAct i a).card_quotH1_eq hdet hi0 hv
  rw [hval] at h1 h2
  exact ⟨h1, h2⟩

end GenuineLocalBlockModel

end Model

/-! ### Local duality: degree-two lengths from degree-zero lengths (printed leaf) -/

section Duality

/-- **PRINT — Milne, *Arithmetic Duality Theorems*, 2nd ed., Ch. I, Corollary 2.3 (local duality),
as cited at tex 3442–3445 ("the local finite dualities"), for the finite coefficient modules of the
text.** For an elliptic curve `E/K` with `E[2^i] ⊂ E(K_S)`, a coefficient character `α` with
`α² = 1` and a place `v ∈ S`: `|H²(K_v, M_i)| = |H⁰(K_v, M_i)|`, `M_i = (E[2^i] ⊗ A_i)(α)`.
(Milne: `H²(K_v, M) ≅ H⁰(K_v, M^D)^*` for a finite `G_{K_v}`-module `M`; here
`M_i^D ≅ M_i(α⁻¹) = M_i` by the Weil pairing on `E[2^i]` and the self-duality of `A_i` over
`ℤ/2^i`.) As a Lean proposition it includes the standard comparison of the continuous cochains
used here with Galois cohomology. -/
def MilneLocalDualityOrder : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
    (v : Places K S), FullTorsion K S W (2 ^ i) → (∀ g, α g * α g = 1) →
      Nat.card (locH W i α v 2) = Nat.card (locH W i α v 0)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The central character has order dividing two. PROVED. -/
theorem centralChar_mul_self (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (g : GKS K S) :
    centralChar i s hs hs0 g * centralChar i s hs hs0 g = 1 := by
  have h1 : movingCharS i (1 : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) g = 1 := by
    rw [movingCharS, ZInQ.Manuscript.RC.HeegnerAlgebra.movingChar, MonoidHom.comp_apply,
      MonoidHom.one_apply, map_one]
  rw [centralChar, alphaChar, charMul_apply, h1, mul_one, MonoidHom.comp_apply, ← map_mul,
    Int.units_mul_self, map_one]

/-- **Degree-two lengths from degree-zero lengths** (local duality): if
`|H⁰(K_v, M_i)| = 2^{ℓ i}` for all large `i`, then `|H²(K_v, M_i)| = 2^{ℓ i}` for all large `i`,
for the central character. PROVED from `MilneLocalDualityOrder`. -/
theorem length_H2_of_H0 (hM : MilneLocalDualityOrder) {W : WeierstrassCurve K} [W.IsElliptic]
    {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}
    (hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)) (v : Places K S) {ℓ : ℕ}
    (h0 : ∃ i₀ : ℕ, ∀ i ≥ i₀,
      Nat.card (locH W i (centralChar i s hs hs0) v 0) = 2 ^ (ℓ * i)) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (locH W i (centralChar i s hs hs0) v 2) = 2 ^ (ℓ * i) := by
  obtain ⟨i₀, hi₀⟩ := h0
  exact ⟨i₀, fun i hi =>
    (hM K S W i _ v (hFull i) (centralChar_mul_self i s hs hs0)).trans (hi₀ i hi)⟩

end Duality

/-! ### The local-block model with the lengths read from the genuine quotients -/

section LengthModel

open ZInQ.Manuscript ZInQ.Manuscript.RC

/-- The valuation of a nonzero `2`-adic integer, read in `ℚ₂`. PROVED. -/
theorem v2_coe_padicInt' (x : ℤ_[2]) (hx : x ≠ 0) :
    v2 (x : ℚ_[2]) = ((x.valuation : ℤ) : WithTop ℤ) := by
  have hx' : (x : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hx
  rw [v2, Padic.addValuation.apply hx', PadicInt.valuation_coe]

/-- **The local-block model with the lengths read from the genuine local quotients** (tex
4066–4080). As `GenuineLocalBlockModel`, but without the Frobenius trace and determinant, the
central moving scalars and the central active block: the central quotient block is, up to unit
changes of basis, the block sum of integral local blocks `B_w, B_w'` at the two places above the
moving prime and `B_a` at the `2ω` active places; each presents the genuine central full/Kummer
quotient at its place at every precision; and the genuine quotients have the lengths
stated in the text: degree-two length `ℓ_mov` at the places above the moving prime (`v₂ N_i`,
tex 4066–4072) and two at the active places (tex 4076–4078), i.e. `|H²(K_v, M_i)| = 2^{ℓ i}` for
all large `i`. The rational invertibility of the local blocks (the central local quotients are
rationally acyclic, tex 3920–3927) is derived, not assumed (`det_ne_zero_of_length`).

| field | content | tex | kind |
|---|---|---|---|
| `S` … `hact_above` | as in `GenuineLocalBlockModel` | 2720–2760, 4066–4080 | definition |
| `PW`, `QW`, `eW`, `Bmov`, `Bmov'`, `Bact`, `hcentral`, `hPW`, `hQW` | the central quotient block is `P_W(0) · diag(B_w, B_w', B_a …) · Q_W(0)` up to relabelling, with unit determinants | 4066–4080 | ELLIOT (direct sum of the local quotients) |
| `presMov`, `presMov'`, `presAct` | each local block presents the genuine central full/Kummer quotient at its place, at every precision | 4066–4080, 3413–3456 | ELLIOT |
| `lenMov`, `lenMov'`, `lenAct` | the genuine lengths: `|H²(K_w, M_i)| = 2^{ℓ_mov i}`, `|H²(K_v, M_i)| = 2^{2i}` for large `i` | 4066–4078 | ELLIOT (local duality and the local points) |
-/
structure GenuineLengthBlockModel (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {κ : Type} [Fintype κ] [DecidableEq κ] (DW : Matrix κ κ (PowerSeries ℚ_[2]))
    (rmov ℓmov ω : ℕ) : Type 1 where
  /-- the finite set of places of the Selmer complexes -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- the curve `E` over `K` -/
  W : WeierstrassCurve K
  [ellW : W.IsElliptic]
  /-- it is the base change of the fixed curve -/
  hW : W = E₀.baseChange K
  /-- a square root of `h` in `K_S` (it defines `χ_h`) -/
  s : KS K S
  /-- `s² = h` -/
  hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)
  /-- `s ≠ 0` -/
  hs0 : s ≠ 0
  /-- `E[2^i] ⊂ E(K_S)` at every precision -/
  hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)
  /-- the first place above the moving prime -/
  wmov : Places K S
  /-- the second place above the moving prime -/
  wmov' : Places K S
  /-- the places above the active primes -/
  act : Fin (2 * ω) → Places K S
  /-- the first place lies above the moving prime -/
  hwmov : (rmov : 𝓞 K) ∈ wmov.1.asIdeal
  /-- the second place lies above the moving prime -/
  hwmov' : (rmov : 𝓞 K) ∈ wmov'.1.asIdeal
  /-- the two places above the split moving prime are distinct -/
  hwne : wmov ≠ wmov'
  /-- the active places are distinct -/
  hact_inj : Function.Injective act
  /-- every active place lies above a prime dividing `h` -/
  hact_above : ∀ a, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ hZ ∧ (p : 𝓞 K) ∈ (act a).1.asIdeal
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the local places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin (2 * ω))
  /-- the integral central local block at the first place above the moving prime -/
  Bmov : Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- the integral central local block at the second place above the moving prime -/
  Bmov' : Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- the integral central local blocks at the active places -/
  Bact : Fin (2 * ω) → Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- at the centre the quotient block is the block sum of the local blocks, up to the changes of
  basis -/
  hcentral : DW.map central = PW.map central *
    ((fromBlocks (fromBlocks Bmov 0 0 Bmov') 0 0 (Matrix.blockDiagonal Bact)).map
      PadicInt.Coe.ringHom).submatrix eW eW * QW.map central
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the first moving block presents the quotient at the first place above `r` -/
  presMov : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov.1) Bmov
  /-- the second moving block presents the quotient at the second place above `r` -/
  presMov' : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov' s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov'.1) Bmov'
  /-- each active block presents the quotient at its active place -/
  presAct : ∀ (i : ℕ) (a : Fin (2 * ω)), PresentsLocalQuotient W i (centralChar i s hs hs0) (act a)
    s hs hs0 (hFull i) (isLocallyQuadAt_centralChar i s hs hs0 (act a).1) (Bact a)
  /-- the genuine quotient at the first place above `r` has degree-two length `ℓ_mov` -/
  lenMov : ∃ i₀ : ℕ, ∀ i ≥ i₀,
    Nat.card (locH W i (centralChar i s hs hs0) wmov 2) = 2 ^ (ℓmov * i)
  /-- the genuine quotient at the second place above `r` has degree-two length `ℓ_mov` -/
  lenMov' : ∃ i₀ : ℕ, ∀ i ≥ i₀,
    Nat.card (locH W i (centralChar i s hs hs0) wmov' 2) = 2 ^ (ℓmov * i)
  /-- the genuine quotient at every active place has degree-two length two -/
  lenAct : ∀ a, ∃ i₀ : ℕ, ∀ i ≥ i₀,
    Nat.card (locH W i (centralChar i s hs hs0) (act a) 2) = 2 ^ (2 * i)

attribute [instance] GenuineLengthBlockModel.ellW

namespace GenuineLengthBlockModel

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {κ : Type}
  [Fintype κ] [DecidableEq κ] {DW : Matrix κ κ (PowerSeries ℚ_[2])} {rmov ℓmov ω : ℕ}

/-- **A block presenting a genuine quotient of finite length is rationally invertible** (all
precisions presented, the length attained for all large precisions). PROVED. -/
theorem det_ne_zero_of_length {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
    [W.IsElliptic] {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}
    {hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)} {v : Places K S}
    {B : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (P : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) v s hs hs0 (hFull i)
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) B) {ℓ : ℕ}
    (hlen : ∃ i₀ : ℕ, ∀ i ≥ i₀,
      Nat.card (locH W i (centralChar i s hs hs0) v 2) = 2 ^ (ℓ * i)) :
    B.det ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := hlen
  exact (P (max i₀ (ℓ + 1))).det_ne_zero_of_card (by omega) (by omega) (hi₀ _ (le_max_left _ _))

/-- **A presented block's valuation is the genuine length** (all precisions presented, the
length attained for all large precisions). PROVED. -/
theorem valuation_of_length {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
    [W.IsElliptic] {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}
    {hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)} {v : Places K S}
    {B : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (P : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) v s hs hs0 (hFull i)
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) B) {ℓ : ℕ}
    (hlen : ∃ i₀ : ℕ, ∀ i ≥ i₀,
      Nat.card (locH W i (centralChar i s hs hs0) v 2) = 2 ^ (ℓ * i)) :
    (B.det).valuation = ℓ := by
  have hdet := det_ne_zero_of_length P hlen
  obtain ⟨i₀, hi₀⟩ := hlen
  exact (P (max (max i₀ (B.det).valuation) 1)).valuation_det_eq hdet (by omega) (by omega)
    (hi₀ _ (by omega))

/-- **The quotient length from the genuine lengths**: `v₂ det D_W(0) = 2 ℓ_mov + 4ω`
(tex 4066–4080). PROVED. -/
theorem hδ (G : GenuineLengthBlockModel K E₀ hZ DW rmov ℓmov ω) :
    v2 (central DW.det) = ((2 * (ℓmov : ℤ) + 4 * (ω : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  set Bc := fromBlocks (fromBlocks G.Bmov 0 0 G.Bmov') 0 0 (Matrix.blockDiagonal G.Bact) with hBc
  have hdetBc : Bc.det = G.Bmov.det * G.Bmov'.det * ∏ a, (G.Bact a).det := by
    rw [hBc, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_blockDiagonal]
  have hdetMov := det_ne_zero_of_length G.presMov G.lenMov
  have hdetMov' := det_ne_zero_of_length G.presMov' G.lenMov'
  have hdetAct : ∀ a, (G.Bact a).det ≠ 0 := fun a =>
    det_ne_zero_of_length (fun i => G.presAct i a) (G.lenAct a)
  have hne : Bc.det ≠ 0 := by
    rw [hdetBc]
    exact mul_ne_zero (mul_ne_zero hdetMov hdetMov')
      (Finset.prod_ne_zero_iff.mpr fun a _ => hdetAct a)
  have hvMov := valuation_of_length G.presMov G.lenMov
  have hvMov' := valuation_of_length G.presMov' G.lenMov'
  have hvAct : ∀ a, ((G.Bact a).det).valuation = 2 := fun a =>
    valuation_of_length (fun i => G.presAct i a) (G.lenAct a)
  have hval : (Bc.det).valuation = 2 * ℓmov + 4 * ω := by
    rw [hdetBc, PadicInt.valuation_mul (mul_ne_zero hdetMov hdetMov')
        (Finset.prod_ne_zero_iff.mpr fun a _ => hdetAct a),
      PadicInt.valuation_mul hdetMov hdetMov', hvMov, hvMov',
      valuation_prod_padicInt _ _ (fun a _ => hdetAct a)]
    simp only [hvAct, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hcoe : ((Bc.map PadicInt.Coe.ringHom)).det = ((Bc.det : ℤ_[2]) : ℚ_[2]) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  rw [ZInQ.Contrib.CloudB3RC53.Calibration.central_det, G.hcentral, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_submatrix_equiv_self, ZInQ.Contrib.CloudB3RC53.Calibration.v2_mul,
    ZInQ.Contrib.CloudB3RC53.Calibration.v2_mul, ← ZInQ.Contrib.CloudB3RC53.Calibration.central_det,
    ← ZInQ.Contrib.CloudB3RC53.Calibration.central_det, G.hPW, G.hQW, zero_add, add_zero, hcoe,
    v2_coe_padicInt' _ hne, hval]
  push_cast
  ring_nf

end GenuineLengthBlockModel

end LengthModel

/-! ### The calibration leaf with the local blocks over the genuine Kummer images -/

section Leaf

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **The inputs of (4.6) at one address, with the local blocks over the genuine Kummer images**
(tex 3987–4141). Every field of `CalibrationModelH` except the local-block fields `Fr`, `hFtr`,
`hFdet`, `PW`, `QW`, `eW`, `zmov`, `zmov'`, `Bact`, `hDW`, `hPW`, `hQW`, `hzmov`, `hzmov'`,
`hact`, with the same names and types; in their place one `GenuineLocalBlockModel` over the
leaf's field `K`, the fixed curve and the twist `h_x`. -/
structure CalibrationModelHG {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- the central valuation of the Kummer coordinate -/
  hK : v2 (central uK) =
    ((((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      ((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
        Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
        Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ)
  /-- **the local blocks over the genuine Kummer images**: the block structure of the quotient
  block with its central blocks presenting the central full/Kummer quotients of the actual
  Kummer conditions at the places above the moving prime and the active primes; it replaces the
  fields `Fr` … `hact` of `CalibrationModelH` -/
  blocks : GenuineLocalBlockModel K (Ecurve ℓ) (Fam.h x) DW rmov amov chimov (omega (Fam.h x))

attribute [instance] CalibrationModelHG.fieldK CalibrationModelHG.nfK CalibrationModelHG.decK
  CalibrationModelHG.quadK CalibrationModelHG.fκ CalibrationModelHG.dκ

namespace CalibrationModelHG

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- **`CalibrationModelH` from `CalibrationModelHG`**: the local-block fields are those of the
genuine local-block model. PROVED. -/
def toModelH (M : CalibrationModelHG D vL G₀ Fam x) : CalibrationModelH D vL G₀ Fam x :=
  { M with
    Fr := M.blocks.Fr
    hFtr := M.blocks.hFtr
    hFdet := M.blocks.hFdet
    PW := M.blocks.PW
    QW := M.blocks.QW
    eW := M.blocks.eW
    zmov := M.blocks.zmov
    zmov' := M.blocks.zmov'
    Bact := M.blocks.Bact
    hDW := M.blocks.hDW
    hPW := M.blocks.hPW
    hQW := M.blocks.hQW
    hzmov := M.blocks.hzmov
    hzmov' := M.blocks.hzmov'
    hact := M.blocks.hact }

/-- `CalibrationModelP` from `CalibrationModelHG`. PROVED. -/
theorem nonempty_modelP (M : CalibrationModelHG D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) :=
  M.toModelH.nonempty_modelP

end CalibrationModelHG

/-- **The remaining inputs of `RCSteps.calibration`, with the local blocks over the genuine Kummer
images** ((4.6), tex 3987–4141): as `CalibrationInputsH`, with `CalibrationModelHG` at every
address. -/
def CalibrationInputsHG {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHG D vL G₀ F x)

/-- `CalibrationInputsH` from `CalibrationInputsHG` (PROVED). -/
theorem calibrationInputsH_of_HG {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsHG D) :
    CalibrationInputsH D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toModelH⟩

/-- **`RCSteps.calibration` from `CalibrationInputsHG`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_HG {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHG D) : CalibrationTarget D :=
  calibrationTarget_of_H Pr hℓ (calibrationInputsH_of_HG h)

end Leaf

/-! ### The calibration leaf with the local lengths read from the genuine quotients -/

section LeafL

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **The inputs of (4.6) at one address, with the local quotient lengths read from the genuine
Kummer quotients** (tex 3987–4141). Every field of `CalibrationModelH` except the local-block
fields `Fr`, `hFtr`, `hFdet`, `PW`, `QW`, `eW`, `zmov`, `zmov'`, `Bact`, `hDW`, `hPW`, `hQW`,
`hzmov`, `hzmov'`, `hact`, with the same names and types; in their place one
`GenuineLengthBlockModel` (no Frobenius trace or determinant, no central moving scalars and no
central active block: the quotient length is computed from the genuine lengths). -/
structure CalibrationModelHL {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- the central valuation of the Kummer coordinate -/
  hK : v2 (central uK) =
    ((((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      ((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
        Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
        Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ)
  /-- **the local blocks with the lengths read from the genuine local quotients**: the
  central quotient block as a block sum of integral local blocks presenting the central
  full/Kummer quotients of the actual Kummer conditions, with the genuine lengths `v₂ N` and
  two; it replaces the fields `Fr` … `hact` of `CalibrationModelH` -/
  blocks : GenuineLengthBlockModel K (Ecurve ℓ) (Fam.h x) DW rmov
    (padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov)) (omega (Fam.h x))

attribute [instance] CalibrationModelHL.fieldK CalibrationModelHL.nfK CalibrationModelHL.decK
  CalibrationModelHL.quadK CalibrationModelHL.fκ CalibrationModelHL.dκ

namespace CalibrationModelHL

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- **`CalibrationModelP` from `CalibrationModelHL`** (tex 4051–4080, 4116–4138): the component
fields from the Edixhoven print, the moving fields from the non-divisibility, and `hvprim` from
the triangular Kummer model, the field `hK` and the quotient length `2 v₂N + 4ω` of the genuine
lengths (`GenuineLengthBlockModel.hδ`). PROVED. -/
theorem nonempty_modelP (M : CalibrationModelHL D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := componentFields_of_edixhovenIso M.hEdix M.hodd M.hram M.goodModel
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  have hvprim := hvprim_of_triangular_model M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
    (D.uPrim Fam x) M.hz M.hw M.hP M.hKc M.hadj (D.jrc (Fam.h x) D.kfin) vL
    ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
    ((padicValNat 2 M.shaA : ℕ) : ℤ)
    ((padicValInt 2 ((M.rmov : ℤ) + 1 - M.chimov * M.amov) : ℕ) : ℤ)
    ((omega (Fam.h x) : ℕ) : ℤ) M.hK M.blocks.hδ
  exact ⟨{ M with
    tp := tp
    hB := hB
    htp := htp
    rmov := (M.rmov : ℤ)
    hchi := hchi
    hmne := hmne
    hrmov := hrmov
    hBexp := hBexp
    hvprim := hvprim }⟩

end CalibrationModelHL

/-- **The remaining inputs of `RCSteps.calibration`, with the local quotient lengths read from the
genuine Kummer quotients** ((4.6), tex 3987–4141): `CalibrationModelHL` at every address. -/
def CalibrationInputsHL {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHL D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsHL` (PROVED). -/
theorem calibrationInputsP_of_HL {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsHL D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- **`RCSteps.calibration` from `CalibrationInputsHL`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_HL {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHL D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_HL h))

end LeafL

end ZInQ.Contrib.RC53Assist.Calibration
