import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.OneProof.RC.Wiring.BaseZeroText
import ZInQKernel.Contrib.RC53Assist.CentralSelmer.Comparison

/-!
# Central Kummer comparison: finite-level Kummer complexes have zero rationalization

The genuine finite-level Kummer Selmer data of the project (`kummerSelData`, with the actual
Kummer conditions `actualKummerAtS`) have coefficients in `A_i = (ℤ/2^i)[t]/t^i` and modules
`M_i = (T₂E ⊗ A_i)(χ_hΨ_i)` (manuscript lines 2723--2726). This file records why such a
complex cannot serve as the ordinary rational Kummer complex `K₀` of the central comparison
(lines 3952--3962), and hence why `K₀` must be built from the `2`-adic Tate module.

* `acoef_two_pow_eq_zero`, `isEmpty_ringHom_acoef`: `2^i = 0` in `A_i`, so there is no ring
  homomorphism `A_i → ℚ₂`; coefficient extension of an `A_i`-complex to `ℚ₂` along a ring map is
  impossible.
* `integralRationalization C`: the rationalization through the integers, `ℚ₂ ⊗_ℤ C`, of a complex
  of modules over a commutative ring `R`. If a nonzero integer `N` vanishes in `R`, every term is zero
  (`isZero_integralRationalization_X`), because a divisible group tensored with an `N`-torsion
  group is zero (`tensor_eq_zero_of_divisible_of_torsion`); in particular its degree-one
  cohomology is zero.
* `finrank_ker_eq_zero_of_finiteLevel`: a degree-one quasi-isomorphism from such a rationalization
  into a specialized base model forces the central kernel `ker ρ(Dm)` to be zero.
* `finiteLevel_input_one_refuted` and `finiteLevel_kummer_input_one_refuted`: if the base model has
  central dimension one in degree one (`rank ρ(Dm) = m`, the conclusion `hcentral` of the
  base-zero lemma), no such quasi-isomorphism exists; in particular not from the rationalization of
  the actual finite-level Kummer Selmer complex `selCx (kummerSelData …)`.
* `baseZeroCoreText_finiteLevel_refuted`: under full Selmer corank one, for every base-zero core of
  the leaf `BaseZeroCoreText` and every model of its matrix with `CU.d 0 1 = 0`, input (1) with
  `K₀` a rationalized finite-level complex fails.

No printed statement is assumed in this file.
-/

noncomputable section

namespace ZInQ.Manuscript.RC53Assist.CentralKummer

open CategoryTheory Matrix ZInQ.Manuscript.RC ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### No ring homomorphism from the finite coefficients to `ℚ₂` -/

/-- `2^i = 0` in the finite coefficient ring `A_i = (ℤ/2^i)[t]/t^i`. -/
theorem acoef_two_pow_eq_zero (i : ℕ) : ((2 ^ i : ℕ) : Acoef i) = 0 := by
  rw [← map_natCast (algebraMap (ZMod (2 ^ i)) (Acoef i)), ZMod.natCast_self, map_zero]

/-- **There is no ring homomorphism `A_i → ℚ₂`.** -/
theorem isEmpty_ringHom_acoef (i : ℕ) : IsEmpty (Acoef i →+* ℚ_[2]) := by
  refine ⟨fun φ => ?_⟩
  have h := congrArg φ (acoef_two_pow_eq_zero i)
  rw [map_natCast, map_zero, Nat.cast_pow, Nat.cast_ofNat] at h
  exact pow_ne_zero i two_ne_zero h

/-! ### Rationalization through the integers -/

/-- A divisible group tensored over `ℤ` with an `N`-torsion group is zero. -/
theorem tensor_eq_zero_of_divisible_of_torsion {Q M : Type} [AddCommGroup Q] [Module ℤ Q]
    [AddCommGroup M] [Module ℤ M] (N : ℕ) (hQ : ∀ q : Q, ∃ q' : Q, N • q' = q)
    (hM : ∀ x : M, N • x = 0) (t : TensorProduct ℤ Q M) : t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul q x =>
    obtain ⟨q', rfl⟩ := hQ q
    have h1 : (N • q') ⊗ₜ[ℤ] x = N • (q' ⊗ₜ[ℤ] x) :=
      map_nsmul (AddMonoidHom.mk' (fun a : Q => a ⊗ₜ[ℤ] x)
        (fun a b => TensorProduct.add_tmul a b x)) N q'
    have h2 : q' ⊗ₜ[ℤ] (N • x) = N • (q' ⊗ₜ[ℤ] x) :=
      map_nsmul (AddMonoidHom.mk' (fun y : M => q' ⊗ₜ[ℤ] y)
        (fun a b => TensorProduct.tmul_add q' a b)) N x
    rw [h1, ← h2, hM x, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

variable {R : Type} [CommRing R]

/-- **The rationalization `ℚ₂ ⊗_ℤ C`** of a complex of `R`-modules: restriction of scalars to
`ℤ`, then coefficient extension along `ℤ → ℚ₂`. -/
def integralRationalization (C : CochainComplex (ModuleCat.{0} R) ℤ) :
    CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  scalarChangedComplex (Int.castRingHom ℚ_[2])
    (((ModuleCat.restrictScalars.{0} (Int.castRingHom R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)

/-- **Every term of the rationalization is zero** when a nonzero integer vanishes in `R`. -/
theorem isZero_integralRationalization_X (N : ℕ) (hN : N ≠ 0) (hR : (N : R) = 0)
    (C : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    Limits.IsZero ((integralRationalization C).X n) := by
  have hN' : (N : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hQ : ∀ q : (ModuleCat.restrictScalars.{0} (Int.castRingHom ℚ_[2])).obj
      (ModuleCat.of ℚ_[2] ℚ_[2]), ∃ q', N • q' = q := by
    intro q
    let q₀ : ℚ_[2] := q
    refine ⟨(q₀ * (N : ℚ_[2])⁻¹ : ℚ_[2]), ?_⟩
    change N • (q₀ * (N : ℚ_[2])⁻¹) = q₀
    rw [nsmul_eq_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hN', mul_one]
  have hM : ∀ x : (ModuleCat.restrictScalars.{0} (Int.castRingHom R)).obj (C.X n),
      N • x = 0 := by
    intro x
    let x₀ : C.X n := x
    change N • x₀ = 0
    rw [← Nat.cast_smul_eq_nsmul R N x₀, hR, zero_smul]
  have : Subsingleton ((integralRationalization C).X n) :=
    ⟨fun a b => (tensor_eq_zero_of_divisible_of_torsion N hQ hM a).trans
      (tensor_eq_zero_of_divisible_of_torsion N hQ hM b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-`n` cohomology of the rationalization is zero. -/
theorem isZero_integralRationalization_homology (N : ℕ) (hN : N ≠ 0) (hR : (N : R) = 0)
    (C : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    Limits.IsZero ((integralRationalization C).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ ((integralRationalization C).sc n)
    (isZero_integralRationalization_X N hN hR C n)

/-! ### Consequences for input (1) -/

variable {m : ℕ} {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT}

/-- **A degree-one quasi-isomorphism from a rationalized finite-level complex kills the central
kernel.** -/
theorem finrank_ker_eq_zero_of_finiteLevel (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (N : ℕ) (hN : N ≠ 0) (hR : (N : R) = 0) (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (i : integralRationalization C ⟶ scalarChangedComplex Rings.rhoT CU) [QuasiIsoAt i 1] :
    Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = 0 := by
  have hz := isZero_integralRationalization_homology N hN hR C 1
  have e : (integralRationalization C).homology 1 ≃ₗ[ℚ_[2]]
      LinearMap.ker (Dm.map Rings.rhoT).mulVecLin :=
    (asIso (HomologicalComplex.homologyMap i 1)).toLinearEquiv.trans
      (specializedModelHomologyOneEquiv Rings.rhoT CU Dm e1 e2 hzero hd)
  have : Subsingleton ((integralRationalization C).homology 1) :=
    ModuleCat.subsingleton_of_isZero hz
  rw [← e.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-- **Input (1) is refuted for rationalized finite-level complexes** once the central degree-one
dimension of the base model is one (`rank ρ(Dm) = m`). -/
theorem finiteLevel_input_one_refuted (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (hcentral : (Dm.map Rings.rhoT).rank = m)
    (N : ℕ) (hN : N ≠ 0) (hR : (N : R) = 0) (C : CochainComplex (ModuleCat.{0} R) ℤ) :
    ¬ ∃ i : integralRationalization C ⟶ scalarChangedComplex Rings.rhoT CU, QuasiIsoAt i 1 := by
  rintro ⟨i, hi⟩
  have h0 := finrank_ker_eq_zero_of_finiteLevel CU e1 e2 hzero hd N hN hR C i
  have h1 := BaseZeroLimit.finrank_ker_of_rank_eq _ hcentral
  omega

open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
  NumberField IsDedekindDomain in
open scoped Classical in
/-- **The actual finite-level Kummer Selmer complex does not supply input (1).** For every stage
`i` and all data of the genuine finite-level Kummer Selmer data `kummerSelData` (the actual Kummer
conditions at the places of `P`, given conditions at the other places of `S₀`, unramified
conditions outside `S₀`), there is no degree-one quasi-isomorphism from the rationalization of
`selCx (kummerSelData …)` into a specialized base model with `rank ρ(Dm) = m`. -/
theorem finiteLevel_kummer_input_one_refuted {K : Type} [Field K] [NumberField K]
    {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
    (i : ℕ) (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
    (α : GKS K S₀ →* (Acoef i)ˣ) (hFull : FullTorsion K S₀ W (2 ^ i)) [IsOpenKer α]
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (hcentral : (Dm.map Rings.rhoT).rank = m) :
    ¬ ∃ ι : integralRationalization
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
            (kummerSelData hS W i s hs hs0 α hFull P hα c))) ⟶
        scalarChangedComplex Rings.rhoT CU, QuasiIsoAt ι 1 :=
  finiteLevel_input_one_refuted CU e1 e2 hzero hd hcentral (2 ^ i) (pow_ne_zero i two_ne_zero)
    (acoef_two_pow_eq_zero i) _

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 in
/-- **The finite-level pin is refuted for every base-zero core.** Under full Selmer corank one,
for every core `M` of the leaf on the text's steps and every model of its matrix `M.Dm` with
`CU.d 0 1 = 0`, there is no degree-one quasi-isomorphism into the specialized model from the
rationalization of a complex over a ring in which a nonzero integer vanishes. -/
theorem baseZeroCoreText_finiteLevel_refuted {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {G : Type}
    [AddCommGroup G] {Pt : G} (M : BaseZeroCoreText D Fam Pt)
    (hSel : SelmerCorankOneOverK ℓ D.kfin)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (M.m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (M.m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = M.Dm *ᵥ e1 x)
    (N : ℕ) (hN : N ≠ 0) (hR : (N : R) = 0) (C : CochainComplex (ModuleCat.{0} R) ℤ) :
    ¬ ∃ i : integralRationalization C ⟶ scalarChangedComplex Rings.rhoT CU, QuasiIsoAt i 1 :=
  finiteLevel_input_one_refuted CU e1 e2 hzero hd
    (BaseZeroLimit.hcentral_of_selmer hSel M.central) N hN hR C

end ZInQ.Manuscript.RC53Assist.CentralKummer
