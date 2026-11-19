import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.TwistDescentProof
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusRootsProof

/-!
# GenusOdd: Elliot's index-at-most-two comparison without `H_c/ℚ` Galois (PROVED)

`two_nsmul_mem_twist_add_torsion` (`Elliot.lean`) uses that the ring class field `H_c` is Galois
over `ℚ` (the GLUE `RingClassGalois`) to have complex conjugation act on `E(H_c)`. Here the same
conclusion is proved inside any finite Galois extension `H̃/ℚ` containing `H_c` (e.g. its normal
closure): the eigen-decomposition `2x = (x + ε ρx) + (x − ε ρx)` is carried out in `E(H̃)`, with `ρ`
a lift to `H̃` of the nontrivial automorphism of `K`, and the Galois descent (`twistDescent_proof`)
along `H̃/ℚ`; the conclusion is brought back to `E(H_c)` by injectivity of base change.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

section TwoFields

variable {H H' : Type*} [Field H] [Algebra ℚ H] [DecidableEq H] [Field H'] [Algebra ℚ H']
  [DecidableEq H']
variable (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (d : ℚ)

include h₁ h₃ in
/-- **Base change of the twist embedding** (PROVED): `ι(ψ_s P) = ψ_{ι s} P` for `ι : H →ₐ[ℚ] H'`. -/
theorem map_twistEmb₂ (ι : H →ₐ[ℚ] H') {s : H} (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d)
    (hs' : ι s ≠ 0) (hsd' : ι s ^ 2 = algebraMap ℚ H' d) (P : (qtwist E d).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι
        (twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P) =
      twistEmb E d (ι s) (twistVC_smul E h₁ h₃ hs' hsd') P := by
  rcases P with _ | ⟨X, Y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero, map_zero]
  · obtain ⟨h', e⟩ := twistEmb_some E h₁ h₃ d hs hsd h
    obtain ⟨h'', e'⟩ := twistEmb_some E h₁ h₃ d hs' hsd' h
    rw [e, e', WeierstrassCurve.Affine.Point.map_some]
    simp only [map_div₀, map_pow, AlgHom.commutes]

theorem twistEmb_congr {s s' : H} (hss : s = s')
    (heq : twistVC s • E.baseChange H = (qtwist E d).baseChange H)
    (heq' : twistVC s' • E.baseChange H = (qtwist E d).baseChange H)
    (P : (qtwist E d).toAffine.Point) : twistEmb E d s heq P = twistEmb E d s' heq' P := by
  subst hss; rfl

end TwoFields

theorem intCast_inj_of_algebra {F : Type*} [Field F] [Algebra ℚ F] {a b : ℤ}
    (h : (a : F) = (b : F)) : a = b := by
  have h' : algebraMap ℚ F (a : ℚ) = algebraMap ℚ F (b : ℚ) := by rw [map_intCast, map_intCast, h]
  exact_mod_cast (algebraMap ℚ F).injective h'

section Closure

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- **Elliot's index-at-most-two comparison inside a Galois closure** (PROVED; tex L2433–2435).
Same conclusion as `two_nsmul_mem_twist_add_torsion`, with `H_c/ℚ` Galois replaced by a finite
Galois extension `H̃/ℚ` containing `H_c` (`Ht`), and complex conjugation by any lift of the
nontrivial automorphism of `K`; the hypothesis `d_R d_T < 0` makes `√d_R √d_T ∈ K` irrational. -/
theorem two_nsmul_mem_twist_add_torsion_closure (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (hK2 : Module.finrank ℚ K = 2)
    (H : Type) [Field H] [DecidableEq H] [Algebra K H] [Algebra ℚ H] [IsScalarTower ℚ K H]
    [FiniteDimensional K H] [IsGalois K H]
    (ε : (H ≃ₐ[K] H) → ℤ) (hε2 : ∀ σ, ε σ * ε σ = 1) {dR dT : ℚ}
    {sR sT : H} (hsR : sR ≠ 0) (hsRd : sR ^ 2 = algebraMap ℚ H dR) (hsT : sT ≠ 0)
    (hsTd : sT ^ 2 = algebraMap ℚ H dT) (hneg : dR * dT < 0)
    (hσ : ∀ σ : H ≃ₐ[K] H, σ sR = (ε σ : H) * sR ∧ σ sT = (ε σ : H) * sT)
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P)
    (Ht : Type) [Field Ht] [DecidableEq Ht] [Algebra K Ht] [Algebra ℚ Ht] [IsScalarTower ℚ K Ht]
    [Algebra H Ht] [IsScalarTower K H Ht] [FiniteDimensional ℚ Ht] [IsGalois ℚ Ht]
    (x : (E.baseChange H).toAffine.Point)
    (hx : ∀ σ : H ≃ₐ[K] H,
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) x =
        ε σ • x) :
    ∃ r : (qtwist E dR).toAffine.Point,
      IsOfFinAddOrder ((2 : ℕ) • x - twistEmb E dR sR (twistVC_smul E h₁ h₃ hsR hsRd) r) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  set ι : H →ₐ[K] Ht :=
    IsScalarTower.toAlgHom K (H) Ht
  set ιQ : H →ₐ[ℚ] Ht := ι.restrictScalars ℚ
  have hιQ : ∀ y, ιQ y = ι y := fun y => rfl
  have hι0 : ∀ y, y ≠ 0 → ι y ≠ 0 := fun y hy => (map_ne_zero ι).mpr hy
  have hιRd : ι sR ^ 2 = algebraMap ℚ Ht dR := by
    rw [← map_pow, hsRd, ← hιQ, AlgHom.commutes]
  have hιTd : ι sT ^ 2 = algebraMap ℚ Ht dT := by
    rw [← map_pow, hsTd, ← hιQ, AlgHom.commutes]
  set φ := AlgEquiv.restrictNormalHom (F := ℚ) K (K₁ := Ht)
  set N := φ.ker
  -- restriction of a `K`-linear automorphism of `Ht` to `H_c`
  have hres : ∀ (g : Ht ≃ₐ[ℚ] Ht) (hg : g ∈ N) (y : H),
      g (ι y) = ι (((toKEquiv' g hg).restrictNormal (H)) y) := by
    intro g hg y
    have := AlgEquiv.restrictNormal_commutes (toKEquiv' g hg) (H) y
    exact this.symm
  have hsgn : ∀ (g : Ht ≃ₐ[ℚ] Ht) (hg : g ∈ N),
      sgnAt (ι sR) g = ε ((toKEquiv' g hg).restrictNormal H) ∧
      sgnAt (ι sT) g = ε ((toKEquiv' g hg).restrictNormal H) := by
    intro g hg
    obtain ⟨h1, h2⟩ := hσ ((toKEquiv' g hg).restrictNormal (H))
    have e1 := hres g hg sR
    have e2 := hres g hg sT
    rw [h1, map_mul, map_intCast, apply_eq_sgnAt hιRd] at e1
    rw [h2, map_mul, map_intCast, apply_eq_sgnAt hιTd] at e2
    exact ⟨intCast_inj_of_algebra (F := Ht) (mul_right_cancel₀ (hι0 sR hsR) e1),
      intCast_inj_of_algebra (F := Ht) (mul_right_cancel₀ (hι0 sT hsT) e2)⟩
  have hNeq : ∀ g ∈ N, sgnAt (ι sR) g = sgnAt (ι sT) g := fun g hg => by
    rw [(hsgn g hg).1, (hsgn g hg).2]
  set act : (Ht ≃ₐ[ℚ] Ht) → (E.baseChange Ht).toAffine.Point →+ (E.baseChange Ht).toAffine.Point :=
    fun g => WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g.toAlgHom with hact
  set x' := WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ιQ x
  have hxN : ∀ g ∈ N, act g x' = sgnAt (ι sR) g • x' := by
    intro g hg
    have hcomp : g.toAlgHom.comp ιQ = ιQ.comp (((toKEquiv' g hg).restrictNormal
        (H)).toAlgHom.restrictScalars ℚ) :=
      AlgHom.ext fun y => hres g hg y
    have := hx ((toKEquiv' g hg).restrictNormal (H))
    simp only [hact, x']
    rw [WeierstrassCurve.Affine.Point.map_map, hcomp, ← WeierstrassCurve.Affine.Point.map_map]
    rw [this, map_zsmul, (hsgn g hg).1]
  -- `√d_R √d_T = r ∈ K`, irrational
  obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (sR * sT)).mpr fun σ => by
    rw [map_mul, (hσ σ).1, (hσ σ).2]
    have := hε2 σ
    calc _ = ((ε σ * ε σ : ℤ) :
          H) * (sR * sT) := by push_cast; ring
      _ = sR * sT := by rw [this]; simp
  have hr2 : r ^ 2 = algebraMap ℚ K (dR * dT) := by
    apply (algebraMap K (H)).injective
    rw [map_pow, hr, mul_pow, hsRd, hsTd, ← map_mul, ← IsScalarTower.algebraMap_apply]
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hr2
    exact hneg.ne hr2
  have hrQ : r ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, rfl⟩
    rw [← map_pow] at hr2
    have := (algebraMap ℚ K).injective hr2
    have : (0 : ℚ) ≤ dR * dT := this ▸ sq_nonneg q
    linarith
  have hcardK : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  obtain ⟨τ, hτ⟩ : ∃ τ : K ≃ₐ[ℚ] K, τ r ≠ r := by
    by_contra hcon
    push Not at hcon
    exact hrQ ((IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) r).mpr hcon)
  have hτr : τ r = -r := by
    have : (τ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr2, AlgEquiv.commutes]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_left hτ
  obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := Ht) τ
  have hρφ : φ ρ = τ := hρ
  have hρr : ρ (algebraMap K Ht r) = -algebraMap K Ht r := by
    have := AlgEquiv.restrictNormal_commutes ρ K r
    rw [← this]
    have h' : ρ.restrictNormal K = τ := hρ
    rw [h', hτr, map_neg]
  have hιr : ι sR * ι sT = algebraMap K Ht r := by
    rw [← map_mul, ← hr, AlgHom.commutes]
  have hρsgn : sgnAt (ι sR) ρ = -sgnAt (ι sT) ρ := by
    have e := hρr
    rw [← hιr, map_mul, apply_eq_sgnAt hιRd, apply_eq_sgnAt hιTd] at e
    have hne : ι sR * ι sT ≠ 0 := mul_ne_zero (hι0 sR hsR) (hι0 sT hsT)
    have e' : ((sgnAt (ι sR) ρ * sgnAt (ι sT) ρ : ℤ) : Ht) * (ι sR * ι sT) =
        ((-1 : ℤ) : Ht) * (ι sR * ι sT) := by push_cast; linear_combination e
    have e'' := mul_right_cancel₀ hne e'
    have hz : sgnAt (ι sR) ρ * sgnAt (ι sT) ρ = -1 :=
      intCast_inj_of_algebra (F := Ht) (by push_cast at e'' ⊢; exact e'')
    have h1 := sgnAt_sq (ι sR) ρ
    have h2 := sgnAt_sq (ι sT) ρ
    unfold sgnAt at hz h1 h2 ⊢
    split_ifs at hz h1 h2 ⊢ <;> omega
  have hnorm : ∀ g ∈ N, ρ⁻¹ * g * ρ ∈ N := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg, mul_one, map_inv, inv_mul_cancel]
  have hρ2 : ρ * ρ ∈ N := by
    rw [MonoidHom.mem_ker, map_mul]
    have := pow_card_eq_one' (G := K ≃ₐ[ℚ] K) (x := φ ρ)
    rw [hcardK, pow_two] at this
    exact this
  obtain ⟨huN, huρ, hwN, hwρ, hsum⟩ := eigen_decomp act (map_mul_algEquiv' E) (sgnAt (ι sR))
    (sgnAt (ι sT)) (by
      have := charZero_of_injective_algebraMap (algebraMap ℚ Ht).injective
      exact sgnAt_mul (hι0 sR hsR) hιRd) (sgnAt_sq (ι sR)) (sgnAt_sq (ι sT)) N hNeq ρ
    hρsgn hnorm hρ2 x' hxN
  -- `ρ` is not `K`-linear
  have hnotK : ¬ ∃ σ : Ht ≃ₐ[K] Ht, ∀ z, σ z = ρ z := by
    rintro ⟨σ, hσρ⟩
    have h1 := hσρ (algebraMap K Ht r)
    rw [AlgEquiv.commutes, hρr] at h1
    have : (2 : Ht) * algebraMap K Ht r = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · have h2 : algebraMap ℚ Ht 2 = 0 := by rw [map_ofNat]; exact h
      rw [map_eq_zero] at h2; norm_num at h2
    · exact hr0 ((map_eq_zero _).mp h)
  -- descent of `u` and `w`
  have hdescent : ∀ (d : ℚ) (s : Ht) (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ Ht d)
      (y : (E.baseChange Ht).toAffine.Point),
      (∀ g ∈ N, act g y = sgnAt s g • y) → act ρ y = sgnAt s ρ • y →
      ∃ P : (qtwist E d).toAffine.Point, twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P = y := by
    intro d s hs hsd y hyN hyρ
    refine twistDescent_proof E h₁ h₃ K hK2 Ht d s hs hsd ρ hnotK y (fun σ => ?_) ?_
    · have hmem : σ.restrictScalars ℚ ∈ N := restrictScalars_mem_ker' (K := K) (H := Ht) σ
      have := hyN _ hmem
      have hfg : (σ.restrictScalars ℚ).toAlgHom = σ.toAlgHom.restrictScalars ℚ :=
        AlgHom.ext fun z => rfl
      simp only [hact, hfg] at this
      rw [this]
      unfold sgnAt
      by_cases h : σ s = s
      · rw [if_pos (by exact h), if_pos h, one_smul]
      · rw [if_neg (by exact h), if_neg h, neg_smul, one_smul]
    · simp only [hact] at hyρ
      rw [hyρ]
      unfold sgnAt
      split_ifs <;> simp
  obtain ⟨P, hP⟩ := hdescent dR (ι sR) (hι0 sR hsR) hιRd _ huN huρ
  obtain ⟨Q, hQ⟩ := hdescent dT (ι sT) (hι0 sT hsT) hιTd _ hwN hwρ
  have key : (2 : ℕ) • x' - twistEmb E dR (ι sR) (twistVC_smul E h₁ h₃ (hι0 sR hsR) hιRd) P =
      twistEmb E dT (ι sT) (twistVC_smul E h₁ h₃ (hι0 sT hsT) hιTd) Q := by
    rw [hP, hQ, ← hsum, add_sub_cancel_left]
  have hψ : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ιQ
      (twistEmb E dR sR (twistVC_smul E h₁ h₃ hsR hsRd) P) =
      twistEmb E dR (ι sR) (twistVC_smul E h₁ h₃ (hι0 sR hsR) hιRd) P :=
    (map_twistEmb₂ E h₁ h₃ dR ιQ hsR hsRd (by rw [hιQ]; exact hι0 sR hsR)
      (by rw [hιQ]; exact hιRd) P).trans (twistEmb_congr E dR (hιQ sR) _ _ P)
  refine ⟨P, isOfFinAddOrder_of_map (WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ιQ)
    (WeierstrassCurve.Affine.Point.map_injective _) ?_⟩
  have e : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ιQ
      ((2 : ℕ) • x - twistEmb E dR sR (twistVC_smul E h₁ h₃ hsR hsRd) P) =
      twistEmb E dT (ι sT) (twistVC_smul E h₁ h₃ (hι0 sT hsT) hιTd) Q := by
    rw [map_sub, map_nsmul, hψ]
    exact key
  rw [e]
  exact isOfFinAddOrder_map _ (htorT Q)

/-- **Elliot's index-at-most-two comparison for the ring class field, without `RingClassGalois`**
(PROVED): as `two_nsmul_mem_twist_add_torsion`, using the normal closure of `H_c` over `ℚ` inside an
algebraic closure of `ℚ` in place of `H_c/ℚ` Galois. -/
theorem two_nsmul_mem_twist_add_torsion' (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (hK2 : Module.finrank ℚ K = 2)
    [DecidableEq (ringClassField (conductorOrder K c))]
    {χ : Pic (conductorOrder K c) →* ℂˣ} {dR dT : ℚ}
    {sR sT : ringClassField (conductorOrder K c)} (hsR : sR ≠ 0)
    (hsRd : sR ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dR) (hsT : sT ≠ 0)
    (hsTd : sT ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dT) (hneg : dR * dT < 0)
    (hσ : ∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      σ sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) :
        ringClassField (conductorOrder K c)) * sR ∧
      σ sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) :
        ringClassField (conductorOrder K c)) * sT)
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P) :
    ∀ x ∈ eigenLattice E χ, ∃ r : (qtwist E dR).toAffine.Point,
      IsOfFinAddOrder ((2 : ℕ) • x - twistEmb E dR sR (twistVC_smul E h₁ h₃ hsR hsRd) r) := by
  intro x hx
  let j : ringClassField (conductorOrder K c) →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let _ : Algebra (ringClassField (conductorOrder K c)) (AlgebraicClosure ℚ) := j.toAlgebra
  have : IsScalarTower ℚ (ringClassField (conductorOrder K c)) (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]; exact (j.commutes x).symm
  let _ : Algebra K (IntermediateField.normalClosure ℚ (ringClassField (conductorOrder K c))
      (AlgebraicClosure ℚ)) :=
    ((algebraMap (ringClassField (conductorOrder K c)) (IntermediateField.normalClosure ℚ
      (ringClassField (conductorOrder K c)) (AlgebraicClosure ℚ))).comp
      (algebraMap K (ringClassField (conductorOrder K c)))).toAlgebra
  have : IsScalarTower K (ringClassField (conductorOrder K c))
      (IntermediateField.normalClosure ℚ (ringClassField (conductorOrder K c))
        (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ K (IntermediateField.normalClosure ℚ (ringClassField (conductorOrder K c))
      (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ _) q, eq_ratCast (algebraMap ℚ K) q, map_ratCast]
  let _ := Classical.decEq (IntermediateField.normalClosure ℚ (ringClassField (conductorOrder K c))
    (AlgebraicClosure ℚ))
  exact two_nsmul_mem_twist_add_torsion_closure E h₁ h₃ hK2 (ringClassField (conductorOrder K c))
    (fun σ => chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ))
    (fun σ => chiSign_sq _) hsR hsRd hsT hsTd hneg hσ htorT
    (IntermediateField.normalClosure ℚ (ringClassField (conductorOrder K c)) (AlgebraicClosure ℚ))
    x hx

end Closure

end ZInQ.Contrib.CloudB3RC53.GenusOdd
