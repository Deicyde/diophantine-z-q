import ZInQKernel.Contrib.OneProof.CMFibreSplit
import ZInQKernel.Contrib.OneProof.CMFibreSplit.Curve

/-! # The original CM curve order statement

`CMCurveOrder324` is the body of `CMCurveOrder` from commit `324f0655a`, before the
fibre-split branch inserted an abelian surface hypothesis. Its corner proof below
reuses that branch's argument, with the rank bound in the existing T6 theorem used
to show that the idempotent is proper. Manuscript: `thm:height`, proof, L582–586. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace HDec.CMBranch.FibreSplit

open scoped TensorProduct

/-- On-the-spot glue for the CM fibers in `thm:height`, L582–586, as originally
stated in `324f0655a`: an elliptic isogeny factor of an abelian variety with
geometric endomorphism algebra `M₂(ℚ(√d))`, `d < 0`, has geometric endomorphism
ring an imaginary quadratic order. Only the factor is assumed to have a given dimension. -/
def CMCurveOrder324 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω] (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
    ∀ (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E) (n : ℕ), 0 < n →
      cmp i h = (n : PkgI3.AbVar.End E) →
      ∃ (k : Type) (_ : Field k) (_ : NumberField k) (R : Subring k),
        IsImagQuadOrder k R ∧ IsCMBy E k R

/-- On-the-spot (CM fibers, `thm:height` L582–586): the retraction cannot split in the
other direction as well. If `i ∘ h = [n]`, then `g ↦ h ∘ g ∘ i` embeds the rank-eight
endomorphism lattice of A in the endomorphism lattice of E, of rank at most four by T6. -/
private theorem reverse_split_impossible
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    {K : Type} [Field K] [CharZero K] (τ : K →+* ℂ) {A E : PkgI3.AbVar K}
    (hE : E.dim = 1) {d : ℚ} (hd : d < 0)
    (e : PkgI3.AbVar.End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d))
    {i : PkgI3.AbVar.Hom E A} {h : PkgI3.AbVar.Hom A E} {n : ℕ}
    (hn : 0 < n) (hF : cmp h i = (n : PkgI3.AbVar.End A)) : False := by
  haveI := fact_irr hd
  obtain ⟨hfree, -, -, -⟩ := hHF K τ A A
  obtain ⟨-, hfin, hrE, -⟩ := hHF K τ E E
  let α : PkgI3.AbVar.End A →ₗ[ℤ] PkgI3.AbVar.End E :=
    { toFun := fun g => cmp (cmp i g) h
      map_add' := fun g g' => by simp only [cmp_add_right, cmp_add_left]
      map_smul' := fun a g => by simp only [RingHom.id_apply, cmp_zsmul_right, cmp_zsmul_left] }
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have hz : cmp h (cmp (cmp (cmp i g) h) i) = 0 := by
      change cmp h (cmp (α g) i) = 0
      rw [hg, cmp_zero_left, cmp_zero_right]
    have hcmp : cmp h (cmp (cmp (cmp i g) h) i) =
        cmp (cmp h i) (cmp g (cmp h i)) := by simp only [cmp_assoc]
    rw [hcmp, hF, cmp_natCast_right, cmp_natCast_left, smul_smul] at hz
    exact eq_zero_of_nsmul (Nat.mul_pos hn hn) hz
  have hle := LinearMap.finrank_le_finrank_of_injective (f := α) hinj
  have h8 : Module.finrank ℤ (PkgI3.AbVar.End A) = 8 := by
    calc
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A) := Module.finrank_baseChange.symm
      _ = Module.finrank ℚ (Matrix (Fin 2) (Fin 2) (Kd d)) := e.toLinearEquiv.finrank_eq
      _ = 8 := by rw [Module.finrank_matrix, finrank_kd hd]; rfl
  have h4 : Module.finrank ℤ (PkgI3.AbVar.End E) ≤ 4 := by
    have hrE' : ((Module.finrank ℤ (PkgI3.AbVar.End E) : ℕ∞) : WithBot ℕ∞) ≤
        (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa only [hE, mul_one, Nat.cast_ofNat, WithBot.coe_ofNat] using hrE
    exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp hrE')
  omega

/-- The original version of `CMCurveOrder` is proved from the chain's T6. -/
theorem cmCurveOrder324_of (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) : CMCurveOrder324 := by
  intro L _ _ A Ω _ _ _ _ d hd ⟨e⟩ E hE1 i h n hn hih
  haveI := fact_irr hd
  letI : NumberField (Kd d) := numberField_kd hd
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  let A' := A.baseChange Ω
  let E' := (E : PkgI3.AbVar L).baseChange Ω
  let i' : PkgI3.AbVar.Hom E' A' := homBC Ω i
  let h' : PkgI3.AbVar.Hom A' E' := homBC Ω h
  have hih' : cmp i' h' = (n : PkgI3.AbVar.End E') := by
    simp only [i', h']; rw [← homBC_cmp, hih, homBC_natCast]
  have hih'' : ∀ {Z : PkgI3.AbVar Ω} (x : PkgI3.AbVar.Hom E' Z), cmp i' (cmp h' x) = n • x := by
    intro Z x; rw [← cmp_assoc, hih', cmp_natCast_left]
  have hdimE' : E'.dim = 1 := (HSyn.G0Split.dimBaseChange L Ω E).trans hE1
  obtain ⟨φL⟩ : Nonempty (L →+* ℂ) := inferInstance
  letI : Algebra L ℂ := φL.toAlgebra
  let τ : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[L] ℂ).toRingHom
  have hnk : (n : Kd d) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- `ψ : End(A_Ω) → M₂(k)`
  let ψ : PkgI3.AbVar.End A' →+* Matrix (Fin 2) (Fin 2) (Kd d) :=
    e.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A' →ₐ[ℤ] PkgI3.AbVar.End0 A').toRingHom
  have hψinj : Function.Injective ψ := fun x y hxy =>
    includeRight_injective A' (e.injective hxy)
  let F : PkgI3.AbVar.End A' := cmp h' i'
  let Φ : PkgI3.AbVar.End E' → PkgI3.AbVar.End A' := fun g => cmp (cmp h' g) i'
  have hΦ : ∀ g, Φ g = cmp h' (cmp g i') := fun g => cmp_assoc _ _ _
  have hΦmul : ∀ g g', Φ g * Φ g' = (n : PkgI3.AbVar.End A') * Φ (g * g') := by
    intro g g'
    rw [mul_eq_cmp, hΦ, hΦ, ← nsmul_eq_mul, mul_eq_cmp, hΦ]
    simp only [cmp_assoc, hih'', cmp_nsmul_right]
  have hΦ1 : Φ 1 = F := by simp only [Φ, cmp_one_right]; rfl
  have hΦadd : ∀ g g', Φ (g + g') = Φ g + Φ g' := by
    intro g g'; simp only [Φ, cmp_add_right, cmp_add_left]
  let χ : PkgI3.AbVar.End E' → Matrix (Fin 2) (Fin 2) (Kd d) := fun g => (n : Kd d)⁻¹ • ψ (Φ g)
  let ε := χ 1
  have hχmul : ∀ g g', χ (g * g') = χ g * χ g' := by
    intro g g'
    simp only [χ]
    rw [smul_mul_smul_comm, ← map_mul, hΦmul, map_mul, map_natCast, ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul (Kd d), smul_smul]
    congr 1
    field_simp
  have hχadd : ∀ g g', χ (g + g') = χ g + χ g' := by
    intro g g'; simp only [χ, hΦadd, map_add, smul_add]
  have hεε : ε * ε = ε := by rw [← hχmul, _root_.mul_one]
  have hχε : ∀ g, χ g * ε = χ g := fun g => by rw [← hχmul, _root_.mul_one]
  have hεχ : ∀ g, ε * χ g = χ g := fun g => by rw [← hχmul, _root_.one_mul]
  have hε0 : ε ≠ 0 := by
    intro h0
    have hF0 : F = 0 := by
      apply hψinj
      have : ψ (Φ 1) = 0 := by
        have h0' : (n : Kd d)⁻¹ • ψ (Φ 1) = 0 := h0
        exact (smul_eq_zero.mp h0').resolve_left (inv_ne_zero hnk)
      rw [hΦ1] at this; rw [this, map_zero]
    have h1 : cmp i' (cmp h' (cmp i' h')) = 0 := by
      rw [show cmp h' (cmp i' h') = cmp F h' from (cmp_assoc _ _ _).symm, hF0, cmp_zero_left,
        cmp_zero_right]
    rw [hih'', hih', natCast_eq_nsmul, smul_smul] at h1
    exact one_ne_zero_of_dim hdimE' (eq_zero_of_nsmul (Nat.mul_pos hn hn) h1)
  have hε1 : ε ≠ 1 := by
    intro h1
    have hψF : ψ F = ψ (n : PkgI3.AbVar.End A') := by
      have h1' : (n : Kd d)⁻¹ • ψ (Φ 1) = 1 := h1
      rw [hΦ1] at h1'
      rw [map_natCast]
      calc ψ F = (n : Kd d) • ((n : Kd d)⁻¹ • ψ F) := by rw [smul_smul, mul_inv_cancel₀ hnk, one_smul]
        _ = (n : Kd d) • 1 := by rw [h1']
        _ = (n : Matrix (Fin 2) (Fin 2) (Kd d)) := by rw [Nat.cast_smul_eq_nsmul, nsmul_one]
    have hF : cmp h' i' = (n : PkgI3.AbVar.End A') := hψinj hψF
    exact reverse_split_impossible hHF τ hdimE' hd e hn hF
  obtain ⟨htr, hcor⟩ := idem_two ε hεε hε0 hε1
  -- the corner map `κ`
  have hχ : ∀ g, χ g = Matrix.trace (χ g) • ε := by
    intro g
    have := hcor (χ g)
    rw [hεχ, hχε] at this
    exact this
  let κ : PkgI3.AbVar.End E' →+* Kd d :=
    { toFun := fun g => Matrix.trace (χ g)
      map_one' := htr
      map_mul' := fun g g' => by
        show Matrix.trace (χ (g * g')) = Matrix.trace (χ g) * Matrix.trace (χ g')
        rw [hχmul]
        conv_lhs => rw [hχ g, hχ g']
        rw [smul_mul_smul_comm, hεε, Matrix.trace_smul, htr, smul_eq_mul, _root_.mul_one]
      map_zero' := by
        show Matrix.trace (χ 0) = 0
        have : Φ 0 = 0 := by simp only [Φ, cmp_zero_right, cmp_zero_left]
        simp only [χ, this, map_zero, smul_zero, Matrix.trace_zero]
      map_add' := fun g g' => by
        show Matrix.trace (χ (g + g')) = Matrix.trace (χ g) + Matrix.trace (χ g')
        rw [hχadd, Matrix.trace_add] }
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have hχ0 : χ g = 0 := by
      rw [hχ g]; exact (smul_eq_zero.mpr (Or.inl hg))
    have hΦ0 : Φ g = 0 := by
      apply hψinj
      rw [map_zero]
      exact (smul_eq_zero.mp hχ0).resolve_left (inv_ne_zero hnk)
    have h1 : cmp i' (cmp (Φ g) h') = 0 := by rw [hΦ0, cmp_zero_left, cmp_zero_right]
    rw [hΦ, cmp_assoc, cmp_assoc, hih'', hih', cmp_natCast_right, smul_smul] at h1
    exact eq_zero_of_nsmul (Nat.mul_pos hn hn) h1
  -- an irrational element
  let r : Kd d := AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d)
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A') 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A') (S := ℚ))
  obtain ⟨⟨x, s0⟩, hxs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) tm (e.symm (Matrix.scalar (Fin 2) r))
  have hs0 : (s0 : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s0
  have hψx : ψ x = ((s0 : ℤ) : Kd d) • Matrix.scalar (Fin 2) r := by
    rw [Submonoid.smul_def] at hxs
    show e ((1 : ℚ) ⊗ₜ[ℤ] x) = _
    rw [show (1 : ℚ) ⊗ₜ[ℤ] x = tm x from rfl, ← hxs, map_zsmul, e.apply_symm_apply, Int.cast_smul_eq_zsmul]
  let g₀ : PkgI3.AbVar.End E' := cmp (cmp i' x) h'
  have hΦg₀ : Φ g₀ = F * (x * F) := by
    simp only [Φ, g₀, F, mul_eq_cmp, cmp_assoc]
  have hψF2 : ψ F * ψ F = (n : Kd d) • ψ F := by
    rw [← map_mul, show F * F = Φ 1 * Φ 1 by rw [hΦ1], hΦmul, _root_.mul_one, hΦ1, map_mul, map_natCast,
      ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  have hκg₀ : κ g₀ = ((s0 : ℤ) : Kd d) * n * r := by
    show Matrix.trace ((n : Kd d)⁻¹ • ψ (Φ g₀)) = _
    have htrF : Matrix.trace (ψ F) = n := by
      have h3 := htr
      simp only [ε, χ, hΦ1, Matrix.trace_smul, smul_eq_mul] at h3
      field_simp at h3
      exact h3
    rw [hΦg₀, map_mul, map_mul, hψx, Matrix.smul_mul, Matrix.mul_smul, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, hψF2]
    simp only [Matrix.trace_smul, smul_eq_mul, htrF]
    field_simp
  have hθ : κ g₀ ∉ Set.range (algebraMap ℚ (Kd d)) := by
    rintro ⟨q, hq⟩
    apply root_not_rat hd
    have hsn : (((s0 : ℤ) : Kd d) * n) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hs0) hnk
    refine ⟨q / ((s0 : ℤ) * n : ℚ), ?_⟩
    refine (eq_ratCast _ _).trans ?_
    have hq' : ((q : ℚ) : Kd d) = κ g₀ := (eq_ratCast _ q).symm.trans hq
    push_cast
    rw [hq', hκg₀]
    field_simp
    rfl
  -- integrality: T6 on `E_Ω`, with an embedding `Ω → ℂ`
  haveI : Module.Finite ℤ (PkgI3.AbVar.End E') := (hHF Ω τ E' E').2.1
  let R : Subring (Kd d) := κ.range
  have hRO : R ≤ (integralClosure ℤ (Kd d)).toSubring := by
    rintro _ ⟨g, rfl⟩
    have hg : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    exact hg.map κ.toIntAlgHom
  have hR : IsImagQuadOrder (Kd d) R :=
    ⟨isTotallyComplex_kd hd, finrank_kd hd, hRO,
      conductor_ne_zero_of_mem (finrank_kd hd) R hRO ⟨g₀, rfl⟩ hθ⟩
  -- `End(E_{L̄}) ≅ End(E_Ω) ≅ R`
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃ₐ[L] AlgebraicClosure L := IsAlgClosure.equiv L Ω (AlgebraicClosure L)
  refine ⟨Kd d, inferInstance, inferInstance, R, hR, ⟨?_⟩⟩
  exact (trEquiv (X := (E : PkgI3.AbVar L)) (σ := σ)).symm.trans
    (RingEquiv.ofBijective κ.rangeRestrict
      ⟨fun a b hab => hκinj (congrArg Subtype.val hab), κ.rangeRestrict_surjective⟩)


/-- Recover the current consumer's surface specialization from the exact original statement. -/
theorem cmCurveOrder_of_324 (h : CMCurveOrder324) : CMCurveOrder :=
  fun L _ _ A _ Ω _ _ _ _ d => h L A Ω d

/-- The original order theorem closes `CMFibreSplit` using only inputs already in the
CM proof chain. The consumer's statement is unchanged. -/
theorem cmFibreSplit_of_curveOrder324 (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplit :=
  cmFibreSplit_of_curveOrder hYu hHF hCover hNOS hRay hTors (cmCurveOrder_of_324 (cmCurveOrder324_of hHF))

end HDec.CMBranch.FibreSplit
