import ZInQKernel.OneProof.H.TailK

/-!
# The `ℓ`-adic Weil pairing on `V_ℓ(A)` over fields of characteristic `0`, from the characteristic-`0` T9

Task fold34-ht (2026-11-16). `HodgeTatePairingWeil.lean` (hodgetate-from-dr) verbatim, with T9 in its
characteristic-`0` form: `h9` has the type of `PicZeroChar0.T09_SymmIsogenyExists0` (written out, so that this
module imports only `TailK`; the linear algebra times out in later environments), and each statement gains
`[CharZero K]`. `h9` is applied only at the field `K` of the statement.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateFromPairing

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj in
/-- `TatePairingZl` over any field in which `ℓ` is invertible (the proof of
`HDec.HSyn.tatePairingZl_of_leaves4`, verbatim). -/
theorem tatePairingZl_field0 (h9 : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K),
      Nonempty (HDec.WeilPairing.SymmIsogeny A))
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) (hT5 : HDec.PkgI2.TorsionStructure.{0})
    (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y := by
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨g, hg⟩ := HDec.WeilPairing.exists_tmu_gen K ℓ
  refine ⟨(HDec.WeilPairing.tatePairing S.D S.lam (NeZero.ne _)).compr₂
    (HDec.WeilPairing.tmuCoordLin hg), ?_, ?_, ?_⟩
  · intro x hx
    exact HDec.WeilPairing.tatePairing_left_ker S.D S.lam hd hψ (NeZero.ne _)
      (fun k t ht => _root_.T5Torsion.TateFree.tate_surj_of_torsionStructure
        (HDec.HSyn.torsionStructureK_of4 hT5) K (HDec.HSyn.toAbVarK4 A) ℓ (NeZero.ne _) k t ht) x
      fun y => HDec.WeilPairing.tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro x
    simp only [LinearMap.compr₂_apply]
    rw [HDec.WeilPairing.tatePairing_self S.D S.lam S.symm (NeZero.ne _) x, map_zero]
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    have h := congrArg (HDec.WeilPairing.tmuCoordLin hg)
      (HDec.WeilPairing.tatePairing_cyclotomic S.D S.lam σ x y)
    rw [map_smul, smul_eq_mul] at h
    exact h

open CategoryTheory MonObj in
/-- **The `ℓ`-adic Weil pairing on `V_ℓ(A)`** over any field `K` with `(ℓ : K) ≠ 0` (the proof of
`HDec.G0Galois.tateGSp_of_zl`, verbatim, from `tatePairingZl_field` and T26 = `tateModuleFree_of_t5'`):
`V_ℓ(A)` has dimension `2 dim A` and carries a nondegenerate alternating form with multiplier the
cyclotomic character of `G_K`. -/
theorem tateGSp_field0 (h9 : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K),
      Nonempty (HDec.WeilPairing.SymmIsogeny A))
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) (hT5 : HDec.PkgI2.TorsionStructure.{0})
    (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]
    (g : ℕ) (hdim : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) :
            ℚ_[ℓ]) * B x y := by
  classical
  obtain ⟨B0, hsep, halt0, hmult⟩ := tatePairingZl_field0 h9 hQ hT5 K A ℓ
  have hℓ : (ℓ : K) ≠ 0 := NeZero.ne _
  obtain ⟨hfree, hfin, hrk⟩ := HDec.HSyn.tateModuleFree_of_t5' hT5 K A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * g := by
    rw [hdim] at hrk
    have h3 : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact_mod_cast WithBot.coe_injective h3
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hnd0 : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have hdet0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd0
  set G := LinearMap.BilinForm.toMatrix b B0 with hG
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  haveI : IsDomain ℚ_[ℓ] := Field.isDomain
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  set G' := G.map φ with hG'
  let B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) := Matrix.toBilin bV G'
  have hBG : LinearMap.BilinForm.toMatrix bV B = G' := LinearMap.BilinForm.toMatrix_toBilin _ _
  have : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis bV
  refine ⟨inferInstance, B, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrank]
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hBG, hG', show G.map φ = φ.mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hdet0 (hφ (by rw [h, map_zero]))
  · have hskew : ∀ i j, G' j i = - G' i j := by
      intro i j
      simp only [hG', hG, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
      rw [HDec.G0Galois.skew_of_alt' B0 halt0, map_neg]
    intro x
    have hsum : B x x = ∑ i, ∑ j, bV.repr x i * G' i j * bV.repr x j := Matrix.toBilin_apply bV G' x x
    have hsum' : B x x = - B x x := by
      conv_rhs => rw [hsum, Finset.sum_comm]
      rw [hsum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hskew j i]
      ring
    have h2 : (2 : ℚ_[ℓ]) * B x x = 0 := by linear_combination hsum'
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  · intro σ
    set c0 := ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
    have hc0 : B0.comp (A.galT σ) (A.galT σ) = c0 • B0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      change B0 (A.galT σ x) (A.galT σ y) = c0 * B0 x y
      rw [hmult σ x y]
    set M := LinearMap.toMatrix b b (A.galT σ) with hM
    have h1 := LinearMap.BilinForm.toMatrix_comp b b B0 (A.galT σ) (A.galT σ)
    rw [hc0, map_smul] at h1
    have hfM : LinearMap.toMatrix bV bV (A.galRep ℓ σ) = M.map φ :=
      LinearMap.toMatrix_baseChange ℚ_[ℓ] (A.galT σ) b b
    have hcomp : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = (φ c0) • B := by
      apply (LinearMap.BilinForm.toMatrix bV).injective
      rw [LinearMap.BilinForm.toMatrix_comp bV bV, hfM, hBG, map_smul, hBG, hG']
      have h2 := congrArg (fun X => X.map φ) h1
      simp only [Matrix.map_mul, Matrix.transpose_map] at h2
      rw [← hG] at h2
      exact h2.symm
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hcomp
    simpa [φ] using this

end ZInQ.Contrib.HodgeTateFromPairing
