import ZInQKernel.Contrib.OneProof.DegEqDetTate.KerDvd

/-!
# deg-det: `DegEqDetTate` (Mumford §19 Thm 4, `deg ψ = det T_ℓ ψ`) from the polynomiality of the degree

Task deg-det (2026-11-16), report `docs/research/deg-det.md`, scratch `scratch/deg-det/`.

charpoly-ell reduced the open field `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` to the printed leaf
`CharPolyEll.DegEqDetTate` and the open field `HomFreeFiniteAlgClosed`. This file proves `DegEqDetTate` from
one new printed leaf and two open fields of the same bundle:

* `DegHomogPoly` (**LEAF**, printed form; `DegEqDetTate/Reduction.lean`): `deg` is a homogeneous polynomial
  function of degree `2g` on `End(A)` (Mumford §19);
* `AvSplit.MumfordTorsionAlgClosed` (open field): `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n`;
* `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (open field): only `End(A)` finite over `ℤ` is used.

Everything else is proved: the algebra of Mumford's proof (`DegEqDetTate/Algebra.lean`, one-sided form
`det_eq_deg_abstract_le`), `deg(ψχ) = deg ψ · deg χ` (`Reduction.lean`), `|det T_ℓ ψ|_ℓ = |#ker ψ|_ℓ`
(`TateIndex.lean`), `#ker ψ ∣ deg ψ` (`KerDvd.lean`), and `rank V_ℓ = 2g`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct

noncomputable section

namespace ZInQ.Contrib.OneProof.DegDet

open ZInQ.Contrib.OneProof.CharPolyEll

section Final

variable {k : Type} [Field k]

/-- `#A(k̄)[ℓⁿ] = ℓ^{2gn}` from `mumfordTorsionAlgClosed` (as in t5-torsion's `tateModuleFree_at`). -/
theorem card_tb_of_mumford (hM : AvSplit.MumfordTorsionAlgClosed) (A : PkgI3.AbVar k) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (n : ℕ) :
    Nat.card (T5Torsion.TateFree.tb ℓ (Additive (A.Pt (AlgebraicClosure k))) n) =
      ℓ ^ (n * (2 * g)) := by
  have hT := AvSplit.torsionStructure_of_mumford hM k
  obtain ⟨e', -⟩ := hT (ObjBridge.toGrp A) g (ℓ ^ n) hg
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by push_cast; exact pow_ne_zero _ hℓ)
  rw [← Nat.card_congr (T5Torsion.TateFree.torsionEquivTb A ℓ n), Nat.card_congr e', Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

/-- `|det V_ℓ(χ)|_ℓ = |#ker χ(k̄)|_ℓ` when the kernel is finite. -/
theorem norm_det_V_eq_card_ker (hM : AvSplit.MumfordTorsionAlgClosed) (A : PkgI3.AbVar k)
    (χ : PkgI3.AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) {I : Type} [Fintype I]
    [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ))
    (hfin : Finite (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) χ).ker) :
    ‖(LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) χ).baseChange ℚ_[ℓ])).det‖ =
      ‖((Nat.card (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) χ).ker : ℕ) : ℚ_[ℓ])‖ := by
  classical
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  have hcard := card_tb_of_mumford hM A ℓ hℓ g hg
  set φ : Additive (A.Pt (AlgebraicClosure k)) →+ Additive (A.Pt (AlgebraicClosure k)) :=
    MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) χ) with hφ
  let eK : φ.ker ≃ (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) χ).ker :=
    { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite φ.ker := Finite.of_equiv _ eK.symm
  have key := TateIndex.norm_det_map_eq (2 * g) hcard φ
  haveI : Module.Free ℤ_[ℓ] (A.T ℓ) :=
    Module.Free.of_equiv (T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard).some.symm
  haveI : Module.Finite ℤ_[ℓ] (A.T ℓ) :=
    Module.Finite.equiv (T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard).some.symm
  rw [LinearMap.det_toMatrix b, LinearMap.det_baseChange]
  change ‖((LinearMap.det (PkgI3.AbVar.homT (ℓ := ℓ) χ) : ℤ_[ℓ]) : ℚ_[ℓ])‖ = _
  rw [← PadicInt.norm_def]
  change ‖LinearMap.det (PkgI3.Tate.map φ)‖ = _
  rw [key, Nat.card_congr eK, PadicInt.norm_def, PadicInt.coe_natCast]

/-- `rank V_ℓ(A) = 2g`. -/
theorem card_basis_V (hM : AvSplit.MumfordTorsionAlgClosed) (A : PkgI3.AbVar k) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) {I : Type} [Fintype I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) : Fintype.card I = 2 * g := by
  have hcard := card_tb_of_mumford hM A ℓ hℓ g hg
  obtain ⟨E⟩ := T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard
  haveI : Module.Free ℤ_[ℓ] (A.T ℓ) := Module.Free.of_equiv E.symm
  haveI : Module.Finite ℤ_[ℓ] (A.T ℓ) := Module.Finite.equiv E.symm
  rw [← Module.finrank_eq_card_basis b]
  change Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] A.T ℓ) = _
  rw [Module.finrank_baseChange, E.finrank_eq, Module.finrank_fin_fun]

/-- `|deg χ|_ℓ ≤ |det V_ℓ χ|_ℓ` when `deg χ ≠ 0` (from `#ker χ ∣ deg χ`). -/
theorem norm_deg_le_norm_det (hM : AvSplit.MumfordTorsionAlgClosed) [IsAlgClosed k]
    (A : PkgI3.AbVar k) (χ : PkgI3.AbVar.End A) (hχ : degEnd χ ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    ‖(degEnd χ : ℚ_[ℓ])‖ ≤
      ‖(LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) χ).baseChange ℚ_[ℓ])).det‖ := by
  obtain ⟨hfin, c, hc⟩ := KerDvd.kerDvdDeg χ hχ
  rw [norm_det_V_eq_card_ker hM A χ ℓ hℓ b hfin, hc, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Padic.norm_int_le_one (p := ℓ) (c : ℤ))

/-- **`DegEqDetTate` from `DegHomogPoly`, `mumfordTorsionAlgClosed` and `homFreeFiniteAlgClosed`.** -/
theorem degEqDetTate_of_degHomogPoly_mumford (hP : DegHomogPoly)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    DegEqDetTate := by
  intro k _ _ A ψ ℓ _ hℓ I _ _ b
  classical
  obtain ⟨-, hfin, -, -⟩ := hH k A A
  obtain ⟨R, hR, hRψ⟩ := IsIntegral.of_finite ℤ ψ
  obtain ⟨g, N, hg, hN, hpoly⟩ := hP k A R.natDegree (fun i => ψ ^ (i : ℕ))
  rw [← rho_apply b ψ]
  refine det_eq_deg_abstract_le ψ degEnd R hR (by rw [aeval_def]; exact hRψ) (2 * g) N hN hpoly
    (degEnd_one A) (fun χ φ hχ hφ => degEnd_mul_of_isIsogeny χ φ
      (isIsogenyMor_of_degEnd_ne_zero hχ) (isIsogenyMor_of_degEnd_ne_zero hφ)) (rho b)
    (card_basis_V hM A ℓ hℓ g hg b) ?_
  intro χ hχ
  rw [rho_apply]
  exact norm_deg_le_norm_det hM A χ hχ ℓ hℓ b

/-- **`CharPolyIndepOfEllAlgClosed` from the printed leaf `DegHomogPoly` and the open fields
`mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`** (with charpoly-ell's
`charPolyIndepOfEllAlgClosed_of_degEqDetTate`). -/
theorem charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford (hP : DegHomogPoly)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  charPolyIndepOfEllAlgClosed_of_degEqDetTate (degEqDetTate_of_degHomogPoly_mumford hP hM hH) hH

end Final

end ZInQ.Contrib.OneProof.DegDet
