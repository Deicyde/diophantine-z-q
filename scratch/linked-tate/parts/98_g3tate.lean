/-! ## linked-tate: `GoodRedG3Bridge` reduced to its torsion-point form `GoodRedTorsion`

`G3Out` asks that inertia act trivially on `ℚ̄_ℓ ⊗ V_ℓ`. Triviality on every `A[ℓⁿ](K̄)` implies
it, because `T_ℓ(A)` consists of compatible sequences of `ℓⁿ`-torsion points
(`tate_eq_one_of_torsion`, proved). What remains of G3's transport is the statement at the level
of points, where NOS itself speaks (`PkgI2.InertiaTrivialOn`). -/

section LinkedTateG3Sec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Inertia acting trivially on all `ℓ`-power torsion acts trivially on `ℚ̄_ℓ ⊗ V_ℓ`**
(proved): each coordinate `xₙ` of `x ∈ T_ℓ(A)` is `ℓⁿ`-torsion. -/
theorem tate_eq_one_of_torsion {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 → A.galAct σ x = x) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hx' : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    show Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hx']; rfl
  have hR : A.galRep ℓ σ = 1 := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, Module.End.one_eq_id, LinearMap.baseChange_id]

/-- **Glue: good reduction away from `3` makes inertia trivial on torsion points of the base
change** (linked-tate; the point-level transport half of G3, given the leaf R7a). Same hypotheses
as `GoodRedG3Bridge`. Conclusion: for `p ∉ {3}`, `p ≠ ℓ`, and an element `σ'` of `G_{L'}` whose
image `resQ σ'` lies in the inertia group of a place `v` of `ℚ̄` above `p`, `σ'` fixes every
`ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`. Route (STANDARD): `v ∩ K` is a DVR of `K` with `3` a
unit; NOS (a) ⇒ (b) over `K` (PkgI2's `InertiaTrivialOn` on `A(K̄)[ℓⁿ]` at a valuation ring of
`K̄` over `v ∩ K`); transport along `\bar{L'} ≅ K̄` over `K` (`resQ`'s embedding `ℚ̄ → \bar{L'}`) and
`A_{L,L'}(\bar{L'}) = A(\bar{L'})` (unram-tate's `bcPt`). GLUE (definitions only; no new
literature). -/
def GoodRedTorsion : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ ({3} : Finset ℕ) → p ≠ ℓ →
        ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        ∀ σ' : Field.absoluteGaloisGroup L',
          (∃ σ ∈ v.inertiaSubgroup ℚ,
            ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = G0Galois.resQ L' σ') →
          ∀ (n : ℕ) (x : (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).Pt
              (AlgebraicClosure L')),
            x ^ (ℓ ^ n) = 1 →
            (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct σ' x = x

/-- **`GoodRedG3Bridge`, proved** from `GoodRedTorsion` (`tate_eq_one_of_torsion`). -/
theorem goodRedG3Bridge_of_torsion (h : GoodRedTorsion) : GoodRedG3Bridge := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact tate_eq_one_of_torsion _ ℓ σ' (h hNOS K L L' hKL hLL' A hA ℓ p hp hpT hpl v hv σ' hσ)

end HSyn.LinkedTate

end

end LinkedTateG3Sec

#print axioms HSyn.LinkedTate.tate_eq_one_of_torsion
#print axioms HSyn.LinkedTate.goodRedG3Bridge_of_torsion
