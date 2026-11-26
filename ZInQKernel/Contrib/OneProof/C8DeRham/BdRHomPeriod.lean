import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRCoefficients
import ZInQKernel.Contrib.OneProof.C8DeRham.HomScalarPeriod

/-! # Extracting the B_dR period of the actual twisting character

Both matrix actions and the intertwiner are read over the same finite
coefficient field in the chosen algebraic closure. The ratio of the period
matrices supplies a nonzero B_dR period. Generating the two period matrices
from the modular and r-side de Rham inputs is a separate obligation.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]

/-- The period row condition for the actual coefficient action on `E^n`. -/
def HasBdRRows {n : ℕ} (r : GQp p →* GL (Fin n) E) : Prop :=
  ∃ A : GL (Fin n) (BdR p), ∀ σ ∈ E.fixingSubgroup,
    Matrix.GeneralLinearGroup.map (bdrAct p σ) A =
      A * Matrix.GeneralLinearGroup.map (coeffToBdR p E).toRingHom (r σ)

set_option maxHeartbeats 1300000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- The actual intertwiner yields a nonzero period for the scalar character
on the fixing subgroup of its coefficients. This does not assume an unrelated
line in another period ring or any statement about its weight. -/
theorem exists_bdr_period_of_hom_line {n : ℕ} (hn : 0 < n)
    (r ρ : GQp p →* GL (Fin n) E) (χ : GQp p →* Eˣ) (T : GL (Fin n) E)
    (htw : ∀ σ, (r σ : Matrix (Fin n) (Fin n) E) * (T : Matrix (Fin n) (Fin n) E) =
      (χ σ : E) • ((T : Matrix (Fin n) (Fin n) E) * (ρ σ : Matrix (Fin n) (Fin n) E)))
    (hr : HasBdRRows p E r) (hρ : HasBdRRows p E ρ) :
    ∃ b : BdR p, b ≠ 0 ∧ ∀ σ ∈ E.fixingSubgroup,
      bdrAct p σ b = coeffToBdR p E (χ σ : E) * b := by
  letI : Field (BdR p) := DeRhamPrint.bdrField p
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨Ar, hAr⟩ := hr
  obtain ⟨Ag, hAg⟩ := hρ
  let f := (coeffToBdR p E).toRingHom
  let mapGL : GL (Fin n) E →* GL (Fin n) (BdR p) := Matrix.GeneralLinearGroup.map f
  let ψ : E.fixingSubgroup → (BdR p)ˣ := fun σ => Units.map f.toMonoidHom (χ σ.1)
  have hfix (σ : E.fixingSubgroup) :
      Matrix.GeneralLinearGroup.map (bdrAct p σ.1) (mapGL T) = mapGL T := by
    apply Units.ext
    ext i j
    simp only [mapGL, Matrix.GeneralLinearGroup.map_apply]
    exact bdrAct_coeffToBdR p E σ.1 σ.2 ((T : Matrix (Fin n) (Fin n) E) i j)
  have hT (σ : E.fixingSubgroup) : mapGL (r σ.1) * mapGL T =
      Units.map (Matrix.scalar (Fin n) : BdR p →+* Matrix (Fin n) (Fin n) (BdR p)).toMonoidHom (ψ σ) *
        (mapGL T * mapGL (ρ σ.1)) := by
    apply Units.ext
    let MT := (mapGL T : Matrix (Fin n) (Fin n) (BdR p))
    let Mr := (mapGL (r σ.1) : Matrix (Fin n) (Fin n) (BdR p))
    let Mρ := (mapGL (ρ σ.1) : Matrix (Fin n) (Fin n) (BdR p))
    change Mr * MT = Matrix.scalar (Fin n) (f (χ σ.1 : E)) * (MT * Mρ)
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map f) (htw σ.1)
    rw [Matrix.map_mul] at he
    ext i j
    have hj := congrFun (congrFun he i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.mul_apply, map_sum] at hj ⊢
    simpa only [Mr, MT, Mρ, mapGL, Matrix.GeneralLinearGroup.map_apply, Matrix.mul_apply] using hj
  obtain ⟨b, hb, hgb⟩ := exists_hom_scalar_period (G := E.fixingSubgroup)
    (fun σ => bdrAct p σ.1) (fun σ => mapGL (r σ.1)) (fun σ => mapGL (ρ σ.1)) ψ Ar Ag (mapGL T)
    (fun σ => hAr σ.1 σ.2) (fun σ => hAg σ.1 σ.2) hfix hT
  exact ⟨b, hb, fun σ hσ => hgb ⟨σ, hσ⟩⟩

end HDec.G0Galois.C8Conrad.Manuscript
