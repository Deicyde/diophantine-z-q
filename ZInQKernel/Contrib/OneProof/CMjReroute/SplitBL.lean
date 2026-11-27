import ZInQKernel.Contrib.OneProof.CMjReroute.Descent

/-!
# The CM fibre split with the class-number bound of a sub-order

`CMBranch.CMFibreSplit` (A8 for a CM fibre and the matrix units; manuscript L520-562, L581-586) gives, at
a fibre over `J(u)` carrying a CM point, a model `A/L` of the fibre surface with `[L:ℚ] ≤ D`, the curve
`E/L` cut out by a multiple of a matrix unit of `End⁰(A) = M₂(k)`, `E² → A`, and the geometric
endomorphism order `R ⊆ k` of `E`. `CMFibreSplitBL` adds an order `R₀ ≤ R` of `k` with
`card Pic(R₀) ≤ 324`: the image in `End(E)` of the order `q⁻¹(𝒪)` of the CM point, whose ring class field
has degree at most the number of points of a fibre of `Y₃ → P¹_j` (Shimura's reciprocity law at CM
points, Deligne, Sém. Bourbaki 389, §5; the fibre bound of the manuscript's map `Y₃ → P¹_j`,
diophantine_zq.tex L420-440). This is the input `faltingsHeight_le_bcm_of_sub` needs in place of
the degree of the singular modulus `j(E)`.

* `CMMatrixUnitSplitBL`, `cmMatrixUnitSplitBL_of`: `FibreSplit.cmMatrixUnitSplit_of` with
  `matrixUnit_restrict` in place of `FibreSplit.matrixUnit_isogeny`, so that the injective
  restriction `ρ : Z(End A) → End E` of central endomorphisms is part of the conclusion;
* `CMFibreSplitBL`, `cmFibreSplitBL_of`: `FibreSplit.cmFibreSplit_of` re-run with the fibre point `y`,
  the QM surface `P`, the non-integral `φ ∈ End_𝒪(P)` (from the failure of `NoCMAt`), the model
  `(A, θ, θ')` and the curve data `(E, ρ, k, R)` kept, followed by `exists_suborder_card_pic_le_324` at
  the rational value `J(u)`;
* `cmFibreSplit_of_bl`: `CMFibreSplitBL` implies `CMFibreSplit`.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HDec.CMBranch HDec.CMBranch.FibreSplit
open HSyn HSyn.G0Split
open _root_.CMBranch
open scoped TensorProduct

/-- **The matrix units with the restriction of central endomorphisms** (manuscript L582-586).
`FibreSplit.CMMatrixUnitSplit` with, in addition, an injective ring homomorphism from the centre of
`End(A)` to `End(E)`: central endomorphisms of `A` commute with the matrix unit that cuts out `E`, so
they restrict to `E`. -/
def CMMatrixUnitSplitBL : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L), A.dim = 2 →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω],
      Function.Surjective (G0ModField.KernelField.endBC A Ω) →
      ∀ d : ℚ, d < 0 →
        Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
        ∃ (E Pr : ZInQ.DefFaltings.AbVar L) (k : Type) (_ : Field k) (_ : NumberField k)
          (R : Subring k),
          E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧
          (∃ φ : Pr.X ⟶ ((LeafAdopt.abVarEquiv L).symm A).X, IsIsogeny φ) ∧
          IsImagQuadOrder k R ∧ IsCMBy E k R ∧
          ∃ ρ : Subring.center (PkgI3.AbVar.End A) →+*
              PkgI3.AbVar.End (LeafAdopt.abVarEquiv L E), Function.Injective ρ

/-- **`CMMatrixUnitSplitBL` from `CMCurveOrder`**: the proof of `FibreSplit.cmMatrixUnitSplit_of`, with
`matrixUnit_restrict` (which also returns the restriction `ρ`) in place of `matrixUnit_isogeny`. -/
theorem cmMatrixUnitSplitBL_of (hCO : CMCurveOrder) : CMMatrixUnitSplitBL := by
  intro L _ _ A hA Ω _ _ _ _ hsurj d hd ⟨e⟩
  let β := RingEquiv.ofBijective (G0ModField.KernelField.endBC A Ω)
    ⟨G0ModField.KernelField.endBC_injective A Ω, hsurj⟩
  let e' : PkgI3.AbVar.End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl β.toIntAlgEquiv).trans e
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs
    have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hsurjs := (_root_.ZInQ.Contrib.AbVarBC.mulIsogeny L A (s : ℤ) hs0).2
    apply cancel_surj ((s : ℤ) : PkgI3.AbVar.End A) hsurjs
    rw [cmp_intCast_left, hs, cmp_zero_right]
  obtain ⟨n, hn, f, hf⟩ := exists_scaledMatrixUnits e' hinj
  obtain ⟨E, i, h, Pr, ρ, hρ, -, -, hih, -, hE1, hPr, hprod, φ, hφ⟩ :=
    matrixUnit_restrict A hA n hn f hf
  obtain ⟨k, i1, i2, R, hR, hcm⟩ := hCO L A hA Ω d hd ⟨e⟩ E hE1 i h n hn hih
  exact ⟨E, Pr, k, i1, i2, R, hE1, hPr, hprod, ⟨φ, hφ⟩, hR, hcm, ρ, hρ⟩

/-- **The CM fibre split with the class-number bound of a sub-order** (manuscript L520-562, L581-586,
with the bound `card Pic ≤ 324` in place of the degree of `j(E)`, L586-587). `CMFibreSplit` with, in
addition, an order `R₀ ≤ R` of `k` with at most `324` proper ideal classes. -/
def CMFibreSplitBL : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → ¬ NoCMAt Y Φ π u →
    ∃ (L : GlueAssembly.NF) (A E Pr : ZInQ.DefFaltings.AbVar L.K) (k : Type) (_ : Field k)
      (_ : NumberField k) (R : Subring k),
      FibreOver Y Φ π u L A ∧ Module.finrank ℚ L.K ≤ heightD ∧ E.dim = 1 ∧
      Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧ (∃ φ : Pr.X ⟶ A.X, IsIsogeny φ) ∧
      IsImagQuadOrder k R ∧ IsCMBy E k R ∧
      ∃ R₀ : Subring k, R₀ ≤ R ∧ IsImagQuadOrder k R₀ ∧ Nat.card (CommRing.Pic R₀) ≤ 324

/-- **`CMFibreSplitBL` from A8's Hom field and the matrix units**, with the three moduli rows that the CM
branch already reads (`Y3FullThreeRepZ30`, `DeligneCanonicalModelY3EveryPrint`, `Y3ToP1j`). The proof
of `FibreSplit.cmFibreSplit_of`, keeping the data that `exists_suborder_card_pic_le_324` needs: the
point `y` over `J(u)`, `P` with `Φ(y) = [P]`, the non-integral `φ ∈ End_𝒪(P)`, the model `A/L` with
`θ : A_ℚ̄ ≅ P.A` and every geometric endomorphism defined over `L`, the curve `E`, the restriction
`ρ` and `End(E_{L̄}) ≅ R`. -/
theorem cmFibreSplitBL_of (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hA8 : CMHomFieldModel) (hMU : CMMatrixUnitSplitBL)
    (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDel : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hY3j : _root_.Y3P1j.Y3ToP1j) :
    CMFibreSplitBL := by
  intro Y Φ π hR1 hR2 u hu hCM
  simp only [NoCMAt, not_forall, not_exists] at hCM
  obtain ⟨y, P, hP, hπ, φ, hφ, hne⟩ := hCM
  obtain ⟨L, hfin, hdeg, A, θ, θ', h1, h2, hsurj⟩ := hA8 Y Φ π u P ⟨hR1, hR2, hu, y, hP, hπ⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := end0Matrix_of_noncentral hYu hHF P φ hφ hne
  let instL : NumberField L := G0ModField.numberField_of_fd L
  have hiso : letI : Algebra L LeafQM.AV.Qbar := (algebraMap L LeafQM.AV.Qbar).toAlgebra;
      Nonempty ((((LeafAdopt.abVarEquiv L).symm A).baseChange LeafQM.AV.Qbar).X ≅ P.A.X) :=
    ⟨⟨θ.hom, θ'.hom, h1, h2⟩⟩
  have hA2 : A.dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L LeafQM.AV.Qbar)
      ((LeafAdopt.abVarEquiv L).symm A) P.A hiso P.surface
  have : Algebra.IsAlgebraic L LeafQM.AV.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨E, Pr, k, i1, i2, R, hE, hPr, hprod, hisog, hR, ⟨eR⟩, ρ, hρ⟩ :=
    hMU L A hA2 LeafQM.AV.Qbar hsurj d hd ⟨(end0EquivOfIso θ θ' h1 h2).trans e⟩
  obtain ⟨R₀, hle, hR₀, hpic⟩ := exists_suborder_card_pic_le_324 hModel hDel hY3j hR1 hR2
    (Jmap u) y hπ P hP hφ hne A θ θ' h1 h2 hsurj ρ hρ R hR eR
  exact ⟨⟨L⟩, (LeafAdopt.abVarEquiv L).symm A, E, Pr, k, i1, i2, R,
    ⟨algebraMap L LeafQM.AV.Qbar, y, P, hP, hπ, hiso⟩, hdeg, hE, hPr, hprod, hisog, hR, ⟨eR⟩,
    R₀, hle, hR₀, hpic⟩

/-- `CMFibreSplitBL` implies `CMFibreSplit` (forget the sub-order). -/
theorem cmFibreSplit_of_bl (h : CMFibreSplitBL) : CMFibreSplit := by
  intro Y Φ π h1 h2 u hu hCM
  obtain ⟨L, A, E, Pr, k, i1, i2, R, hFib, hd, hE1, hPr, hprod, hiso, hR, hCMR, -⟩ :=
    h Y Φ π h1 h2 u hu hCM
  exact ⟨L, A, E, Pr, k, i1, i2, R, hFib, hd, hE1, hPr, hprod, hiso, hR, hCMR⟩

end HDec.CMBranch.CMjReroute
