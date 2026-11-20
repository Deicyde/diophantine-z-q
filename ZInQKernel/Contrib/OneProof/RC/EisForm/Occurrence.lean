import ZInQKernel.Contrib.OneProof.RC.O12EisConst.Branch

/-! Labeled occurrence, conditional on a block decomposition at a fixed stage
and fixed U (tex 9647–9654, 9754–9771). Recovery of the scale from the first
possible positive coefficient and descent to the common field are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisForm

open AddressGenuine O12 O12EisConst O12Eisenstein UpperHalfPlane TauCeti PrintsArith
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {D : Type} [Field D] {p : ℕ} [Fact p.Prime]
variable {E : CharacterPair D p} {c : D →+* ℂ}

/-- The first possible positive coefficient of the normalized old vector is
at its degeneracy degree, and is one. This pins down its scale even when the
first coefficient at index one vanishes. -/
theorem atLevel_coeff_degree (F : BaseForm E c) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) (s : D) :
    (qExpansion 1 (c s • F.atLevel h)).coeff d = c s := by
  have hn : d ≠ 0 := NeZero.ne d
  simpa [degenerate, Nat.div_self (Nat.pos_of_ne_zero hn), coeff_one] using
    F.atLevel_coeff h s ⟨d, hn⟩

/-- A nonzero column on the labeled complex old line descends to a nonzero
multiple over the common field once its degree coefficient is defined there. -/
theorem scale_of_labeled_line (F : BaseForm E c) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf : f ≠ 0)
    (hline : f ∈ Submodule.span ℂ {F.atLevel h})
    (s : D) (hs : c s = (qExpansion 1 f).coeff d) :
    s ≠ 0 ∧ f = c s • F.atLevel h := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hline
  have h₁ : (qExpansion 1 (F.atLevel h)).coeff d = 1 := by
    simpa using atLevel_coeff_degree F h (1 : D)
  have hsa : c s = a := by
    rw [hs, ← ha]
    change (qExpansion 1 (a • ⇑(F.atLevel h))).coeff d = a
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N)]
    simp [h₁, smul_eq_mul]
  refine ⟨?_, by rw [hsa]; exact ha.symm⟩
  intro hz
  exact hf (by simpa [← hsa, hz] using ha.symm)

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B chiType}
variable {A : FourierData X}

/-- For a labeled nonzero column of a realized block, recover the occurrence
of the normalized old copy in that block and the exact model-column comparison.
The complex line test contains no coefficient identity and specifies no scale. -/
theorem column_of_labeled_line (F : BaseForm E c) (k : D →+* X.K) {d N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ N) (i : X.I)
    (W : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 2))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf : f ≠ 0)
    (hW : f ∈ W) (hline : f ∈ Submodule.span ℂ {F.atLevel h})
    (lift : PosIndex → D)
    (hc : ∀ n, c (lift n) = (qExpansion 1 f).coeff n.val)
    (hk : ∀ n, k (lift n) = X.coefK (column X i 1) (A.index n)) :
    ∃ s : D, s ≠ 0 ∧ f = c s • F.atLevel h ∧ F.atLevel h ∈ W ∧
      Nonempty (ColumnRealization F k h s A i) := by
  let n₀ : PosIndex := ⟨d, NeZero.ne d⟩
  have ⟨hs, hscale⟩ := scale_of_labeled_line F h f hf hline (lift n₀) (hc n₀)
  have hW' := W.smul_mem (c (lift n₀))⁻¹ hW
  rw [hscale, smul_smul, inv_mul_cancel₀ ((map_ne_zero c).mpr hs), one_smul] at hW'
  refine ⟨lift n₀, hs, hscale, hW', ⟨⟨lift, ?_, hk⟩⟩⟩
  intro n
  have hcn := hc n
  rw [hscale] at hcn
  exact hcn

/-- When the label comes from a block with the manuscript's exponent bound,
this occurrence and the attachment give the exact predecessor interface.
Apply this pointwise to its selected labels. -/
theorem realizedCoordinate_of_labeled_line [TopologicalSpace X.K]
    (F : BaseForm E c) (k : D →+* X.K) {d M N : ℕ} [NeZero d]
    (h : d * pairLevel E ∣ M) (hM : ¬ p * p ∣ M) (hN : M ∣ N)
    (i : X.I) (avoid : Finset ℕ)
    (W : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 2))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf : f ≠ 0)
    (hW : f ∈ W) (hline : f ∈ Submodule.span ℂ {F.atLevel (h.trans hN)})
    (lift : PosIndex → D)
    (hc : ∀ n, c (lift n) = (qExpansion 1 f).coeff n.val)
    (hk : ∀ n, k (lift n) = X.coefK (column X i 1) (A.index n))
    (hρ : RepInput (X := X) (mapPair E k) i avoid) :
    Nonempty (RealizedCoordinate (p := p) (A := A) D c k N avoid i) := by
  obtain ⟨s, hs, -, -, ⟨Cs⟩⟩ :=
    column_of_labeled_line F k (h.trans hN) i W f hf hW hline lift hc hk
  exact ⟨{
    pair := E
    primitiveForm := F
    degree := d
    degree_pos := Nat.pos_of_ne_zero (NeZero.ne d)
    blockLevel := M
    divides_block := h
    block_exponent_le_one := hM
    block_dvd := hN
    scale := s
    scale_ne_zero := hs
    column := Cs
    attachment := hρ }⟩


end ZInQ.Manuscript.RC.EisForm
