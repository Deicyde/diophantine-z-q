/-!
# g8-tate: G4's bound `[L:ℚ] ≤ D` in G7's interface (g8-object's recommended fix)

g0-mod-field's `G7Data` does not carry G4's bound `Module.finrank ℚ L ≤ heightD` (G4Out has it,
`scratch/g0-mod-field/ModField.lean` L403). g8-object found that without it `LinkedTateObjS` is false
(enlarge `L` by `ℚ(ζ_{2^k})`). Existing files are not edited, so this part states
* `G7DataD`: the text of `G7Data` with the bound appended as a last conjunct (the proposed new text
  of `G7Data`), and `g7DataD_iff : G7DataD ↔ G7Data ∧ [L:ℚ] ≤ D`;
* the supply theorem `g7OutUnrD_of_g4Out` (g0-mod-field's `g7OutUnr_of_g4Out` already has the bound
  from `G4Out`; its proof, copied, with one more component), `fieldDescentUnrD`;
* the D-form `AfterG7D` of g0-mod-field's `AfterG7` (quantified over `G7DataD`), the trivial
  `afterG7D_of_afterG7`, and `modularConstituent_of_rangesD : … → AfterG7D → ModularConstituentG`:
  the strengthened interface still yields g0-mod-field's `ModularConstituentG`.
-/

noncomputable section

namespace G8Tate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

/-- **`G7Data` with G4's bound `[L:ℚ] ≤ D` (proposed new text of `G0ModField.G7Data`).** The text
of g0-mod-field's `G7Data` (ModField.lean L611-622) with the conjunct
`Module.finrank ℚ L ≤ heightD` appended. -/
def G7DataD (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P ∧
  Module.finrank ℚ L ≤ heightD

/-- `G7DataD` is `G7Data` plus the bound (proved). -/
theorem g7DataD_iff {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ}
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} :
    G7DataD u P L A ε N χ β L' hLL' ↔
      G7Data u P L A ε N χ β L' hLL' ∧ Module.finrank ℚ L ≤ heightD := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hD⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hD⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hD⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hD⟩

/-- **G7's output with the twist and G4's bound** (the D-form of `G0ModField.G7OutUnr`). -/
def G7OutUnrD (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7DataD u P L A ε N χ β L' hLL'

/-- **The supply theorem (proved): `g7OutUnr_of_g4Out` supplies G4's bound.** The proof of
g0-mod-field's `g7OutUnr_of_g4Out` (ModField.lean L634-660), copied, with the bound `hLD` of
`G4Out` added as the last component. -/
theorem g7OutUnrD_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnrD u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver, hLD⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

/-- `G7OutUnrD → G7OutUnr` (proved; forgets the bound). -/
theorem g7OutUnr_of_D (u : ℚ) (P : QML3 Qbar) (h : G7OutUnrD u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ := h
  exact ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, (g7DataD_iff.mp hdata).1⟩

/-- **G2 → G4 → G7 with the twist and the bound (proved)**: g0-mod-field's `fieldDescentUnr` with
`g7OutUnrD_of_g4Out`. -/
theorem fieldDescentUnrD (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnrD u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnrD_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **The D-form of `G0ModField.AfterG7`** (G8-G16 for G7 data with `[L:ℚ] ≤ D`): the text of
`AfterG7` (ModField.lean L823-833) with `G7Data` replaced by `G7DataD`. -/
def AfterG7D : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7DataD u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- `AfterG7 → AfterG7D` (proved; trivially). -/
theorem afterG7D_of_afterG7 (h : AfterG7) : AfterG7D :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' (g7DataD_iff.mp hdata).1

/-- **`ModularConstituentG` from the D-form (proved)**: g0-mod-field's
`modularConstituent_of_ranges` with `AfterG7D` in place of `AfterG7` (`fieldDescentUnrD`
supplies the bound). -/
theorem modularConstituent_of_rangesD (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7D) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdataD⟩ :=
    fieldDescentUnrD hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdataD
  have hdata := (g7DataD_iff.mp hdataD).1
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

end G8Tate

end

#print axioms G8Tate.g7DataD_iff
#print axioms G8Tate.g7OutUnrD_of_g4Out
#print axioms G8Tate.g7OutUnr_of_D
#print axioms G8Tate.fieldDescentUnrD
#print axioms G8Tate.afterG7D_of_afterG7
#print axioms G8Tate.modularConstituent_of_rangesD
