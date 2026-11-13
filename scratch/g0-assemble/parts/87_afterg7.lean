
/-! ## g0-assemble: `AfterG7` (G8-G16) from g0-mod-galois and g0-mod-newform

`G0ModField.AfterG7` is proved from the leaf bundles, g0-mod-galois' `GaloisPieces` (with `R14Det`,
the published determinant clause of R14, as g0-mod-galois found), g0-mod-newform's leaves and glue,
and two new named glue Props on the data of G7:

* `ModelG3G6`: the outputs of G3 (inertia outside `T` acts trivially on `V_ℓ(A_{L'})`, `ℓ = 3, 5`)
  and of G5-G6 (`End(A_{L'})` a noncommutative division ring) for the model `A_{L'}` that
  g0-mod-field's `G7Data` delivers. G6 is NoCM on the fibre: **QM-PIN** (like FS5).
* `LinkedTateData`: g0-mod-field's bridge `TateBridge` at `ℓ = 5` and `ℓ = 3` **from the same
  descent datum** (the Tate functor applied to one family `m_σ = μ_σ ∘ σ`), together with
  g0-mod-newform's two AV-side Props `G14TraceCompat` and `G15RamG` for every `r₅`, `r₃` that G8
  attaches to these data. They must be stated jointly: g0-mod-newform found that `G14TraceCompat`
  is false for unrelated constituents (a twist by a character of `Gal(L'/ℚ)` changes `r_ℓ` but
  not its restriction to `G_{L'}`), and `TateBridge` alone (∀ ℓ ∃ data) does not link the data at
  3 and 5. Only clauses (i)-(ii) of `G15RamG` are asked (`G15RamWild`); clause (iii) is G11's
  output (`G0Galois.g11`), applied in `g15RamG_of_wild`.

The composition: `galoisG2Out_of_g7Data` (g0-mod-field, G2Out from G7Data) → `g8_g12_of_leaves`
at 5 and `g8_g11` at 3 (g0-mod-galois) → `g12Spec_of_galois` (g0-mod-newform; the G8 and G12
outputs are g0-mod-galois' definitions, copied verbatim there) → `modularConstituent_tail_G`
(g0-mod-newform, G13-G16). -/

section G0AssembleAfterG7Sec

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue G3 + G5-G6 on G7's model** (g0-assemble; QM-PIN for the G6 part). For every fibre
context and G7 data of g0-mod-field: `End(A_{L'})` is a noncommutative division ring
(`G0Galois.G6Out`; NoCM, N5 G6), and inertia at primes outside `T(u)` acts trivially on
`ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` for `ℓ = 5, 3` (`G0Galois.G3Out`; G3, good reduction of the QM model away
from `T` with Néron–Ogg–Shafarevich R7a). -/
def ModelG3G6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G6Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- Clauses (i)-(ii) of g0-mod-newform's `LocalRamG` (its clause (iii) is G11's output): for
`p ≤ D`, absolute upper ramification groups above `U₀` act trivially; for `p > D`, wild inertia
acts trivially (N5 L819-852, "D1-D4 on G8's `r_ℓ`"). -/
def LocalRamWild (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : PkgI4.GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1)

/-- g0-mod-newform's `G15RamG` without clause (iii): `LocalRamWild` for `r₅` at `p ≠ 5` and for
`r₃` at `p = 5`. -/
def G15RamWild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamWild p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamWild p ⟨hp⟩ 3 _ D.r3)

/-- **`G15RamG` from its clauses (i)-(ii) and G11's output** (proved): clause (iii) at
`p ∉ S_mul`, `p ∤ M_{S_mul}(u)` is `G0Galois.G11Out (T u)`, since such `p` is not in
`T u = S_mul ∪ supp M_{S_mul}(u)`. -/
theorem g15RamG_of_wild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) (u : ℚ) (hw : G15RamWild D)
    (h5 : G0Galois.G11Out (T u) D.r5) (h3 : G0Galois.G11Out (T u) D.r3) :
    G0ModNewform.G15RamG D u := by
  intro p hp
  have hT : p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → p ∉ T u := by
    intro hS hM hmem
    simp only [T, GlueDescent.ramSet, Finset.mem_union] at hmem
    rcases hmem with h | h
    · exact hS h
    · exact hM (Nat.dvd_of_mem_primeFactors h)
  refine ⟨fun h5' => ?_, fun h5' => ?_⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).1 h5'
    exact ⟨hi, hii, fun hS hM => h5 p hp (hT hS hM) h5'⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).2 h5'
    exact ⟨hi, hii, fun hS hM => h3 p hp (hT hS hM) (by omega)⟩

/-- **Glue: linked Tate data with G14-G15 on them** (g0-assemble; g0-mod-field's `TateBridge`
at `ℓ = 5, 3` from one descent datum, with g0-mod-newform's `G14TraceCompat` and `G15RamG`).
For every fibre context and G7 data: operator data at `ℓ = 5` and `ℓ = 3` satisfying
g0-mod-galois' `G7Out`, such that for all `r₅`, `r₃` with G8's output on these data and all
embeddings `i`, `ι_ℂ`, `ι₅`, some `ι₃` makes the traces compatible (`G14TraceCompat`, N5 L776-795)
and `r₅`, `r₃` have Glazer's wild local ramification (`G15RamWild`: clauses (i)-(ii) of
g0-mod-newform's `G15RamG`, N5 L819-852; clause (iii) is proved from G11, `g15RamG_of_wild`). -/
def LinkedTateData : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a₅ β₅ : PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a₃ β₃ : PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅ a₅ β₅ u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃ a₃ β₃ u₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ a₅ β₅) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ a₃ β₃) r₃ →
        ∀ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L') (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
          (ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5), ∃ ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3,
          G0ModNewform.G14TraceCompat
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) ∧
          G15RamWild
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))

/-- g0-mod-newform's leaf bundle from the two leaf bundles and the concrete R17
(`LadicCond.CarayolR17'`; the bundle's `r17` is still an `opaque` placeholder). -/
theorem newformLeaves_of (r : ResearchLeaves) (t : TextbookLeaves)
    (hCar : LadicCond.CarayolR17') : G0ModNewform.NewformLeaves :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    hCar, r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

/-- The two textual copies of `CommonConstituent` (g0-mod-newform's, g0-mod-field's) agree. -/
theorem commonConstituent_copy' {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) :
    G0ModNewform.CommonConstituent A J ↔ G0ModField.CommonConstituent A J := Iff.rfl

/-- **`AfterG7` (G8-G16), proved** from the leaf bundles, g0-mod-galois' `GaloisPieces`,
g0-mod-newform's `DirichletOfFinite`, the concrete R17 `CarayolR17'`, the three LadicCond glue
Props, and the two glue Props `ModelG3G6`, `LinkedTateData`. -/
theorem afterG7_of (r : ResearchLeaves) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves r t m _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) m.deRham m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

end HSyn.G0AssembleMod

end G0AssembleAfterG7Sec

#print axioms HSyn.G0AssembleMod.afterG7_of
