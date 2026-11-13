
section KWFixFinalSec

/-! ### §3. `LocalGlue` on the data of the bridges in Glazer's normalization -/

noncomputable section

namespace KWFix

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

/-- **`TateBridge35E` contains g14-trace's `TateBridge35` (proved)**, with `j_ℓ = Φ_ℓ ∘ ι_ℂ`. -/
theorem tateBridge35_of_E (h : TateBridge35E) : G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨aQ, βQ, jOf Φ5 ιC, jOf Φ3 ιC, Tm5, c5, _, u5, Tm3, c3, _, u3,
    g7Out_beta_congr _ 5 _ _ _ _ _ _ _ h5 fun g => congrArg Φ5 (hιβ g),
    g7Out_beta_congr _ 3 _ _ _ _ _ _ _ h3 fun g => congrArg Φ3 (hιβ g), hF, ιC, hιβ⟩

/-- **`KerWild` for `Φ ∘ β` (proved)**: local-glue's `kerWild_of_g7Data` with the injective
`ι = Units.map Φ` and G7Data's kernel-field clause. -/
theorem kerWild_of_equiv {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) {u : ℚ}
    {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL') :
    @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L :=
  G15Ram.kerWild_of_g7Data β (LGKerWild.g7Data_ker hD)
    (Units.map (Φ : ℂ →+* PadicAlgCl ℓ).toMonoidHom) (Units.map_injective Φ.injective)
    (fun _ => rfl)

/-- **`LocalGlue` on `G7Out` in Glazer's normalization (proved).** For G7's data with
`[L:ℚ] ≤ D`, `G7Out` at `ℓ` on `A_{L'}` with `β' = Φ ∘ β`, `ε' = Φ ∘ ε`, and `p ≠ ℓ`:
`LocalGlue p Tm a (Φ ∘ β) L`, from R6, I2-Tors and `UnramRoots`. `G7Clauses` is
`g7Clauses_of_g7Data`, `KerWild` is `kerWild_of_equiv`, `DescentPts` is `descentPts_of_g7`. -/
theorem localGlue_of_E (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (Φ : ℂ ≃+* PadicAlgCl ℓ)
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L :=
  LGKerWild.localGlue_of_kerWild hR6 hTors hU hpℓ hLL' A h7 (kerWild_of_equiv Φ hD)
    (G8Tate.g7Clauses_of_g7Data Φ hD hLD)

/-- **`LocalGlue` at every `ℓ` from `TateBridgeE` (proved; replaces lg-kerwild's
`exists_localGlue_of_tateBridgeK`).** For G7's data with `[L:ℚ] ≤ D`, `dim A_{L'} = 2`,
`rank End(A_{L'}) = 4` and every coefficient prime `ℓ`: operator data with `G7Out` at `ℓ` in
Glazer's normalization, and for these data `G7Clauses`, `KerWild` and `LocalGlue p` at every
`p ≠ ℓ` hold. No hypothesis on the hidden data. -/
theorem exists_localGlue_of_tateBridgeE (hB : TateBridgeE) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
      G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L := by
  obtain ⟨Φ, Tm, c, a, uu, h7⟩ := hB u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Φ, Tm, c, a, uu, h7, G8Tate.g7Clauses_of_g7Data Φ hD hLD, kerWild_of_equiv Φ hD,
    fun p hp hpℓ => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact localGlue_of_E hR6 hTors (hU p ℓ) hpℓ hD hLD Φ h7

/-- **Main result (every `ℓ`): `LocalGlue` from the leaves I3.M0, R6, I2-Tors and the textbook
Prop `UnramRoots` (proved).** `TateBridgeE` is `tateBridgeE_of_tateModuleFree`. -/
theorem exists_localGlue_of_leaves (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
      G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L :=
  exists_localGlue_of_tateBridgeE (tateBridgeE_of_tateModuleFree hT) hR6 hTors hU
    u P L A ε N χ β L' hLL' hD hdim hrk hLD ℓ

/-- **`LocalGlue` at `ℓ = 5` and `ℓ = 3` on `TateBridge35E`'s data (proved)**: the operators
`Tm₅`, `Tm₃` are linked by `FrobTraceLink`, and `LocalGlue` holds at every `p ≠ 5` for `Tm₅` and
every `p ≠ 3` for `Tm₃`, with `G7Clauses` and `KerWild` discharged. -/
theorem exists_localGlue35_of_tateBridge35E (hB : TateBridge35E)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) :
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
      (Φ5 : ℂ ≃+* PadicAlgCl 5) (Φ3 : ℂ ≃+* PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      (∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5
        (fun g h => Φ5 (ε g h : ℂ)) (fun g => Φ5 (ιC (aQ g))) (fun g => Φ5 (β g : ℂ)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3
        (fun g h => Φ3 (ε g h : ℂ)) (fun g => Φ3 (ιC (aQ g))) (fun g => Φ3 (β g : ℂ)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      G15Ram.G7Clauses (fun g => Φ5 (β g : ℂ)) (fun g h => Φ5 (ε g h : ℂ)) L ∧
      G15Ram.G7Clauses (fun g => Φ3 (β g : ℂ)) (fun g h => Φ3 (ε g h : ℂ)) L ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5
        (fun g => Φ5 (ιC (aQ g))) (fun g => Φ5 (β g : ℂ)) L) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 → @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3
        (fun g => Φ3 (ιC (aQ g))) (fun g => Φ3 (β g : ℂ)) L) := by
  obtain ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  refine ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF,
    G8Tate.g7Clauses_of_g7Data Φ5 hD hLD, G8Tate.g7Clauses_of_g7Data Φ3 hD hLD,
    fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_E hR6 hTors (hU p 5) hp5 hD hLD Φ5 h5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_E hR6 hTors (hU p 3) hp3 hD hLD Φ3 h3

end KWFix

end

end KWFixFinalSec

#print axioms G8Tate.exists_complex_equiv
#print axioms G8Tate.g7Clauses_of_g7Data
#print axioms KWFix.tateBridge_of_E
#print axioms KWFix.g7Out_eps_congr
#print axioms KWFix.tateBridgeE_of_tateModuleFree
#print axioms KWFix.tateBridge35E_of_algFrobLink
#print axioms KWFix.tateBridge35_of_E
#print axioms KWFix.kerWild_of_equiv
#print axioms KWFix.localGlue_of_E
#print axioms KWFix.exists_localGlue_of_tateBridgeE
#print axioms KWFix.exists_localGlue_of_leaves
#print axioms KWFix.exists_localGlue35_of_tateBridge35E
