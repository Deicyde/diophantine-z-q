/-! # lt-local, part 4: `LinkedTateLocal` on `TateBridge35`'s data

* `LinkedTateLocalD` (the corrected statement): g0-assemble2's `LinkedTateLocal` with the premise
  `[L:ℚ] ≤ D` added (as g8-object's `LinkedTateDataD` adds it to `LinkedTateData`).
* `ModelEndRank4` (GLUE, named here): `rank_ℤ End(A_{L'}) = 4` on G7's model. It is
  `TateBridge35`'s second hypothesis, and a consequence of `LinkedTateLocal` itself (its `G7Out`
  contains it), so it costs no truth.
* `localGlue_at`: lg-kerwild's `localGlue_of_transport`, with `UnramRoots p ℓ` needed only at
  `p = 2` (its proof, through local-glue's `localGlue_of_descent`).
* **`linkedTateLocalD_of_tateBridge35`**: R6 + I2-Tors + `UnramRoots 2 5` + `UnramRoots 2 3` +
  `TateBridge35` + `ModelEndRank4` ⟹ `LinkedTateLocalD`.
* `linkedTateLocal_of_D`: `LinkedTateLocalD` + `G7DegreeBound` ⟹ `LinkedTateLocal` (trivial;
  shows what the unrestricted statement would need). -/

noncomputable section

-- the section-level opens of G0Assemble2.lean's `section G0A2_a85_linked`, as for the copy
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue (G5-G6 on G7's model, N5 L528-563): the endomorphism ring of `A_{L'}` has rank 4.**
For every fibre context and G7 data, `rank_ℤ End(A_{L'}) = 4`. Proof plan (not formalized):
`≥ 4` from the QM structure `ι : 𝒪 → End(PK.A)` of `IsQMModel`, base-changed to `L'` (unram-tate's
`endBaseChange`; `𝒪` has rank 4 and `ι` is injective because `[n] ≠ 0`, cf. g0-assemble2's
`modelNoncomm_of_mulIsogeny`); `≤ 4` from `End(A_{L'})` a division-ring order (g0-split's
`FibreSimple`, already in `GluePieces3` through FS5) and Albert's bound `[End⁰(A):ℚ] ≤ 2g` for a
simple abelian variety in characteristic `0` (Mumford, *Abelian Varieties*, §21; locator
UNVERIFIED). This is `TateBridge35`'s (and g0-mod-field's `TateBridge`'s) second hypothesis. -/
def ModelEndRank4 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4

/-- **G4's degree bound on G7's data (GLUE, N5 L532-563).** `[L:ℚ] ≤ D` for every G7 datum in a
fibre context. g0-mod-field's `G4Out` carries this bound but its `G7Data` does not (local-data's
finding F3); `G7Data` admits fields `L` larger than G4's Hom field, so this Prop is not expected to
hold as stated (SPECULATIVE). It is named only to record what the unrestricted
`LinkedTateLocal` would need on this route; the fix is to add the bound to `G7Data`
(`LinkedTateLocalD`). -/
def G7DegreeBound : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' → Module.finrank ℚ L ≤ ZInQ.heightD

/-- **Glue (corrected `LinkedTateLocal`, for `GluePieces4`):** the text of g0-assemble2's
`HSyn.G0AssembleMod.LinkedTateLocal` (GLUE field 39 of `GluePieces3`) with the premise
`Module.finrank ℚ L ≤ ZInQ.heightD` added after `G7Data`. The local data at `p > D` (tame
closure of `L_v`) and the `G7Clauses` used at every `p` need this bound (N5 L848-851:
`[L_v:ℚ_p] ≤ D < p`). Proved from `TateBridge35`, `ModelEndRank4` and leaves
(`linkedTateLocalD_of_tateBridge35`). -/
def LinkedTateLocalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **lg-kerwild's `localGlue_of_transport` with `UnramRoots` only at `p = 2` (proved; its proof,
through local-glue's `localGlue_of_descent`).** -/
theorem localGlue_at (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_descent hR6 hTors hpℓ h7 hCl
    (LGKerWild.kerWild_of_g7Data_alg hD βQ j ιC hC)
    (fun _ => LGKerWild.descentPts_of_g7 hLL' A hdim)
    (fun h2 => G15Ram.betaTwist2_of_unramRoots h2 hCl (hU h2))

/-- **`LinkedTateLocalD` from `TateBridge35` (proved).** Inputs: the leaves R6
(`ObjBridge.RaynaudCriterion`) and I2-Tors (`ObjBridge.TorsionStructure`); local-glue's textbook
Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`; g14-trace's glue `TateBridge35`; the glue
`ModelEndRank4`. Steps: `dim A_{L'} = 2` (`dim_bc_of_g7Data`) and `ModelEndRank4` feed
`TateBridge35`; its output gives `G7Out` at 5 and 3, `FrobTraceLink` and `ιC ∘ βQ = β`;
`G7Clauses` for `j_ℓ ∘ βQ` (`g7Clauses_of_transport`, with `[L:ℚ] ≤ D`); `LocalGlue` at `p ≠ ℓ`
(`localGlue_at`: lg-kerwild's `KerWild` and `DescentPts` discharges); `LocalData` for every `r_ℓ`
with G8's output (local-data's `localData_of_g7`). -/
theorem linkedTateLocalD_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hRk : ModelEndRank4) :
    LinkedTateLocalD := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hLD
  letI : NumberField L' := numberField_of_fd L'
  have hdim := dim_bc_of_g7Data hD
  have hrk := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  have hCl5 := g7Clauses_of_transport hD hLD βQ j5 ιC hC h5.2.2.2.2.1
  have hCl3 := g7Clauses_of_transport hD hLD βQ j3 ιC hC h3.2.2.2.2.1
  refine ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF,
    fun r5 r3 h85 h83 => ⟨fun p hp hp5 => ?_, ?_⟩⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact G15Ram.localData_of_g7 h85 hCl5
      (localGlue_at hR6 hTors (fun h2 => by subst h2; exact hU5) hp5 hD βQ j5 ιC hC h5 hCl5)
  · exact G15Ram.localData_of_g7 h83 hCl3
      (localGlue_at hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num) hD βQ j3 ιC hC
        h3 hCl3)

/-- `LinkedTateLocalD` and `G7DegreeBound` give g0-assemble2's `LinkedTateLocal` (proved,
trivially). -/
theorem linkedTateLocal_of_D (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)

/-- The unrestricted Prop gives the restricted one (proved, trivially). -/
theorem linkedTateLocalD_of_local (h : HSyn.G0AssembleMod.LinkedTateLocal) : LinkedTateLocalD :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD _ =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD

/-- `ModelEndRank4` follows from `LinkedTateLocal` (its `G7Out` at `5` contains the rank), so
naming it costs no truth (proved). -/
theorem modelEndRank4_of_localD (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, -⟩ :=
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)
  exact h5.2.1

end LTLocal

end
