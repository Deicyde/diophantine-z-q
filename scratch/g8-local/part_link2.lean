/-! ## g8-local, part 2: the restated `GluePieces2` field `LinkedTateObjS` from its core

`LinkedTateObjS` (g8-object, part_split.lean) = `LinkedTateObjSCore` (TateBridge35's data and
`OnL`: g8-tate's targets) + the two `LocalDataS` conjuncts (this task, `LocalPartS`). The texts of
`LinkedTateObjSCore` and `LocalPartS` are generated mechanically from part_split.lean's
`LinkedTateObjS` (`scratch/g8-local/py/gen_link2.py`): the core drops the last two conjuncts,
`LocalPartS` keeps the binders and the premise `[L:ℚ] ≤ D` and only those two conjuncts. -/

noncomputable section

namespace G8Local

open PkgI4 (GQ GQp decomp)
open LadicCond
open G0ModField G8Object
open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2
open HSyn.G0AssembleMod (G15RamWild)

/-- **G15's local data for every G7 datum with `[L:ℚ] ≤ D`** (the two `LocalDataS` conjuncts of
`LinkedTateObjS`, with its binders). Proved from `RaynaudNF`, `TorsionFieldBound` and
`Char2UpperBreak` (`localPartS_of`). -/
def LocalPartS : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataS p ⟨hp⟩ L _ A 5 _ β) ∧
      LocalDataS 5 L A 3 β

/-- **`LinkedTateObjS` without its two `LocalDataS` conjuncts** (TateBridge35's data, `ιC ∘ βQ = β`,
and `OnL` for `Tm₅`, `Tm₃`). GLUE: g8-tate's part. -/
def LinkedTateObjSCore : Prop :=
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
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (ψ₅ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 ≃ₗ[PadicAlgCl 5]
        G0Galois.Vb A 5)
      (ψ₃ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 ≃ₗ[PadicAlgCl 3]
        G0Galois.Vb A 3),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      OnL L A Tm₅ (fun g => j5 (aQ g)) ψ₅ ∧ OnL L A Tm₃ (fun g => j3 (aQ g)) ψ₃

/-- **`LocalPartS` (proved from the three named Props).** -/
theorem localPartS_of (hR : RaynaudNF) (hT : TorsionFieldBound) (hC : Char2UpperBreak) :
    LocalPartS := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata hLD
  exact localDataS_all hR hT hC hdata hLD

/-- **`LinkedTateObjS` = core + local part (proved).** -/
theorem linkedTateObjS_of_core (hL : LocalPartS) (hcore : LinkedTateObjSCore) :
    LinkedTateObjS := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata hLD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, ψ₅, ψ₃, h75, h73, hF, hι, hOn5,
    hOn3⟩ := hcore Y Φ π u P hctx L A ε N χ β L' hLL' hdata hLD
  obtain ⟨hl5, hl3⟩ := hL Y Φ π u P hctx L A ε N χ β L' hLL' hdata hLD
  exact ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, ψ₅, ψ₃, h75, h73, hF, hι, hOn5, hOn3,
    hl5, hl3⟩

/-- **g0-assemble's `LinkedTateData` (restricted to `[L:ℚ] ≤ D`) from T7, the core, and the three
named Props (proved).** -/
theorem linkedTateDataD_of_core (hM : PkgI3.CharPolyIndepOfEll) (hR : RaynaudNF)
    (hT : TorsionFieldBound) (hC : Char2UpperBreak) (hcore : LinkedTateObjSCore) :
    LinkedTateDataD :=
  linkedTateDataD_of_S hM (linkedTateObjS_of_core (localPartS_of hR hT hC) hcore)

end G8Local

end

#print axioms ZInQ.Contrib.G8Local.fix_of_wild_pow
#print axioms ZInQ.Contrib.G8Local.exists_ppow_fix
#print axioms ZInQ.Contrib.G8Local.fix_of_wild_rootOfUnity
#print axioms ZInQ.Contrib.G8Local.fix_of_wild_pRootOfUnity
#print axioms ZInQ.Contrib.G8Local.fix_of_wild_root
#print axioms ZInQ.Contrib.G8Local.decomp_ppow_mem
#print axioms ZInQ.Contrib.G8Local.cyc_decomp_eq_one
#print axioms ZInQ.Contrib.G8Local.galChar_decomp_eq_one
#print axioms ZInQ.Contrib.G8Local.cochain_eq_one_of_wild
#print axioms ZInQ.Contrib.G8Local.repBaseChange_galRep_eq_one_of_fix
#print axioms ZInQ.Contrib.G8Local.fixed_of_unipSq_of_pow
#print axioms ZInQ.Contrib.G8Local.exists_fix_field
#print axioms ZInQ.Contrib.G8Local.algClosure_surjective
#print axioms ZInQ.Contrib.G8Local.ramCard_le_finrank
#print axioms ZInQ.Contrib.G8Local.exists_galois_closure
#print axioms ZInQ.Contrib.G8Local.decomp_spec
#print axioms G8Local.chiLevel_split
#print axioms G8Local.chiLevel_split_two
#print axioms G8Local.beta_mul
#print axioms G8Local.beta_wild_eq_one
#print axioms G8Local.betaUpper_odd
#print axioms G8Local.fix_of_inertia_rootOfUnity
#print axioms G8Local.galChar_sq_inertia_two
#print axioms G8Local.betaUpper_two
#print axioms G8Local.exists_ppow_fix_point
#print axioms G8Local.fix_of_pow_coprime_wild
#print axioms G8Local.wildTate_of
#print axioms G8Local.localDataS_of
#print axioms G8Local.localDataS_all
#print axioms G8Local.localPartS_of
#print axioms G8Local.linkedTateObjS_of_core
#print axioms G8Local.linkedTateDataD_of_core
