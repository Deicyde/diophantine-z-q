import ZInQKernel.OneProof.Main
import Lean
/-! triage2 probe C (task 1, the prune of `deligneComponentsX6PrintedAb` + `geomConnOfAlgClosure`):
(1) the weakened row `R1R2fpRepW` and its consumer bridge `R1R2fp_of_repW`, compiled;
(2) the base witness from González–Rotger's leaf (no Deligne, no `GeomConnOfAlgClosure`);
(3) the list of live constants whose *type* mentions the row or the producer statements (the rethreading work). -/
open CategoryTheory AlgebraicGeometry Lean

namespace HDec.LeafAdopt
open _root_.LeafQM _root_.LeafQM.AV

/-- `R1R2fpRep` without its last conjunct `R1pi0Props X` (never read on the live path: probe `Pi0Use.lean`). -/
def R1R2fpRepW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

theorem R1R2fpRepW_of_rep (h : R1R2fpRep) : R1R2fpRepW := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩

/-- The consumer bridge, proof of `R1R2fp_of_rep` unchanged. -/
theorem R1R2fp_of_repW (h : R1R2fpRepW) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

end HDec.LeafAdopt

namespace HDec.QMSplit.Moduli
open _root_.LeafQM _root_.LeafQM.AV

/-- `GeomConnX6` without `R1pi0Props`. -/
def GeomConnX6W : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY

/-- The base witness from González–Rotger's leaf (already a field; no Deligne, no `GeomConnOfAlgClosure`). -/
theorem geomConnX6W_of_gr (hG : GonzalezRotgerX6) : GeomConnX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hG
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

end HDec.QMSplit.Moduli

-- the rethreading work: live constants whose type mentions a statement carrying `R1pi0Props`
def pcClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen

run_cmd do
  let env ← getEnv
  let s := pcClosure env `ZInQ.OneProof.frozenTarget
  let watched : List Name := [`HDec.LeafAdopt.R1R2fpRep, `HDec.QMSplit.Moduli.CanonicalCoarseX6,
    `HDec.QMSplit.Moduli.GeomConnX6, `HDec.QMSplit.Moduli.CoarseX6OfFine,
    `HDec.QMSplit.Moduli.DeligneComponentsX6, `ShimuraGlue.DeligneComponentsX6Printed,
    `HDec.QMSplit.Moduli.GeomConnOfAlgClosure]
  for w in watched do
    let mut hits : Array Name := #[]
    for n in s.toList do
      if n == w then continue
      if let some ci := env.find? n then
        if (ci.type.find? fun x => x.isConstOf w).isSome then hits := hits.push n
    logInfo m!"{w}: {hits.size} live constants mention it in their type:\n{hits.toList}"
