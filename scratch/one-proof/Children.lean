import Mathlib
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TotallySplit
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Contrib.AbsFrob.AlgFrobRed
import ZInQKernel.Contrib.AbsFrob.Basic
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.AbVarBC.G9Instance
import ZInQKernel.Contrib.AbVarBC.KerUnit
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Tangent
import ZInQKernel.Contrib.AbVarBC.Tate
import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.Dim.HodgeLattice
import ZInQKernel.Contrib.FrobChain.AlgFrobRed
import ZInQKernel.Contrib.FrobChain.Bridge35
import ZInQKernel.Contrib.FrobChain.FExtend
import ZInQKernel.Contrib.FrobChain.FrobTrace
import ZInQKernel.Contrib.FrobChain.LinkedStatement
import ZInQKernel.Contrib.FrobChain.Pieces
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.FrobChain.TateBridge
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import ZInQKernel.Contrib.HeightBC.Copies
import ZInQKernel.Contrib.HeightBC.CotangentBC
import ZInQKernel.Contrib.HeightBC.CotangentSpan
import ZInQKernel.Contrib.HeightBC.G0StableBC
import ZInQKernel.Contrib.HeightBC.GlueC
import ZInQKernel.Contrib.HeightBC.H5GlueMinimal
import ZInQKernel.Contrib.HeightBC.H5GlueOpen
import ZInQKernel.Contrib.HeightBC.H5GlueReduction
import ZInQKernel.Contrib.HeightBC.HodgeBCInjective
import ZInQKernel.Contrib.HeightBC.LocalStructure
import ZInQKernel.Contrib.HeightBC.Main
import ZInQKernel.Contrib.HeightBC.Natural
import ZInQKernel.Contrib.HeightBC.OmegaBC
import ZInQKernel.Contrib.HeightBC.StalkPullback
import ZInQKernel.Contrib.HeightBC.StalkTensor
import ZInQKernel.Contrib.HeightBC.UniformizationLift
import ZInQKernel.Contrib.HodgeBC2.ExtFrac
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.Mobius.CurveFacts
import ZInQKernel.Contrib.Mobius.Glue
import ZInQKernel.Contrib.Mobius.ImagePlane
import ZInQKernel.Contrib.Mobius.InfraDim
import ZInQKernel.Contrib.Mobius.Main
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.RLeaf.X1ConstantField
import ZInQKernel.Contrib.SpreadOut.NumberField
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.T31.Main
import ZInQKernel.Contrib.TauCeti.Algebra.Group.Equiv.Pi
import ZInQKernel.Contrib.TauCeti.Algebra.Module.Torsion.Decomposition
import ZInQKernel.Contrib.TauCeti.Data.ZMod.Torsion
import ZInQKernel.Contrib.TauCeti.GroupTheory.FiniteAbelian.RankTwo
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.InertiaDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Existence
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TwistDescent.GaloisDescent
import ZInQKernel.Contrib.UnramRoots.FrobData
import ZInQKernel.Contrib.UnramRoots.Main
import ZInQKernel.Contrib.UnramRoots.Metric
import ZInQKernel.Contrib.UnramRoots.Procyclic
import ZInQKernel.Contrib.UnramRoots.Reduction
import ZInQKernel.Contrib.ZariskiConn.Basic
import ZInQKernel.HDecomp.A6.A6
import ZInQKernel.HDecomp.Analytic.QMLattice
import ZInQKernel.HDecomp.Analytic.Torus
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.Assembly.C8
import ZInQKernel.HDecomp.Assembly.E1Lin
import ZInQKernel.HDecomp.Assembly.E2Index
import ZInQKernel.HDecomp.Assembly.F3Glue
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.HDecomp.C10.Trace
import ZInQKernel.HDecomp.Conductor.ArtinUpper
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.HDecomp.Conductor.Dyadic
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Conductor.SqrtChar
import ZInQKernel.HDecomp.Descent.B1Quat
import ZInQKernel.HDecomp.Descent.B2Assembly
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Descent.Chi
import ZInQKernel.HDecomp.Descent.Cochain
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.Faltings.H5Neron
import ZInQKernel.HDecomp.Faltings.Height
import ZInQKernel.HDecomp.Faltings.HodgeData
import ZInQKernel.HDecomp.Faltings.IdealLines
import ZInQKernel.HDecomp.Faltings.Leaves
import ZInQKernel.HDecomp.Faltings.Models
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.I3Linalg.TateBC
import ZInQKernel.HDecomp.LeafPush2.R18
import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.LeafPush2.R3
import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.ModCurves.E1Sub
import ZInQKernel.HDecomp.ModCurves.Genus
import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.ModCurves.Leaves
import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.HDecomp.Repo.A1Quaternion
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Sqrt.Disj
import ZInQKernel.HDecomp.Sqrt.SqrtLocal
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Textbook.FrobeniusDense
import ZInQKernel.HDecomp.Textbook.Igusa.Forward
import ZInQKernel.HDecomp.Textbook.KroneckerWeberUse
import ZInQKernel.HDecomp.Textbook.SkolemNoether
import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.HDecomp.Textbook.T30SqrtCrit
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
/-! op-compact: the constants strictly below each alias target (structure fields, constructors, `T.x.lemma`, ...),
written to scratch/one-proof/export_children.txt as `target child module`. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let ts ← IO.FS.lines "scratch/one-proof/export_targets.txt"
  let tset : NameSet := ts.foldl (fun s t => s.insert (t.toName)) {}
  let mut out : Array String := #[]
  let mods := env.header.moduleNames
  for (n, _) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    let m := match env.getModuleIdxFor? n with | some i => mods[i.toNat]! | none => `none
    let mut p := n.getPrefix
    while !p.isAnonymous do
      if tset.contains p then
        out := out.push s!"{p} {n} {m}"
      p := p.getPrefix
  IO.FS.writeFile "scratch/one-proof/export_children.txt" (String.intercalate "\n" (out.qsort (· < ·)).toList ++ "\n")
  logInfo m!"{out.size} children"
