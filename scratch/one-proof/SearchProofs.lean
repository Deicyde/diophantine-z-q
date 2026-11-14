import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.FrobChain.AlgFrobRed
import ZInQKernel.Contrib.FrobChain.FExtend
import ZInQKernel.Contrib.FrobChain.FrobTrace
import ZInQKernel.Contrib.FrobChain.LinkedFrob
import ZInQKernel.Contrib.FrobChain.Main
import ZInQKernel.Contrib.FrobChain.Pieces
import ZInQKernel.Contrib.G9.G9
import ZInQKernel.Contrib.G9.I3Layer
import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.G9.Reduction
import ZInQKernel.Contrib.G9.Statement
import ZInQKernel.Contrib.HeightBC.H5GlueOpen
import ZInQKernel.Contrib.HeightBC.H5GlueReduction
import ZInQKernel.Contrib.HeightBC.Main
import ZInQKernel.Contrib.HomUnify.Corr
import ZInQKernel.Contrib.Mobius.CurveFacts
import ZInQKernel.Contrib.Mobius.Glue
import ZInQKernel.Contrib.Mobius.ImagePlane
import ZInQKernel.Contrib.Mobius.Main
import ZInQKernel.Contrib.R10.Amend
import ZInQKernel.Contrib.R10.Final
import ZInQKernel.Contrib.R10.Glue
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.IgusaLocal
import ZInQKernel.Contrib.RLeaf.IgusaX0
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.RLeaf.X1ConstantField
import ZInQKernel.Contrib.RLeaf.X1RationalCusp
import ZInQKernel.Contrib.SpreadOut.NumberField
import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.ZariskiConn.Basic
import ZInQKernel.HDecomp.A6.A6
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.HDecomp.C10.Trace
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Faltings.H5Neron
import ZInQKernel.HDecomp.Faltings.Height
import ZInQKernel.HDecomp.Faltings.Leaves
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.LeafPush2.Bridge
import ZInQKernel.HDecomp.LeafPush2.R18
import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.LeafPush2.R3
import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.LeafPush2.UnifBridge
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
import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.HDecomp.Textbook.T10Etale

import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.GZTheta.New32
import ZInQKernel.Contrib.GZTheta.NewCMFinal
import ZInQKernel.Contrib.GZTheta.Split
import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.TYZGenus.CM
import ZInQKernel.Contrib.TYZGenus.Package
import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.RingClassGalois
import ZInQKernel.Contrib.TYZGenus.ShimuraCusp
import ZInQKernel.Contrib.TYZGenus.ShimuraEtaInv
import ZInQKernel.Contrib.TYZGenus.ShimuraField
import ZInQKernel.Contrib.TYZGenus.ShimuraMain
import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import ZInQKernel.Contrib.TYZGenus.ShimuraQExp
import ZInQKernel.Contrib.TYZGenus.ShimuraRecip
import ZInQKernel.Contrib.TYZGenus.ShimuraTheta
import ZInQKernel.Contrib.TYZGenus.ShimuraZn
/-! op-dedupe step 4: for each field of frozenTarget's hypothesis structures, a theorem outside `HDec` (in the
imported kernel modules) whose type is that field's Prop (syntactically, or by `isDefEq` among theorems with the
same head constant). Prints: structure, field, field type, provers. -/
open Lean Meta Elab Command

def opdHead (e : Expr) : Option Name := e.getAppFn.constName?

elab "#opd_search " ids:ident* : command => liftTermElabM do
  let env ← getEnv
  let mut byHead : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if (`HDec).isPrefixOf n || n.isInternal then continue
      if let some h := opdHead ci.type then
        byHead := byHead.insert h ((byHead.getD h #[]).push n)
  for id in ids do
    let s := id.getId
    let some info := getStructureInfo? env s | throwError "not a structure"
    for f in info.fieldNames do
      let some ci := env.find? (s ++ f) | continue
      forallTelescope ci.type fun _ t => do
        let t ← instantiateMVars t
        let mut found : Array Name := #[]
        if !t.hasFVar then
          if let some h := opdHead t then
            for c in byHead.getD h #[] do
              let some cc := env.find? c | continue
              if cc.levelParams.length != 0 then continue
              if cc.type == t then found := found.push c
              else if ← (try withoutModifyingState (isDefEq cc.type t) catch _ => pure false) then
                found := found.push c
        IO.println s!"{s}\t{f}\t{(← ppExpr t).pretty 100000}\t{found.toList}"
elab "#opd_search_thm " id:ident : command => liftTermElabM do
  let env ← getEnv
  let some ci := env.find? id.getId | throwError "unknown"
  let mut byHead : Std.HashMap Name (Array Name) := {}
  for (n, c) in env.constants.toList do
    if let .thmInfo _ := c then
      if (`HDec).isPrefixOf n || n.isInternal || n == id.getId then continue
      if let some h := opdHead c.type then
        byHead := byHead.insert h ((byHead.getD h #[]).push n)
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      let mut found : Array Name := #[]
      if let some h := opdHead t then
        for c in byHead.getD h #[] do
          let some cc := env.find? c | continue
          if cc.levelParams.length != 0 then continue
          if cc.type == t then found := found.push c
          else if ← (try withoutModifyingState (isDefEq cc.type t) catch _ => pure false) then
            found := found.push c
      IO.println s!"{id.getId}\t{(← x.fvarId!.getUserName)}\t{(← ppExpr t).pretty 100000}\t{found.toList}"
#opd_search_thm ZInQ.OneProof.frozenTarget
#opd_search HDec.HSyn.OpenResearchLeaves2 HDec.HSyn.OpenTextbookLeaves4 HDec.HSyn.OpenAddedLeaves4 HDec.HSyn.OpenGlue4
