import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.Pi0Prune
import Lean
/-! pi0-prune: (1) the closure of the new top theorem contains no projection of the two fields, no
`DeligneComponentsX6Printed(Ab)`, `GeomConnOfAlgClosure`, `R1pi0Props`, `R1R2fpRep`; (2) `frozenTarget` rerouted
through `sixContactMin_of_open29_pruned` (same type as `frozenTarget`), and through `sixContactMin_of_open29P` over
the bundle minus the two fields. -/
open Lean

def ccClosure (env : Environment) (root : Name) : NameSet := Id.run do
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
  for root in [`HDec.HSyn.sixContactMin_of_open29_pruned, `HDec.HSyn.sixContactMin_of_open29P] do
    let s := ccClosure env root
    let bad := s.toList.filter fun n =>
      (match n with
        | .str _ l => (l == "deligneComponentsX6PrintedAb" || l == "geomConnOfAlgClosure")
        | _ => false) ||
      [`ShimuraGlue.DeligneComponentsX6PrintedAb, `ShimuraGlue.DeligneComponentsX6Printed,
       `HDec.QMSplit.Moduli.GeomConnOfAlgClosure, `HDec.LeafAdopt.R1pi0Props, `HDec.LeafAdopt.R1R2fpRep,
       `HDec.HSyn.sixContactMin_of_open29, `HDec.HSyn.sixContactMin_of_open17,
       `HDec.QMSplit.Moduli.r1r2_of_published].contains n
    logInfo m!"{root}: closure {s.size} constants; forbidden constants in closure: {bad}"

namespace ZInQ.Contrib.TYZChain.Pi0PruneCheck
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `frozenTarget` with `sixContactMin_of_open29` replaced by `sixContactMin_of_open29_pruned` (same statement). -/
theorem frozenTarget_pruned
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29_pruned r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

/-- `frozenTarget` from the bundles minus the two fields (`OpenAddedLeaves17P`). -/
theorem frozenTarget_P
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17P)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29P r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain.Pi0PruneCheck

#print axioms ZInQ.Contrib.TYZChain.Pi0PruneCheck.frozenTarget_pruned
#print axioms ZInQ.Contrib.TYZChain.Pi0PruneCheck.frozenTarget_P
