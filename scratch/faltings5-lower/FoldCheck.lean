import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower

/-! faltings5-lower: check of the manual fold (scratch; not a module). `sixContactMin_of_open17'` is
`HDec.HSyn.sixContactMin_of_open17` (ZInQKernel/OneProof/H/TailZ23.lean L811-814) with the term at L814
replaced; `open18'` ... `open28'` are copies of `open18` ... `open28` (TailZ24 L835, TailZ25 L136, TailZ26 L192,
TailZ27 L124, TailZ28 L123, TailZ29 L120, TailZ30 L73, TailZ31 L69, TailZ32 L45, TailZ33 L121, TailZ34 L171)
calling the primed predecessor; `frozenTarget'` is `ZInQ.OneProof.frozenTarget` (Main.lean L57-67) on `open28'`.
The closure test then lists which `faltingsLemma5` constants the new top theorem still reaches. -/

namespace HDec

namespace HSyn

theorem sixContactMin_of_open17' (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l) t (addedLeaves9_of_open14 r t l) g
    (_root_.ReductSplit.faltingsLemma5BCLower_final
      _root_.GapHeight.faltingsLemma5Lower) hYu

theorem sixContactMin_of_open18' (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves13)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open17' r t (addedLeaves12_of_open13 l) g hYu

theorem sixContactMin_of_open19' (r : OpenResearchLeaves15) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves13) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open18' (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu

theorem sixContactMin_of_open20' (r : OpenResearchLeaves16) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open19' (openResearchLeaves15_of_OpenResearchLeaves16 r) t (openAddedLeaves13_of_OpenAddedLeaves14 l) g hYu

theorem sixContactMin_of_open21' (r : OpenResearchLeaves17) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open20' (openResearchLeaves16_of_OpenResearchLeaves17 r) t l g hYu

theorem sixContactMin_of_open22' (r : OpenResearchLeaves18) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open21' (openResearchLeaves17_of_OpenResearchLeaves18 r) t l g hYu

theorem sixContactMin_of_open23' (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open22' (openResearchLeaves18_of_OpenResearchLeaves19 r) t l g hYu

theorem sixContactMin_of_open24' (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves15) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open23' r t (openAddedLeaves14_of_OpenAddedLeaves15 l t) g
    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed)

theorem sixContactMin_of_open25' (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open24' r t (openAddedLeaves15_of_OpenAddedLeaves16 l) g

theorem sixContactMin_of_open26' (r : OpenResearchLeaves19) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open25' r (openTextbookLeaves10_of_OpenTextbookLeaves11 t) l g

theorem sixContactMin_of_open27' (r : OpenResearchLeaves20) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open26' (openResearchLeaves19_of_OpenResearchLeaves20 r t) t l g

theorem sixContactMin_of_open28' (r : OpenResearchLeaves21) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open27' (openResearchLeaves20_of_OpenResearchLeaves21 r t) t (openAddedLeaves16_of_OpenAddedLeaves17 l) g

end HSyn

end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget'
    (r : HDec.HSyn.OpenResearchLeaves21) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open28' r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget'

open Lean Meta Elab Command

partial def f5Closure' (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for c in ci.type.getUsedConstants do
        unless seen.contains c do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless seen.contains c do todo := todo.push c
    | none => pure ()
  return seen

elab "#liveUses' " root:ident : command => do
  let env ← getEnv
  let s := f5Closure' env root.getId
  let hits := s.toList.filter fun n =>
    let str := n.toString
    (str.splitOn "altingsLemma5").length > 1 || (str.splitOn "ilneIsogeny").length > 1
  logInfo m!"{root.getId}: {s.size} constants in closure; matches: {hits}"

#liveUses' ZInQ.Contrib.TYZChain.frozenTarget'
#liveUses' ZInQ.OneProof.frozenTarget
