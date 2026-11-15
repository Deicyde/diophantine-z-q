# holfam log

## Setup
- Base 822da7b5 (composite-out). Build tree copied from ~/dzq-wt/composite-out (.lake/build, lean/.lake/build).
- unif-printed (origin/wip/unif-printed) had no report commit at start (tip 43513d87 = leaf-fold25): nothing to merge.

## Findings
- VERIFIED (read): ShimuraSplit2.ShimuraHolFamilyAb = ∃ (Y,Φ) R1fpPropsAb ∧ ∃ yτ, IsShimuraHolFamily (moduli clause as QM pair + ShimuraSplit.IsHolFamily).
- VERIFIED (read): none of uniformizationLeafAll, GAGAMorphism (single abelian varieties, TailQ.lean:875), HomLatticeCorr,
  R1fpPropsAb (R1univAbProps only for algebraic families over proper smooth curves over ℚ), mumfordGroupLaw, MainTheoremCM
  speaks of a family over ℍ. SPECULATIVE judgement: holomorphy in τ cannot be derived from them (needs a relative
  analytic/algebraic comparison); agrees with composite-out §2.
- Route chosen: new leaf PELHolFamily = Deligne's M_{K3} with its universal QMAbScheme and holomorphic [τ,1];
  no fine witness in the statement. Transport to every fine witness via R1univAbProps + ShimuraSplit2.isHolFamily_comp.

## Compiles
- ZInQKernel/Contrib/OneProof/HolFamilyPrinted.lean: `lake env lean` 0 errors 0 warnings, 1m32 (compile1.txt). VERIFIED.
- `lake build +Main +Discharges +HolFamilyPrinted`: success, 12999 jobs (build1.txt). VERIFIED.
- `#discharges` (Discharges-output.txt): 63 open, 2223 checked, 7 discharge one (all pre-existing); no field matched
  by HolFamilyPrinted (expected: bypass, composite not proved as stated). All 7 theorems: [propext, Classical.choice, Quot.sound]. VERIFIED.
- BypassFold.lean (composite-out's dry run, shimuraHolModAll -> pelHolFamily): sixContactMin_of_open31 and
  frozenTarget_holfam standard axioms (BypassFold-output.txt). VERIFIED.
- autofold.json written (bypass; leaves mainTheoremCM published, pelHolFamily published + pending reading of analytic clause).
- Rating note: deligneComponentsX6PrintedAb (same moduli content as clause (R)) is kinds.tsv published/LEAF with
  "locator UNVERIFIED"; under that standard pelHolFamily is LEAF and the fold is -1 strict GLUE. SPECULATIVE.
