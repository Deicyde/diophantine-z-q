# sga1-fix results log

Base: wip/gaga-chart 5626f0b0. Build tree copied (cp -r) from ~/dzq-wt/gaga-chart (same commit, full build incl. GAGAChart).

## Plan (fixed 11-16 06:50)
1. New leaf `SGA1_XII_3_3a`: topological half only (Q ↦ (f_i Q) local homeomorphism), SGA 1 XII Rem. 3.3(a).
   Regular-functions half proved in Lean from étaleness alone: Mathlib `Algebra.IsEtaleAt.exists_isStandardEtale`
   (Stacks 00UE) + analytic inverse function theorem (`OpenPartialHomeomorph.analyticAt_symm'`).
2. New leaf `SGA1_XII_2_4`: X loc. fin. type, X preconnected ⇒ X^an preconnected.
3. Concrete sheaf of holomorphic functions on X^an (`AnFunAt`: locally H ∘ (regular functions), H analytic) and
   analytic morphisms (`IsAnMorphism`); prove IsAnStr-holomorphic ⇔ AnFun; new atlas-free GAGA leaf.

## 11-16 07:10 A.lean, B.lean (VERIFIED compiled)
- A.lean: `exists_analytic_of_standardEtale` (standard étale presentation over ℂ[y] + ring maps `ev z` over `y z`,
  `y`, `ev · x` continuous ⇒ every element is locally `h ∘ y`, `h` analytic). Analytic inverse function theorem
  for Φ(y,τ) = (y, f(y;τ)). Standard axioms.
- B.lean: `regular_half` (half (2) of sga1-etale's leaf, from étaleness only: `Algebra.IsEtaleAt.exists_isStandardEtale`
  on D(s) ∋ P). `#print axioms regular_half`: [propext, Classical.choice, Quot.sound].
  `sga1_XII_3_1_Etale_of_3_3a`, `connectedPreconnectedAn_of_2_4`, `uniformizationLeafAll_of_printed`
  (from MumfordComplexTorus, SGA1_XII_3_3a, ProperCompactAn, SGA1_XII_2_4): standard axioms.

## 11-16 07:30 C.lean (VERIFIED compiled, all standard axioms)
- `AnFunAt`/`AnFunOn` (structure sheaf of reduced X^an: locally H ∘ (regular g), H analytic), `IsAnMorphism`
  (continuous + pulls back AnFun), leaf `SGA1_XII_4_4` (IsAnMorphism A(ℂ) → B(ℂ) is P ↦ P ≫ f).
- `contMDiffAt_iff_anFunAt` (any IsAnStr atlas), `contMDiff_iff_isAnMorphism`, `anFunAt_iff_etale`
  (AnFun = pullback of holomorphic functions along étale coordinates, X smooth, from SGA1_XII_3_3a),
  `isAnStr_of_3_3a`, `gagaChart_of_printed`, `printed_of_gagaChart`, `gagaChart_iff_printed (hL)`,
  `gagaMorphism_of_printed (hM hL hPC hC hG)`. All [propext, Classical.choice, Quot.sound].

## 11-16 07:50 contribution module + #discharges (VERIFIED)
- `ZInQKernel/Contrib/OneProof/SGA1Printed.lean` (C.lean minus #print, docstrings); `lake build
  ZInQKernel.Contrib.OneProof.SGA1Printed` OK (9084 jobs, no warnings in the file).
- `lake env lean scratch/sga1-fix/DischargesCheck.lean` → discharges.txt:
  gagaMorphism by gagaMorphism_of_printed, still assumes [MumfordComplexTorus, SGA1_XII_3_3a, ProperCompactAn,
  SGA1_XII_2_4, SGA1_XII_4_4]; uniformizationLeafAll by uniformizationLeafAll_of_printed, still assumes the first
  four. Axioms standard. "#discharges: 63 open hypotheses, 1976 theorems checked, 17 discharge one".

## 11-16 08:00 autofold (VERIFIED)
- `scratch/sga1-fix/autofold.json`: discharges uniformizationLeafAll and gagaMorphism (textbook bundle); leaves
  mumfordComplexTorus, sga1_XII_3_3a, properCompactAn, sga1_XII_2_4 (under the first), sga1_XII_4_4 (second).
- `autofold.py --dry-run` exit 0: "strict count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11" (this base
  rates both fields LEAF). With the two rows set to GLUE as in the 11-16 re-rating (origin/wip/leaf-fold32,
  temporary edit of kinds.tsv, restored): "44/12 on 56 -> 49/10 on 59; strictest 43/13 -> 48/11" = -2 GLUE.
- FoldDryRun.lean (dry run minus line 1) compiles; sixContactMin_of_open30 axioms standard.
