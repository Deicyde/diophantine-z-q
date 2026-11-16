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
