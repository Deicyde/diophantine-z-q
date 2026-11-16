# sga1-fix results log

Base: wip/gaga-chart 5626f0b0. Build tree copied (cp -r) from ~/dzq-wt/gaga-chart (same commit, full build incl. GAGAChart).

## Plan (fixed 11-16 06:50)
1. New leaf `SGA1_XII_3_3a`: topological half only (Q ↦ (f_i Q) local homeomorphism), SGA 1 XII Rem. 3.3(a).
   Regular-functions half proved in Lean from étaleness alone: Mathlib `Algebra.IsEtaleAt.exists_isStandardEtale`
   (Stacks 00UE) + analytic inverse function theorem (`OpenPartialHomeomorph.analyticAt_symm'`).
2. New leaf `SGA1_XII_2_4`: X loc. fin. type, X preconnected ⇒ X^an preconnected.
3. Concrete sheaf of holomorphic functions on X^an (`AnFunAt`: locally H ∘ (regular functions), H analytic) and
   analytic morphisms (`IsAnMorphism`); prove IsAnStr-holomorphic ⇔ AnFun; new atlas-free GAGA leaf.
