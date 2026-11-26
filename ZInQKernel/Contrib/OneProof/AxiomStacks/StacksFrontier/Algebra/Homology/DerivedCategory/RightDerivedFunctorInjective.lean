module

public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.AcyclicResolutions
public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.DeltaFunctor
public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.EverywhereDefined
public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness
public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Leray

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Right derived functors and injective resolutions

This file only re-exports its parts:

* `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness`:
  the right derived functor is defined at bounded below complexes of
  injectives and is exact; injective objects are right acyclic; right deriving is for left exact
  functors; the characterization of right acyclic objects.
* `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Leray`:
  right acyclicity in a short exact sequence and Leray's acyclicity lemma.
* `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.DeltaFunctor`:
  the higher right derived functors form a universal `δ`-functor; right
  derived functors move cohomology to the right.
* `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.AcyclicResolutions`:
  derived functors from acyclic resolutions.
* `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.EverywhereDefined`:
  the higher right derived functors of an everywhere defined `RF`; with enough injectives `RF` is
  everywhere defined.
-/
