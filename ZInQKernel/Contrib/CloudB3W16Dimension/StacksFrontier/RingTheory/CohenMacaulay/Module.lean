module

public import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.RingTheory.CohenMacaulay.Module.DepthCoheight
public import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.RingTheory.CohenMacaulay.Module.GoodElement
public import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.RingTheory.CohenMacaulay.Module.DimensionDrop
public import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.RingTheory.CohenMacaulay.Module.RegularSequenceExtension

-- Match upstream elaboration settings; enable current Mathlib defeq compatibility.
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.defeqAttrib.useBackward true


/-!
# Cohen-Macaulay modules

This file was split into the following parts, which it re-exports:

* `StacksFrontier.RingTheory.CohenMacaulay.Module.DepthCoheight` : good elements (Stacks 00N2) and
  the depth-coheight bound for Cohen-Macaulay modules (Stacks 0AUJ);
* `StacksFrontier.RingTheory.CohenMacaulay.Module.GoodElement` : quotients by good elements
  (Stacks 00N4) and the depth-coheight bound Stacks 00LK;
* `StacksFrontier.RingTheory.CohenMacaulay.Module.DimensionDrop` : cutting a Cohen-Macaulay module
  by a dimension-dropping element;
* `StacksFrontier.RingTheory.CohenMacaulay.Module.RegularSequenceExtension` : extending a
  dimension-dropping family to a maximal regular sequence (Stacks 00N6), the basic API of
  `IsCohenMacaulayModule`, and restriction of scalars (Stacks 0AAD).
-/
