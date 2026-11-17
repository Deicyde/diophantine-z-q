import ZInQKernel.Contrib.OneProof.JavanpeykarFix.Basic
import ZInQKernel.Contrib.OneProof.JavanpeykarFix.BelyiMap

/-! # javanpeykar-fix: `JavanpeykarBound` from printed leaves only

Task javanpeykar-fix (2026-11-16), report `docs/research/javanpeykar-fix.md`, scratch
`scratch/javanpeykar-fix/`.

**Target.** The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound`
(`ZInQKernel/OneProof/H/TailY.lean`). javanpeykar-dict proved it from `JavanpeykarDict.JavanpeykarPrinted`
and Stichtenoth's theorem; the review rated `JavanpeykarPrinted` GLUE for four dictionary steps:
(a) the kernel height is `GroupModel.height` of the Néron model, not the printed stable height;
(b) only the `K`-to-`ℚ̄` half of the Belyi translation was proved, not function field to morphism;
(c) the print says projective where the leaf says proper; (d) `V_ℚ̄ = Jac X` was asserted, not proved.

**Result.** `javanpeykarBound_of_printed_fix : JavanpeykarPrintedMap → ConstantFieldExtensionUnramifiedFull →
UniformizationLeafAll → MumfordTorsionAlgClosed → JavanpeykarBound`, where
* `JavanpeykarPrintedMap` (`JavanpeykarFix/Basic.lean`) is Javanpeykar's Thm 1.1.1 for `X = X₀ ×_K ℚ̄`
  over height-dict's printed stable height `IsPrintedStableHeight` (a), with a Belyi *map*
  `X → ℙ¹_ℚ̄ = Proj ℚ̄[X₀, X₁]` (finite, unramified at closed points over `ℙ¹ ∖ {0, 1, ∞}`, of degree `d`)
  (b), `X` projective (c), and `Jac(X)` an abelian variety over `ℚ̄` representing `Pic⁰_{X/ℚ̄}` with a
  model `V` over `K` (d);
* `ConstantFieldExtensionUnramifiedFull` (`JavanpeykarFix/Basic.lean`) is Stichtenoth's Thm 3.6.3(a)
  with his standing hypothesis that `K` is the full constant field of `F`;
* `UniformizationLeafAll`, `MumfordTorsionAlgClosed` are the existing textbook fields giving T35
  (height-dict's `isPrintedStableHeight_of`).
Proved glue: (a) height-dict's identification; (b) `belyiMapOfFunction_proof` (`JavanpeykarFix/BelyiMap.lean`);
(c) `exists_closedImmersion_projectiveSpace`; (d) `exists_jacBar`; the full constant field of `K(X)`
(`fullConstantField_of_bijective`, from `K(X) ⊗_K K̄ ≅ K̄(X_K̄)`, i.e. from `X` geometrically integral).

No `sorry`, no `axiom`. -/

namespace JavanpeykarFix

/-- **`javanpeykarBound` from printed leaves only** (Javanpeykar 2014 Thm 1.1.1 in its printed terms,
Stichtenoth Thm 3.6.3(a), and the textbook fields giving T35). -/
theorem javanpeykarBound_of_printed_fix (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFull)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.JavanpeykarBound :=
  javanpeykarBound_of_map hJ hS belyiMapOfFunction_proof hUL hMT

end JavanpeykarFix
