import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.Contrib.CloudW08EigenformTwists.Bridge

/-!
# H-33 proved: `PkgI4.EigenformTwist`

Row H-33 of `docs/research/frontier.md` (`t24 : EigenformTwist`, K ModCurves/C9.lean:373;
issue elliotglazer/diophantine-z-q#83). The kernel Prop `PkgI4.EigenformTwist`, stated in
`ZInQKernel/HDecomp/ModCurves/C9.lean` §7 (fixed at fork `main` `cba8157f`, byte-identical at the
working base `f70ec251`) and unchanged here, as a closed theorem, from
`ZInQ.Contrib.CloudW08EigenformTwists.eigenformTwist` (`Bridge.lean`), whose witness is Tau Ceti's
twist `CuspForm.twist` (vendored under `ZInQKernel/Contrib/TauCeti/`, Apache-2.0).

This is not Atkin–Li's `AtkinLiTwistNew` (`ZInQKernel/Contrib/GZTheta/Split.lean`, proved in
`ALFinal.lean`), a different Prop (newness at level `M r²` of the twist of a weight-2 newform with
trivial nebentypus by `(·/r)`); it is neither used nor reproved here. Both rest on the same Tau
Ceti `CuspForm.twist`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ZInQ.Contrib.CloudW08EigenformTwists

/-- **H-33 / T24 `PkgI4.EigenformTwist`** (twisting a normalized eigenform by a Dirichlet
character; Shimura 1971 Prop. 3.64), proved. -/
theorem EigenformTwist_proof : PkgI4.EigenformTwist :=
  eigenformTwist

end ZInQ.Contrib.CloudW08EigenformTwists
