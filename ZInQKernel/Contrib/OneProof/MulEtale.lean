import ZInQKernel.Contrib.MulEtale.Direct.NativeChecks

/-!
# Multiplication by a unit is étale on an abelian scheme over any commutative base

The textbook hypothesis `mulEtaleAbelianScheme` of the single proof (BLR 7.3 Lemma 2; Mumford, GIT
§6), proved with no restriction on the base by the contribution in `ZInQKernel/Contrib/MulEtale/`
(fork PR #19). This file only names that theorem at the contributor location.
-/

namespace ZInQ.Contrib.OneProof.MulEtale

/-- **`[m]` is étale on an abelian scheme over `Spec O` when `m` is a unit in `O`**, for every
commutative ring `O` (`H101DirectFieldRoute.multiplication_etale`). -/
theorem mulEtaleAbelianScheme_proof : _root_.AvSplit.T4.MulEtaleAbelianScheme :=
  H101DirectFieldRoute.NativeChecks.mulEtale

end ZInQ.Contrib.OneProof.MulEtale
