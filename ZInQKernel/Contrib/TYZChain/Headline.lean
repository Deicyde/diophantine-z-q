import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.MainLiterature

/-!
# TYZ chain: the headline theorem with the TYZ side replaced by its leaves

Task tyz-chain (2026-11-14). `TYZChainLeaves` bundles the four hypotheses (all leaves) of
`tyzThm35ReadingA_of_leaves` (for an assembly that takes structures of leaves), and
`frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves` is the fork's headline
(`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`)
with `TYZThm35ReadingA` replaced by these leaves and the two proved providers
`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5` filled in.

No `sorry`, no `axiom`.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **The remaining TYZ-side hypotheses (four leaves, no glue)** (see `tyzThm35ReadingA_of_leaves` for sources). -/
structure TYZChainLeaves : Prop where
  /-- LEAF: TYZ Theorem 1.1, first assertion, odd case (`𝓛(m) ∈ ℤ`). -/
  thm11Integral : TYZThm11Integral
  /-- LEAF: TYZ Lemma 2.9 with Proposition 2.3, modulo 2. -/
  lemma29Mod2 : TYZLemma29Mod2
  /-- LEAF (textbook): main theorem of complex multiplication for rational modular functions on
  `X₀(N)` at Heegner points (Shimura 1971 Thm. 5.4 + canonical model; UNVERIFIED). -/
  shimuraModFn : Shimura.ShimuraReciprocityModFn
  /-- LEAF: TYZ Theorem 3.3 with Lemma 3.14 for the pinned CM points, every sign choice of `𝓛`. -/
  thm33Pinned : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ

/-- Reading A from the bundled leaves. -/
theorem tyzThm35ReadingA_of_tyzChainLeaves (t : TYZChainLeaves) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves t.thm11Integral t.lemma29Mod2 t.shimuraModFn t.thm33Pinned

/-- **Theorem 1.1 ("ℤ is Diophantine in ℚ", `ZInQ.FrozenTarget`) from `SixContactMin`, Gross–Zagier
and the TYZ-side leaves**: the fork's headline with `TYZThm35ReadingA` replaced by
`TYZChainLeaves` and `HeckeContinuation`, `FunctionalEquation5` discharged by the registered
providers. -/
theorem frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves (hH : ZInQ.SixContactMin)
    (hG : ZInQ.Literature.GrossZagier) (t : TYZChainLeaves) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    hH (tyzThm35ReadingA_of_tyzChainLeaves t) ZInQ.Contrib.heckeContinuation
    ZInQ.Contrib.functionalEquation5 hG

end ZInQ.Contrib.TYZChain
