# h5-neron (fleet note)

**Main result.** H5 (stable Faltings height = published Néron-model height) is reduced in Lean
to two precisely stated leaves plus glue. All of the following is in `scratch/h5-neron/H5Neron.lean`
(compiled; 27 `#print axioms`, each only propext/Classical.choice/Quot.sound; no sorry):
- `stableFaltingsHeight_eq_neron_all`: from leaf **N1** `NeronModelExists` (BLR 1.4/3), leaf **N2**
  `SemistableNeronIdentityComponent` (SGA 7 IX 3.6 + 3.3), and glue `NeronModelMinimal`,
  `ModelHeightBaseChange`, `GroupModelBaseChangeExists`, `OpenSubgroupHeight`, there are `L₀` and
  a Néron model `𝒩₀` with h(A) = h(𝒩₀), and h(A) equals the Néron height over every `L' ⊇ L₀`.
  `compositum` is proved.
- `stableFaltingsHeight_add_le'`: h(A)+h(B) ≤ h(A×B) (the direction E4 uses) from N1,
  `NeronModelMinimal` and `ProductModelHeight` only. Two pieces of glue are proved: a product of
  Néron models is a Néron model, and `productGroupModelExists`. No semistable reduction is needed.
- Néron glue, proved: comparison map 𝒢 → 𝒩, uniqueness of Néron models, transport along isos.
- Non-vacuity in the only constructible case, the zero abelian variety `Spec K`: proved that
  h = 0, every group model has height 0, and StableHeightFinite, NeronModelMinimal, R19, R20,
  R21, N1, N2 and the glue all hold for it.

**Findings.**
- (a) `LeafAdopt.H5 = StableHeightFinite ∧ NeronModelMinimal` does not suffice for R19-R21.
  It compares models over a single L. Base change (N2 plus glue) is needed.
- (b) The Néron model does not commute with base change, even when A is semistable. Only its
  identity component does, so def-faltings and rv-blueprints should be reworded.
- (c) Additivity needs no semistable reduction.
- (d) NeronModelMinimal is glue, not a leaf.

An independent model review found no problem with N1, N2 or the glue. It flagged two docstring
inaccuracies, now fixed.

**Not provable now.** StableHeightFinite for any nonzero A, including elliptic curves: Mathlib
cannot construct a nonzero AbVar (AV7), and AN3 is still open. Products cannot be formed as an
AbVar either (Mathlib has no composition instance for GeometricallyIntegral).

**Remains.** Glue still to prove: `ModelHeightBaseChange`, `OpenSubgroupHeight`,
`NeronModelMinimal`, `ProductModelHeight`, `GroupModelBaseChangeExists`. For the last one,
`BaseChange.lean` compiles its monoid-morphism lemmas, but its final assembly hits a kernel
deterministic timeout caused by mismatched instance terms. Locators are UNVERIFIED.

Report: `docs/research/h5-neron.md`. Log: `scratch/h5-neron/log.md`.
