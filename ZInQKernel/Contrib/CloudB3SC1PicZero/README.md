# Pic⁰ identity-component contribution

This directory records the focused `picZeroAbVar` contribution in progress.
The unchanged target is `T09Pic.PicZeroAbVar`, declared in
`ZInQKernel/OneProof/H/TailZ24.lean`.

The proposed proof reduces that target to explicitly projectivity-retaining
instances of Kleiman's Picard-scheme statements over genuine scheme and
relative fppf Picard-functor definitions. It reuses the existing open-component
group-object construction rather than reproving or modifying it.

## Source located

Stephen L. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry*
(FGA Explained), AMS Mathematical Surveys and Monographs 123 (2005), Chapter 9.
The author's preprint, arXiv `math/0504020v1`, was read at Remark 5.24,
pp. 50–51, and Theorem 4.8(1), p. 27. The chapter-prefixed book locators
are Remark 9.5.24 and Theorem 9.4.8; the book page numbers remain unverified.

Remark 5.24 states that for a projective abelian scheme over a Noetherian
base, its Picard identity component exists and is a projective abelian scheme.
Over a field this supplies smoothness and properness. The projectivity
hypothesis is retained explicitly; its abelian-variety instance follows from
the already-proved `T09Pic.exists_isVeryAmple`.

The open-subgroup construction is available in the existing `PicDictionary`
source at revision `4e95795b509f1bf8e381a405b04b836f1b59885f`. Only the
necessary proof material will be reused, with attribution. Unrelated
Weil-pairing, cube, square, degree and isogeny work is outside this contribution.

## Current validation boundary

This is a draft claim, not a completed proof or discharge. No compiler,
axiom, independent-review or fold result is asserted here. The final
contribution must compile on Lean 4.35.0 and the unchanged Mathlib pin,
match the exact original target, and include the prescribed complete
`#discharges` output. Printed hypotheses, if any, will remain explicit.

Source reading is AI-assisted, not a human-reading acceptance or a change
of any repository source-review flag. No existing module, statement,
assembly or dependency pin is changed.
