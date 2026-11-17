# Historical native port attempts — summary only

This file is a narrative summary, not compiler stdout. Complete original failed
and cancelled logs are preserved unchanged privately and omitted from the public
tree. No failed attempt is evidence of a successful proof or axiom check.

The initial factoring attempt exposed two namespace issues: promoted private
root helpers lost dot-notation lookup across import boundaries, and a scoped
polynomial open selected a local namesake. The affected chains were cancelled
before applying a shared correction. Transparent private root abbreviations
restored field lookup without assuming any mathematical statement, and scoped
opens were made absolute.

Subsequent compatibility corrections selected tensor-product induction
explicitly, pinned definition/equality expressions before unfolding or casts,
and included attribute-prefixed private definitions in the bridge map while
retaining their attributes and bodies. Later checks also removed confirmed
absent optional export entries, made an existing adic-completeness proof explicit,
proved inverse-conjugation cancellation, closed an implicit factoring scope, and
updated TFAE indices to their 1-based convention.

The corrected 23 proof parts, six facades, and auxiliary helper then compiled.
The final original solution signatures and standard axiom lists are selected
verbatim in `PUBLIC_TYPE_AXIOM_EXCERPTS.md`. That file is labeled as excerpts,
not a complete raw transcript. No H102 discharge or integration is claimed by
this historical summary.
