---
article_id: af_d38993d579aa24520aa860cc
---

# An ineffective height estimate through von Känel's bound

[nasqret/z-in-q-lean](https://github.com/nasqret/z-in-q-lean) is a separate Lean project on the same theorem,
described in fork issue #104. It builds on the congruent-number route: it pins a commit of
elliotglazer/diophantine-z-q that contains that route's Lean.

Besides a theorem that assumes the minimal height hypothesis with its exact constants (as fork issue #104
records), it proves a qualitative theorem: some integer polynomial has rational zero projection to its first
variable exactly $\mathbb Z$, with no bound on its number of variables, its degree or its coefficients. For that theorem it
derives a six-contact height estimate with an unknown constant from ten statements, among them results on
Prym varieties, Guitart's descent, cluster pictures, Serre–Tate theory and von Känel's bound. Its own
documentation says that several of its hypotheses still have to be identified with their published
constructions.

The estimate is ineffective: its constant is not explicit, so it cannot give the minimal height hypothesis
or the bounds of Theorem 1.1. It is not a route to the target statement of this blueprint and has no chapter
here; it is recorded as another way to a height estimate. The height input of both headlines comes from
[the height-decomposition chapter](height-decomposition/README.md). The Lean of this estimate is in that
project, not in this repository.
