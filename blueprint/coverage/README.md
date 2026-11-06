# Coverage contract

| Area | Coverage | Evidence |
| --- | --- | --- |
| Section 1: main theorem and assembly | `MAPPED` | The target and the conditional main theorem are stated in the first chapter; Lemma 1.2 still needs its own decomposition. |
| Section 2 and Appendix C: literal finite specification | `DECOMPOSED` | The [specification chapter](../roadmap/syntax/README.md) defines the expression language, every template, constant, constructor and recipe, and the polynomial; correctness of each template is assigned to the chapter that uses it. |
| Section 3: elliptic model, generator and addition | `DECOMPOSED` | The [elliptic model chapter](../roadmap/model/README.md) covers the field, the descent, the heights and the finite search, membership and raw addition. |
| Section 4: proof of the six-contact estimate | `OUT` | Uses Shimura curves, integral models and modularity, which are not formalizable here; its conclusion is the hypothesis H in the first chapter. |
| Section 5: pole predicate | `MAPPED` | Lemma 5.1 is elementary and awaits decomposition; Theorem 5.2 is the hypothesis PC in the first chapter. |
| Section 5.1 and Sections 7–9, Appendices E–G: restricted converse | `OUT` | Uses Kato, Waldspurger, Bump–Friedberg–Hoffstein, Nekovář and Gross–Zagier–Kolyvagin; replaced by the hypothesis PC. |
| Section 6: multiplication and the false-triple guard | `MAPPED` | Awaiting decomposition; Proposition 6.2 is the hypothesis 22P in the first chapter. |
| Section 10: precision computation and compilation | `MAPPED` | Awaiting decomposition of the natural polynomial, the alpha and power formulas and the rational translation. |
| Section 11: variable-shift relation | `MAPPED` | Awaiting decomposition. |
| Section 12: cutoff and polynomial size | `MAPPED` | Awaiting decomposition; the progression estimate enters as the hypothesis CAT in the first chapter. |
| Section 13: consequences | `DEFERRED` | The three corollaries follow the main theorem and are scheduled after it. |
| Appendix H: de Rham comparison in the height argument | `OUT` | Part of the proof of the six-contact estimate, replaced by the hypothesis H. |
