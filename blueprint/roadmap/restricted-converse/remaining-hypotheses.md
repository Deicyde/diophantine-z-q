---
article_id: af_dc151131341c0ee3cad47e0a
declaration: structure
origin: bridged
statement: formalized
lean: ZInQ.Manuscript.RC.Wiring.RCLeaves
---

# The remaining hypotheses

Every hypothesis of the Lean proof of Theorem 5.3 that remains beyond [the cited results](printed-results.md)
is a field of one structure. Each field records the manuscript lines it covers and whether it is a printed
result or a step between results. The fields are:
- printed results: Hoffstein–Luo on nonvanishing twists, Shimura's 1973 theorem on conjugate eigenforms
  and Li's 1975 strong multiplicity one in weight two;
- two readings of the literature: the elliptic curve of a rational newform and its Euler factors (Shimura
  with Carayol), and Faltings' 1983 isogeny theorem in its local-factor form;
- the coefficient data of the proof, chosen for each genus partner, with the steps of Sections 7–9 and
  Appendices E–G that do not involve the odd minimum depth, and those that do.

None of the fields is proved here.

The interface data are chosen by whoever discharges the structure and are constrained only by the fields.
Several step fields are stated in a form equivalent or close to the conclusion of the manuscript step they
cover (see the module docstring of `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean`), so the reduction
is only as strong as those fields.

## Depends on

- [Theorem 5.3: the restricted converse](restricted-converse.md)

## Sources

- [Section 7](../../sources/manuscript.md#section-7)
- [Section 8](../../sources/manuscript.md#section-8)
- [Section 9](../../sources/manuscript.md#section-9)
- [Appendix E](../../sources/manuscript.md#appendix-e)
- [Appendix F](../../sources/manuscript.md#appendix-f)
- [Appendix G](../../sources/manuscript.md#appendix-g)
