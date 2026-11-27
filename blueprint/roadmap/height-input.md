---
article_id: af_28ee2b89c71b8f992d7ca972
---

# The height input

The construction uses one instance of the manuscript's six-contact height estimate (its Theorem 4.1), the
[minimal height hypothesis](multiplication/certificate/six-contact-min.md): for every rational $u$ outside the six contact values,
$h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}$, with an explicit constant. Both headlines assume it. It is not a
published theorem: its proof combines refereed theorems and exact computations with new arguments, the
manuscript's and this project's, reviewed only by AI models.

**The manuscript's proof: the height decomposition.** [The height-decomposition chapter](height-decomposition/README.md)
follows the manuscript's proof of Theorem 4.1 and reduces the minimal height hypothesis in Lean to open statements:
published theorems, consequences of them, statements from unrefereed sources and a few of the manuscript's
own claims, on a Shimura curve of discriminant 6, complex multiplication, abelian varieties,
Néron models, Faltings heights, $p$-adic Hodge theory and modular forms. Lean proves every step from those
statements to the hypothesis; the statements themselves are open, and the chapter gives each one's form, its
difference from the print and its source. The chapter is regenerated after each fold by
`scripts/one_proof/vault_chapter/gen.py`.

**The $j$-form.** The hypothesis may also be assumed as a bound on the height of the Hauptmodul value (not a
published theorem), from which [the minimal form is proved](main/j-form/README.md).

**Another way to a height estimate.** A separate project, nasqret/z-in-q-lean, reaches a six-contact height
estimate with an unknown constant through von Känel's bound. Its constant is not explicit, so it cannot give
the minimal height hypothesis or the bounds of Theorem 1.1 ([a note on it](height-von-kanel-note.md)).
