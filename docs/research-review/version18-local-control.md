# Version 18 local-control application at two

This candidate follows PR108's certificate and halving change. It incorporates only the two repeated local-control applications, old S21/S22, from the unaccepted 31-block source candidate. It addresses the source comparison in `43664822557-2-fable-F108-1`; it does not claim to close the other source, history or incorporation findings. Author-prepared record, not an independent gate acceptance.

Base manuscript SHA256 `d6966b1921ff796d0f26592be5579e644f40085745f193c600210c1b198e9028`. Candidate SHA256 `ca1ea465a0ebae934162a2c278186ab09477a91f14b60eefa71c5398ee71a165`. The current Version17 selector, all released V16/V17 files, polynomial, variable count, statement environments and labels are unchanged.

| Application | Base lines | Candidate lines |
|---|---:|---:|
| 1 | 19111-19123 | 19111-19139 |
| 2 | 19166-19177 | 19182-19194 |

## Published input, actual object and map

Nekovar, *Selmer complexes*, Asterisque310 (2006), Corollary8.4.8.2(i), printed p.215, gives the injection from the coinvariants of degree-j Iwasawa cohomology into degree-j continuous cohomology. It assumes a profinite G, closed normal H with quotient Gamma isomorphic to Z_p, and the admissible finite-type coefficient complex over its standing complete local ring. The extra finite-cohomological-dimension assumption is in part(ii), not part(i). For the inverse-limit interpretation, Proposition8.3.5(ii), pp.203-204 applies under finite cohomology of finite discrete modules.

Here R=Z_2, T_chi=T_2(E) tensor a quadratic sign character, G=G_Q2 and H is the kernel of the local real-cyclotomic Z_2 quotient. T_chi is a finite free continuous lattice and hence admissible, by 3.2.4 and4.1.1. The local groups have the required finite cohomology. The actual corestriction limit is therefore the group to which the corollary applies. At j=2 it injects M_chi/(gamma-1) into H^2(Q_2,T_chi). Inverting two is flat. Changing the deck convention from gamma to its inverse multiplies gamma-1 by a unit and preserves the augmentation ideal. Rational restriction/corestriction separates the finite sign component before applying this Z_2 statement; no integral division by two is asserted.

The Weil pairing and chi squared equal to one identify V_chi dual(1) with V_chi. Trivialize chi over a finite extension and use finite local elliptic torsion to obtain zero invariants. Local Tate duality kills H^2(Q_2,V_chi). The injection kills the augmentation quotient. Kato, Asterisque295 (2004), (12.2.3), printed p.220, supplies the finite generation and degree-two torsion input. Nakayama after localization at the augmentation prime excludes that prime from the characteristic element. The fixed finite list of local types permits their product, with a fixed power of two to clear denominators. This gives the existing nonzero value F_2(0) consumed by the length comparison. No assertion about vanishing of a third Iwasawa group is needed.

Both applications use the same lattice, tower, direction of maps and argument. Nothing here re-audits the global Euler-system construction or changes its index set.

## Source access and review history

The [official Nekovar PDF](https://www.numdam.org/item/AST_2006__310__R1_0.pdf#page=224) has printed p.215 at PDF page224 and SHA256 `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`. It is about43MB; the full-PDF reader may reject its size even though direct download works. The indexed primary source can also be located by searching `site:numdam.org "8.4.8.2" "Corollary"`. The [official Kato PDF](https://www.numdam.org/article/AST_2004__295__117_0.pdf#page=105) has printed p.220 at PDF page105. The [Nekovar book correction list](https://webusers.imj-prg.fr/~jan.nekovar/pu/selerr.pdf) is the book errata, not a similarly named parity-paper correction. No source scan or extended book quotation is committed.

The earlier PR107 Astra review reported a favorable scoped check; PR108's Fable reviewer could not retrieve the source and did not accept it. A further native Astra source check compared the published PDF, hypotheses and both consumers; its local report is available through the operator. These observations do not replace this PR's required independent reviewers or imply whole-proof acceptance. An unavailable source must be reported as such, not treated as verified by this author summary.
