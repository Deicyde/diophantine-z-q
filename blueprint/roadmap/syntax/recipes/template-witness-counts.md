---
article_id: af_d39cd2ab708fcb0972372183
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.templateLibrary_params, ZInQ.Syntax.templateLibrary_witnesses
---

# Parameter and witness counts of the templates

The $23$ templates of the library, as constructed, have the parameter and witness counts
of the library table: $\mathtt{member}$ $(5,7)$, $\mathtt{raw\_add}$ $(15,6)$, $\mathtt{raw\_z}$
$(7,1)$, $\mathtt{raw\_inverse\_x}$ $(7,0)$, $\mathtt{log25}$ $(4,0)$, $\mathtt{pole}$ $(1,11)$,
$\mathtt{test\_group}$ $(44,162)$, $\mathtt{slope}$ $(22,1298)$, $\mathtt{height\_certificate}$
$(36,35106)$, $\mathtt{multiply.scalar}$ $(10,1)$, $\mathtt{multiply.guard}$ $(15,1)$,
$\mathtt{multiply}$ $(15,35134)$, $\mathtt{natural}$ $(5,140604)$, $\mathtt{value.signed\_encode}$
$(10,140654)$, $\mathtt{value.abs}$ $(2,4)$, $\mathtt{value.close\_coordinates}$ $(16,53)$,
$\mathtt{value.test}$ $(11,35282)$, $\mathtt{value.exceptions}$ $(6,406)$ and
$\mathtt{scalar.integer\_constant}_k$ $(10,1)$ for $k=0,\dots,4$.

This is a closed decidable statement about the constructed templates: run each
construction's allocation counter. The counts do not depend on any fixed constant. By
hand: $162=40+4(7+6)+8\cdot7+2+12$; $1298=7+6(24+162+24+3)+2+11$;
$35106=3\cdot11+9(3+3\cdot1298)$; $35134=3+4\cdot6+35106+1$; $140604=40+4\cdot35134+10+18$;
$140654=15+7+7+140604+6+3+6+6$; $53=16+21+3+8+1+4$;
$35282=25+49+35134+12+20+6+5+2+12+3+2+1+11$; $406=3+36\cdot11+7$.

## Depends on

- [The template library](../templates/template-library.md)

## Proof depends on

- [Template construction from formulas](../language/builder-soundness.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
