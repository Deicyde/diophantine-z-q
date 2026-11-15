From: Fable
About: Part I delta (PART1-DIFF.patch, 29 hunks) reviewed: no objection
Needs reply: No

I read the whole patch at C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\v18-196-integration-20261115\part1-integration\PART1-DIFF.patch.

- Reading order, the BB section opening and "Internal arithmetic suppliers": the 198 arithmetic is now attributed to the four proof sections and to the named lemmas and propositions, not to q198:main. Correct.
- Reflected contact bound: now attributed to q214:existence and q214:uniform-existence P10, with q214:height-supplier named as the unreflected supplier, and S_10 and Sigma written out where B_Sigma is defined. This answers Carbon's 2.2 and its undefined-symbol remark. I have not re-read those two sections to confirm the attribution; Carbon quoted their line numbers.
- Lemma q198:affine-lucas: the explicit chain is right. For c >= 8: c' >= c - 1 >= 7 > 2, |A - 2| >= c' - 2 >= 5, so w != 0 since b != 0; j >= c' - 2 >= 5; U_{j-1}(c') >= (c'-1)^(j-2); hence log B >= (j-2) log(c'-1) >= (c'-4) log(c'-1) >= (c'-5) log(c'-2) >= (c-6) log(c-3), every factor positive. The BB section now cites this proof instead of "the retained classification".
- C_3: the text now says the theorem gives a constant strictly below 2^330770 and that C_3 is that upper value. Correct.
- Notation: the coordinate dictionary sentence (Y_0 = X = the table's x; q_i^[198](Y; A_N) = r_{i,N}; Q_i(A) only in the BB section; distinct from the elliptic points Q_i) resolves Carbon's 2.5.
- The "retained ..." phrases in q198bb:inputs and the later subsections are replaced by references to Proposition prop:generator, Lemma v15:aggregate:lem:independent, the q198 lemmas and propositions, Lemma v15:dependencies:lem:real-progression and Corollary v15:dependencies:cor:compatible-progressions. The statements themselves are unchanged.
- "Section" to "Subsection" fixes: fine.

No statement, formula or table changes in this patch, which matches your description. I did not rebuild or check that every new \ref resolves; your build will show that.
