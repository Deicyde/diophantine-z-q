# rv-h-c3: second review of lem:de-rham-descent (C3 of H)

**Verdict: the lemma holds as stated** (N5 L10939-10992), and its conclusion is exactly what N5
uses at L733-741 and L755-768. Every step checks out: Scholze's comparison has its hypotheses met
(F is finite over Q_l and has characteristic 0); then duals, summands, the Hilbert 90 descent
F' -> K (filtered) and the weights {0,0,-1,-1} -> {0,-1} at every component of K (x) C_l. There is
no counterexample: being de Rham, and the HT weights, depend only on the restriction to any finite
extension. The lemma's hypothesis matches the application (K = Q_l, F = L'_lambda). On G_L',
mu = 1, a = 1 and beta = 1, so rho_l is the Tate action (VERIFIED against N5 L632-731). My verdict
was written before reading rv-h-trust and agrees with its §2.1.

**Repairs (wording and citations only).**
- R1: add the routine step "de Rham over F => de Rham over F'".
- R2: swap the [P] sources (Milne notes, Brinon-Conrad). h-trust's proposed "Fontaine Ast. 223
  Exp. VIII" may be the wrong exposé: from memory, VIII is the l-adic pst exposé and III has the de
  Rham formalism (SPECULATIVE).
- R3: see below.
- Optional: pst follows directly (a summand of V_l(A_F) (x) C_l, pst by SGA 7 semistable reduction
  plus C_st), so the descent paragraph and Berger are not load-bearing. This corrects rv-h-trust §3.

**Most serious issue (C8, not C3, and harmless).** "k = 2 and power zero" holds only if rho_g is
normalized to weights {0,1-k} (trace of arithmetic Frobenius = a_p). Pan fixes geometric Frobenius.
In the cohomological normalization the power is 1. Still k = 2, and the end result is the same,
because rho^coh (x) eps = rho^Tate (x) finite. PARI confirms the Tate normalization on 4 curves,
p < 200 (scratch/rv-h-c3/frob_norm.py).

**Consequence for H.** C3 now has two independent model reviews, both positive, and it is no
longer the thinnest N5-only passage. H's trust statement needs no change beyond R1-R3.

**Single next step:** check the Fontaine Ast. 223 exposé numbers and Scholze's Cor. 1.8 (journal
and corrigendum) against the sources, then apply R1-R3 to h-trust C3/C8.

Full note: docs/research/rv-h-c3.md; log: scratch/rv-h-c3/log.md.
