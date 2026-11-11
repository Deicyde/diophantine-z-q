# up-h work log

## Step 0 (setup)
- Fresh start (no earlier log). Prior related note: docs/research/h-v14.md (V14 §4 audit, 2026-11-10).
- Upstream: ~/upstream @ d76bcde (codex/version16-fable-corrections); ~/upstream-p214 @ 110cf72.

## Step 1 (locate the H analogs)
- Working copies (CR stripped, outside repo): /tmp/up-h/v13.tex (22087 lines), v14 (24347), v15 (39896, from research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex), v16 (39932), n5 (11259).
- `thm:height` "Six-contact estimate": V13 L480; V14 L682; V15 L707; V16 L707 (sec:height V13/V14 L448, V15/V16 L473).
- V15/V16 add a new section `v15:height` "Integral evaluation and the effective contact height": V15 L30155, V16 L30186; subsections "The five-contact height estimate" V15 L30658 / V16 L30689; "Numerical constants in the contact-height bound" (`v15:numerical-height`) V15 L30871 / V16 L30902.
- p214 (~/upstream-p214 @110cf72): research/quartic214/{README.md,PROOF.md,proofs/*.md,contracts/*.json}. PROOF.md: field Q(sqrt2), ten contacts Θ∪(2−Θ), Θ={0,−1/2,−1,1/2399,−32/407}; height via modular-Jacobian (X_1(N_level)/ker ε) and height-averaging; "H4 proves h(u)<C2 M_S10(u)^(2103/1024)"; uniform-existence P08–P10 h(t_j)≤H2 M_j^(7/6); M2 and N0 "fixed and ineffective".

## Step 2 (statement and constants of thm:height)
- VERIFIED (diff of the block "Set ... \end{align*}" plus the theorem statement): identical in N5 (L378-409), V13 (L454-475, L480-485), V14 (L454-475, L682-687), V15 (L479-500, L707-712), V16 (L479-500, L707-712). C={0,-15,-20,-24,-30,-60}, M_S, F_0=324!, D, G_0, E_0, Q_R, B_cm, C_cm, H_6(S;R); h(u) ≤ H_6(S;R) M_S(u)^24.
- V15/V16 add after the align block: "The constants in the displayed definition of H_6(S;R) are unchanged" (V16 L503-504).

## Step 3 (where the height estimates are used in V16)
- V16 thm:target (L113, 292890231905 variables) proof: "Theorem thm:height proves H for each of the two sets of constants used below" (L219). So the target the fork formalizes still uses the six-contact estimate, unchanged.
- V16 other height estimates (all for the quartic constructions, not for thm:target):
  - hyp:o8-height "The five-contact height estimate" L7651: S_*={p≤76176}, D={0,1,2401,-343/32}, contacts ∞,0,1,2401,-343/32; h(a) ≤ H_* M_5(a)^24, H_*=2(4608^165888+6^100)(∏_{p≤76176}p)^24+128 (L7640-7650), log2 H_*<4783227. Proof starts from the Shimura curve of the disc-210 quaternion algebra, genus 5, González–Rotger 2006 Thm 4.2/Table 2 models (L7660-7680). L7622: "Theorem thm:height uses a different contact set".
  - thm:quartic-height19 L10005: h(a) ≤ H_19 M_5(a)^19, A_19=2^109 210^1800, H_19=2A_19 B_*^19+128, log2 H_19<2093966; reuses the construction of hyp:o8-height.
  - v15:height:thm:contactheight L30758ff (section v15:height L30186): h(a) ≤ C_3 M_5^3(1+log M_5), C_3=19 D_0 B_*^3 log B_* < 2^330770, D_0=4608·210^300; h(a)<2^330789 M_5^{7/2}. Input: Lemma "Modular realization" v15:height:def:input (L30710ff; proof L30730-30732 points to thm:quartic-height19): CM alternative h_F(A)<854R, else A_{L'} isogeny factor of Jac(X_1(N)/ker ε), [L':Q]≤2304φ(R), N≤210^300 R^2, rad N | R.
- V16 abstract (L58-70): featured objects are the 292890231905-variable polynomial, the 314-variable quartic (thm:v15-decimal L100) and the 222-variable family with ineffective N_0 (thm:v15-main L104).

## Step 4 (diff of sec:height across V13-V16; V15→V16 diff)
- sec:height spans: V13 L448-1048 (601 lines), V14 L448-1680 (1233), V15 L473-1704 (1232), V16 L473-1704 (1232).
- VERIFIED `diff`: V16 sec:height == V15 sec:height (0 changed lines).
- VERIFIED `diff` V14→V15 sec:height: only the b11-integral-model-project citations change: V14 L784-785 (offset 337-338) "\cite[§13.3]{voight2021} in \cite{b11-integral-model-project}" → "\cite[§13.3]{voight2021}" (V15 L809); V14 L808 → "Section v15:marking-descent" (V15 L832); V14 L870 → "faithful, by the integral-lattice proof in Section v15:tate-polarized" (V15 L894); V14 L912 "[scheme provider, §§4–6]{b11-...}" → "Section v15:marking-descent" (V15 L936); V14 L1117 → "Section v15:marking-descent" (V15 L1141). (V15 line = V14 line + 24 or +25 by offset; exact lines to be rechecked.)
- VERIFIED `diff v15 v16` (whole file): title/date; Tao–Ziegler adaptation (V16 L20060-20077); nilsequence lift fix (V16 L26822-26842, L26908-26915); GR citations: V15 L30633,30646 `gr2014` → V16 L30664,30677 `gr-periods2014`; new bibitem gr-periods2014 V16 L39342-39346 (Gaudron–Rémond, Théorème des périodes et degrés minimaux d'isogénies, Comment. Math. Helv. 89 (2014) 343–403, §2.3 and Cor. 8.4); AI statement. No change in sec:height.

## Step 5 (new in-manuscript sections replacing b11 supplement)
- V16 (=V15 content) appendix sections, read in full: `v15:tate-polarized` V16 L30096-30107 (Tate module of an abelian surface, finite generation of integral End by a lattice argument, finiteness of pointed polarized automorphisms; inputs Milne 1986 §§8, 12, 17); `v15:marking-descent` V16 L30109-30122 (R=Z[1/30]; X_35→X_5 finite étale via Isom sheaf (Stacks 03RV), projectivity 0B3I/01W7; free G_5=(O/5O)^× action, quotient Y=X_35/G_5 (07S7), descent 02LA/02VN/036U/02L6/03GN/0BD4/0B45; abelian scheme descent 0CCJ/023Q/02L1/02VL; BLR §8.4 Cor. 6 p.234 regular-base projectivity; BLR §8.2 Thm 1, Prop 4, §8.4 Thm 5 for dual; principal polarization descends; identifies full-three moduli problem "without an extra five-marking factor in its degree"); `v15:picard-norm` L30124-30132 and `v15:cm-reduction` L30134-30184 concern the 222/aggregate parts (X_1(N), CM points), not thm:height.
- Section headers: V15 L30065 etc. not rechecked; V16 numbers above.

## Step 6 (Gaudron–Rémond citations)
- §4 GR cites, all to `gr2014` = Duke 163 (2014) 2057-2108 "Polarisations et isogénies" (bibitem N5 L11063-11066, V16 L39347-39350): CM branch Thm 1.4 (N5 L615, V13 L691, V14 L1298, V15/V16 L1322); transfer Thm 1.4 (N5 L878, V13 L954, V14 L1575, V15/V16 L1599); Bost lower bound "recorded in [Section 9]" (N5 L895, V13 L971, V14 L1592, V15/V16 L1616). Unchanged in V16.
- V16 correction (only in v15:height, proof of lem:surface): V16 L30664 Bost lower bound h_F(E) ≥ −log(π√2) dim E, "see [§2.3 and Corollary 8.4]{gr-periods2014}" (V15 L30633 had gr2014); V16 L30677 isogeny variation ≤ ½ log deg, "see [§2.3]{gr-periods2014}" (V15 L30646 had gr2014). gr-periods2014 = CMH 89 (2014) 343-403 (V16 L39342-39346). Isogeny bound there: [Thm 1.9(1)]{v15-height-GaudronRemond} (V16 L30672), a different (2023?) GR paper — check bibitem.
- Upstream V16 records (read): research/version16/RELEASE-NOTES.md L5 (three changes incl. "two corrected Gaudron–Rémond citations"); FINDINGS.json L12-17 ("Two existing inequalities cite wrong Gaudron–Rémond paper"); APPLICATIONS.json L27-41 (lines 30664, 30677; "Bibliography correction only. Preserve gr2014 Duke key for Theorem1.4/Section9 applications"); review/current/REVIEW.md L25-27 (CMH §2.3 pp.351-352: h_F = h − (g/2)log π, h ≥ −(g/2)log(2π) ⇒ h_F ≥ −g log(π√2) > −3g/2; §2.3 additivity and h_F(A) ≤ h_F(B)+½log D; Cor 8.4 p.400; "separate Duke gr2014 entry and its earlier Theorem 1.4 and Section 9 uses remain intact").
- N5 L893-905 / V16 L1615-1620: "general lower bound h_F(Z) ≥ −3/2 dim Z ≥ −2g is recorded in [Section 9]{gr2014}" + "Additivity and height variation" (uncited). h-trust E3 (Duke Thm 1.4) and E4 (Bost via Duke §9, ASTRA-READ; variation via Faltings 1983 Lemma 5 / Raynaud) — compare in note.
- Audit PDF research/version16/audits/fable-5-2-audit-4.pdf not text-searchable here (no pdftotext/pypdf).
