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
