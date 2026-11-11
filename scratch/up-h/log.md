# up-h work log

## Step 0 (setup)
- Fresh start (no earlier log). Prior related note: docs/research/h-v14.md (V14 §4 audit, 2026-11-10).
- Upstream: ~/upstream @ d76bcde (codex/version16-fable-corrections); ~/upstream-p214 @ 110cf72.

## Step 1 (locate the H analogs)
- Working copies (CR stripped, outside repo): /tmp/up-h/v13.tex (22087 lines), v14 (24347), v15 (39896, from research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex), v16 (39932), n5 (11259).
- `thm:height` "Six-contact estimate": V13 L480; V14 L682; V15 L707; V16 L707 (sec:height V13/V14 L448, V15/V16 L473).
- V15/V16 add a new section `v15:height` "Integral evaluation and the effective contact height": V15 L30155, V16 L30186; subsections "The five-contact height estimate" V15 L30658 / V16 L30689; "Numerical constants in the contact-height bound" (`v15:numerical-height`) V15 L30871 / V16 L30902.
- p214 (~/upstream-p214 @110cf72): research/quartic214/{README.md,PROOF.md,proofs/*.md,contracts/*.json}. PROOF.md: field Q(sqrt2), ten contacts Θ∪(2−Θ), Θ={0,−1/2,−1,1/2399,−32/407}; height via modular-Jacobian (X_1(N_level)/ker ε) and height-averaging; "H4 proves h(u)<C2 M_S10(u)^(2103/1024)"; uniform-existence P08–P10 h(t_j)≤H2 M_j^(7/6); M2 and N0 "fixed and ineffective".
