# tyz-5b log

## Step 0 (setup)
- No earlier run. Sources: TYZ arXiv:1411.4728v1 (only version; Period7.tex), Smith arXiv:1603.08479v2
  (cnc.tex, cnc2.tex) downloaded to a temp dir outside the repo. PARI via cypari2 in a temp venv.
- Slot-k output: |n| = |beta| q0 * (glue primes = 1 mod 8), |beta| = 7 mod 8, q0 = 3 mod 8,
  so |n| = 5 mod 8, n odd; theta = 1 mod 8 so |n theta| = 5 mod 8. Only row 5b needed; row 6 never.

## Step 1 (TYZ statement) -- findings
- TYZ Thm 1.2 (label lg') = Thm 3.5(2) (label m3), arXiv v1 Section 1 and Section 3.1.
- Statement combines the brackets: "first sum = second sum = 0 mod 2". For n = 5 mod 8 the
  second sum contains the (7,3) terms (= Smith 5b) and (5,1) terms.
- Proof of Thm 3.5(2) (last subsubsection of Section 3, "Proof of Theorem m3: part (2)") shows
  separately: coefficient of tau(1/2) (d0 = 7, d1 = 1,3 => d1 = 3) is even, and coefficient of
  tau((1-i)/2) (d0 = 5) is even. The tau(1/2) bracket is exactly Smith's 5b sum, with no
  ambiguity about d1 = 1 (d1 = 3 mod 8 forces d1 > 1).
- If d1 = 1 is allowed in the statement (as the proof needs: Z(n) term), statement-level sums are
  5a and 5a+5b, so "5b odd => certified" follows from the statement itself. Literal reading
  (d1 > 1) gives second sum = 5a + 5b + g(n); then one needs the proof's separate bracket.
