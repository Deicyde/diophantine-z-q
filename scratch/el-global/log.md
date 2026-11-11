# el-global step log

Marks: VERIFIED (script here or proof), STANDARD (reference), SPECULATIVE.

## Definitions (step 1)

- `A = Res_{K0/Q} E`, abelian surface over Q; `A(Q) = E(K0) = Z P0 + T` (T = E[2], order 4; index_two_E = 8).
- Data space `Y = A^1_t x A^1_q x {eta, bits} x A^m` (data labels: [n]P0, [h]P0, [s0]P0, [h-k]P0, [s0-kn]P0).
  Tests (SixLocalTests.lean:40): D1 = w([h]P0), D2 = w([s0]P0), D3 = w([h-k]P0)^*, D4 = w([s0-kn]P0)^*,
  D5 = z([s0]P0)/z([h]P0) - t, D6 = (z([s0-kn]P0)/z([h-k]P0))^* - t; w = 1/x, z = -x/y.
- Label gadget: `X ⊂ Y x A^s x A^w` (s extra labels, w further witnesses), Phi'(y) :<=> X_y(Q) nonempty.
  A finite correspondence Z ⊂ Y x A^s is part of the equations of X.
- Honest set `H ⊂ (Y x A^s)(Q)`: honest data plus the labels the honest prover uses; `V' = Zariski closure of H`.
- Soundness notions, for p > p0:
  - LUS: no x in X(Q_p) over Bad_p.
  - label-global: no x in X(Q_p) over Bad_p whose label coordinates lie in A(Q)^s and data labels in A(Q)^m.
  - MW-adelic: no adelic family whose labels come from one element of the closure Zhat P0 + T of A(Q) in A(A_f).
  - global: no x in X(Q) over Bad.
- V' is *t-free* if V' = A^1_t x pr(V') (t algebraically independent of the other coordinates on H).

## Step 2: Theorem GG, statements (proofs in step 3)

Hypothesis (P11): on the slice {labels fixed, q fixed}, B has an odd pole (order 11) along t = c for every
contact c (rv-barrier C5 with arbitrary D_j; E1 below with genuine label coordinates).

- **GG-A (label slicing, local, unconditional).** If X -> Y x A^s has RC generic fibre (R1 of rv-barrier),
  then for honest data labels lab0 and labels L0 in A(Q)^s outside a proper Zariski-closed set there is a
  positive-density set of p and x in X(Q_p) over Bad_p with data labels lab0 and label L0. So the
  globality of L adds nothing to local soundness. (Lemma G' applied to the slice {lab0} x {L0}.)
- **GG-B (explicit completeness => global unsoundness, unconditional).** If V' is t-free and the honest
  non-label witnesses are values of a Q-rational map Lam on V', then X has bad rational points: all
  coordinates honest except t (and Lam). No RC hypothesis.
- **GG-C (RC completeness => global unsoundness under Colliot-Thelene's conjecture).** If V' is t-free and
  X -> V' has RC generic fibre, then CT's conjecture (X(Q) dense in X(A)^Br for smooth proper RC X)
  gives rational bad points close to an honest point at any finite set of places other than p (in
  particular real-close: the Close conjunct still holds). Unconditional where the slice total space has
  weak approximation (e.g. Q-rational with a point; quadric bundles of rank >= 5).
- **GG-D (residual cases).** If V' is not t-free, or X -> V' is not RC, completeness needs per instance a
  rational point on a non-RC variety (column form: a curve of genus >= 1 in (q, L); t-slice through a
  fixed label: a curve of genus >= 2 by Riemann-Hurwitz over the six contacts) or a point of A(Q)^s on
  a proper subvariety H_{n,lab} (a Mordell-Lang intersection). Neither is supplied by holding a label.
