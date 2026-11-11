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
