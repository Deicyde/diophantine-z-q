# rv-routek log (findings and computations)

## Computations
- `checks.py` (output `checks.output.txt`, ALL OK):
  - `|GL4(F3)| = 24261120`, `|GL4(Z/4)| = 1321205760`, `G0 = |GL4(F5)| = 116064000000`; both
    alternatives are `<= G0`, so hdec-elementary's switch to `A[4]` at `p = 3` keeps `D G0`.
  - `2 + 2U0 = 2 + 8(DG0)^2 <= 10(DG0)^2 = E0` (N5 L716 defines `E0 = 10(DG0)^2`), so
    `f_p(B) <= 2 dim B (1 + U0) <= dim B * E0` (G16 -> G17).
  - `2^(v2(p-1)-1) <= (p-1)/2` for odd `p < 2000`: the degree that an odd nebentypus at `p` forces
    is bounded by the `p`-factor of `m <= 2R^R M` (hdec-alt §1.1 (ii)).
  - S4 model of the Ind/Mackey facts in G14/G16: `Ind_{A4}^{S4} chi` is trivial on `V4` (normal in
    `S4`, inside `ker chi`); control case nontrivial; Frobenius reciprocity
    `<r, Ind_H r|_H> = <r|_H, r|_H>` for `H = A4, V4` (values 2, 4).
- `ind_conductor.py` (output `ind_conductor.output.txt`): 28 (field, p) pairs of Galois fields
  (cyclotomic and splitting fields of `x^k - a`): PARI's ramification groups give `v_p(disc)`
  equal to PARI's discriminant valuation, and `v_p(disc L) <= [L:Q](1 + u_last)` — the bound G16
  applies to the permutation part of `Ind_{G_L'}^{G_Q}`. ALL OK.

## Findings
- N5 L715: `L'` is the kernel field of `beta|G_L` (VERIFIED by reading). So N5's "above `U0` the
  upper groups lie in `G_L` and kill `beta`" gives `G^u ⊂ G_{L'}`, which G16 needs for the
  permutation part of the induced representation. Route P never needed this.
- N5 L813-817: wild inertia of `F = L_v(A[3])` (resp. `A[5]` at `p = 3`) acts trivially on
  **each** `V_ell(A)`, `ell != p` (VERIFIED by reading). So at `p = 3` route K can keep `A[5]`
  and use `ell = 2`; the `A[4]` switch is unnecessary (harmless).
- G14 (hdec-elementary §2.2): each step checked (Frobenius reciprocity for finite index;
  Faltings over Q for `B`; `V_tau ≅ W_tau^s`; dimension count). VERIFIED as an argument over
  STANDARD inputs.
- hdec-alt step 3: "for an embedding tau" must be "for some tau" unless L13 includes
  isotypicity of `B0_Qbar`; repair found (choose tau by Frobenius reciprocity on `G_K`).
- hdec-alt §1.1 (ii) ("dim B0 not bounded in M") is contradicted by G14: the factor `B` of
  `Res_{L'/Q} A` is GL2-type with `dim B <= 2[L':Q] <= 2QM`.
- hdec-elementary R2 ("Kisin's 2-adic result is not needed") concerns only the statement; the
  proof of Serre's conjecture for arbitrary level (KW II) uses Kisin's 2-adic modularity lifting
  (STANDARD reading, UNVERIFIED).
