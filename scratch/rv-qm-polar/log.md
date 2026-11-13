# rv-qm-polar results log

Marks: VERIFIED (read/computed/compiled), STANDARD (published, reference), SPECULATIVE.
Theorem numbers from memory: UNVERIFIED (no network).

## Step 1. Exact computations (`polar_checks.py`, ~/pyenv/bin/python; all VERIFIED, exact arithmetic)

Setting: B = (2,-3) (i^2=2, j^2=-3, k=ij), O = Z<1, i, (1+j)/2, (i+k)/2>, mu = 2j+k (N5 L410-420).
- mu^2 = -6.
- Twisting elements (Rotger's sense): chi2 = i (i^2 = 2), chi3 = j+k ((j+k)^2 = 3), both in O, both
  anticommute with mu; i(j+k) = mu. Ad(i), Ad(j+k), Ad(mu) commute with dag_mu(x) = mu^-1 xbar mu
  on the basis of O. So the Atkin-Lehner group W (classes of i, j+k, mu in N_B(O)/Q^* O^*)
  preserves the Rosati type mu.
- Elements of B anticommuting with mu: a*i + b*(j+k), reduced norm -2a^2-3b^2 < 0 (never +-1 over Q
  unless a=b=0... norm -1 would need 2a^2+3b^2 = 1, impossible: (2,3) local obstruction; recorded
  only as the computed formula).
- Other types: 12 pure mu' in O with mu'^2 = -6 and coordinates in [-6,6]; for each, the form
  E_mu'(x,y) = trd(mu'^-1 x ybar) has integral Gram matrix of determinant 1 on N5's basis.
  Example mu' = 2j - k: Gram [[0,0,-1,-1],[0,0,-1,-2],[1,1,0,0],[1,2,0,0]] (not a multiple of
  N5's Gram [[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]]); dag_mu'((1+j)/2) differs from
  dag_mu((1+j)/2) (k-coordinate +1 versus -1).
- mu' = 2j-k = -v' mu v'^-1 with v' = -1+i in O, nrd v' = -1 (so type mu' is the transport of
  type mu by the automorphism iota(v')).
- All 12 small mu' are conjugate to +-mu by a unit of O with coordinates in [-4,4] (466 units).
  Evidence (not proof) that O^* acts transitively on {mu' in O : mu'^2 = -6}/+-1.
- mu^-1 (u mu u^-1) lies in O with reduced norm 1 for all 126 units u of O with coordinates in
  [-2,2] (the PEL twist by an inner automorphism transports lambda by an element of O^1).

## Step 2. Lean: `QMPolar.lean` (Mathlib only) — COMPILED

`lake env lean scratch/rv-qm-polar/QMPolar.lean`: no errors (linter warnings only), about 1 min.
`#print axioms` for `two_principal_types`, `Enu_not_rosati_mu`, `type_eq_mu_mul`, `dag_conj_chi3`,
`chi3_normalizes`, `w_eq_chi_mul`: [propext, Classical.choice, Quot.sound]. VERIFIED.
§§1-4 copied from scratch/bp-qmmoduli/QMOrder.lean (O, mu, dag, E0, eq_smul_E0,
eq_pm_E0_of_principal). New:
- `two_principal_types`: E0 and E_nu (nu = 2j - k, nu^2 = -6, nu in O) are both alternating,
  Gram determinant 1 on O, compatible with their own involutions x -> c^-1 xbar c; E_nu is not a
  rational multiple of E0. `Enu_not_rosati_mu`: E_nu is not compatible with dag_mu.
  `dagNu_ne_dag`: the two involutions differ on (1+j)/2. `nu_conj`: nu*v = -(v*mu), v = -1+i,
  nrd v = -1.
- `type_eq_mu_mul`: for every c in O with c*c = -6 there is v in O with c = mu*v, nrd v = 1,
  dag v = v, and E_c(x,y) = E0(x, v*y) for all x, y (E_c(x,y) = trd(c^-1 x ybar)).
- `chi2_mem`, `chi3_mem`, `chi2_sq` (= 2), `chi3_sq` (= 3), `chi2_mu`, `chi3_mu` (anticommute
  with mu), `chi2_chi3` (= mu), `chi2_normalizes`, `chi3_normalizes`, `dag_conj_chi2/3/mu`
  ((chi x chi^-1)^dag = chi x^dag chi^-1), `w_eq_chi_mul` (bp-qmmoduli's w2 = 1+i+j and w3 = j
  are chi2, chi3 times units of norm -1).
- `twist_type` (added, compiled, axioms [propext, Classical.choice, Quot.sound]): for every ring
  automorphism alpha of O, alpha(mu) = mu*v with v in O, nrd v = 1, dag v = v. (The type-mu
  polarization of (A, iota o alpha) is lambda o iota(+-v): the twist is a functor automorphism of
  the PEL problem of type mu, in families.)

## Step 3. Findings (report docs/research/rv-qm-polar.md)

- Verdict: PREMISE HOLDS WITH CONDITIONS. Lemma P: for FIXED mu in O, mu^2 = -6, an abelian
  surface (A, iota) in char 0 has exactly one principal polarization of type mu (Rosati restricts
  to b -> mu^-1 bbar mu on iota(O)); also at CM points. Without the type: one per c in O,
  c^2 = -6, up to sign (infinitely many; type_eq_mu_mul, two_principal_types). Conditions:
  C1 type fixed, C2 char 0, C3 O maximal, C4 isomorphisms automatic, twists via twist_type.
- Leaves (R1fpProps, X6Props, R1heckeProps, R2X6Props/R2fpProps, CMExists, X6Surj, R1recProps,
  R1rec, R5ptProps, R5fp, R5fpCount): each lambda-free form is a consequence of the published
  type-mu PEL statement + Lemma P. No Lean statement corrected; docstring repairs listed (§4).
- Glue: A4, A7 (unpolarized, compiled), NV step 2, h-b1 M9 use no lambda: unaffected. Polarized
  A7 (N5 L532) follows from W_0 = W for D = 6 (dag_conj_chi2/3/mu). rv-jac-ext N1 gets lambda over
  K from Lemma P (descent).
- Published locators (UNVERIFIED): Buzzard 1997 p. 592 (cited by N5 v14 for the uniqueness);
  Rotger Crelle 561 (2003) §§3-4; Rotger Trans. AMS 356 (2004) §§2-4; Boutot-Carayol III.
- SPECULATIVE: pi_0(A) = 1 for D = 6 when End(A) = O (evidence: 12 small solutions all
  O^*-conjugate to +-mu).
