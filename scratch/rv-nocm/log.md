# rv-nocm results log

## Computations
- `nocm_check.py` (pure Python 3, no PARI: `~/pyenv` and cypari2 are absent on this host and no
  network install was attempted), output `nocm_check.output.txt`. VERIFIED (computed):
  - Part A: on the 24 non-elliptic rows of Elkies' Table 1 (rational points of X*), (Emb) holds,
    `2^b h(R) = 4` = fibre size in every row; the unqualified `#CM(R) = h(R)` contradicts the
    4-point fibre in 15 of 24 rows (all rows with b >= 1, e.g. |D| = 19: h = 1, 4 points).
    The 9 rows with b = 0 are exactly the rows where `#CM = h` holds.
    Elliptic: |D| = 4, 3: h = 1, b = 1, 2 points each; |D| = 24: h = 2, b = 0, 2 points.
  - Part B: fibre fields on X6 agree with GR Thm 5.12 (degree 2h with K inside if b >= 1;
    degree h, K not inside, if b = 0) in all 24 rows; [K.Q(x):K] = h; unramified-outside-f
    consistency check passes.
  - Part C: D = -24: on X* the point t = 0 (j = -16/27) is rational, [H_R:Q(j)] = 4; on X6 the
    points over t = 0 have Q(x) = Q(sqrt -3), index 2 in H_R = Q(sqrt -6, sqrt 2).
  - Part D: X6 -> P^1_t has index 2 at t = 0, 1, inf. |(O/3O)^*| = 72, nrd-kernel mod 3 = 36,
    [Gamma*:Gamma_3] = 72 (x 2 components = 144 = h-b1 M3). Riemann-Hurwitz for a component
    of Y3 over P^1_j: indices (4,6,2) give g = 4; indices (2,2,2) give g = -17 (impossible).
    Of the 6 assignments of {4,6,2} to (0, inf, -16/27), only (4,6,2) makes "p not | M_S(u)
    => unramified" hold.

## Lean
- `OrbifoldIndex.lean`: COMPILES (`lake env lean`, 2026-11-12 ~01:21), no sorry; axioms
  [propext, Classical.choice, Quot.sound] (labelling: [propext, Quot.sound]).
  - `orbitStab N x` (stabilizer of an N-orbit), `orbitStab_eq_sup : orbitStab N x = N ⊔ Stab x`,
    `relIndex_orbitStab : N ⊓ Stab x = ⊥ → [orbitStab N x : N] = |Stab x|`,
    `inf_stabilizer_eq_bot` (torsion-free N, finite stabilizer), `ramification_eq_orbifold_order`.
  - `rh_462` (deg 72, indices 4,6,2: g = 4), `rh_222_impossible`, `euler_ratio`,
    `labelling` (only (4,6,2) among permutations), `inertia_trivial_of_dvd` (needed direction
    holds for any indices dividing (4,6,2)).

## Findings (statements)
- NoCM (h-cm 4.1.4 and rv-h-cm 7.2): the arguments use `#CM(R) = 2^b h(R)` (h-cm, JGR) or
  `#CM(R) = h(R)` only when D(R) = 1, i.e. b = 0 (rv-h-cm 7.2) — both correct. VERIFIED by
  reading. The unqualified leaf `#CM(R) = h(R) for (f,6)=1` appears in h-decomposition R5,
  glue-repo L14 (A10 table), Leaves.lean `R05_GonzalezRotger` docstring, hdec-elementary
  l.252: FALSE as stated (Part A; e.g. |D| = 4: h = 1 but two Z[i]-CM points on X6).
- Every field-of-definition claim in NoCM is on X6 = X0(6,1) (GR's own curve), none on X* or Y3.
  VERIFIED by reading h-cm 4.1.4, rv-h-cm 2.3 and 7.2.
- A5 needs the indices of Y3 -> P^1_j (Prop. TS inertia `e/gcd(e,m)`; Lemma NV step 3), which
  equal the orbifold orders (4,6,2) of Gamma* since Gamma_3 is torsion-free and normal
  (manuscript l.488-490 says so). Lemma NV step 4 uses the indices 2 of X6 -> P^1_j, derived
  internally. The leaf texts "X6/W branched with indices 4,6,2" (h-decomposition R2, glue-repo
  L2, Leaves.lean R02 docstring, pkg-I1 A2 row) misdescribe the finite map.
- `Neat.lean`: COMPILES (`lake env lean`, ~01:40), no sorry, axioms [propext, Classical.choice,
  Quot.sound]. `RvNocm.Neat.eq_zero_of_pow_eq_one`: for `B = ℍ[ℚ,2,0,-3]`, `y = comb n ∈ 𝒪`,
  `(1 + 3y)^m = 1`, `m > 0` ⇒ `y = 0` (so `Γ₃` is torsion-free and `−1 ∉ 1 + 3𝒪`). Proof by
  `nrd ≡ 1 mod 3` ⇒ `nrd = 1`, Cayley–Hamilton, growth of `p_{j+2} = t p_{j+1} − p_j` for
  `|t| = |2 − 9K| ≥ 7`, anisotropy of the norm form (`norm_descent` copied from glue-repo
  `A1Quaternion.lean`). Also `nrd_pow`, `normInt`, `nrd_comb`, `comb_eq_zero_of_normInt`,
  `cayley_hamilton`, `pseq`, `pow_formula`, `pseq_growth`, `pseq_ne_zero`.
