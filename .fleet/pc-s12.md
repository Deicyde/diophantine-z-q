# pc-s12 (fork issue #83, round 2): Theorem 5.2 from the printed Theorem 5.3

**Result (compiled, only standard axioms):**
`ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine` in
`ZInQKernel/Contrib/OneProof/PoleCompletenessFromRCGenuine.lean` proves `Manuscript.PoleCompleteness`
(Theorem 5.2) from `SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3 as printed, P :=
SelmerCorankOne) and five statements:
- `Lemma54` (lem:corank over Tau Ceti's Sel₂/Sel_{2^∞}; cited leaf, Poonen–Stoll);
- `KummerSelmerM` (#Sel₂(E_ℓ/ℚ) = #SelM ℓ; textbook GLUE, Silverman X.1.4; the one GLUE left);
- `BCDTThmA`, `KolyvaginThm1` (r = 1, with finite Ш), `MordellWeil` (printed leaves).

**Proved this round** (`ZInQKernel/Contrib/OneProof/PoleS12/`, from S12, ELLIOT (supplement)):
- `MatrixRealization` (S12 par:simultaneous-matrices: K♯, deletion, block, Boolean toggles, CRT+Dirichlet);
- the dimension-three count with every local condition (S12 par:descent): 2-adic necessity (incl. the
  mod-8 step), b ≡ 1 (mod 4) from the bad-prime equations, the eight classes local at 2, 3, q | ℓ,
  and `LocalGoodUnram` (via 𝔽_p: Kummer map onto by counting, then Hensel on x);
- so round 1's `LocalTwo/Three/Bad/Good`, `DimThreeCount`, `SimultaneousConstruction` are all gone;
- support bound (e): `selM_finite`; Lemma 5.5 from BCDT + Kolyvagin; Lemma54At from Lemma54 + Kummer.

**Manuscript check** (docs/research/pc-s12.md): 22 rows over tex L1019–1121; no error; every round-1
gap is filled by S12 and now compiles; S11 not needed (not available under that name). Known issues:
`a` undefined in tex L1045, D₁ notation, Boolean step correct only because one determinant varies,
Kolyvagin a preprint, Silverman bibitem lists Ch. IV/VII only (Ch. X used).

**Remains:** `KummerSelmerM` (Tau Ceti has only the one-root Kummer map), the printed leaves, Theorem 5.3.
#discharges (34 open, 16366 checked): no PoleS12 discharge, since (PoleCompleteness is not in frozenTarget); autofold not applicable.
Report: docs/research/pc-s12.md; log: scratch/pc-s12/log.md.
