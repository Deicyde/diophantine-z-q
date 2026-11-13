# gz-theta: Hecke's theorem for ψ₁ proved; L1 (HeckeThetaNewform) reduced to Atkin–Li

**Main result.** The leaf `ZInQ.GZDecomp.HeckeThetaNewform` follows from one standard theorem,
the Atkin–Li twist theorem (`AtkinLiTwistNew`: a newform of level `M`, trivial character, twisted
by the primitive quadratic character `(·/r)`, `r ≡ 1 mod 4` squarefree prime to `M`, is new at
level `M r²`; Atkin–Li 1978 Thm 3.1, UNVERIFIED locator). Everything specific to `ψ_d` is
proved in Lean, standard axioms only:

- `cmForm32 : CMForm32` — the theta series `∑ heckeCoeff 1 n qⁿ` of the Hecke character of
  `y² = x³ − x` is `η(4τ)²η(8τ)² ∈ S₂(Γ₀(32))` (modularity via a Euclidean multiplier for `η²`
  and Schreier generators of `Γ₀(32)` checked by `decide`; the `q`-expansion via Jacobi's triple
  product identity, proved here for Mathlib's `jacobiTheta₂`);
- `newAt32 : NewAt32` — it is new at level 32;
- `exists_eigenform_heckeCoeff` — `f_d = f₁ ⊗ (·/d)` is a Hecke eigenform (all `T_n`) on
  `Γ₁(32 d²)`, trivial nebentypus, `q`-expansion `∑ heckeCoeff d n qⁿ`;
- `heckeThetaNewform_of_atkinLi : AtkinLiTwistNew → HeckeThetaNewform`;
- `frozenTarget_of_sixContactMin_tyzThm35ReadingA_atkinLi_gzLeaves : SixContactMin →
  TYZThm35ReadingA → AtkinLiTwistNew → FHNonvanishing → GrossZagierHeegner → FrozenTarget`.

**What compiles.** New files `ZInQKernel/Contrib/GZTheta/{Basic, BadCoeff, Eta, Eta32, EtaForm32,
Main, ThetaUnique, TripleProduct, JacobiGauss, HeckeComb, EtaTheta, Final, Split, New32}.lean`
(namespace `ZInQ.GZTheta`); `lake build ZInQKernel.Contrib.GZTheta.New32` builds them all.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for every theorem
(`scratch/gz-theta/out_check_axioms{,2,3}.txt`). One Tau Ceti module vendored unmodified from
tc-oct16: `Newforms/BadPrime/Vanishing.lean` (NOTICE entry; `diffcheck2.py` IDENT).
Other exact declarations proved: `jacobiTheta₂_eq_jtpP` (triple product), `eq_zero_of_theta_fe`,
`hasSum_jacobi`, `hasSum_gauss`, `etaThetaIdentity`, `etaForm32`, `etaQuot32_slash_eq`,
`eta_sq_mobius`, `heckeThetaNewform_of_newCM`, `heckeThetaNewform_of_badCoeffCM`,
`newCM_of_newAt32_atkinLi`.

**What remains.** `AtkinLiTwistNew` (`Split.lean`) — not in Tau Ceti (its `Newforms/Twist.lean`
gives the primitive associate of a twist but "the sharp level is not determined"). Equivalent
intermediate leaves, each also sufficient: `NewCM` (newness of `f_d` at `32 d²`) and `BadCoeffCM`.

Report: `docs/research/gz-theta.md`; log: `scratch/gz-theta/log.md`.
