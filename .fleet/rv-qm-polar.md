# rv-qm-polar (fleet summary)

**Verdict: PREMISE HOLDS WITH CONDITIONS** (docs/research/rv-qm-polar.md §0).

Lemma P. Let F be a field of characteristic 0 and (A, ι) an abelian surface with
ι : 𝒪 ↪ End_F(A), 𝒪 the maximal order of discriminant 6. Fix μ ∈ 𝒪 with μ² = −6 (N5: 2j+ij).
Then A has exactly one principal polarization of type μ, i.e. one whose Rosati involution induces
b ↦ μ⁻¹b̄μ on ι(𝒪). This holds also at CM points (End ⊋ 𝒪).

Conditions:
- **The type must be fixed.** Without it, uniqueness fails (Rotger): (A, ι) has one principal
  polarization λ_μ∘ι(v) for each type c = μv, with c² = −6. These are infinitely many. Compiled:
  `type_eq_mu_mul`, and the explicit second type ν = 2j − k in `two_principal_types`.
- **Characteristic 0.**
- **𝒪 maximal.**
- Aut(𝒪)-twists change λ by ι(εv_α) (`twist_type`). The Atkin–Lehner generators i and j+k
  anticommute with μ, so they keep λ (`dag_conj_chi2/3`). So W₀ = W for D = 6, matching
  Baba–Granath's polarized quotient X₆/W.

Leaves:
- Every λ-free QM leaf in scratch/leaf-qm-fp/QMLeaves.lean is a consequence of the published
  type-μ PEL statement plus Lemma P: R1fpProps, X6Props, R1heckeProps, R2X6Props/R2fpProps,
  CMExists, X6Surj, R1recProps, R1rec, R5ptProps, R5fp, R5fpCount.
- **No Lean statement needs correcting.** Docstring and note repairs are listed in §4: replace
  "§2.2 SPECULATIVE" by Lemma P with its conditions and status.
- Lemma P stays folded into the leaves until AbVar has polarizations (WP4).

Glue:
- A4, A7, Lemma NV step 2 and h-b1 M9 use no λ, so they are unaffected.
- N5's polarized A7 follows from W₀ = W.
- rv-jac-ext N1 gets λ over K from Lemma P by descent.

Compiles: scratch/rv-qm-polar/QMPolar.lean (Mathlib only, `lake env lean`, no sorry, axioms
propext / Classical.choice / Quot.sound):
- §§1-4: the bp-qmmoduli core.
- §5: the second type ν.
- §6: `type_eq_mu_mul`, `twist_type`.
- §7: the twisting elements i and j+k (normalize 𝒪, anticommute with μ, commute with †).
- §8: `riemann_sign` and `lemmaP_lattice`, the sign step. x ↦ E₀(xj, x) is definite for every
  complex structure j, via an explicit LDLᵀ. So exactly one of ±E₀ is a principal Riemann form
  on every QM torus.

Exact checks are in polar_checks.py; results in scratch/rv-qm-polar/log.md.

Remains:
- The published locators are UNVERIFIED (no network): Buzzard 1997 p. 592 (N5 v14's citation
  for the uniqueness), Rotger Crelle 561 (2003), Trans. AMS 356 (2004).
- Not in Lean:
  - class number one (H₁ free over 𝒪);
  - descent from ℂ to F;
  - Lemma P for abelian varieties, which needs polarizations.
- π₀(A) = 1 for D = 6 when End(A) = 𝒪 is SPECULATIVE (evidence only).
