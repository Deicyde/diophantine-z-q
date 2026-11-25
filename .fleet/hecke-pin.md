# hecke-pin (fleet summary)

**Verdict: the shared dictionary gap of `HeckeJ1DS`, `AfShimura` and `AfCharpolyDS965` is closed.** Two parts
are proved outright; the other two reduce to two analytic leaf candidates and one piece of algebraic-geometry
glue. New file: `ZInQKernel/Contrib/OneProof/HeckePin.lean` (namespace `AfTateLam.HeckePin`).

**Proved outright (no extra input):**
- `isAfQuotient_unique`: `A_f` is unique up to unique isomorphism compatible with `π`.
- `induced_comm`: the endomorphisms `T_p` induces on two such quotients correspond under that isomorphism.
- `theta_unique`: `θ` is unique, because `a_n ∈ ℚ(a_p, χ(d))` (`coeff_mem_genField`, from the coefficient
  relations of `IsNormalizedEigenform`).

**Gap 1 (`KillsIf` is DS's `I_f`):** `evF_eq_zero_of_heckeJ_eq_zero_of_leaves` proves
`ker(heckeJ) ⊆ ker(evF)`. From it, `killsIf_iff_IfDS_of_leaves` shows `KillsIf` kills exactly DS's `I_f J`.
- Remaining inputs: the leaf candidates `X1TauPoints` (consequence of DS §7.7) and `AbelJacobiX1`
  (DS Thm 6.1.2 composed with the algebraic Jacobian). Neither is in printed form.
- The Eichler glue is proved. `eichlerPrimitive`: a holomorphic primitive of `f` exists. `eichlerHecke`: `T_p f =
  a_p f` from the `q`-expansion, plus the double-coset identities for the primitive.
- The method: lift the double cosets to formal divisors on `ℍ`; the class map intertwines them with `heckeJ`
  (Claim A); the sum of the primitive over the divisor multiplies by `evF` (Claim B); a countability argument
  finishes.

**Gap 2a (pinning `T_p`, `⟨d⟩`):** `isHeckeT_unique` and `isDiamond_unique`. Inputs: `X1TauPoints` and the GLUE
`ConstOnTauPoints` (a morphism `X → J` constant on the `x_τ` is constant). The proof goes through the Albanese
property.

**Reading:** DS Thm 9.6.5, 2016 printing p. 404 (human read, issue #14 comment 7121091136). The paragraph after
Thm 9.6.5 ("Section 9.5 constructed ρ_{f,λ} when k = 2 …") *asserts* that the §9.5 representation is 9.6.5's `ρ`
at k = 2, so it is not merely presupposed. It gives no proof.

**Compiles (VERIFIED).**
- `lake build ZInQKernel.Contrib.OneProof.HeckePin` succeeds, and every main theorem uses only the standard axioms.
- The verbatim target copy checks by `Iff.rfl`.
- `#discharges`: `r16CoreY` is still discharged by `r16CoreY_of_ds965`. The fold's leaf set is unchanged, and the
  dry run gives the same `11/18 on 29 → 15/17 on 32`.
- The three leaves' docstrings now point at `HeckePin.lean`.

**Remains.** `X1TauPoints` and `AbelJacobiX1` are open leaf candidates (not printed form), and
`ConstOnTauPoints` is open glue. A proof route for it is in the report §3; it needs two pieces the tree lacks:
the dimension-one finiteness fact for curves, and geometric irreducibility of `X_ℂ`. A human reading of DS Thm 9.6.5 at k = 2 was still needed (since posted: issue #14 comment 7121091136, 2016 printing p. 404). Report:
`docs/research/hecke-pin.md`.
