# rv-h-c3: second adversarial review of the de Rham descent lemma (step C3 of H)

Scope: Lemma `lem:de-rham-descent` (N5 L10939-10992, remark L10994-10997) and its use in the
proof of Theorem 4.1 (N5 L733-741, and L755-768 = C8 so far as it uses the lemma's weights). "N5"
is the frozen 11/5 `diophantine_zq.tex` at the repository root. Work log and script:
`scratch/rv-h-c3/`. The verdict (§4) was written in the log (Step 4) before reading rv-h-trust's
treatment of C3; the comparison is §5.

Marks: **VERIFIED** (checked against N5, a repository note, or by exact computation),
**STANDARD** (published theorem; locators UNVERIFIED unless stated, since no source text could be
read here: the sources are not in the repository and network commands are not allowed),
**SPECULATIVE**.

## 1. Verdict

**The lemma holds as stated, and its conclusion is exactly what N5 uses.** No step fails. The
repairs are a missing routine line, citation swaps, and one normalization sentence in C8 (§4).
For H's trust statement: C3 goes from "[M] (rv-h-trust only)" to "[M] (rv-h-trust, rv-h-c3:
two independent model reviews)". It also has a shorter route (§3.2) that needs neither the descent
paragraph nor Berger.

**Most serious issue (wording, not mathematics).** C8, not the lemma. N5 says that comparing
`{0,−1}` with "the modular weights `{0,1−k}`" forces "k = 2 and power zero". That holds only if
`ρ_g` is normalized so that its weights are `{0, 1−k}`, i.e. the arithmetic-Frobenius (Tate)
normalization. Pan fixes geometric Frobenius. In the cohomological normalization the same
comparison gives `k = 2` and power `1`. The final conclusion is the same either way (§3.4).

## 2. The statement

- Data: `K/ℚ_ℓ` finite, `F/K` finite, `A/F` an abelian surface, `C_ℓ/ℚ_ℓ` finite, and a continuous
  `r : G_K → GL₂(C_ℓ)` with `V_ℓ(A) ⊗_{ℚ_ℓ} C_ℓ ≃ r|_{G_F} ⊕ r|_{G_F}` as `C_ℓ[G_F]`-modules.
  Dimensions: 4 = 2 + 2 over `C_ℓ`. Consistent.
- Conclusion: `r` is de Rham (as a `ℚ_ℓ`-representation of `G_K`). At every component of
  `K ⊗_{ℚ_ℓ} C_ℓ` (N5: "every coefficient embedding") the HT weights are `{0, −1}`, with
  `ℚ_ℓ(1)` of weight `−1`.
- de Rham is the right notion. N5 claims nothing crystalline or semistable from the lemma;
  potential semistability comes afterwards from Berger (C4). So the lemma does not need to
  descend a crystalline or semistable structure, which in general would not descend. N5 says
  this itself ("requires no semistable descent assertion").
- **Match with the application (VERIFIED against N5 L632-657, L709-731).** Take `K = ℚ_ℓ` (the
  decomposition group of a fixed embedding `ℚ̄ → ℚ̄_ℓ`), `F` = the completion of `L'` at the
  induced place, `A` = the base change of `A/L`, `r = r_ℓ|_{G_{ℚ_ℓ}}`. For `σ ∈ G_{L'}`:
  - `μ_σ = μ_1 = 1` and `a_σ = 1`, because `μ` is inflated from `Gal(L/ℚ)` (L640);
  - `β(σ) = 1`, because `L'` is the kernel field of `β|_{G_L}` (L709).
  So `ρ_ℓ|_{G_F}` is the Tate action on `V_ℓ(A) ⊗ C_ℓ`. Matrix units of `B ⊗ C_ℓ = M₂(C_ℓ)`
  (`C ⊃` a splitting field of `B`, L718) give `ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`. This is the lemma's hypothesis
  exactly.

## 3. The proof, step by step

Notation: `D_E(W) = (B_dR ⊗_{ℚ_ℓ} W)^{G_E}`. `W` is de Rham over `E` iff
`dim_E D_E(W) = dim_{ℚ_ℓ} W`.

### 3.1 Steps P1-P6 (each correct)

| Step | N5 claim | Check | Mark |
|---|---|---|---|
| P1 | `H¹_et(A_F̄, ℚ_ℓ)` is de Rham (Scholze Cor. 1.8, Thms 9.1, 9.3, corrigendum) | Cor. 1.8 needs a proper smooth rigid space over a discretely valued `K` with perfect residue field. `F` is finite over `ℚ_ℓ`, so this holds. The algebraic-analytic comparison of `ℤ/ℓⁿ`-cohomology needs `ℓⁿ` invertible on `A`, which holds since `char F = 0`. The hypotheses are met. Scholze is more than needed: Faltings 1989 or Tsuji 1999 (`C_dR` for proper smooth schemes) gives this with no GAGA step | STANDARD |
| P2 | `V_ℓ(A) ≅ H¹_et(A_F̄, ℚ_ℓ)^∨`, `G_F`-equivariantly | Holds. N5's source (Milne's notes) is a [P] source: replace by Mumford §§19-20 or Milne 1986 §15 | STANDARD |
| P3 | de Rham is closed under duals and subquotients | Fontaine's admissibility formalism | STANDARD |
| P4 | coefficient extension is a finite direct sum over `ℚ_ℓ` | As a `ℚ_ℓ[G_F]`-module, `V ⊗ C_ℓ ≅ V^{[C_ℓ:ℚ_ℓ]}`, and `r|_{G_F}` is a summand of it | VERIFIED (argument) |
| P5 | descent `F → K` | Take `F' ⊇ F` Galois over `K`. **Unstated step:** de Rham over `F` implies de Rham over `F'`. Reason: `F' ⊗_F D_F → D_{F'}` is injective (`B_dR^{G_{F'}} = F'`, linear independence), so `dim D_{F'} ≥ dim W`, and `≤` always holds. Then `D_{F'}` has a semilinear `Gal(F'/K)`-action with invariants `D_K`, and Hilbert 90 (Speiser) gives `F' ⊗_K D_K ≅ D_{F'}`. Each `Fil^i D_{F'} = (Fil^i B_dR ⊗ W)^{G_{F'}}` is a stable `F'`-subspace, so it descends too. Correct | VERIFIED (argument) |
| P6 | weights `{0, −1}` | `Fil⁰ H¹_dR = H¹_dR` (dim 4), `Fil¹ = H⁰(A, Ω¹)` (dim 2), `Fil² = 0`. In the convention where `ℚ_ℓ(1)` has weight `−1`, the weights are the jumps of `Fil` on `D_dR` (`D_dR(ℚ_ℓ(1)) = K t⁻¹ ⊗ e ⊂ Fil⁻¹`). So `H¹` has weights `{0,0,1,1}` and `V_ℓ(A)` has `{0,0,−1,−1}`. On each factor field of `F ⊗ C_ℓ`, `Fil¹ ⊗ C_ℓ` has rank 2, so every component sees `{0,0,−1,−1}`. Since `D(r ⊕ r) = D(r)²`, `D(r)` has `{0,−1}` at every component. Filtered descent (P5) carries this to `K ⊗ C_ℓ`. Sanity check: for an ordinary elliptic curve, `0 → ℚ_ℓ(1) ⊗ unr → V_ℓ(E) → unr → 0` has weights `{−1, 0}` | VERIFIED (argument) |

The remark after the proof is correct: Faltings 1988 gives Hodge–Tate, and Hodge–Tate does not
imply de Rham.

**Refutation attempts.** Could some 2-dimensional `r` of `G_K` have `r|_{G_F}` de Rham without
`r` being de Rham? No. P5 shows that being de Rham depends only on the restriction to any finite
extension (Brinon–Conrad Prop. 6.3.8 as cited; Fontaine). The same holds for HT weights. So no
counterexample to the lemma can exist. No finite computation bears on P1-P6, and none was run for
them.

### 3.2 A shorter route (STANDARD; SPECULATIVE as a recommendation)

Pan needs pst at 5, and "potentially semistable over `ℚ_ℓ`" is defined by restriction to some
finite extension. Two facts suffice:
- `r|_{G_F}` is a summand of `V_ℓ(A_F) ⊗ C_ℓ`;
- `V_ℓ(A_F)` is pst, by Grothendieck's semistable reduction (SGA 7 IX) and `C_st` (Tsuji 1999;
  for abelian varieties also Breuil, Coleman–Iovita).

Hence `r_ℓ|_{G_{ℚ_ℓ}}` is pst, with neither P5 nor Berger. The weights also need no descent, since
HT weights over `ℚ_ℓ` are read off on `G_F`. So the descent paragraph is correct but not
load-bearing. This contradicts rv-h-trust §3, which says C8 needs the descent paragraph "in
either route".

### 3.3 Use in N5 (VERIFIED against N5 L733-768 and Pan's statement as quoted in h-a011 §1.1)

- L733-737 states exactly the lemma's conclusion for `K = ℚ_ℓ`.
- L739-741: Berger, de Rham ⇒ pst (C4, [R]).
- Pan 1.0.4 needs pst at `p` and distinct HT weights at `p`. `{0, −1}` are distinct, and Pan's
  convention (`ε` has weight `−1`) is N5's. Pan's coefficients are `Q̄_p`, which contains `C_5`.
- C8 uses only the multiset `{0, −1}` at the single embedding of `ℚ_5`. Its other inputs (the de
  Rham property of `ρ_g`, local algebraicity) are C8 suppliers, not C3.

### 3.4 C8's weight comparison: a normalization point

Write `r_5 ≅ ρ_g ⊗ ψ` with `ψ|_{I_5} = ε^n · (finite)`. With `ε` of weight `−1`, the weights of
`ρ_g ⊗ ψ` are `wt(ρ_g) − n`.

- **Tate normalization** (trace of arithmetic `Frob_p` is `a_p`, `det = ε^{k−1}χ`):
  `wt = {0, 1−k}`. Then `{−n, 1−k−n} = {0, −1}` with `k ≥ 2` forces `k = 2`, `n = 0`. This is
  N5's reading.
- **Cohomological normalization** (trace of geometric `Frob` is `a_p`; Pan fixes geometric
  Frobenius): `wt = {0, k−1}`. This forces `k = 2`, `n = 1`, so "power zero" fails.
- Harmless either way. For `k = 2`, `ρ^coh = (ρ^Tate)^∨ ≅ ρ^Tate ⊗ ε⁻¹χ⁻¹`, so
  `ρ^coh ⊗ ε = ρ^Tate ⊗ χ⁻¹`, a finite twist. That twist is absorbed into `f` as N5 does.
- **Repair R3:** say "normalize `ρ_g` to have weights `{0, 1−k}` (trace of arithmetic Frobenius
  `a_p`)".
- PARI check of the Tate normalization: for four elliptic curves, the trace of the Frobenius
  endomorphism (= arithmetic Frobenius on `T_ℓ E`), computed as `p + 1 − #E(𝔽_p)` by brute-force
  point counting, equals the newform's `a_p` for every good prime `p < 200`. Result: equality
  holds for 11a1, 37a1, 43a1 and 389a1 (45-46 primes each; script
  `scratch/rv-h-c3/frob_norm.py`). VERIFIED for these samples; in general it is Eichler–Shimura
  (STANDARD). Level 5077 was dropped because PARI's `mfeigenbasis` overflowed a 2 GB stack.

## 4. Repairs

- **R1 (C3, N5 proof).** Add one line: de Rham over `F` implies de Rham over `F'` (§3.1, P5), or
  cite it with the same Brinon–Conrad / Fontaine reference as the descent.
- **R2 (C3, citations; already in h-trust as [P]).**
  - Milne's notes → Mumford §§19-20 or Milne 1986 §15.
  - Brinon–Conrad notes → Fontaine, Astérisque 223 (1994).
  - h-trust C3 names "Exp. VIII" as the replacement. From memory (SPECULATIVE): Exp. VIII is
    Fontaine's exposé on potentially semistable ℓ-adic representations, and the de Rham
    admissibility formalism is in Exp. III. Check this locator before adopting it.
  - The Scholze locators (Cor. 1.8, Thms 9.1, 9.3, corrigendum) are UNVERIFIED here. Faltings 1989
    or Tsuji 1999 is a citation-only fallback with no GAGA step.
- **R3 (C8).** State the normalization of `ρ_g` before "power zero" (§3.4).
- **Optional simplification.** §3.2: pst directly from semistable reduction and `C_st`, which
  removes the descent paragraph and Berger from the critical path.

## 5. Comparison with rv-h-trust (read after §§1-4 were fixed in the log)

- rv-h-trust §2.1 reaches the same verdict: the lemma holds given Scholze, and the weight step and
  the Hilbert 90 descent are correct. Its weight argument (base change along `τ`) and mine
  (components of `F ⊗ C_ℓ`) agree.
- New here:
  - (a) the unstated restriction step (R1);
  - (b) the descent paragraph is not load-bearing for pst or for the weights (§3.2). This
    corrects rv-h-trust §3;
  - (c) the normalization dependence of "power zero" (R3). rv-h-trust §1.2 and h-trust C8 state
    `wt(ρ_g) = {0, 1−k}` without a normalization;
  - (d) the suspect "Exp. VIII" locator in h-trust C3.

## 6. Consequence for H's trust statement

- C3 stays a repository argument with model reviews only, but it now has two independent ones
  that agree. The lemma is a routine consequence of standard `p`-adic Hodge theory: de Rham
  comparison, Fontaine's formalism, Hilbert 90. It has a citation-only alternative (§3.2).
- Nothing in C3 threatens H. Among the three N5-only passages, C3 is no longer the thinnest point.
- In C8, R3 is wording only. C8's own unreviewed input (the Hodge–Tate / de Rham property of
  `ρ_g`) is outside this review.

**Single next step:** check the Fontaine Astérisque 223 exposé numbers (and Scholze's Cor. 1.8 in
the journal) against the sources, then apply R1-R3 to h-trust's C3/C8 entries.
