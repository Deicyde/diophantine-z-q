# ds965-weak: `dsThm965` made robust to the wording of Diamond–Shurman 9.6.5

Task ds965-weak (2026-11-15). Scratch: `scratch/ds965-weak/`. Contribution:
`ZInQKernel/Contrib/OneProof/DSThm965Weak.lean` (namespace `DS965Weak`).

## 1. Result

**`DSThm965` is proved from its weakest reading alone, with no second leaf.** (VERIFIED: compiled; axioms
`propext`, `Classical.choice`, `Quot.sound`.)

```lean
theorem DS965Weak.dsThm965_of_weak (hW : DS965Weak.DSThm965Weak) : ZInQ.Contrib.HodgeSplit.DSThm965
theorem DS965Weak.dsThm965Weak_of_dsThm965 (h : ZInQ.Contrib.HodgeSplit.DSThm965) : DS965Weak.DSThm965Weak
```

`DSThm965Weak` is `DSThm965` word for word except the last line: `ρ(Frob_𝔭)` *satisfies* the Hecke
polynomial,

```lean
          aeval (ρ.mat σ) (X ^ 2 - C (ιL α) * X + C (ιL β)) = 0
```

and not `(ρ.mat σ).charpoly = X ^ 2 - C (ιL α) * X + C (ιL β)`. The second theorem (Cayley–Hamilton) shows the
new leaf is a consequence of the old field, so it is never stronger than the print, whatever the print
says. All the glue is proved: the kernel's Chebotarev density (T18, through hodge-split's
`frobeniusDense_C9`), Mathlib's cyclotomic characters (through hodge-split's `eps0` and `cycQ`), and new
elementary lemmas in the file. No determinant leaf is needed: `dsThm966`, `tateTwistInvariants`, the Weil
pairing leaf and Ribet's irreducibility theorem are all unused.

The new leaf is printed under every reading:
* if DS 9.6.5 says "satisfies the polynomial equation", the leaf is the print;
* if it says "has characteristic polynomial", the leaf follows from the print by Cayley–Hamilton.

So the strictest-reading flag of `dsThm965` (kinds.tsv: "DS 9.6.5 may print only that Frobenius satisfies the
polynomial") no longer applies. The fold spec `scratch/ds965-weak/autofold.json` swaps the field for the leaf.
Its dry run gives: strict 45/11 → 45/11, **strictest 43/13 → 44/12** (one GLUE fewer under the strictest
reading).

## 2. Statements

* Target (verbatim copy `DSThm965Copy` in `scratch/ds965-weak/Check.lean`, with
  `DSThm965Copy = ZInQ.Contrib.HodgeSplit.DSThm965 := rfl`, compiled): `ZInQKernel/OneProof/H/TailS.lean`
  l.1110, bundle field `HDec.HSyn.OpenResearchLeaves22.dsThm965`.
* **LEAF `DS965Weak.DSThm965Weak`** (published). Diamond–Shurman, *A First Course in Modular Forms*, GTM 228
  (2005), Thm 9.6.5, in its weakest reading (numbering UNVERIFIED, no network). Deligne, Sém. Bourbaki 355
  (1969, published 1971), and for `k = 2` Shimura 1971 Thm 7.14 (UNVERIFIED) are the same theorem. The Lean
  conventions are those of the field it replaces: coefficients extended along `ιL ∘ ιC⁻¹`, places of `ℚ̄` as
  valuation subrings, pkg-I4's `IsArithFrob`, unramified at `p ∤ Nℓ`.
  **Rating: printed form (weakest reading).** Reason: it is literally the print if the print says
  "satisfies", and otherwise a consequence of the print (`dsThm965Weak_of_dsThm965`). Locator UNVERIFIED, as
  for the old field.

## 3. The proof (all GLUE, proved in Lean)

Let `ρ` be the weak leaf's representation and `P_p = X² − a X + b`, with `a = ιL α`, `b = ιL β`, the Hecke
polynomial at `p ∤ Nℓ`. Let `F = ε₀ · χ_ℓ^{k−1}`, where `ε₀` is hodge-split's `eps0`, the nebentypus as a
finite-order Galois character. Then `F` is continuous and multiplicative, and `F(Frob_𝔭) = b` (copied from
`detFromFrobenius_proof`).

1. **Matrix algebra** (`charpoly_of_aeval_nonScalar`, `charpoly_of_aeval_det`, `root_of_aeval_scalar`,
   `nonScalar_mul`). Suppose a `2 × 2` matrix `M` satisfies `P(M) = 0`.
   * If `M` is not scalar, then `charpoly M = P`: compare the entries of `P(M) = 0`.
   * If `det M = b ≠ 0`, then `charpoly M = P`. In the scalar case `M = c·1`, `c² = b` and `c² − ac + b = 0`
     give `a = 2c`.
   * A scalar matrix times a non-scalar one is non-scalar.
2. **Chebotarev on an open set** (`eq_on_open_of_eq_on_arithFrob`). Two continuous functions on `G_ℚ` that
   agree at the Frobenius elements lying in an open set `W` agree on `W`. Same proof as
   `C9Rhof.eq_of_eq_on_arithFrob`, from `frobeniusDense_C9` (the kernel's T18).
3. **Case: some `ρ(σ₀)` is not scalar.** The non-scalar locus `W` is open (it is defined by entries).
   * At Frobenius elements in `W`, step 1 gives `det ρ = b = F`, so `det ρ = F` on `W` by step 2.
   * If `ρ(σ)` is scalar, then `σσ₀ ∈ W`, so `det ρ(σ) = F(σσ₀) F(σ₀)⁻¹ = F(σ)`.
   * Hence `det ρ(Frob_𝔭) = b` at every Frobenius element, and step 1 gives `charpoly ρ(Frob_𝔭) = P_p`.
     `ρ` itself is the witness.
4. **Case: every `ρ(σ)` is scalar.** Then `ρ = ψ₀ · 1` with `ψ₀(σ) = ρ(σ)₀₀`, a continuous character
   (`psi0`).
   * The witness is `ρ' = diag(ψ₀, F ψ₀⁻¹)` (`psi1`, hodge-split's `diagHom`).
   * At `Frob_𝔭`, `c = ψ₀(Frob_𝔭)` is a root of `P_p` and the other diagonal entry is `b/c`, the other root.
     So `charpoly ρ'(Frob_𝔭) = X² − (c + b/c) X + b = P_p`.
   * `ρ'` is unramified at `p ∤ Nℓ`. `ψ₀` is, because `ρ` is. `ε₀` and `χ_ℓ` are trivial on inertia above
     `p ∤ Nℓ` (`eps0_inertia`, `cycQ_inertia`, new): an inertia element acts trivially on the residue field,
     and roots of unity of order prime to `p` stay distinct modulo a place above `p`
     (`eq_of_sub_mem_nonunits`, the argument of hodge-split's `arithFrob_pow_of_rootOfUnity`, generalized).

Case 4 is why no determinant leaf is needed. A weak-reading `ρ` could a priori be scalar, `ψ ⊕ ψ`, with
`ψ(Frob_p)` one root of `P_p`. From the weak statement alone such a `ρ` cannot be excluded, and its
determinant is `ψ²`, not `χ χ_ℓ^{k−1}`. But `DSThm965` only asks for *some* `ρ`, and `ρ'` is built from `ψ`.

## 4. `R16Used.AfTateCharPoly` (wip/r16-used, dcf24ac6): the same argument does not fully repair it

`AfTateCharPoly` (Diamond–Shurman Lemma 9.5.3 and Thm 9.5.4, existence form) gives an abelian variety `A`, a
quotient `π : J₁(N) ↠ A` and `θ : K_f → End⁰(A)`. It states the characteristic polynomial over
`ℚ_ℓ ⊗ K_f` of Frobenius acting on `V_ℓ(A)`. Its weak reading would say that Frobenius satisfies `esPoly`
over `ℚ_ℓ ⊗ K_f`. (Analysis only, not formalized.)

* **Transfers.** Steps 1–3 transfer to each `ι`-component `V_ℓ(A) ⊗_{ℚ_ℓ⊗K_f, ι} ℚ̄_ℓ` (2-dimensional by the
  rank-two clause; r16-used's `eigenFun`, `frobOn`). Take `F = ε₀ χ_ℓ` (`k = 2`), with `ε₀` built from
  `ι ∘ (K_f ↪ ℂ)⁻¹` instead of `ιL ∘ ιC⁻¹`. If Frobenius acts by a non-scalar endomorphism of the component
  for some `σ₀ ∈ G_ℚ`, then the trace and determinant at every Frobenius are `ι(a_p)` and `ι(χ(p)) p`, and the
  weak reading gives every clause of R16 that the route uses (`R16Trace`). SPECULATIVE (not compiled).
* **Does not transfer: step 4, the scalar case.** In `AfTateCharPoly` the representation is the Tate module of
  the abelian variety in the existential, not a free choice, so `ρ` cannot be replaced by
  `diag(ψ, F ψ⁻¹)`. Excluding a component on which `G_ℚ` acts by scalars needs an input about the same `A`.
  Any one of these suffices:
  1. the determinant over `ℚ_ℓ ⊗ K_f`, `det ρ_{A_f,ℓ} = χ χ_ℓ`. Diamond–Shurman obtain it from the Weil pairing
     and the Hecke adjoint `T_p^* = ⟨p⟩⁻¹ T_p`, which the existential `A` of `AfTateCharPoly` does not carry,
     so the bundle's `weilPairingMumford` alone does not give it;
  2. the irreducibility of each `λ`-component (Ribet 1977, *Galois representations attached to eigenforms
     with Nebentypus*, UNVERIFIED locator);
  3. the strong reading itself.

  Each would have to be stated about the same `A`, so it would be a combined existential leaf rather than a
  separate printed statement.

  **Verdict:** under the weakest reading of DS 9.5.4, `AfTateCharPoly` has a residual reading risk, confined
  to the scalar case. The DSThm965 argument does not remove it.

## 5. Checks (VERIFIED, 11-15)

* `scratch/ds965-weak/DSThm965Weak.lean` (identical to the contribution file) and `Check.lean` (adds the
  verbatim copy and `#print axioms`) compile with `lake env lean`. Both theorems use only the standard axioms.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSThm965Weak`
  succeeds. The `#discharges` run (`scratch/ds965-weak/Discharges.lean`, full output in `discharges.out`) gives:

  ```
  DISCHARGES [OpenResearchLeaves22.dsThm965] by DS965Weak.dsThm965_of_weak
    still assumes: [DS965Weak.DSThm965Weak]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 62 open hypotheses, 2165 theorems checked, 8 discharge one
  ```

  The other seven discharges are earlier contributions already in the tree.
* `python3 scripts/one_proof/autofold.py scratch/ds965-weak/autofold.json --dry-run` reports strict
  45/11 → 45/11 and strictest 43/13 → 44/12. Its output without line 1 (`scratch/ds965-weak/FoldDryRun.lean`:
  `OpenResearchLeaves23`, `sixContactMin_of_open30`) compiles. `sixContactMin_of_open30` uses only the standard
  axioms.
* The contribution file has no code that runs at build time.

## 6. What remains

* **The `locators.md` row.** It was not added, because shared docs are outside this task's write scope.
  Proposed row: | `dsThm965Weak` (weakest reading of DS 9.6.5) | Diamond–Shurman, GTM 228 (2005), Thm 9.6.5;
  Deligne, Sém. Bourbaki 355; Shimura 1971 Thm 7.14 (`k = 2`) | — | numbering UNVERIFIED | **printed form under
  the weakest reading; CONSEQUENCE (Cayley–Hamilton) under the characteristic-polynomial reading** |.
* **The DS 9.6.5 page check.** This field no longer needs it. The citation is still locator UNVERIFIED.
* **`AfTateCharPoly` (§4).** Not formalized; the scalar case needs an input about the same `A`.
