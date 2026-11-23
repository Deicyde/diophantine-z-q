# Serre A6 cyclotomic sign check

**Closed.** Lean proves the (iv) side of `LocalArtin.serreA6OnIntegerUnits` at the
cyclotomic character and constant weight `n = 1`, on all integer units of every
finite Galois `K/ℚ_[p]` inside `PadicAlgCl p`.

## Statement proved

```lean
theorem serreA6_integerUnits_cyclotomic [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K] :
    serreConditionIVUnits p K (cyclotomicCharacterToK p K)
      (cyclotomicCharacterToK_continuous p K) (fun _ => 1) := by
```

[SerreA6CyclotomicCheck.lean](../../ZInQKernel/Contrib/OneProof/ConradSerre/SerreA6CyclotomicCheck.lean)

## Proof

The manuscript uses the Tate convention in which the cyclotomic Hodge–Tate
weight is `−1`. Here `n` is the exponent of the cyclotomic character in
Serre's III-A5 and III-A6 formulation. [Manuscript](../../diophantine_zq.tex#L755) · [Source notes in LocalArtin.lean](../../ZInQKernel/Contrib/OneProof/ConradSerre/LocalArtin.lean)

1. Compose Tau Ceti's continuous local cyclotomic character with the two unit
   embeddings `ℤ_[p]ˣ → ℚ_[p]ˣ → Kˣ`. Compose the corresponding continuous
   maps to the ambient algebraic closure to obtain the hypothesis of (iv).
2. Choose the full depth-zero unit group. For an integer unit `u`,
   `character_norm` sends evaluation at `artinK u` to evaluation at the
   downstairs Artin symbol of `N(u)`. Tau Ceti's norm valuation lemma shows
   that `N(u)` has valuation zero and hence comes from a unit of `ℤ_[p]`.
3. Apply `abelianizedLocalCyclotomicCharacter_artinMap_padic` at `k = 0`.
   The resulting character value in `K` is `N(u)⁻¹`. Reindex the product by
   `σ ↦ σ.symm` and apply `Algebra.norm_eq_prod_automorphisms` to identify
   the product with `N(u)`. Their product is `1`. [Tau Ceti's Artin-symbol formula](../../ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean)

## Axiom output

```text
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.serreA6_integerUnits_cyclotomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

[Raw output](../../scratch/serre-a6-cyc/axioms.txt) · [Build log](../../scratch/serre-a6-cyc/log.md)

## Known issues

GitHub access through the proxy returned HTTP 403 on the fetch and branch push.
The cached `origin/fold/conrad-serre-1123` matched the requested base
`8ed0590c0cd95dbb16643c338aca466ddb5fb1eb`, which was used for the check.
