# t31-unram: leaf T31 (`GlueDescent.B2Q.LeafUnramified`) is proved

## Main result (VERIFIED: compiled, `#print axioms`)

```lean
theorem ZInQ.Contrib.T31.leafUnramified : GlueDescent.B2Q.LeafUnramified
```

in `ZInQKernel/Contrib/T31/Main.lean` (module `ZInQKernel.Contrib.T31.Main`). It has no
hypotheses. Its type is exactly the leaf, i.e. (ZInQKernel/HDecomp/Descent/B2Glue.lean:318)

```lean
def LeafUnramified : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
    ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)
```

The blocks `namespace GlueDescent.B2 … end` and `namespace GlueDescent.B2Q … end` of
`scratch/h-decomposition/Leaves.lean` (lines 8544-8737 and 8749-8837) are textually identical
to those of `ZInQKernel/HDecomp/Descent/B2Glue.lean` (checked with `diff`), so this is also
the `t31` field of the leaf list at Leaves.lean:21524.

`#print axioms` (scratch/t31-unram/Axioms.lean, run with `lake env lean`):

```
ZInQ.Contrib.T31.leafUnramified : GlueDescent.B2Q.LeafUnramified
'ZInQ.Contrib.T31.leafUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T31.signCob_of_cyclic_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T31.exists_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T31.exists_unramifiedExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T31.exists_iota' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build ZInQKernel.Contrib.T31.Main` succeeds (9129 jobs). No `sorry`, no `axiom`, no
existing file edited, no Tau Ceti module newly vendored.

## Files (all new)

| file | content |
|---|---|
| `ZInQKernel/Contrib/T31/Cyclic.lean` | abstract lemma `signCob_of_cyclic_even` (imports only `B2Glue`, i.e. Mathlib) |
| `ZInQKernel/Contrib/T31/Good.lean` | global algebraic number theory, `exists_base` (Mathlib only) |
| `ZInQKernel/Contrib/T31/Local.lean` | local part, `exists_unramifiedExtension` (Mathlib + vendored Tau Ceti) |
| `ZInQKernel/Contrib/T31/Main.lean` | assembly, `leafUnramified` |
| `ZInQKernel/Contrib/T31/Wired.lean` | consumers with `hUnr` discharged: `b2_of_leaves_T31`, `b3_degree_le_QM_of_T14_T15_T31` |

## The intermediate results (exact statements)

1. **Cyclic inflation** (`Cyclic.lean`). For a topological group `G`, a group `H`, a commutative
   group `U`:
   ```lean
   theorem signCob_of_cyclic_even (ψ : G →* H) (hker : IsOpen (ψ.ker : Set G)) (φ : H)
       (hpow : ∀ h : H, ∃ k : ℕ, φ ^ k = h) (g₁ : G) (hg₁ : ψ g₁ = φ) (f : ℕ)
       (hord : orderOf φ = 2 * f) (η : G → G → U) (hη : IsSignCocycle η)
       (hinv : ∀ σ σ' τ τ' : G, (∃ i : ℕ, ψ σ' = ψ σ * (φ ^ f) ^ i) →
         (∃ j : ℕ, ψ τ' = ψ τ * (φ ^ f) ^ j) → η σ τ = η σ' τ') :
       SignCob η
   ```
   Proof: with `u(k) = ∏_{i<k} η(g₁, g₁^i)` one has `η(g₁^a, g₁^b) = η(1,1)·u(a+b)/(u(a)u(b))`
   (induction on `a`, cocycle identity); `u` is `2f`-periodic because
   `η(g₁, g₁^{i+f}) = η(g₁, g₁^i)` makes `∏_{i<2f}` a square of a sign; `γ(σ) = η(1,1)/u(k(σ))`
   with `ψ σ = φ^{k(σ)}` has `dγ = η` and is constant on cosets of the open kernel. This is the
   vanishing of inflation `H²(ℤ/f, ±1) → H²(ℤ/2f, ±1)`.

2. **Good elements** (`Good.lean`). For `L` a number field, Galois over `ℚ`:
   ```lean
   theorem exists_base (w : Ideal (𝓞 L)) [hw : w.IsMaximal] (hw0 : w ≠ ⊥)
       (he : w.ramificationIdx ℤ = 1) {p : ℕ} (hp : (p : 𝓞 L) ∈ w) :
       ∃ b₀ : 𝓞 L, ∀ y : 𝓞 L,
         aeval (b₀ + p * y) (derivative (minpoly ℤ (b₀ + p * y))) ∉ w
   ```
   Proof: `e = 1` makes the inertia group trivial (Mathlib
   `Ideal.card_inertia_eq_ramificationIdxIn`); `θ` lifts a generator of `(𝓞 L ⧸ w)ˣ`;
   `b ≡ θ (mod w)` and `b ∈ ρ • w` for all conjugates `ρ • w ≠ w` (prime avoidance); then
   `b − τ b ∉ w` for every `τ` moving `b`, and `(minpoly b)'(b) = ∏ (b − τ b)`
   (`Splits.eval_root_derivative`, `Normal.minpoly_eq_iff_mem_orbit`).

3. **Local part** (`Local.lean`). For `K` a nonarchimedean local field (Tau Ceti/Mathlib
   `IsNonarchimedeanLocalField`), `Ω/K` algebraic with a valuative relation extending `K`'s,
   `L` a number field Galois over `ℚ`:
   ```lean
   theorem exists_unramifiedExtension [IsGalois ℚ L] (ι : L →+* Ω) {p : ℕ}
       (hp : valuation K (p : K) < 1) (hp0 : p ≠ 0)
       (hunr : ∀ P : Ideal (𝓞 L), P.IsPrime → (p : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1) :
       ∃ f ≠ 0, ∀ x : L, ι x ∈ TauCeti.unramifiedExtension K Ω f
   ```
   Proof: `w = {x ∈ 𝓞 L | v(ι x) < 1}` is a maximal ideal containing `p`, so `e(w) = 1`. For
   `b ∈ b₀ + p𝓞 L` (item 2) the element `ι b` generates over `K` a field `K(ι b)` in which it is a
   root of `minpoly ℤ b` with unit derivative, so `K(ι b)/K` is unramified (Tau Ceti
   `TauCeti.isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative`) and `ι b ∈ K^{ur}`
   (`IntermediateField.le_maximalUnramifiedExtension`). Then `ι y = (ι(b₀+py) − ι b₀)/p ∈ K^{ur}`
   for all `y ∈ 𝓞 L`, hence `ι(L) ⊆ K^{ur}`; a primitive element puts `ι(L)` in one `K_f`
   (`TauCeti.mem_maximalUnramifiedExtension_iff`).

4. **Assembly** (`Main.lean`). `exists_iota p` gives the embedding `ι₀ : ℚ̄ → ℚ̄_p` underlying
   Mathlib's `Field.absoluteGaloisGroup.map` with `ι₀ (resp p σ x) = σ (ι₀ x)`. Item 3 with
   `K = ℚ_[p]`, `Ω = AlgebraicClosure ℚ_[p]` (valuative relation
   `TauCeti.algebraicExtensionValuativeRel`, `v(p) < 1` from `TauCeti.Padic.irreducible_natCast_self`)
   gives `ι₀(L) ⊆ K_f`. With `M = K_{2f}`: `Gal(M/K)` is cyclic (`TauCeti.isCyclic_algEquiv`, from
   `TauCeti.isUnramified_unramifiedExtension`) of order `2f` (`TauCeti.finrank_unramifiedExtension`),
   `K_f ≤ M` (`TauCeti.unramifiedExtension_le_of_dvd`), and `φ^f` fixes `K_f` because
   `|Gal(K_f/K)| = f`. Item 1 with `ψ = restrictNormalHom M` (open kernel:
   `IntermediateField.fixingSubgroup_isOpen`) concludes.

## Route taken, versus the suggested one

The task suggested the Brauer-group route (Tau Ceti `mk_eq_zero_of_forall_mem_unitFiltration_zero`,
`brBaseChange_relBrInfl_eq_zero`, `h2MuToBr_injective`, Kummer theory, continuous-cohomology
comparison). It was not needed: the leaf follows from the elementary fact that `H²(ℤ/f, ±1)` dies
on inflation to `ℤ/2f`, once one knows that `ι₀(L)` lies in a finite unramified extension of
`ℚ_p` (cyclic Galois group). The only Tau Ceti input is its theory of unramified extensions of
local fields (`LocalField/Unramified/{Existence,Maximal,Criterion}.lean`,
`LocalField/ResidueCorrespondence.lean`, `LocalField/FiniteExtension/IntermediateField.lean`,
`LocalField/AlgebraicExtension/*`, `LocalField/Padic.lean`), all already vendored by tc-port.
Consequently `Brauer/Torsion.lean` and its 7 missing modules were **not** vendored, and no
completion `L_w` or decomposition-group equivalence is used (the prime `w` is defined directly by
the spectral valuation of `ℚ̄_p`).

## Wiring (VERIFIED: compiled, standard axioms)

`ZInQKernel/Contrib/T31/Wired.lean`:
- `ZInQ.Contrib.T31.b2_of_leaves_T31`: `GlueDescent.B2Q.b2_of_leaves` without `hUnr`.
- `ZInQ.Contrib.T31.b3_degree_le_QM_of_T14_T15_T31`: `GlueWP3.b3_degree_le_QM_of_T14_T15`
  without `hUnr`.

`#print axioms` of both: `[propext, Classical.choice, Quot.sound]`
(scratch/t31-unram/AxiomsWired.lean).

## Remaining

Nothing for T31. Other consumers (`b3_of_leaves`, `b3_degree_le_QM`, and whatever is built on
`b3_degree_le_QM_of_T14_T15`) still take `hUnr : LeafUnramified` because existing files may not be
edited; `ZInQ.Contrib.T31.leafUnramified` can be passed for it.
