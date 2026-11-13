# T31: explicit sign-cocycle inflation and the remaining unramified bridge

Date: 2026-11-12.

**Status: checked partial contribution.** The finite cyclic inflation theorem and the actual odd-degree number-field cases are proved. The full production `GlueDescent.B2Q.LeafUnramified` remains open: no absolute unramified residue/Frobenius quotient or compatible doubled lift is asserted here.

This is an AI-assisted contribution. The serving model identity is unknown. No independent Astra acceptance, assembled-proof acceptance, or new polynomial record is supplied.

## Frozen statement and scope

The base is `a5937595cde3e3db00975b81e5171cdef92c801a`. The statement reference is `ZInQKernel/Targets/H/T31.lean` at PR41 head `2757349fbd8ca613340b679bbd149f78c2baba6b`, SHA-256 `66420e2424cfd7d93248a3905d19e524e588e09c4abac0e4b8d98803e9979884`.

The production consumer is `ZInQKernel/HDecomp/Descent/B2Glue.lean`, SHA-256 `bd7e603f92928ff3f34121d053be9d945b82968200486fb77ea3a22a968cd545`, with this exact target:

```lean
∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] [IsGalois ℚ L]
  (ε : GQ → GQ → ℂˣ),
  IsSignCocycle ε → InflatedFrom L ε →
  ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)
```

Only six modules under `ZInQKernel/Contrib/UnramifiedCocycle/` and this note are proposed. The baseline definitions, compiler/dependency pins, root imports, registry, audit code, manuscript, and acceptance policy are unchanged. No unregistered `Targets/H` module is imported and no `T31_holds` provider is declared. This is not a record release, so manuscript/PDF release maintenance does not apply to this focused contribution.

## Closed finite result and explicit witness

The fixed-coefficient theorem has no universe parameters or ambient section hypotheses:

```lean
ZInQ.Contrib.UnramifiedCocycle.finiteCyclicInflation :
  ZInQ.Contrib.UnramifiedCocycle.FiniteCyclicInflation
```

Its proposition expands to:

```lean
∀ (n : ℕ) [NeZero n]
  (ε : CyclicGroup n → CyclicGroup n → ℂˣ),
  IsSignCocycle ε → SignCob (pull (cyclicReduction n) ε)
```

Here `CyclicGroup n = Multiplicative (ZMod n)`, and `cyclicReduction n` is the actual residue reduction `C_(2*n) → C_n`, induced by `ZMod.castHom`. It is proved surjective. There is no parity restriction on `n`; `n = 1` is included. Zero is excluded because the required cyclic groups are finite groups of positive order, whereas `ZMod 0` is the integers.

The baseline cocycle predicate does **not** require normalization. Put

```text
c = ε(1,1),    η(x,y) = ε(x,y)c⁻¹,
g = the residue class of 1 in C_n,
B(k) = ∏_{0 ≤ i < k} η(g^i,g)⁻¹,
b(x) = c B(x.toAdd.val),    x ∈ C_(2*n).
```

The proof is the following source-to-consumer calculation:

1. The actual cocycle equation gives `ε(1,x) = ε(x,1) = c`. Hence `η` is normalized, is still sign-valued, and satisfies the same cocycle equation.
2. Induction on `l` proves `η(g^k,g^l) B(k+l) = B(k)B(l)` (`powerCochain_mul`). This is a literal finite-product calculation, not an appeal to cohomology vanishing.
3. Since `g^n = 1`, `B(2n) = B(n)^2 = 1`; the same identity proves `B(k+2n) = B(k)` for every natural `k`. `nat_mod_of_period` supplies the reduction step when residue coordinates wrap around.
4. Thus `η` inflated to `C_(2n)` is `dB B`. Multiplying the cochain by `c` restores **the original cocycle exactly**, because `dB(cB) = c dB(B)`.
5. Every value of `b` has square `1`, and `b` is locally constant on the discrete finite group. `signCob_cyclicDouble` packages these into the actual baseline `SignCob`.

For a topological group `G`, `signCob_of_cyclicLift` consumes actual homomorphisms

```text
q : G → C_n,    q₂ : G → C_(2n),
Continuous q₂,    cyclicReduction n ∘ q₂ = q
```

and constructs `SignCob (pull q ε)`. Continuity of the lift, not just existence of an abstract cyclic extension, is an explicit input.

## Genuine finite Galois descent and actual field cases

`FiniteQuotient.lean` defines `finiteRestriction L : GQ →* Gal(L/ℚ)` by Mathlib's genuine normal restriction. Its surjectivity supplies a set-theoretic section; that section is **not** asserted to be a homomorphism. The baseline `InflatedFrom` predicate and `AlgEquiv.restrictNormal_commutes` prove

```text
finiteCocycle L ε (finiteRestriction L σ) (finiteRestriction L τ) = ε σ τ.
```

Descent preserves the sign and cocycle equations. The genuine finite Galois group has discrete Krull topology, so the descended cochain is locally constant.

`ArithmeticBridge.lean` proves `unramifiedAt_iff_prime`: the original ramification-index condition is equivalent to `Algebra.IsUnramifiedAt ℤ P` at every prime `P` containing `p`. The `NumberField L` instance is derived from the original finite-dimensional hypothesis, not added to the statement. This proves the integral predicate transition; it does not identify a completed extension or construct an absolute residue quotient.

`ExceptionalCases.lean` discharges the actual degree-one case `InflatedFrom ⊥ ε` at every finite prime. It also handles a trivial actual finite local action directly.

`OddOrder.lean` gives a stronger actual-field branch:

```lean
signCob_of_odd_degree
  (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] [IsGalois ℚ L]
  (hodd : Odd (Module.finrank ℚ L))
  (ε : GQ → GQ → ℂˣ)
  (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) : SignCob ε
```

For any finite odd-order group, the cochain is the literal product `B(g) = ∏ x, ε(g,x)`. Multiplying the cocycle equation over the **entire group**, and reindexing by the proved bijection `x ↦ h*x`, gives

```text
ε(g,h)^|G| B(gh) = B(g)B(h).
```

Sign values and odd `|G|` reduce the exponent to `ε(g,h)`. This works without normalization. For the actual finite Galois group, Mathlib's `Nat.card Gal(L/ℚ) = finrank ℚ L` supplies the order comparison, and continuity of actual restriction supplies the inflated global cochain. `signCob_local_of_odd_degree` then covers every finite prime, including `2`, without even needing unramifiedness.

## Exact remaining arithmetic input

The supplied assembly theorem is explicitly conditional:

```lean
leafUnramified_of_cyclicBridge : UnramifiedCyclicBridge → LeafUnramified
```

`UnramifiedCyclicBridge` asks for `Nonempty (LocalCyclicLift L p)` for every original finite Galois `L` and every `p` satisfying `UnramifiedAt L p`. The required data are:

```text
n > 0
q : GQp p →* C_n
f : C_n →* Gal(L/ℚ)
q₂ : GQp p →* C_(2n)
Continuous q₂
cyclicReduction n ∘ q₂ = q
f ∘ q = finiteRestriction L ∘ resp p
```

These equalities concern the original field and the original decomposition-group map. The cochain consumer requires these maps and their compatibility; it does not need a separate surjectivity premise for `q` or `q₂`. No such map data are constructed here for arbitrary unramified fields.

A complete arithmetic supplier must connect the global ideal condition to the extension selected by the embedding underlying `resp p`, identify its finite unramified residue/Frobenius action, construct a compatible unramified level of degree `2n`, and prove continuity and the displayed equalities. This must cover every prime, both parities of `n`, and the identity quotient. An abstract `IsCyclic` assertion or a statement that `H²(ℤ̂, ±1)` vanishes does not supply those maps.

The current assembly takes the all-field bridge, which is sufficient but stronger than necessary after the separate odd-degree theorem. An integration can bypass the odd-degree branch using that theorem; genuine even-degree unramified cases still need arithmetic work. No stronger claim is made about an unproved residue or Frobenius construction.

## Hypothesis and transition checks

- **Source hypotheses:** original `IsSignCocycle` and `InflatedFrom` are preserved; normalization is derived.
- **Constructed objects:** actual cyclic residue groups, complex units, finite Galois restriction, and baseline `resp p` are used.
- **Index coverage:** the power proof covers all natural exponents and every `n ≥ 1`; the odd-order product is over the whole finite group. The missing field supplier must cover all required `L,p`.
- **Maps:** residue reduction is specified, and both lift compatibility and agreement with the actual finite field action are explicit fields.
- **Consumed object:** `finiteCocycle_apply` and `action_compatible` identify the pulled cocycle with `pull (resp p) ε`, not just with a related cohomology class.
- **Coefficients and normalization:** all witnesses are sign-valued complex-unit cochains; `c = ε(1,1)` is restored. The action is the baseline's trivial action.
- **Local conditions:** finite/discrete local constancy and continuous pullback are proved. Integral unramifiedness is connected to the actual algebra predicate. The absolute unramified field transition remains unresolved.
- **Exceptional cases:** `n = 1`, unnormalized constant `-1`, both parities of `n`, the actual bottom field, and all finite primes in the odd-degree branch are covered.
- **Downstream strength:** the finite helper is closed; the arithmetic leaf assembly retains its explicit bridge hypothesis. It is not a registered full-leaf provider.

## Adverse cases and reconstruction findings

1. The initial description's normalization wording was not an extra target hypothesis. `constantMinusOne_isSignCocycle` and `constantMinusOne_cochain` prove that a valid constant `-1` cocycle requires restoration of `c`; its cochain is `-1`, not `1`. The normalization issue is handled in every current finite cyclic use. The odd-order proof accepts unnormalized cocycles directly.
2. `orderTwoCarry` is a genuine sign cocycle on `C_2`, proved **not** to be a sign coboundary there. After inflation to `C_4`, its explicit cochain is `(-1)^(floor(k/2))`. The two-element case split and all four residue coordinates are proved, not sampled. Thus the original cocycles have not been made trivial by definition.
3. The missing absolute unramified bridge is a formalization obligation, not a counterexample to the mathematical theorem. The search/read scope here was the frozen statement, production definitions, and the named Mathlib suppliers below. This note does not classify the full historical justification or claim novelty; historical manuscript and published Serre-source incorporation remain outside this contribution's reviewed scope.
4. No Brauer/cohomology comparison or half-character contribution is imported or duplicated. No external proof source was ported or vendored for this packet.

## Verification and reproduction

Lean: `4.35.0`, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).

All six modules compile. The unchanged `scripts/audit_kernel.lean` (SHA-256 `673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc`) replayed **105 declarations in six modules**, with no runtime declaration skipped. The actual dependency closure uses only `propext`, `Classical.choice`, and `Quot.sound`. The scoped report marks `FiniteCyclicInflation` as `proved_exact_type`, `LeafUnramified` as `open`, and `protocol_acceptance` as `false`. This is not a whole-project audit or independent acceptance.

The following command bodies reproduce the scope. `PROOF_GATE` denotes the caller-provided resource wrapper; its machine-local path is not part of this public note. Session runs used that wrapper, two Lean threads, and the caller's four-command global limit.

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/UnramifiedCocycle
for m in PowerCochain CyclicInflation FiniteQuotient ArithmeticBridge ExceptionalCases OddOrder; do
  LEAN_NUM_THREADS=2 python3 "$PROOF_GATE" lake env lean -j2 \
    -o ".lake/build/lib/lean/ZInQKernel/Contrib/UnramifiedCocycle/$m.olean" \
    "ZInQKernel/Contrib/UnramifiedCocycle/$m.lean" || exit 1
done
```

For scoped replay, create `build/t31/scoped-spec.json` with this data, then run the command below:

```json
{
  "modules": [
    "ZInQKernel.Contrib.UnramifiedCocycle.PowerCochain",
    "ZInQKernel.Contrib.UnramifiedCocycle.CyclicInflation",
    "ZInQKernel.Contrib.UnramifiedCocycle.FiniteQuotient",
    "ZInQKernel.Contrib.UnramifiedCocycle.ArithmeticBridge",
    "ZInQKernel.Contrib.UnramifiedCocycle.ExceptionalCases",
    "ZInQKernel.Contrib.UnramifiedCocycle.OddOrder"
  ],
  "headline": {
    "declaration": "ZInQ.Contrib.UnramifiedCocycle.finiteCyclicInflation",
    "type_declaration": "ZInQ.Contrib.UnramifiedCocycle.finiteCyclicInflation_explicit"
  },
  "exports": [],
  "targets": [
    {
      "declaration": "ZInQ.Contrib.UnramifiedCocycle.FiniteCyclicInflation",
      "provider": "ZInQ.Contrib.UnramifiedCocycle.finiteCyclicInflation"
    },
    {
      "declaration": "GlueDescent.B2Q.LeafUnramified",
      "provider": "ZInQ.Contrib.H.T31_holds"
    }
  ]
}
```

```sh
LEAN_NUM_THREADS=2 python3 "$PROOF_GATE" lake env lean -j2 --run \
  scripts/audit_kernel.lean build/t31/scoped-spec.json build/t31/audit.json
```

The recorded run additionally checked the presence of the named helper exports. Export-presence selection does not narrow the replay: every declaration in all six listed modules is replayed in either case.

### Frozen contribution SHA-256

Paths below are relative to `ZInQKernel/Contrib/UnramifiedCocycle/`:

```text
ArithmeticBridge.lean  9ee968d0fd9c0898346b2623282e1f98b6568b329c30201ff831965f211883ca
CyclicInflation.lean   6682d7410edf63ff9363f21d60f1c6f5d649b6ed960bcc0f6538615cc89f9030
ExceptionalCases.lean  113fda4e0b9383d44a0ea2159b2d0b38824946cffa6c6613e4e30b4a7fdcd5bf
FiniteQuotient.lean    5e7f2494b35375bfdc4e549f1539fe43503007838e277a3cf6389ce713063390
OddOrder.lean          e91993bd0275bf684447d8a27dd7cd7c75e0adf2aeb2df92bbfc0e3f415973b1
PowerCochain.lean      fffc12b21af693b1f91243f80261715cdd41e2a190a7877c486c58dc0a5d4760
```

### Imported supplier provenance

The existing Mathlib dependency is imported, not copied into this contribution. Its source headers identify Apache-2.0; `LICENSE` SHA-256 is `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`. No new dependency is introduced. These supplier paths are relative to the pinned Mathlib repository:

```text
Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
  45b548e8d8491da4820c71eb29b0a2c92786f98e300d947e677f6fbe16e6f78a
  prod_range_succ, prod_mul_distrib, prod_const
Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
  b39f19daf0988119572dc908b7d70c9b1b0a7c597f61e3f217acf2d8ed69ccd9
  prod_pow, Fintype.prod_equiv
Mathlib/Data/ZMod/Basic.lean
  f86120453447f00e0c87188381e0e8d15e0d8c85a080c8f8a8ba2da04f5e2f8a
  castHom, castHom_surjective, natCast_zmod_val, val_add
Mathlib/Algebra/Group/TypeTags/Basic.lean
  eacdf256d38ddbe5c16b7fc7611613ce7b29f7d8b9320facccc46517bf88f31c
  multiplicative/additive power and coordinate identifications
Mathlib/Topology/Instances/ZMod.lean
  1e90e84426475ff4f6b14c863c0b881c5e4018de49efe7a75a0f600297fefbeb
  discrete topology on the actual residue groups
Mathlib/Topology/LocallyConstant/Basic.lean
  e3bb2d2c51ec6c7a390319f826bf2564394cc486adb0ca524f128cf8fdbf8270
  of_discrete, comp_continuous
Mathlib/FieldTheory/Normal/Basic.lean
  5be9073482541e9f8377e915cf0d7964155468342fc045ab1e470e387abd34c4
  restrictNormalHom_surjective
Mathlib/FieldTheory/Normal/Defs.lean
  131279d5867651ea15aecc6442076b7ff3d4b165265cec7533cfbc504a164389
  restrictNormal_commutes
Mathlib/FieldTheory/KrullTopology.lean
  2de23536f3f6b0376b53ffc8be26e5b919050d1704fc71d2a5f533a755661e2c
  krullTopology_discreteTopology_of_finiteDimensional
Mathlib/FieldTheory/Galois/Profinite.lean
  fc73d2ca5d71085e817689303741f1e98e52856b0f52efe34abd480605c11897
  restrictNormalHom_continuous
Mathlib/FieldTheory/Galois/Basic.lean
  5455e013f4173fed23bd28270503eea43e3957ee09e9daa2dde5f1eec47c550a
  IsGalois.card_aut_eq_finrank (lines 107-124)
Mathlib/NumberTheory/NumberField/Basic.lean
  274c1010666fcdd4a1b6d9cdc120d54f3b54fe2a8cdf57bf40f0a363aa2229ff
  NumberField.of_module_finite and ring-of-integers finite-module instances
Mathlib/RingTheory/RamificationInertia/Ramification.lean
  21f8b46d93925fdbae8c5ced0bcf78049d5be305a34ca9602c7b34df20aebe02
  ramificationIdx_eq_one_iff
Mathlib/NumberTheory/RamificationInertia/Unramified.lean
  fa34565f71e4f3746ceca739cce9ce298d647ec66fe14909dae37a36f5653efd
  imported finite-residue/separability infrastructure
```
