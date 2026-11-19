# Target 9: strict local symmetry and the degree-two audit

The degree-≤1 reduction is proved for the defined genuine derivative, Kummer, and unramified conditions. The all-places target is not closed when unchanged full local complexes are retained: they have degree-two cochains.

Base revision: `a6c70bd54e403ce3ead8ff2b8e40f80445fe58cc`.

## Mathematical statement of the targets

Let S be the strict local-condition complex, U the relaxed complex, f : S → U their inclusion, and ι : U → L the local cochain map. Let h be the forward isotropy homotopy for a c-symmetric pairing. For s ∈ S² and t ∈ S¹, the general target is

    h₂₁(s, f₁t) = c · h₁₂(t, f₂s)
      + X(ι₂f₂s, ι₁f₁t) − Z(ι₂f₂s, ι₂f₂(d_S t)).

`Hsw.StrictSymm` requires this equality in E². `Hsw.StrictSymmTrunc` requires its deficit to be a local coboundary: it equals d_E w for some w ∈ E¹. Equivalently, the equality holds in E²/d_E(E¹), the degree-two term of the canonical target truncation.

The integration convention `SelmerComplex.StrictSymm` is placewise and uses the deficit

    h₂₁(s, φ₁t) − c · h₁₂(t, φ₂s)
      − H₂₁(ι₂φ₂s, ι₁φ₁t),

again modulo d_E(E¹). Here H₂₁(x,b)(g,h) = β(x(g,h), g·b(h) + b(g)). The conventions are not silently identified. Both conditions follow from S² = 0, by bilinearity; this does not require S¹ = 0.

## Actual condition definitions and manuscript support

### Derivative conditions

`GenuineInst.strictCxK`, `strictToLocalK`, and `strictAt` give the actual truncation [Z⁰ → 0]. `relaxedCxK`, `relaxedToLocalK`, and `relaxedAt` give [C⁰ → Z¹]. The field-generic switch uses `SwitchInputs.strSubK`, `relSubK`, `sideSubK`, and `switchFamK`. Their submodule family `degS` is zero outside degrees 0 and 1; its strict degree-one term is also zero.

Manuscript Lemma `ex:limits-derivative-switch`, tex 4834–4887, explicitly distinguishes the ambient complex

    L_v = D⁰ ⊕ (F_v ⊕ S_v)[−1] ⊕ D²[−2]

from its four conditions

    U_str = D⁰,
    U_rel = D⁰ ⊕ (F_v ⊕ S_v)[−1],
    U_F = D⁰ ⊕ F_v[−1],
    U_S = D⁰ ⊕ S_v[−1].

The ambient D² is in none of them. In particular tex 4874–4876 explicitly says the relaxed derivative condition is not the full local complex. The switch discussion at tex 5055–5061 repeats these conventions. Several earlier module docstrings refer to tex 5068–5072; in this revision those lines concern localization duality instead. The exact definitions occur at tex 4834–4876 and 5060–5061.

`derivativeAt_degreeTwoZero` proves vanishing for both genuine per-place truncations over any commutative coefficient ring, including the finite arithmetic coefficient rings.

### Kummer conditions

`CoefModules.cocycleCondition` is the explicit subcomplex with

    U⁰ = C⁰_cont,
    U¹ = span_Kummer ⊔ B¹_cont,
    Uⁿ = 0 for n ≥ 2 or n < 0.

`kummerConditionIn` specializes its cocycle submodule to the actual extended Kummer cocycles. `kummerAt` uses the actual local elliptic curve and an equivariant coefficient map. `KummerMaps.actualKummerAt` uses the actual twist and `kummerIota`; `actualKummerAtS` uses the corresponding inflated coefficient map.

Manuscript Lemma `ex:arith-local-kummer`, tex 3413–3456, retains two-primary torsion in degree zero and the Kummer quotient in degree one after derived reduction. Degree-zero torsion was not removed in the proof here. The three named Kummer degree-two vanishing theorems apply to their genuine defined subcomplexes, not a zero-pairing example.

The existing comparison discussion in `KummerMaps.KummerImage` distinguishes this explicit finite-level subcomplex from the manuscript's derived object. These degree bounds do not prove a new derived comparison or compatibility of its chosen isotropy homotopies.

### Unramified conditions

`CoefModules.urAt` is the genuine map from the two-term unramified complex [M₀ --(Φ−1)--> M₀] in degrees zero and one, inflated to local continuous cochains. `urAt_degreeTwoZero` proves its degree-two term is zero.

Manuscript tex 3471–3498 specifies this complex and the retention of arbitrary old conditions during support changes.

### The retained-full-condition caveat

`CoefModules.fullAt` is the full local continuous cochain complex with the identity map. For a nontrivial coefficient module, a nonzero constant continuous 2-cochain proves

    ¬ DegreeTwoZero (fullAt ... v).U.

This is `fullAt_not_degreeTwoZero`. It concerns the cochain term, not H²; acyclicity would not make all its 2-cochains zero.

The switch keeps the old condition at every place other than the new derivative place. This is literal in `switchStrK` and `switchFamK`, and the manuscript retains primitive ramified full conditions at tex 5055–5061. The proved exact criterion is

    DegreeTwoZero (switchFamK ... q old T).Ustr
      ↔ ∀ v, v ≠ q → DegreeTwoZero (old v).cx.

Thus a blanket assertion that the complete global strict family has no degree-two terms would be unjustified in the presence of unchanged full conditions.

## Formal results and verification

`DegreeTwoZero U` means exactly `∀ x : U.X 2, x = 0`.

The contribution contains thirteen theorems and one reverse-isotropy construction. The audit records every compiler-printed complete type, with full names and explicit proof arguments, and every `#print axioms` result.

The named actual bounds are:

- `derivativeAt_degreeTwoZero`;
- `kummerAt_degreeTwoZero`;
- `actualKummerAt_degreeTwoZero`;
- `actualKummerAtS_degreeTwoZero`;
- `urAt_degreeTwoZero`.

The exact and truncated target reductions are `strictSymm_of_degreeTwoZero` and `strictSymmTrunc_of_degreeTwoZero`. The latter proves both the pre-quotient coboundary condition and the exact equality after target truncation.

The genuine Galois interface reductions are `genuine_strictSymm_of_degreeTwoZero` and `genuine_strictSymmTrunc_of_degreeTwoZero`. They work for any given forward truncated isotropy datum whose actual strict complexes have the proved degree bound. In particular the integration result replaces its earlier sufficient hypothesis U_str¹ = 0 by U_str² = 0, which applies to Kummer conditions with nonzero degree-one terms. `genuine_reverseIsotropy_of_degreeTwoZero` supplies the genuine reverse field without another strict-symmetry premise.

The supporting results are `degreeTwoZero_pi_iff`, `double_degreeTwoZero`, `switch_degreeTwoZero_iff`, and `fullAt_not_degreeTwoZero`.

The final single-file Lean check succeeds without warnings. No dependency module was built by this contribution. Every axiom report is a subset of `propext`, `Classical.choice`, and `Quot.sound`; `strictSymm_of_degreeTwoZero` uses only `propext` and `Quot.sound`. No new printed premise was introduced.

## What remains open precisely

1. There is no degree-two strict-symmetry obligation for the actual derivative/Kummer/unramified bounded subcomplexes after their degree bounds are connected to the given switch datum.
2. For a complete switch retaining full complexes at old places, the degree-bound route does not discharge the target. One must either construct the required compatible isotropy/cup-one homotopy on those actual full complexes, or use an authorized contraction and prove that replacing them by zero preserves the retained maps, isotropy homotopies, and traced pairing. Manuscript tex 2813–2815 permits replacement only where the displayed contraction exists. That contraction-and-compatibility step is not proved here.
3. The existing arithmetic bindings `FullTorsion` and `IsLocallyQuadAt`, and the finite-level/derived Kummer comparison, have not been discharged by the degree-bound proofs.
4. No target, integration module, manuscript passage, or previously existing source was modified. The contribution is a set of new files on a review branch and has not been integrated.
