# Characteristic-zero switch residue nondegeneracy

## Result and scope

`Nondegenerate.lean` supplies proved nondegeneracy reductions on the genuine local fibre cochains and on the retained split derivative model. It also proves that the literal finite-target derivative shape consumers cannot have their nondegeneracy premise over a characteristic-zero coefficient field.

The relevant manuscript passages are `diophantine_zq.tex`, lines 2798–2820, 4385–4388, 4391–4451, 4854–4896, 4977–4980, and 5026–5071. In particular, the derivative conditions are `D^0` and `D^0 + (F + S)[-1]`, not zero and the full local complex. The coefficient-stage limit precedes the characteristic-zero field fibre. The moving derivative label is not a fixed local Galois group.

## What is supplied

1. `cupTrace_left_radical` and `cupTrace_right_radical` extract both degree-one radicals from a local duality quasi-isomorphism. Their conclusions are actual cochain boundaries. The right-radical proof uses surjectivity of the derived adjoint; finite-dimensionality is not assumed.
2. `fibreCup_right_radical_VP` instantiates the right-radical result with the genuine pair `VP(alpha)`, `VP(alpha^-1)`, and `Tate1P`, using the existing `NekovarFibreLocalDuality` proposition. Coefficient perfectness, continuity, lattice topology, and the Tate-twist identification are supplied by the existing fibre pairing results. The local trace must induce `H^2 = k(P)`.
3. `resForm_eq_neg_localTrace` identifies the residue with minus the traced local cup product, with the two arguments reversed. It is field-generic. The existing `HswResidual/Residual.lean` and `HswIdent/Identifications.lean` specialize their identifications to `ZMod 2`; they are not characteristic-zero coefficient identifications.
4. `b11_bijective_of_localDuality` extracts perfectness of the split model's degree-one pairing from its local orthogonality quasi-isomorphism. It assumes no residue coordinate identity. `limit_hnd_of_localDuality` consequently supplies exactly the residue nondegeneracy premise of `Hsw.hsw_of_localDuality` on that model. It uses no global duality and no pairing certificate containing the desired residue identity.
5. `fibreLimit_hnd_of_retained` supplies that premise on the realized retained diagram at an odd height-one prime, from `RetainedLimitPairingStages` and the existing retained local-pairing identification. The matrix is the genuine `conjMatrix`, with its square proved to be one. For degree-one nondegeneracy only `epsilon != 0` and `sigma != 0` are needed; no retained global inverse and no unit condition on the degree-two scalar are needed.
6. `hnd_of_localResidueComparison`, `fibre_hnd_of_localComparison_VP`, `hnd_of_splitResidueComparison`, and `hnd_of_comparison_to_retained` transport the local results to the exact shape-consumer premise through explicitly typed cochain and trace comparisons. No residue nondegeneracy is included in these comparison data.
7. `finite_charZero_module_subsingleton` and `genuine_finiteTarget_no_hnd` prove the literal finite-target obstruction. A finite module over a characteristic-zero field is zero, so the traced local product is zero. The rank-four switch quotient and vanishing strict degree-two term give a relaxed cocycle with nonzero quotient class. Thus the consumer's nondegeneracy premise is false, even for an arbitrary linear cone trace.

`limitComparison` constructs all fields of the split comparison for the split model itself, without any perfectness assumption. Thus the comparison is not an empty or inherently nondegenerate hypothesis package.

## Exact remaining comparisons

Put `k = ResAt P`. Let `R` be the actual switch intended by the application, `Ustr` its strict condition, `f : GHom Ustr R.D.U`, `Q : SelPairData (restrictData R.D f) R.D`, and `tr : (coneCx Q.resE).X 3 ->_k k` its actual trace.

For a comparison to the retained derivative model, the precise missing type is

```lean
Nonempty (SplitResidueComparison R Ustr f Q tr
  (localPairingOfMat (D.locK P)))
```

The fields are:

- `localMap : GHom R.D.L (splitLocalComplex k)`, in all degrees;
- `read : GHom R.D.U (splitLocalComplex k)` and `read = ghomComp R.D.ι localMap`;
- `quotient : Coords k →ₗ[k] R.Wrel.toCC.homology 1` and equality of the actual quotient class with the quotient of the reading;
- every split degree-one vector is read from a relaxed cocycle;
- the restriction of the actual cone trace to the local cup product equals `B.b11 (read u) (read t)` on relaxed cocycles.

The complete Lean field types are in `Nondegenerate.lean` and are printed in `Statements.txt`. This asks for maps of the full local complex, their compatibility with the actual local-condition map, the quotient comparison, and trace normalization. It is not a renaming of residue nondegeneracy and does not assume switch coordinates.

For the literal retained model

```lean
R = limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)
Q = retainedPairing U hU C D P
tr = limitTrace (ResAt P)
```

this comparison is already constructed by `limitComparison`. What is not proved here is the identification of a different manuscript or derivative-family realization with these actual retained complexes and traced cup products.

The retained arithmetic provenance still has its existing type:

```lean
hloc : localPairingOfMat (D.locK P) =
  transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)
```

with `D : RetainedLimitPairingStages U C`, `epsilon != 0`, and `sigma != 0`. No new nondegeneracy assumption is substituted for `hloc`. The existing coefficient formula `betaConj_vpBasis` identifies the genuine conjugate fibre coefficient pairing with the transported cross pairing; it does not by itself identify the local cochain trace and the switch quotient.

For a comparison to a genuine fixed-place fibre pairing, the precise missing type is

```lean
Nonempty (LocalResidueComparison R Ustr f Q tr
  (fibreLocalPairing W P α q) trq)
```

Its two comparison maps go from `R.D.L` to the genuine local complexes of `VP(alpha)` and `VP(alpha^-1)`. It records the quotient comparison, surjectivity of the local tests modulo boundaries, and equality of the traced cup products. The remaining arithmetic inputs of this route are the existing `NekovarFibreLocalDuality K`, `NekovarFibreSetting K S`, and `InducesIsoH2 trq`. This route does not identify a moving derivative label with one fixed `q`.

## Literal consumer substitution

The exact premise taken by both derivative shape files is

```lean
∀ t (ht : R.D.U.d 1 2 rfl t = 0),
  (∀ u (_hu : R.D.U.d 1 2 rfl u = 0),
    resForm R Ustr f Q tr t u = 0) →
  gClass R t ht = 0
```

For those files substitute

```lean
R = (derivSwitch F eR).toQuasi
Ustr = piCx (derivSwitch F eR).US
f = piMap (derivSwitch F eR).φ
Q = galoisPairData K S k β hβ
  (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I
```

A scratch specialization checks this exact type. The finite-target hypotheses of these literal consumers remain incompatible with nondegeneracy at characteristic-zero coefficients. The non-discrete characteristic-zero application must use the retained model or an appropriate non-discrete switch interface, not instantiate the residual theorem with `Finite T`.

## Verification evidence

- The source compiles with Lean 4.35.0 by the prescribed single-file invocation, with six threads, affinity 16–31, and niceness 10.
- `Statements.txt` records every exported theorem's complete printed Lean type and its axiom report, as well as the comparison structures and the four definitions.
- Every one of the sixteen theorem reports contains only `propext`, `Classical.choice`, and `Quot.sound`; the four definition reports have the same allowed set.
- The audit uses a byte-identical copy of the complete source followed by scratch print commands and the consumer-type specialization. The source itself contains no print or check commands.
- The source contains no prohibited proof command or declaration and its heartbeat bound is 800000. All twenty-two top-level declarations have kind and manuscript-locator docstrings.

These are compiled mathematical reductions and comparison contracts. They do not discharge the existing printed local-duality proposition, prove the retained arithmetic provenance, or make the residual consumers characteristic-zero theorems.
