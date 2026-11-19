# Side-identification audit


## Scope note (2026-11-18)

The frame of `InnerLimitSwitchInputsIso` keeps the field `primitive` (some coordinate of the class is nonzero modulo the maximal ideal), which is residue-primitivity. The manuscript only has the class nonzero, with the primitive kernel vector proved over the discrete valuation ring (tex 4987-4992); residue-primitivity is a departure from the text. The structure also keeps no side-to-fibre tie beyond the constructed H^1 equivalences. A repaired structure with a nonvanishing class and chain-level side homotopy equivalences is being built on the integration branch; this interface maps into it.

## Exact consumers

The complete structure-name search in `CloudB3RC53/SwitchInputs/` finds
`InnerLimitWiring.lean` only. In `OneProof/RC/Wiring/`, the direct consumers
are `InnerLimitRegularity.lean` and the explanatory references in
`InnerLimitRegularityPK.lean`.

- `InnerLimitWiring.lean:212–226`: `InnerLimitSwitchInputs.toGalois`
  forwards the retained step, coordinate step and both literal equalities.
  It does not use either equality to transport a class, functional or map.
- `SwitchInputs/GenuineSteps.lean:512–553`:
  `GaloisSwitchData.toHeightOneSwitchData` discards both equalities when it
  extracts each switch. In the nonquadratic branch, it uses only
  `QuasiNonquadStep.toNonquadDims`, together with the coordinate step and
  the specified successor. The quadratic branches are excluded here by
  `hnq`.
- `SwitchInputs/GenuineSteps.lean:284–300`: the dimension proof uses
  `φ`, `φ'` to transport finite-dimensionality and cohomology ranks to the
  two stage fibres; the shared strict rank, duality and detection supply
  the exact-sequence dimension equations. These equivalences are already
  fields of every retained step.
- `UniformSwitch/Regularity.lean:358–400`: the original descent consumer
  uses the dimension drop and the coordinate relation. Primitivity gives
  positivity; the unchanged two-term coordinate theorem gives terminal
  integrality. It reads no Selmer-data equality or local-condition image.
- `InnerLimitRegularity.lean:273–292`: `ILSwitchInputs.toInner` forwards
  the same equalities and `regular_of_ILSwitchInputs` calls the original
  regularity theorem. The higher leaf at lines 308–366 consumes the
  resulting local regularity, not the equalities.
- `InnerLimitRegularityPK.lean:187–225`: the primitive-kernel and
  nonzero-class consumers already construct the lower switching data
  directly, discarding both side equalities.

## Remaining fields

`stage` and `model` fix each family fibre rank and provide the inverse
cohomology identifications. `hz0` and `hw0` retain the actual starting class
and paired functional; the lower descent does not read them again. `hu0`
is used in the final equality transporting the starting stage coordinate
to `u`. `hnq` excludes the quadratic branches. `primitive` is consumed only
for positivity of reachable fibre dimensions. The step's dependent stage
types retain the identity of the next configuration, and its `CoordStep`
provides the integral coordinate multiplier.

## Minimal replacement

No additional equality of ranks is needed. The retained step is typed
between the stages of `c` and `next c p`; its two cohomology equivalences,
composed with the inverse family models, construct linear equivalences to
the prescribed family fibres. Consecutive switches are connected by
composing the singular equivalence with the inverse next finite
equivalence. They need not identify their local-condition inclusions.

`Interface.lean` retains all family and starting fields and the original
retained-step data. Its regularity theorem reuses the original
`QuasiNonquadStep.toNonquadDims` and `regular_of_switchData`, with no
regularity statement, terminal-stage choice or dimension-drop conclusion
among the new input fields.

## Producer boundary

The original `SwitchWiring.RemainingInputs` still contains condition tags
and column comparisons which imply the literal equalities. Merely mapping
that old structure into the new one cannot make the old structure
inhabited above dimension three. The adapted producer therefore also has
a new remaining-input structure omitting those four comparisons/tags,
while retaining each original arithmetic request, detecting label,
integral side models and coordinate step. The original step producer
constructs the cohomological switch on the same retained output.

## Mathematical scope

The repaired interface proves the same conditional local regularity. It
does not construct the remaining number-field, retained arithmetic,
cochain-model or coordinate inputs. A finite-dimensional example tests
the weakened model-level interface through two switches, starting in
cohomology dimension five; it is not an arithmetic realization.

Sources: tex L4391–4451, L4976–5003, L5027–5086, L5137–5195.
