# One Atkin–Lehner sign for the actual (O.7) row

**Main result (case b).** `AtkinSign.oddStagedActual` supplies
`Nonempty (OddStagedInstance W)`, the type of `PreLeaves.odd_staged`,
without an `hSign` argument. Its geometry is supplied as
`SpecialFibreAtSigns … w`, where `w` is exactly the sign function
used by the theta stage. The special-fibre quotient identity still
has to be supplied on every supersingular point, before applying
`L` or the detector. It is an **ELLIOT** input from tex 8487–8489.
The other inputs to the existing row and odd instance are unchanged.

## Reading the sign

`O7Assemble.actualStage` takes `w : ℕ → ℤˣ` as a parameter and
passes it to `ThetaClose.actualPmLocal`. Inside that constructor,
`levelRoots` builds a `LevelRoots` with the prescribed
`ParityAt` relation:
`α_p(-1) = w(p) χ_{h_*}(p)^(N.factorization p)`.
The coefficient field and local factors are built with this same
`w`. They do not read the sign from `I.f` or from
`PMAdelic.SpecialFibre`.

The analytic eigenvalue is already defined:
`HeckeRing.GL2.Newform.atkinLehnerSign` in
`ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/AtkinLehner/Sign.lean`.
It is the eigenvalue (±1) of the normalized operator at an exact
divisor on the trivial-nebentypus newform. For a level prime `p`,
`TauCeti.Nat.isExactDivisor_primePow` supplies the exact divisor
`p ^ N.factorization p`. This is the manuscript's intended value of
`w p`; the analytic operator theorem does not mention the elliptic
quotient. The actual consumer carries `I.f` as a weight-two
`Γ₀` cusp form with the elliptic curve's coefficients.

The tree defines the analytic parametrization `CST.phiAn` by the
scaled Eichler integral. No theorem was found identifying the action
of the normalized operator with the action on the rational elliptic
quotient, then on its special fibre. The existing ELLIOT
`atkin_quotient` field already takes the specialized transformation
as input, with a separately supplied integer sign. It cannot
identify an independent `w`. Even given two signed-action
equations, cancellation requires a point whose double is nonzero:
opposite signs agree on points killed by 2, including nonzero
2-torsion. That observation is on-the-spot (c); no such extra
nonvanishing premise is required for the re-encoding.

## Statements

The declarations below are in `ZInQ.Manuscript.RC.AtkinSign`.

| Declaration | Statement and use |
| --- | --- |
| `SpecialFibreAtSigns … w` | Retains the existing coarse fibre, cusp, Jacobian, maps and Hecke/Frobenius identities. The Atkin field states, for `p.Prime`, `0 < N.factorization p`, and `x ∈ X.ss`, that `quotient (divisorClass (center infinity (of (X.W p x) - of (X.W p infinity)))) = (w p : ℤ) • quotient (divisorClass (center infinity (of x)))`. |
| `SpecialFibreAtSigns.toSpecialFibre` | Builds `PMAdelic.SpecialFibre …` with `atkinSign p := (w p : ℤ)`. The sign range follows from the integer unit; the quotient field is the input above. Every other field is copied directly. The adapter is (c). |
| `SpecialFibreAtSigns.atkinSign_eq` | `(w p : ℤ) = S.toSpecialFibre.atkinSign p` for all `p`, by `rfl` (c). The transported `GeometricInput` and `PM.Geometry` read this same field. |
| `SpecialFibreAtSigns.ofSpecialFibre` | An old fibre `G` with `(w p : ℤ) = G.atkinSign p` at each level prime gives `SpecialFibreAtSigns … w` by rewriting the quotient equation (c). The conversions may differ on old sign values outside the level, where no Atkin equation or (O.7) move reads them. |
| `actualRowFamily` | For `hD : W.admissible i D`, gives `DatumAt (actualFamily … i) (D.toNat : ℤ) (lamOf W.Mθ L I.selG s.ev i (D.toNat : ℤ))` through the existing row constructor with its former `hSign` set to `fun _ _ => rfl` (c). |
| `oddStagedActual` | With that family and the unchanged phase/coefficient reading, `MultiplierKillsNativeTorsion … L` and `AdmissibleOddSign W.toRCData`, gives `Nonempty (OddStagedInstance W)` (c). |

`geometricInput` and `geometry` are the existing constructors;
they preserve the coarse labels, specialization, cusp images,
and operators when built from the same underlying geometry.
`O7Normalizers.actual_atkin_weight` still matches the Schwartz
factor with the sign of the norm-weighted parametrization;
`PM.Geometry.P_atkin` uses the existing cusp annihilation input. No theta
coefficient, weight, CM point, or precision has been redefined.

## Remaining inputs

| Input | Kind and remaining content |
| --- | --- |
| `w` and fixed stage arithmetic | Data: use the newform eigenvalue as an integer unit at each level prime. There is no new analytic theorem required to define the eigenvalue. The wrapper works with the same supplied `w` for the stage and quotient. |
| `S i : SpecialFibreAtSigns … w` | ELLIOT special-fibre geometry, including the exact Atkin quotient equation above, good Hecke compatibility and Frobenius compatibility. To derive the Atkin equation from the analytic operator would require a bridge through the rational modular parametrization and its specialization; the construction here leaves that existing geometric content in the input. |
| `J i : PMAdelic.JetchevKane …` | Existing named comparison input: coarse supersingular points and their operators, with the source scope below. |
| `hCusp` | ELLIOT (tex 8488–8489, 9338–9339): `L • cusp p = 0` at each level prime. |
| `PointInputs` on the whole admissible family | Existing selector value and reference embedding; ELLIOT point identities `hCM` (the manuscript's application of Cornut–Jetchev) and `hπ` (specialization at the detector's place). These are about individual points before the detector. |
| `ha` | Existing coefficient interface: the fixed integer `W.aθ i D`, multiplied by the reference phase, reads the actual theta coefficient at precision `W.Mθ i`. |
| `hL` and `hsign` | Existing native-torsion annihilation and odd root-number inputs for the odd instance. The global root-number input is distinct from the local `w p`. |

## Known issues

- The inherited source audit records that the Jetchev–Kane citation
  at tex 8468–8474 does not cover level one. Its source locators are
  UNVERIFIED here. The new constructor uses the existing comparison
  as an input and adds no print.
- As in the residual report, `GenusOddInstance.hselG` alone does not
  give selector coverage on every admissible row. The wrapper still
  takes `PointInputs` at every admissible index, including torsion
  rows.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8209–8217, 8295–8306 | The conductor-one point and multiplier are used throughout the admissible filter. | unverified |
| 8462–8474 | Identify coarse supersingular pairs and the adelic class set. The cited scope omits level one. | error |
| 8476–8487 | Extend the parametrization at good reduction and use the good Hecke quotient relation. These geometry fields remain inputs. | unverified |
| 8487–8489 | Use the Atkin eigenvalue on the based degree-zero divisor and recover the affine translation at the moved cusp. The exact quotient identity is retained; no rational-to-special-fibre derivation is supplied. | unverified |
| 8488–8492, 9336–9339 | Kill the cusp translation with `L`; use the already checked detector identity conditional on `hCusp`. | OK |
| 8505–8511, 8531–8534 | Choose the root characters with (O.3) using this sign, also at two when present. | OK |
| 9265–9279 | Identify the reference orbit and its place with the actual CM points. The point identities remain inputs. | unverified |
| 9331–9341, 9359–9362 | The normalizer gives the same sign on the weight and the norm-weighted parametrization. The Lean adapter identifies the two reads of `w` by definition (c). | gap filled |
| 9343–9358 | The division uniformizer uses the Frobenius and norm signs already supplied to the row constructor. | OK |
| 9365–9399 | Sum the orientations at the original precision; use the separate reading for the fixed `W.aθ`. | OK |

## Verification

`AtkinSign.Geometry` and `AtkinSign.Family` each passed a serial
`lake build` in a user scope capped at 60 GB, using compiled dependencies
for the unchanged base. The in-module `#print axioms` commands report
only `propext`, `Classical.choice`, and `Quot.sound` for all six
checked declarations.
