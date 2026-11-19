# Appendix F: the supersingular stage function

The stage function on `Eichler.ClassSet R` is
`P_M(z) = λ_M(L • π_ℓ₀(z))` in `ZMod (2 ^ M)`. From the geometric inputs at
tex 8462–8490, it has the good Hecke eigenvalue `a_p`, the Atkin–Lehner
eigenvalue `w_{p^e}`, and the division-uniformizer eigenvalue `+1`. The last
two are available both as equalities of residues and as divisibility statements
for arbitrary integral lifts. The two existing theta stage records use this
same function. App F uses its image in `𝒪/2^M𝒪`; Visibility uses an integral
lift, and relifting preserves every coefficient modulo `2^M𝒪`.

All three new Lean files compiled individually with `lake env lean --threads=1`.
The 24 `#print axioms` checks use only `propext`, `Classical.choice`, and `Quot.sound`.

## Statements and consumers

Names below are in `ZInQ.Manuscript.RC.PM`. Write `X = Eichler.ClassSet R`,
`n = 2^M`, `u` for an integer lift and `w = w_{p^e}`. Notation
`A ≡ B mod n𝒪` means `(2 : 𝒪)^M ∣ A - B`.

| File and declaration | Statement and consumer |
| --- | --- |
| `Stage.lean`: `Geometry.pi_eq_of_rel` | Equivalent locally principal right ideals give equal specialized points. Supplies the class function used for both stages. |
| `Stage.lean`: `lam_frob` | `λ_M(Frob x) = λ_M(x)` on the quadratic fixed subgroup. Uses the reduced Kummer map and the fixed finite row. Supplies the sign used in `Odd.orientation_signs`. |
| `Stage.lean`: `scaled`, `P`, `P_eq_of_rel` | `scaled : E(𝔽_{ℓ₀²}) →+ ZMod n` is `x ↦ λ_M(L • x)`; `P = scaled ∘ π_ℓ₀` and `P([I]) = P([J])` for equivalent ideals. These supply the common `P` and the additivity used in `Visibility.kummer_heegnerSum`. |
| `Stage.lean`: `P_hecke_at` | At a prime `p ∤ Nℓ₀`, for the given `LineIndex`, `∑ i, P_M(nbAt lines z i) = (a_p : ZMod n) * P_M(z)`. |
| `Stage.lean`: `P_hecke` | The same equality for `Eichler.nb` at every prime of `Good`, when `Good` implies prime and prime to `Nℓ₀`. Supplies `AppF.ThetaStage.hecke` and hence the transfer of the Brandt operator. |
| `Stage.lean`: `P_atkin` | At `p^e ‖ N`, if `L • cusp p = 0`, then `P_M(W_{p^e}z) = (w : ZMod n) * P_M(z)`. Supplies the parametrization sign of `Odd.orientation_signs`. |
| `Stage.lean`: `P_uniformizer` | `P_M(Uz) = P_M(z)` for the right division-uniformizer operation. Supplies the other parametrization sign of `Odd.orientation_signs`. |
| `Theta.lean`: `isLift_valLift` | The least nonnegative representative has residue `P_M(z)` at every class. Gives one valid choice of `Visibility.ThetaStage.P`. |
| `Theta.lean`: `dvd_sub_of_cast_eq` (private), `lifts_dvd` | Equal residues of integers imply divisibility of their difference by `n`; applied pointwise to two lifts of `P_M`. Supplies the hypothesis to `Visibility.thetaCoeff_relift_dvd`. |
| `Theta.lean`: `lift_atkin_dvd`, `lift_uniformizer_dvd` | `n ∣ u(W_{p^e}z) - w u(z)` and `n ∣ u(Uz) - u(z)`. Lift forms for the orientation comparison. |
| `Theta.lean`: `normWeighted_atkin_dvd`, `normWeighted_uniformizer_dvd` | Given the corresponding local norm-character identity, `χN(Wz) u(Wz) ≡ (w χ_p^e) χN(z) u(z) mod n𝒪` and `χN(Uz) u(Uz) ≡ -χN(z) u(z) mod n𝒪`. These give the parametrization factors of `Odd.orientation_signs` and the pointwise input to the orientation sum in `Visibility.ComparisonCore.orientation`. |
| `Theta.lean`: `lift_at_reduction` | For additive reduction `red` and `π_ℓ₀(z) = red(y)`, `n ∣ u(z) - val((λ_M ∘ red)(L • y))`. At a Heegner conjugate, this is the lift premise of `Visibility.lamOf_reduction` with `StageKummer` equal to that same composite. |
| `Theta.lean`: `visibilityStage`, `visibility_relift_dvd` | Fill `X`, `fintypeX`, `G`, `card_G_dvd` from the order and `P` from any lift. For a second lift `v`, `thetaCoeff (S.relift v) k ≡ thetaCoeff S k mod n𝒪` at every index. The remaining fields come from the theta data. |
| `Theta.lean`: `stageCast`, `stageCast_P` | The canonical ring map `ZMod n →+* 𝒪/2^M𝒪` sends `P_M(z)` to the class of `u(z)` for every lift `u`. This is the identification of the two `ThetaStage.P` fields. |
| `Theta.lean`: `appFStage` | Assemble `X`, `fin`, `w`, `w_pos`, `w_dvd`, `P`, `nb`, `hecke` and `adjoint` in the existing record. The weights and adjointness are those of `Eichler`; the coefficient and local frame inputs remain parameters. |
| `DetectorRow.lean`: `Evaluation.ofTateRow`, `Evaluation.ofTateRow_row_proj` | For a torsion specialization equivalence `sp`, the reduced row is `finiteRow b M ∘ sp⁻¹`; on `sp(proj M t)` its value is `b(t) mod 2^M`. Supplies the row in the same `λ_M` used on both sides. |

## Geometric input and provenance

| Input | Manuscript lines and provenance |
| --- | --- |
| `Geometry.ram`: ramification at `ℓ₀,∞` | 8462–8463; existing PRINT `AppF.VoightMainThm1461`, Voight Main Theorem 14.6.1 (locator UNVERIFIED). |
| `Geometry.eichler`: Eichler order at level `N`, prime to `ℓ₀` | 8464, 8469, 8477; ELLIOT, using the local normal form of `Eichler.IsEichler` already in the tree. |
| `Geometry.SS`, `classes`: coarse supersingular pairs and their class-set description, with the model over the quadratic residue field | 8465–8474; Jetchev–Kane §§1.1–1.2 and 2.5 as cited (locators UNVERIFIED). The formal input is the equivalence with the ideal class set. |
| `Geometry.specialize`: reduction of the parametrization `π` based at `∞` into `E(𝔽_{ℓ₀²})` | 8476–8479; ELLIOT. The reduction and extension of the map are taken as input. |
| `Geometry.hecke`: the sum of specialized points over ideal neighbours equals `a_p(E) • π_ℓ₀(z)` | 8480–8487; ELLIOT, from the quotient intertwining with `[a_p]` and `T_p(∞)=(p+1)∞`. The `LineIndex` is supplied; `nbAt` gives the classes with multiplicity. |
| `Geometry.atkin`, `atkin_involutive`, `atkinSign`, `atkinSign_eq`, `cusp`, `atkin_affine` | 8282–8285, 8487–8489, 9331–9339; ELLIOT. Supply the involution at each exact level power, its sign, the reduced point `π(W_{p^e}∞)`, and the affine parametrization identity before scaling. The eigenrelation separately takes `L • cusp p = 0`, from the multiplier at 8282–8285 and 8295–8297. |
| `Geometry.frobSS` | 8469–8474; arithmetic Frobenius in the supersingular model, Jetchev–Kane as cited (locators UNVERIFIED). |
| `Geometry.uniformizer`, `uniformizer_spec` | 8489–8490, 9343–9358; ELLIOT. The right uniformizer operation on the class set carries the stated Frobenius action on pairs. |
| `Geometry.specialize_frob` | 9347–9355; ELLIOT. The specialization intertwines that Frobenius and the arithmetic Frobenius on the reduced elliptic curve. |
| `Evaluation.ell_ne_two`, `square_trivial`, `row`, `row_fixed` | 8358–8390, 8439–8456; ELLIOT. The detecting prime is odd; the square of arithmetic Frobenius fixes the finite torsion; the reduced row is Frobenius invariant. `Stages.reducedKappa` and `Stages.lambda_frobenius_plus` supply the Kummer construction and its equivariance. |
| Torsion and Heegner specialization, where used | 8392–8395, 8452–8459, 9278–9291; ELLIOT. `ofTateRow` takes the torsion specialization and invariance at the chosen place. `lift_at_reduction` takes the equality of the two specialized points of the existing comparison and an additive reduction map. |
| Norm-character identities, where used | 9336–9339, 9346–9358, 9359–9362; ELLIOT. The weighted congruences take the reduced norm-character factors `χ_p^e` and `-1` separately from the point eigenvalues. |

Neither the printed-form leaf list nor the existing theta and stage interfaces
change. The geometric hypotheses are data on one stage. Constructing an actual
instance requires the supersingular/adelic correspondence, specialization of
the modular parametrization and its relations with these correspondences. This
is a missing modular-curve and reduction layer, not an additional algebraic
lemma. The `Geometry` record is the finite comparison it needs to supply. At a
chosen place, matching the finite detector row requires the single
specialization equivalence on `2^M`-torsion and Frobenius compatibility there.
Matching a Heegner evaluation additionally requires the pointwise reduction
identity used by `Visibility.lamOf_reduction`. The line-index, local-order,
coefficient, and witness work remain with their respective tasks.

## Known issues

- Jetchev–Kane and Voight locators are UNVERIFIED. In particular, the scope of
  the citation for arbitrary level prime to the detecting prime, including
  powers of two, was not checked independently.
- The pre-existing `Odd.lambda_frobenius_sign` uses a row on all geometric
  points. The manuscript needs a row on finite torsion. This work uses
  `Stages.lambda_frobenius_plus`, the finite-torsion interface.
- No mathematical error found in the checked manuscript steps.

## Manuscript check

- 8282–8285, 8295–8297: OK — killing the cuspidal image is what removes the Atkin–Lehner translation.
- 8378–8390, 8439–8456: OK — the arithmetic `ℓ₀`-Frobenius is distinguished from its square; Kummer equivariance and the fixed finite row give sign `+1`.
- 8392–8395, 8452–8459: unverified — the actual torsion comparison at the chosen place is an input.
- 8462–8474: unverified — the ramification and supersingular/adelic descriptions are used as cited; the geometric identification is an input.
- 8476–8479: unverified — good reduction, extension and specialization of the parametrization are geometric inputs.
- 8476, 8491–8492: OK — the function factors through the right-ideal class set and evaluating at a class is well defined.
- 8480–8487: unverified — the Hecke identity on specialized points and its identification with ideal neighbours are geometric inputs.
- 8487–8490: unverified — the affine Atkin–Lehner identity and the uniformizer identification with Frobenius are geometric inputs.
- 8491–8493: OK — applying the additive evaluation gives the three asserted eigenvalues in the residue ring, which has integral representatives.
- 8602–8621, 9373–9392: OK — the weight denominators are cleared over the integers, and relifting preserves the full retained precision.
- 9039–9042, 9067–9076: gap filled — use the existing ideal arrow count and its duality on a supplied line index; this gives App F exactly the weighted adjoint and Hecke fields it uses.
- 9278–9291: gap filled — given pointwise specialization, the same `λ_M` and additive reduction identify the residue of a lifted class value with the `StageKummer` evaluation.
- 9331–9339, 9343–9358: OK — the raw Atkin–Lehner and uniformizer signs combine with the asserted norm-character factors at precision `M`.
