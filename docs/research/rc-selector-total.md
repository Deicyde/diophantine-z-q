# Total genus selection for the odd staged leaf

`SelectorTotal.oddStagedOfParamValues` supplies the type of `PreLeaves.odd_staged`,
`Nonempty (OddStagedInstance W)`, for the data `W := withParamIndices a`. The
new genus instance is built from the raw fixed-scale parametrization values.
It has a selected conductor-one datum on every admissible row, including
torsion rows. The per-row selection equation `ht` and the two
index equations `hjg` and `hjr` are discharged. All other hypotheses of the
actual comparison are retained. No new prints are introduced, and neither
the comparison wiring nor the height argument for (3.4) is edited.

## Statements and consumers

Names below are in `ZInQ.Manuscript.RC.SelectorTotal`. Write `E := Ecurve ℓ`,
`n_E := newformLevel E`, `W := withParamIndices a`, and `I := genusInstance a`.

| Declaration | Statement and hypothesis supplied |
| --- | --- |
| `withParamIndices a` | `W : WData ℓ`, with `jgen := jgenOf E a.f a.Lat a.κ W₀.hstar (selectGenus … (genusValues a))`, `jrc := jrcOf E a.f a.Lat a.κ (selectRing … (ringValues a))`, and every other projection of `W₀` unchanged. This makes `hjg` and `hjr` reflexive. |
| `genusInstance a` | `GenusOddInstance W`. Applies `instanceOfParamValues` with `halgG` from `ParamJoin.genus_values`, `halgR` from `ParamJoin.ring_values`, and `hjg` and `hjr` by `rfl`. |
| `selG_isSome_of_admissible a hglue` | `∀ i D, W.admissible i D → (I.selG D).isSome`, for `hglue : PreparedGlue W`. Uses `hglue`, `I.hprep` and `selectGenus_isSome`. Supplies the coverage needed for `ht` without using `I.hselG`. |
| `exists_selected_of_admissible a hglue` | `∀ i D, W.admissible i D → ∃ t, I.selG D = some t`. Supplies the selection equation for the actual point interface. |
| `selectedDatum a s i D hD` | `{t : HeegnerDatum E a.f a.Lat a.κ ((D.toNat : ℤ) * W₀.hstar) 1 W₀.hstar // I.selG (D.toNat : ℤ) = some t}`. `Setup.hstages.withStages_eq` discharges the bridge via `preparedGlue_of_withStages`; positivity identifies the integer index with its natural reading. |
| `pointInputs a s hN hcop H w hm J G comparisons i D hD` | `O7Residual.PointInputs s i hN (hcop i) (H i) w hm (J i) (G i) (admissibleNatAt … i D hD)`. Copies the reference data and two given pointwise comparisons at `selectedDatum …`; `ht` comes from the subtype property. |
| `oddStagedOfParamValues` | `Nonempty (OddStagedInstance W)` from the inputs below. Instantiates `oddStagedActual` with the constructed point family. This is the original leaf type. |

`genusValues` and `ringValues` are abbreviations for the two existing raw
parametrization results. `ParamInputs W₀` groups their inputs and the
remaining genus assembly inputs; `PointComparisons` groups the existing
point data and pointwise identities at the selected datum.

Of the hypotheses to `instanceOfParamValues`, only `hjg` and `hjr` mention
the rewritten index fields. In particular, `SupportSpec` depends on `S`
and `PreparedSpec` on `S` and `prepared`; the other support, local square,
partner, central normalization and final companion hypotheses read fields
left unchanged. The two algebraic value families depend on `hstar` but
neither index. The same stage and admissibility projections are kept.

There are consumers outside the literal domain of prepared simple zeros
and companions. `Visibility/Inputs.lean` and `Visibility/Models.lean` state
the `jgen` reading on **all** admissible rows. In the proof of visibility the
numerical bound uses it on the rank-one branch, while the torsion branch
uses the point without a rank-one index. `FinalFamilyAt` uses `jgen` for
nonzero addresses with preparation and rank one; the calibration target
and its `CalibrationModel` use `jrc` at every address meeting the two
rank tests, including the zero address if those tests hold. In particular,
`FinalFamilyAt` itself does not impose preparation at zero. The total
functions are the existing Lean conventions from `jgenOf` and `jrcOf`
(including zero on missing entries and the existing `index.toNat`
reading on present entries). This change does not claim any rank-one
index interpretation on torsion rows or preserve arbitrary old index values
of `W₀`. Any existing hypotheses about those old indices must be supplied
for `W`. The stage setup and point comparisons here use the same new
selector, including its witness datum.

## Remaining hypotheses

The list is the set of main-theorem binders and the fields of its two
input records. The proof inputs are strictly narrower **in scope** than
(O.7), the congruence between the weighted theta coefficient and the
detector on the reduced multiplied CM sum (tex 9110–9114). This is not a
claim that (O.7) implies the underlying construction data, or that the
inputs are logically independent.

| Input | Owner | Scope relative to (O.7) |
| --- | --- | --- |
| `ℓ, W₀`; `a.hℓ : 0 < ℓ` | RC0 integrator / actual-curve lane | Curve parameter, base interface and positivity; these fix the domain. No comparison is specified. |
| `a.P : Prints` | Existing shared GLUE prints | Existing published-form interfaces; the assembly uses the modularity field to obtain a positive newform level. None provides this theta congruence. |
| `a.f, a.hf` | Actual-curve lane / BCDT | Weight-two form at the curve's least level and agreement of its positive Fourier coefficients with the curve L-series. These are coefficients of the modular form, not the stage theta coefficient. |
| `a.Lat, a.hLat, a.hNC, a.κ, a.hκ` | Uniformization and parametrization lanes | Lattice with the curve invariants, its non-CM property, and the nonzero scale with the Eichler period inclusion. These fix which analytic map is used. |
| `a.hr : ∃ c : ℚ, (c : ℂ) = a.κ` | Parametrization lane | Rationality of one fixed scalar. Tex 1785–1787 selects the based map via the rational isogeny; 1825–1828 retains its period normalization. |
| `a.hCMField : CMFieldOfDefinition (X0Branch.model n_E)` | Heegner anchor residual | One shared proof of ring class descent on the source modular curve. It contains neither the elliptic image nor specialization, detector or weighted sums. The positive-level instance is from `curve_form`; `NeZero n_E` is proof irrelevant, so the Heegner anchor may pass the same proof. |
| `a.N, a.hN`; `a.hElkikMD` | RC11; Elkik–Manin–Drinfeld lane | Central normalization and equality to `W₀.Lstar`, and `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar E a.Lat W₀.hstar`. These concern central values and periods, with no stage coefficient. |
| `a.hpartner, a.hlevel0, a.hS, a.hprepared, a.hstarS, a.hpreparedLoc` | RC13, actual-curve and stage support lanes | Partner properties, support of the primes of `2 * n_E`, support and preparation specifications, membership of the partner's prime factors, and prepared local squares. These determine eligible fields and forms. |
| `a.hk0, a.hksq, a.hk4, a.hk2N, a.hkcop` | Final companion lane | Final `kfin` is negative, squarefree, 1 mod 4, a local unit square at the primes of `2 * n_E`, and coprime to the partner. These belong to the genus record's companion interface. |
| `L, s : StageKummer.Setup I L` | RC23 / Appendix F Stage Kummer | Fixes the multiplier, selected witness (including its existing witness pin), division tower, detector, chosen places, sequence and precision. It does not require any theta comparison. |
| `m, hN, hcop, H, w, hm` | ThetaClose / stage arithmetic | Positive stage level, level coprime to each stage prime, discriminant data `H i`, fixed sign function `w`, and `(m : ℤ) = -W.hstar`. These fix weights and the detecting primes, without taking a weighted point sum. |
| `ap, X, J, G` | PM adelic geometry | Data for the eigenvalues and coarse fibres, Jetchev–Kane ideal-class identification and geometric special fibres. These are the local maps and sets used to compare individual points. |
| `comparisons.embedding, comparisons.ref, comparisons.r` (per row) | O7Orbits / PM adelic geometry | A rational quaternion embedding of the selected field, reference orientation and coarse points labelled by the class group. These are choices, with no comparison of sums. |
| `comparisons.hCM` (per row) | X0 model / Cornut–Jetchev | Identifies each coarse point with the corresponding ideal-class point at the reference orientation. No parametrized value or coefficient occurs. |
| `comparisons.hπ` (per row) | X0 model / Stage Kummer | Identifies each coarse specialization with reduction of the actual Artin conjugate under the parametrization. No detector or summation is required. |
| `hSign, hCusp` | O.7 normalizers / PM adelic geometry | For every stage and level prime, the fixed sign agrees with the Atkin sign and `L` annihilates the cusp translation. Both are local identities before a coefficient is formed. |
| `ha` | Theta coefficient interface / integrator | For every admissible row `2^(W.Mθ i) ∣ row.weights.phase row.reference * W.aθ i D - thetaCoeff … (m * D)`, in the fixed coefficient ring. This reads the integer representative on the theta side; there is no CM sum or detector value in the congruence. |
| `hL, hsign` | RC23 / root-number lane | `MultiplierKillsNativeTorsion E a.f a.Lat a.κ W.hstar L` and `AdmissibleOddSign W.toRCData`. Annihilation and sign are separate arithmetic facts, with no theta coefficient. |

## Known issues

- Inherited citation scope: the Jetchev–Kane passage used at tex 8468–8474
  omits level one according to the O.7 source audit. The PM adelic input is
  retained. The Milne references at tex 1784 do not by themselves give the
  normalized newform or the Hecke identity of tex 1788, as recorded in
  `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean`. Neither issue
  is needed for the selector proof; primary source locators are
  **UNVERIFIED** in this run.
- Matching the selected datum with the reference CM origin and the
  Artin-labelled conjugates at the detector's place still requires
  `hCM` and `hπ`; orientation alone does not fix the origin.
- The primary source locator for the field of definition is **UNVERIFIED**.
  Tex 2915–2917 uses it; the separate trace theorem cited immediately
  afterward is not used to prove it here.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1779–1784: modularity and the normalized newform of the actual curve. | OK — existing curve and coefficient inputs are used. |
| 1784, 1788: Milne citation scope. | error — inherited citation issue described above. |
| 1785–1787, 1825–1828: fix the based map and reuse its period convention. | OK — keep the supplied scale and require its rational representative explicitly. |
| 2404–2410, 8209–8212: prepared and admissible filters, and the genus partner. | gap filled — use the stage record's prepared projection and convert it through `I.hprep` (c). |
| 2411–2416, 8219–8220: conductor one and conductor `abs h` are different selections. | OK — two selectors define the corresponding index functions by reflexivity (c). |
| 2839–2844, 2915–2917: the point on the modular curve is defined over the appropriate ring class field and is sent through the fixed map. | unverified — CM field descent on the model is a shared input; the existing parametrization join evaluates the map given that input. |
| 8209–8217: construct the conductor-one point on the whole filter before restricting rank. | gap filled — prove selection on all admissible rows from the prepared option selector (c). |
| 8225–8244, 8298–8306: keep the witness and the fixed multiplier. | OK — the setup uses the instance's selector, and the multiplier remains an input. |
| 8468–8474: geometric and adelic descriptions. | error — inherited level-one citation scope issue described above. |
| 8476–8479, 9265–9286: geometric reduction and specialization at the chosen place. | unverified — pointwise identities are retained. |
| 9105–9114: the coefficient comparison uses the actual selected CM point at each stage. | gap filled — feed the natural row's selector equation to the existing actual comparison (c). |
| 9329–9362: other orientations use the fixed Atkin signs and killed cusp translations. | unverified — the corresponding input proofs are retained. |
| 9372–9398: same precision and unit phase for the fixed coefficient. | unverified — the integer representative reading remains `ha`. |
| 9417–9423, 9439–9443: the multiplier also kills torsion on the nonsimple-zero branch. | OK — the selector covers these rows; no rank-one index is asserted there. |

## Verification

`SelectorTotal/Assembly.lean` compiled with serial `lake env lean -j1
-DautoImplicit=false`. The imported ParamJoin modules missing from the local
cache were compiled serially first. The build and audit ran under
`MemoryMax=60G`, with the load and available memory checked before each Lean
invocation. The local import closure excludes `ZInQKernel.OneProof.Main`.

The separate [axiom check](../../scratch/rc-selector-total/Axioms.lean) also
compiled. Each of `selG_isSome_of_admissible`, `exists_selected_of_admissible`,
and `oddStagedOfParamValues` reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. The same three axioms were reported for the constructors and
abbreviations audited there: `ParamInputs`, `genusValues`, `ringValues`,
`withParamIndices`, `genusInstance`, `selectedDatum`, `PointComparisons`, and
`pointInputs`.
