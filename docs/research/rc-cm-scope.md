# CM field of definition at manuscript scope

`CMFieldOfDefinitionScoped` restricts the existing pointwise source descent to tex 2839–2844 and 2915–2916. The broad assertion implies it, and both level-one models satisfy it. **At general level this is an input, not a proved result.** No general descent, branch comparison or new print is used.

**Verification stop.** Only the scoped definition, restriction and level-one proofs, and orientation specialization compiled. Host load reached 220.01 against the 120 limit while a check was stalled on disk I/O. The five wrapper modules are preserved as an unverified [scratch patch](../../scratch/rc-cm-scope/pending-wrappers.patch). The wrappers and axiom audits still need Lean verification.

**Scope finding.** The existing Heegner anchor asks for every positive conductor prime to `N · |D_K|`. Tex 2841 requires the conductor to be prime to `2N · |D_K|`. The drafted scoped anchor versions keep the old conclusions and explicitly require `2 ∣ N`, which puts the old conductor domain in scope. The original anchor binder does not supply that parity fact. The genus and rough-companion selectors already carry the stronger local hypotheses.

## Where the CM quantifiers are instantiated

In the table, N is the newform level, c the order conductor, and d the **order discriminant**. In tex 2915 the subscript denotes the conductor. All selected forms below have leading coefficient N.

| Path to evaluation | Field, order and discriminant | Selected form and available hypotheses |
| --- | --- | --- |
| `ParamJoin.genus_values` → `PreparedParam.genusParamValues` → `preparedParamValues` → `value_of_cmFieldOfDefinition` | K = ℚ(√(h h*)), `conductorOrder K 1`, d = h h* | `StageSelector.formAtLevel`. Preparation and the partner give a negative squarefree product, by coprimality, and unit squares at every prime of 2N. The field discriminant is the product, it is 1 modulo 8, and c = 1 satisfies the conductor condition. |
| `PreparedParam.missingParamValues` and `ParamAtScale.prepared_and_missing_at_scale`, via `ModFnClassify.{prepared_values,missing_values}` and `ParamJoin.AtScale` | Same conductor-one field, order and discriminant | Same `formAtLevel`; `Setup` supplies positive level and the partner, and `preparedGlue` supplies preparation for a missing row. The setup's witness is unchanged. |
| `ParamJoin.ring_values` → `value_of_cmFieldOfDefinition` | K = ℚ(√k′), `conductorOrder K h.natAbs`, d = k′ · c² with c = `h.natAbs` | `Gz34Instance.companionForm`. The companion is negative, squarefree, 1 modulo 4, and a unit square at all primes of 2Nh. Preparation gives coprimality of c to 2N; the companion gives coprimality of c to the discriminant k′, which is 1 modulo 8. |
| `ParamJoin.gz34CompAt`, `PreparedParam.gz34CompAt_of_scaledParametrization`, and `SelectorTotal.ParamInputs.hCMField` → genus and ring values, including `genusInstance` and `oddStagedOfParamValues` | Same two rows above; the prepared and companion points have different native fields and orders | No additional CM descent application. The selected genus datum is reused in the staged row. The two identities in `PointComparisons` concern specialization, and are separate from `hCMField`. |
| `HeegnerAnchor.genuineHeegnerAnchor` → `cmPointsAtScale` → `cmPointValue` | One supplied quadratic totally complex K, `conductorOrder K c`, d = D_K · c² | `conductorForm` produces [N,B,C] and d coprime to N. Splitting at 2N is supplied; at 2 it already rules out the two exceptional fields. The old conductor premise lacks the separate condition at 2. |

The generic evaluators `value_of_cmFieldOfDefinition` and `cmPointValue` specialize the broad input once, to the supplied order and form. A proof of a restricted universal proposition cannot fill the old broad binder. The new wrappers reuse the pointwise evaluation in those proofs, including `projectiveValue_map`, and call the existing form, parametrization and stage assemblies. This is on-the-spot interface work, provenance (c).

The definition binds a fixed root β² ≡ D_K modulo 4N before the conductor, and requires B ≡ cβ modulo 2N. The primitive form with d prime to N specifies a proper ideal pair of the same order: the first lattice is spanned by A and ω, the scaled one by A/N and ω, with ω = (−B + √d)/2. `CMField2.formIdeal_scaled_eq_levelInverse_mul` gives their relation by the oriented level ideal. At a supplied point the arithmetic specialization recovers its orientation using an inverse of c modulo 4N. The scoped anchor chooses the conductor-one form first and uses its orientation at every conductor. The shared input remains pointwise: it does not give simultaneous embeddings of the ring class fields into a tower, identify a chosen class group action, or prove norm relations.

At the level of the conductor predicates, N = 1, D_K = −7 and c = 2 give d = −28 and the primitive form [1,0,7]. The field is split at 2 and 2 is coprime to 7, but 2 is not coprime to 14. This example does not assert that the actual curve has odd level. To discharge `2 ∣ N`, the actual-curve owner needs the level parity result in Lean, or the anchor owner needs an agreed change of the predicate. The mathematical route to parity is bad reduction at 2 and identification of the minimal newform level with the conductor. For the displayed model the discriminant has 2-adic valuation 8 + 6v₂(ℓ), never a multiple of 12. Thus a change of variables cannot produce unit discriminant at 2. This route is on the spot (c) and is not formalized here.

## Verified declarations and wrapper drafts

All declaration names below are under `ZInQ.Manuscript.RC.CMScope`. Value statements use the original curve, scale and analytic map `phiAn`. Only the first four rows of the table have compiled.

| Declaration | Statement and binder |
| --- | --- |
| `CMFieldOfDefinitionScoped X` | For an imaginary quadratic K split at 2N with D_K different from −4 and −3, choose a fixed orientation β as above. For each positive conductor c prime to 2N times the absolute field discriminant and each oriented primitive Heegner form [A,B,C] with negative order discriminant d prime to N, there are `ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ` and a field point x in that ring class field with `x.map ι = X.complexPoint (cmPoint A B d)`. |
| `cmFieldOfDefinitionScoped_of_broad` | `CMFieldOfDefinition X → CMFieldOfDefinitionScoped X`. |
| `cmFieldOfDefinitionScoped_modelOne`, `cmFieldOfDefinitionScoped_one` | Scoped input for `X0Model2.modelOne` and `X0Branch.model 1`, respectively. |
| `orientation_of_form` (private), `CMFieldOfDefinitionScoped.atForm` | For an eligible form at a conductor prime to 2N, the first gives the orientation root with the two congruences. The second specializes the scoped binder to the supplied form over a split nonexceptional field and with the full conductor coprimality. |
| `value_of_cmPoint` | Given the fixed rational parametrization and `x.map ι = X.complexPoint τ` for x over H, there is an elliptic point y over H with embedded value `phiAn E f Lat κ τ`. This is the pointwise part of `value_of_cmFieldOfDefinition`. |
| `coprime_level` | Local unit squares for d at every prime of 2N imply d is prime to N. |
| `preparedParamValues` | A matching rational parametrization, positive level, genus partner and scoped CM input give `PreparedParamValue` on every prepared row, as in `PreparedParam.preparedParamValues`. |
| `genus_values`, `ring_values` | The exact `ParamJoin` value slots with the new `hCM` type. The ring slot keeps the original companion form, conductor and elliptic value. |
| `prepared_values`, `missing_values` | The `ParamJoin.AtScale` slots with the scoped input. Both use the same conductor-one evaluation; missing rows keep their existing witness. |
| `ParamInputs`, `genusValues`, `ringValues`, `withParamIndices`, `genusInstance` | Scoped `ParamInputs.hCMField` feeds both value families; the index functions and instance use those families. |
| `selG_isSome_of_admissible`, `exists_selected_of_admissible`, `selectedDatum`, `pointInputs` | Total selector and data interfaces with the scoped record. The last two carry the same selection equation into the existing per-row comparison. |
| `oddStagedOfParamValues` | `Nonempty (OddStagedInstance (withParamIndices a))`, with the scoped record. |
| `discr_ne_of_split_two`, `scale_form` | Splitting at 2 excludes the two exceptional discriminants. Scaling the chosen conductor-one form at a conductor prime to N preserves primitivity and scales its middle coefficient by c and its last coefficient by c². |
| `factor_embedding`, `fieldPoint_map_map`, `anchorValue` | Factor an algebraic embedding through the fixed algebraic closure of ℚ; compose field point maps; then transport and evaluate one descended point. |
| `cmPointsAtScale`, `genuineHeegnerAnchor` | The old two anchor conclusions with `CMFieldOfDefinitionScoped (X0Branch.model N)` and explicit `2 ∣ N`. The first gives one matching map and point and value comparisons at each conductor; the second packs the original `GenuineHeegnerAnchor` predicate. |

The selector field and the anchor input are the identical proposition `CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))`. The selector derives `NeZero` from its existing curve theorem and the anchor takes it as an instance; the proofs of `NeZero` are definitionally interchangeable.

## Remaining inputs and owners

The table lists the hypotheses of the public consumer interfaces, grouping the fields of `ParamInputs`. Pointwise helpers use only the corresponding part of those hypotheses and the already specialized point equality or form. In the last column, “weaker” means a strictly smaller part of the construction than (O.7); the unrelated input propositions are not claimed to follow logically from (O.7). The full comparison at tex 9105–9115 connects a weighted theta coefficient to a Kummer value of the unaveraged genus sum at the same precision.

| Remaining input | Owner | What it controls, short of (O.7) |
| --- | --- | --- |
| `hCMField` / `hCM` at `X0Branch.model N` | Shared CM source descent, next branch comparison lane | A rational point on the source curve over one ring class field. No modular image, reductions, theta coefficients, or Kummer values enter this statement. |
| Curve/index data `ℓ`, `W₀` / `W`, `P`, `hℓ` and anchor `IsElliptic` and `NeZero`; normalized `f`, `hf` | RC integrator, actual-curve and existing print layers | Fix the modular curve and form. `P` carries existing modularity and arithmetic inputs; no staged coefficient or its comparison is assumed. |
| `Lat`, `hLat`, `hNC`, `κ`, `hκ`, `hr` (or the corresponding `CSTParam` fields) | Fixed-scale parametrization and uniformization | Match lattice and scalar, including a rational representative of the same scale. The generic prepared evaluator takes the matching rational morphism directly. None compares its point values to a theta coefficient. |
| `hpartner`, `hlevel0`, `hS`, `hprepared`, `hstarS`, `hpreparedLoc` and row premises `Prepared` / `Companion` | Genus partner, support and rough-companion lanes | Choose eligible fields and forms and certify filters and avoidance. They do not assert any relation between the two points or with the staged coefficient. |
| `N` (the `CentralNormalization` field of the record), `hN` for its `Lstar`, `hElkikMD` | RC11 normalization and Elkik–Manin–Drinfeld lane | Identify the chosen central normalization and certify one nonzero rational partner value. This is independent of the rowwise weighted theta comparison. |
| `hk0`, `hksq`, `hk4`, `hk2N`, `hkcop` | Final companion lane | Sign, squarefreeness, congruence, local square classes and avoidance for the final companion. No statement about the sum or its reduction. |
| `L` and `s`, or `s` supplied to `prepared_values` / `missing_values` | Stage Kummer and witness/detector lanes | Give stages, places, witness and finite comparison maps on which (O.7) is to be proved. The missing-value wrapper needs only the selector's prepared data. |
| `m`, level positivity `hN`, `hcop`, `H`, `w`, `hm` | Stage arithmetic and local theta geometry | Give discriminant, prime-to-level guards and orientation sign data, without a global comparison. |
| `ap`, `X`, `J`, `G` | PM adelic geometry | Supply the coarse special fibre and its identification and specialization maps. They describe where reduction takes place. |
| `comparisons`, including `embedding`, `ref`, `r` and its `hCM` and `hπ` | Point matching: orbit and PM geometry, source model and Stage Kummer | Identify individual coarse points and their specialization with the selected conjugates before summing. No equality between the final theta count and the Kummer value is posited. |
| `hSign` and `hCusp` | O.7 normalizers and PM geometry | Fixed local Atkin signs and cusp translations killed by the multiplier. Neither proves the phase and norm comparison for the sum. |
| `ha` | Theta coefficient interface and integrator | Reads the supplied integer coefficient at the given phase and precision from the theta side. It contains no Kummer value and does not assert the other side of (O.7). |
| `hL` and `hsign` | Native torsion and root-number lanes | The multiplier kills native torsion and the admissible twists have odd sign. Neither identifies the coefficient or its value. |
| Anchor `K`, `Field`, `NumberField`, `IsTotallyComplex`, `hK`, `hsplit`, `ι`, and explicit `h2N` | Anchor field and embedding data; actual-curve lane for level parity | Select the field and ambient embedding, and admit all old conductors into the scoped domain. These are arithmetic and geometric inputs before any norm or theta relation. |

The anchor quantifies over the two old Galois slots in its conclusion. It supplies no `CCLGenuine` norm-relations proof or identification of a separately chosen witness to that print with the points constructed here.

## Known issues

- The old anchor's conductor range is a Lean interface mismatch. Tex 2919 describes a condition of the cited comparison and does not remove the independent conductor condition in tex 2841. The conditional replacement preserves the existing anchor predicate.
- The prior audit of tex 1784 and 1788 records a citation mismatch for the normalized newform and the Hecke identity. The existing parametrization join is used and the Hecke identity is not used here.
- The independent field-of-definition passage in Cai–Chen–Liu `2 and the Shimura fallback are still unread, as in the broad statement. The candidate for the next run is Gross, *Heegner points on X₀(N)* (1984), `1, **UNVERIFIED**. The D_K = −7, N = 2 collision from `CMField2` lies inside the scoped domain at conductor one; the two plane coordinates alone do not specify the normalized branch.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 1785–1787, 1825–1828 | unverified | Keep the existing fixed-scale rational-map identification and its rational-scale input. The citation mismatch is recorded above. |
| 2404–2410 | OK | Preparation and partner unit classes give the split genus field; the companion's avoidance supplies the additional conductor coprimality. |
| 2411–2416 | OK | Distinct native fields and conductors, with the genus form at conductor one and the companion at the absolute prepared parameter. |
| 2839–2844 | OK | Split at every prime of 2N, exclude the extra-unit fields, and use the order with conductor prime to 2N times the field discriminant. |
| 2915–2916 | gap filled | The input explicitly fixes the orientation modulo 2N and uses the corresponding proper lattice pair. Existing form arithmetic and the new specialization establish the caller-side congruences. |
| 2915–2916 | unverified | General-level descent on the normalized model and coherence with the chosen class field tower are not proved here. |
| 2917 | OK | Applying the rational morphism commutes with the complex embeddings by base change. |
| 2918–2919 | unverified | The CCL identification and reduction of its condition are not needed for the pointwise evaluation and have not been checked against the source. |
| 8209–8217 | OK | The selected conductor-one point for each prepared row is the one at the existing Heegner root. The wrapper supplies its algebraic value before summation. |
| 8219–8220 | OK | The conductor-one point and the rough ring-class point use separate selectors. |
| 9105–9115, 9439–9443 | OK | The odd-staged wrapper uses selection on the full filter. It takes the same inputs for the existing comparison and does not use analytic rank as a gate for choosing the point. |

## Verification status

- `Field.lean` and `Orientation.lean` passed serial `lake env lean -j1` under `MemoryMax=60G`. No axiom or sorry was added. The script checked load and available memory before each Lean invocation.
- `Evaluation.lean`: the first check found a missing classical instance. The corrected retry was started while resource gates passed, then stopped after stalling on disk I/O while load was above the limit. No claim is made about that retry's result. `Prepared.lean`, `Values.lean`, `Anchor.lean`, and `Selector.lean` were not checked.
- The requested `#print axioms` commands are in [ScopeCheck.lean](../../scratch/rc-cm-scope/ScopeCheck.lean), [CoreCheck.lean](../../scratch/rc-cm-scope/CoreCheck.lean), and [ConsumersCheck.lean](../../scratch/rc-cm-scope/ConsumersCheck.lean). None of those three audit files ran; no axiom list was verified in this run.
- Resume by checking the resources, then running the scope audit and applying the scratch patch. Build existing imports serially, and check the drafted files in the order Evaluation, Prepared, Values, Anchor, Selector, then run the core and consumer audits. `git apply --check` passed for the patch.
