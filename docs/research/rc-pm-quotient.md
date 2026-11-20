# The special-fibre quotient in (O.7)

The two inherited citation errors are recorded in
[the verdict](../../.fleet/rc-pm-quotient2-verdict.md): Milne's stated
locators do not supply the normalized-newform and good-Hecke claims
(tex 1784–1788), and the cited Jetchev–Kane comparison does not cover
level one (tex 8468–8474).

The quotient is defined by residue evaluation of the Néron extension of
the fixed rational parametrization. One diagram per detector stage supplies
the special-fibre operator equations, the pointwise specialization `hπ`
of each selected datum, and the cusp annihilation in the odd staged
constructor. No existence theorem for the integral modular model is asserted.

The target of the existing interface is the quadratic fixed subgroup
inside the geometric points of the reduced Weierstrass curve. First
read geometric sections in the full point group, then use arithmetic
Frobenius twice to see that the point lies in the subgroup. Extend the
reading additively on the free abelian group and restrict to degree zero.
Use this degree-zero group itself in the old `J` slot and the identity
for `divisorClass`. The old consumer only uses their composite; there
is no claim that this group is the Jacobian or that a Jacobian
factorization has been formalized.

## Statements

These declarations are in `ZInQ.Manuscript.RC.PMQuotient` (model and
operator methods in its `GoodRow` namespace).

| Declarations | Statement and use |
| --- | --- |
| `residueSource`, `residueFrob`, `residueUnit` | The geometric residue spectrum over the prime field, its arithmetic Frobenius over the prime field, and its unique point on the base changed unit object. |
| `GoodRow`, `special`, `πInt`, `hInt` | Data for the two models, Néron mapping property and isomorphisms with the fixed generic source and target; integral cusp and level operators; actual coarse points and the coordinate reading of the reduced elliptic group. `special` is base change to the prime residue field. `πInt` is chosen from the Néron bijection and `hInt` proves its generic square. |
| `evaluate`, `evaluate_frob`, `value` | Read a geometric section after the extension; precomposition by arithmetic Frobenius is compatible with elliptic Frobenius. `value` is that reading in the quadratic group, by the coarse Frobenius involution. |
| `quotient`, `quotient_center`, `frobenius_quotient` | Add the readings on degree-zero divisors. The centered class of a point reads as the difference from infinity. Applying Frobenius before reading gives Frobenius of that difference. |
| `readAt`, `Based`, `value_infinity` | Base change followed by section evaluation is a group homomorphism. `Based` says the generic image of the integral infinity section is the group identity; uniqueness of extension gives zero at its reduction. |
| `movedCusp`, `AtkinIdentity`, `atkin_quotient` | The integral section obtained by applying the integral level operator to infinity and then the extension. `AtkinIdentity` is the generic morphism equation with this translation and the prescribed sign. `atkin_quotient` specializes it through `GoodReduction.atkinQuotient_of_integralRelation`, subtracting the values at the two moved points. |
| `HeckePacket`, `HeckeIdentity`, `hecke_quotient` | At one coarse supersingular point, a smooth integral chart of the correspondence with a section and all \(q+1\) branches. The generic identity is the equality of the sum of the branch values with \([a_q]\pi\) evaluated on the source (written as an ordered product in the group of maps). Néron uniqueness identifies the maps integrally; section evaluation reads precisely the corresponding sum with multiplicities. |
| `toAdd_ofFn_prod` (private) | Converts the ordered product of a finite list in a multiplicatively written additive group to the indexed sum of its values. |
| `Relations`, `specialFibre`, `specialize_eq_value` | Package generic normalization and signed and Hecke relations, and the integral good-Hecke chart. The resulting `SpecialFibreAtSigns` has a fixed divisor group, divisor map and quotient. Its PM point evaluation is the original residue value by `quotient_center` and normalization. |
| `genericInclusion`, `genericInclusion_comp` | Forget the generic identifications to maps of total spaces; their commuting square is the one used by the previous integral-diagram lemma. |
| `geometricResidue`, `rawSection`, `rawSection_over`, `rawSection_map`, `sectionOf`, `sectionOf_rawSection` | Convert residue sections over the prime field to geometric maps into the integral models, and recover the section by pullback. These operations are natural in a map of integral models. |
| `readRaw`, `readRaw_eq`, `readRaw_value` | Adapt the section reading to the old diagram lemma's untyped maps into the total space. The comparisons only use maps over the selected residue point whose values are in the quadratic group. The residue reading at a coarse source section is literally `value`. |
| `cmRing`, `cmGeneric`, `cmGeneric_dominant`, `cmResidue`, `fixedMap` | Contract the detector's place along the selected datum embedding, take the generic point of that valuation ring and the given geometric residue embedding, and view the fixed rational parametrization as a map over \(\mathbb Q\). |
| `CMDiagram`, `hpi_of_cmDiagram` | The selected generic CM point and its complex-chart comparison, source and target lifts at the contracted place, identification of the coarse reduction before applying the map, and target coordinate reduction. `hpi_of_cmDiagram` applies `GoodReduction.hpi_of_integralDiagram`; its `hPM` follows from `specialize_eq_value` and `readRaw_value`. |
| `RationalPoints`, `rationalCusp`, `CuspInput`, `hCusp` | The generic group of sections at \(\operatorname{Spec}\mathbb Q\), including the image of the moved rational cusp. Assume the actual rational Jacobian class, its torsion, its image under the fixed elliptic quotient, and that \(L\) kills that torsion image. Extend annihilation integrally by uniqueness and evaluate additively on the residue fibre. |
| `signedFamily`, `fibreFamily`, `hCuspAt` | Supply the exact family of signed/unsigned special fibres and the cusp condition for each level-prime index. |
| `Reference`, `hpiAt`, `referenceComparisons` | The selected row keeps the reference embedding, orientation and geometric CM identification, and now takes `CMDiagram` instead of a PM equality. `hpiAt` has the `O7Residual.At` conclusion with the actual Artin label and `StageKummer.reduceDatum`. |
| `oddStagedOfGoodRows` | Compose with `AtkinPin.oddStagedOfPinnedParamValues` at `F.signs = wNew F.form F.trivial` to fill the `OddStagedInstance` slot. The other theta and arithmetic hypotheses are inherited. |

The constructions of the section and divisor readouts, their
naturality, all three passages from geometry to the operator proofs,
and joining the row interfaces are ON THE SPOT (c). For the Hecke
packet, start with a smooth scheme chart of the modular stack at a
representative of the enhanced curve, and adjoin an ordering of the
cyclic subgroups of order \(q\) by a finite étale cover. The geometric
lift chooses such an ordering. The quotient morphisms with their
induced level structure define the branches; coincident coarse
points still have their separate indices. At infinity the separate
known divisor formula suffices, so the packet need not split there.
No finite étaleness of the correspondence on coarse schemes is used.

For the signed identity, the Néron mapping property and base change
carry the given rational equation to the geometric sections. The
constant cancels on the difference of the two moved points. For good
Hecke, uniqueness carries the generic sum of branch maps to the
smooth chart, and evaluation there preserves the sum. For Frobenius,
precomposition on the geometric residue spectrum commutes with the
base changed map, and the coordinate reading identifies that action
with arithmetic Frobenius. Its square fixes the coarse labels, so the
readings land in the detector's quadratic subgroup.

For the CM square, both lifts are taken over the valuation ring
contracted from the detector's place. The square compares the residue
reading with the separately specified Weierstrass coordinate
reduction. The old `hPM` premise is supplied by
`specialize_eq_value` and `readRaw_value`; the coincident readings
are of the same morphism because the generic square commutes and the
target is separated. For the cusp, a homomorphism carries torsion in
the rational Jacobian to torsion in the rational elliptic group. The
stipulated rational annihilation holds integrally by uniqueness and
on the residue fibre by the group law. These are ON THE SPOT (c).

## Remaining (O.7) inputs

| Input | Refereed source or reason it remains |
| --- | --- |
| `ℓ,W₀,a`: fixed curve and stage data, form, rational scale, lattice, normalized partner value, genus and ring class selector values, admissible indices and local support | Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises* (2001), Theorem A; Shimura, *On the factors of the jacobian variety of a modular function field* (1973), Theorem 1 **UNVERIFIED**. The fixed scale and selector joins are in the tree; they still need the chosen rational scale, CM field of definition and the specified companion arithmetic. The normalization of an independently supplied scale or index is a model comparison. |
| `π,hQ,han`, `F`, and the level and ellipticity instances | The fixed parametrization on the normalized rational chart, with the exact analytic identity on interior points, and the same normalized newform from modularity. The generic-map input is shared by every stage. An independently chosen algebraization of the wrong scalar would not suffice. Stage level transport is `AtkinPin.stageLevel_eq`; the rational equation is transported by `EcurveZ_baseChange`. |
| `s,L,m,hN,hcop,H,hm` | Actual witness and stage sequence, determinant and coprimality conditions, partner discriminant, precision and fixed multiplier. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques* (1972), open image theorem, number **UNVERIFIED**, and Chebotarev for the stage sequence; the existing detector and stage proofs are used. These hypotheses include choices of data, for which no theorem identifies an arbitrary family with the prescribed one. |
| `R,G`: one good model diagram per detector prime, on the local base with fraction field ℚ and its map to the prime residue field | Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*, LNM 349 (1973), VI.6 **UNVERIFIED**; Igusa, *Kroneckerian model of fields of elliptic modular functions* (1959), title and locator **UNVERIFIED**. For the good elliptic model: the good Weierstrass equation and Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §1.2 **UNVERIFIED** (mapping property for a good group model proved in tree). The remaining work is substantial: construct the compactified integral coarse modular curve over ℤ localized at the detector prime, identify its generic chart and the integral elliptic group model with the fixed source and target, and compare its reduced coordinates and operators. `GoodRow` names the exact interface needed; its existence is not a new printed leaf. |
| `ap,X,J`: good eigenvalues, coarse fibre, class-set/operator dictionary | Ribet, *On modular representations of Gal(ℚ̄/ℚ) arising from modular forms*, Invent. Math. 100 (1990), Prop. 3.3, Prop. 3.6 and Rem. 3.5(a)(b), **UNVERIFIED**, via the reviewer's Version 21 route, including level one. Voight, *Quaternion Algebras* (2021), Main Thm. 14.6.1 (manuscript locator, **UNVERIFIED**), for the ramified quaternion algebra. The name `PMAdelic.JetchevKane` denotes the existing signature, not a new application of its old citation at level one. Compatibility at the actual residue field and uniformizer is separate model glue. |
| `relations.based`, `relations.atkin` | Tex 1785–1787, 2943–2946. Atkin–Lehner, *Hecke operators on Γ₀(m)* (1970), eigenrelation locator **UNVERIFIED**. The existing chart identity is known; identify the integral involution on the generic fibre with the rational one and carry `BasedAtkinOnPoints` / `translatedAtkinAtInfinity` to equality of morphisms using faithful evaluation on the generic point (or density and separatedness). This remaining comparison must also identify the integral and normalized rational infinity. The hypothesis is the generic equation on the fixed map, before any reduction. |
| `relations.hecke`, `relations.eigen` | Deligne–Rapoport VI.6 **UNVERIFIED** and finite étaleness of prime-to-residue-characteristic torsion give the integral cyclic subgroups; the chart and multiplicity identification is (c). Shimura (1973), paper above, Thm. 1 **UNVERIFIED**, is the intended classical Hecke quotient route in place of the insufficient Milne locators. After the fixed Jacobian map is identified, apply its generic Hecke identity to the based class and use the generic cusp formula. |
| `cusps`: genuine cuspidal class, image, torsion, annihilation | Elkik, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), Théorème, p. 59 (reviewed locator). The actual \(J_0(N)\) class and its image are the cusp identification work; the exact-divisor rational involution carries rational infinity to a rational cusp. The `kills` field is only annihilation of that rational torsion image; manuscript \(B_{\rm cusp}\mid L\) supplies it (tex 8282–8297). No new printed leaf. |
| `refs.embedding/ref/r/hCM` | The reference orientation, class-group and torus comparison and the actual conductor-one CM reduction. Version 21's direct reduction via Ribet replaces the preprint citation for `hCM` on the reviewer's route. Identifying the chosen reference orientation and Artin label at the actual place is model glue; no proof of this input is made here. |
| `refs.diagram`: the selected CM point and local source/target comparisons | Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Ch. 6 **UNVERIFIED**, for field of definition; the valuative criterion for properness gives both lifts. The smallest remaining special-fibre comparisons are that the geometric source section is the residue of that conjugate and that the target reading of the independent Weierstrass lift agrees with the detector's coordinate reduction. The same valuation ring and residue embedding are taken from the selected datum. Neither comparison asserts a value of the composite PM map. |
| `ha`: the phase and precision reading of the fixed integer \(a_\theta\) on the constructed row | There is no theorem reading an independently indexed integer. The needed equality modulo the retained precision is the theta coefficient identification, using the actual Schwartz data, coefficient ring and phase of this row. The (O.7) point/weighted comparison does not need to be assumed again. |
| `hL`, `hsign` | The separate native torsion bound, not the rational cusp bound: Silverman, *The Arithmetic of Elliptic Curves*, second ed. (2009), VII.3.1 **UNVERIFIED**, via prime-to-residue-characteristic torsion at two good primes. The odd root-number condition is the manuscript's local filter (tex 1994–2001; Desjardins, *Root number of twists of an elliptic curve*, 2020, Prop. 3.3, bibliographic details **UNVERIFIED**), together with the initial odd sign from Dokchitser–Dokchitser, *Root numbers and parity of ranks of elliptic curves* (2011), Thm. 1.8 **UNVERIFIED**. |

## Known issues

- Tex 1784–1788 and 8468–8474: the inherited citation issues in the
  verdict above. The exact locators for the proposed refereed
  replacements were not checked.
- The older tex 9265–9279 Cornut–Jetchev source is an unrefereed
  preprint and is not a new leaf here. The direct conductor-one
  reduction remains separate work.
- The requested `ElkikPrint/Prints.lean` path and
  `ManinDrinfeldTorsion` identifier are absent at these pins. The source
  transcript is in `RC/PrintsArith/Heegner.lean`; the older
  `RC/ElkikMD/Prints.lean` uses an abstract finite cuspidal subgroup.
  `CuspInput.torsion` takes precisely the reviewed torsion assertion
  on the actual degree-zero classes as a premise; it declares no print.
- Arithmetic Frobenius over the prime field is the action on the
  coarse points in this interface; its square fixes the points used
  in the detector. Matching the adelic uniformizer with this action
  is a separate geometric comparison.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1779–1783: modularity and a fixed normalized form | OK |
| 1784–1788: cited Milne statements for the newform and equivariance | error |
| 1785–1787: use the based modular parametrization | unverified |
| 2933–2936: good Hecke action and base cusp divisor | unverified |
| 2937–2942: Manin–Drinfeld and a fixed cuspidal multiplier | OK |
| 2943–2946: signed generic translation with the moved cusp | unverified |
| 8282–8297: include the rational cusp annihilator in the multiplier | OK |
| 8462–8467: ramified quaternion algebra and Eichler level | OK |
| 8468–8474: cited supersingular description includes every level | error |
| 8476–8479: specialize the fixed map over the local base | gap filled — the extension and its evaluation are defined given the good models |
| 8480–8487: specialize the generic Hecke relation on the good correspondence | gap filled — conditional on the integral chart and generic equation |
| 8487–8489: specialize the signed relation and kill the residue translation | gap filled — conditional on the generic identity and cusp inputs |
| 8489–8492: Frobenius action on the same specialization | gap filled — conditional on the operator and coordinate dictionary |
| 8505–8507: keep the same newform sign in the theta construction | OK |
| 9101–9113: unaveraged weighted coefficient of the actual row | unverified — the specialization input is filled; the fixed coefficient and other arithmetic inputs remain |
| 9265–9279: use the actual reduced reference CM orbit at the chosen place | unverified |
| 9283–9291: reduce the selected conjugates under the fixed map, then add | gap filled — conditional on the CM diagrams, with the existing additive comparison |
| 9330–9341: apply the same signed translation in the orientation change | gap filled — the sign and cusp equations now refer to the same specialized map |
| 9343–9358: the uniformizer comparison and arithmetic Frobenius | unverified — the Frobenius equation for the parametrization is proved, but the uniformizer identification is separate |
| 9372–9398: retain the precision and read the fixed stage coefficient | unverified |

## Verification

`Model`, `Operators`, `Cusps`, `CM` and `Assembly` passed individual
`lake build` checks with source-matched prerequisites and a serial
compiler in a 60 GB user scope. The 25 axiom prints cover all 21 new
theorems and four definitions used in the construction. They list only
`propext`, `Classical.choice` and `Quot.sound`.

The focused [discharge audit](../../scratch/rc-pm-quotient/Discharges.lean)
passed against the actual `Wiring.PreLeaves.odd_staged` projection at
`SelectorTotal.withParamIndices a`. It prints all 30 binders with their
types; there is no independent special fibre, quotient, `hπ`, or
`hCusp` binder. It checks this field of the restricted converse, not
`hRC` as a whole. The [results log](../../scratch/rc-pm-quotient/log.md)
records the build outcomes and the complete binder list.
