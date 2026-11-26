# rc-hcm-v21g review (branch tip 2630f292)

Three review lenses (separable scope, vacuity and Lean, report accounting). An adversarial verifier checked each finding above nit level. No Lean was run for the review. Line numbers refer to the tip above.

**Verdict: one error, in the accounting of what part (2) rests on. Not fold-ready until a fixup.** Soundness is fine: every candidate is a hypothesis, none is false or stronger than the full print, and nothing is vacuous.

## Error: VoightThm4232Etale reaches arbitrary curves, so injectivity carries hidden GLUE
Two lenses found this independently, and both verifications hold.
- VoightCandidates.lean:90-98 quantifies over all supersingular E, E′ (:93). Nothing assumes an étale isogeny E₀ → E.
- Its own docstring (:87-89) says the clause "reaches an arbitrary E only through an étale isogeny E₀ → E, which is SeparableIsogenyExists (GLUE), never this candidate". The statement contradicts that.
- nonempty_enhancedIso_of_translate (LevelDeuringInjective.lean:212-215) applies hEt directly to arbitrary X.curve and Y.curve. levelDeuringClass_injective (:276) has no SeparableIsogenyExists binder.
- The brief required the bijection clause to reach an arbitrary E "only through an étale isogeny E₀ → E: take that from the separate Prop SeparableIsogenyExists, never from the candidate". In separable scope the clause holds only modulo four inputs, and the brief required the audit to record all four:
  - SeparableIsogenyExists (GLUE);
  - Prop. 42.2.16 (GLUE, Nehrkorn);
  - Exercise 16.11 (not built);
  - the Silverman III.4.11 reading of Lemma 42.2.7.
- Restricting the morphisms to étale ones does nothing: any lift of a bijective module map is an isomorphism, so it is étale anyway. Scope depends on how the objects are reached, and that is left unrestricted.
- The report books the opposite:
  - :9 says the only GLUE of part (2) is used by no theorem;
  - :159 says hEt reaches the curves "through placements, not through SeparableIsogenyExists";
  - :161 says 42.2.16, 16.11 and 42.2.7 are "not used".
- Fix (a), required: add premises to VoightThm4232Etale that E and E′ are each reached from E₀ by an étale isogeny. Add hSep : SeparableIsogenyExists to nonempty_enhancedIso_of_translate and levelDeuringClass_injective, and book injectivity as resting on SeparableIsogenyExists (GLUE). List all four inputs in the hEt row and in the candidate docstring, and drop the "GLUE unused" sentences.
- Correction (2026-11-26): the first version of this review proposed proving SeparableIsogenyExists from the invertibility clause (two maps whose composite is an integer prime to q, then finiteEtale_mul_of_ne_zero and finiteEtale_of_etale_composites). That does not work. Invertibility of Hom(E, E₀) holds for every supersingular E, whether it is reached from E₀ by a separable isogeny or only by an inseparable one, so it cannot produce a separable isogeny. A replacement route is being evaluated: derive the reach from printed statements, not from Voight p. 786.

## Warns
1. **VoightCor4237** (VoightCandidates.lean:140-148) restricts the ideal (integral at :145, an integer prime to q at :146), and its one use at LevelOrderLemma.lean:311-324 satisfies that. But E is arbitrary (:143-144).
   - The print gets End(E) from Lemma 42.2.9 on φ_I : E₀ → E_I, so applying it to the given E needs E ≅ E_I. That is the same reach.
   - The ring statement also rests on the Silverman III.4.11 reading of 42.2.7, through 42.2.9.
   - Fix it the same way as the error: add a reach premise or record the reach. Add the III.4.11 caveat to the docstring and to audit row :158, and correct row :161 ("42.2.7 enters through 42.2.9").
2. **Interaction with wip/rc-goodrow-wire.** The branches are textually disjoint. Merged together on main 162d4636 (checks27), the merge is clean but the build fails with 9 errors, all in GoodRowWire/Assembly.lean. They are compile errors; nothing is silent.
   - Reference now takes J O G (PMWire/Assembly.lean:204).
   - actualRows, actualRowFamily, pointInputs and actualFamily need `(fun i => adaptOperators (O i))`.
   - hCuspAt and oddStagedOfGoodRows need `(O := O)`.
   - The positional ha would otherwise land in the O slot.
   - The wire must add an O family binder after J and thread it through.
   - The degenerate-witness argument survives with O.frobenius (Comparison.lean:103-104), but that pin now rests on the ELLIOT O, not on the GLUE J.
   - Agreed order: the wiring lands first; this branch's fixup then threads O.
3. **The audit table has no file:line in any row**, which the brief's step 14 requires. Binder lines: LevelDeuringMap.lean:211-215/:235, LevelDeuringOrder.lean:69-74/:109-112, LevelDeuringInjective.lean:133-138/:276, LevelOrderLemma.lean:421-426/:324, EnhancedObjects.lean:148.
4. **The manuscript-check row for tex 9136-9142 overclaims.** Tex 9136-9148 classifies local orientations (2^(ω(N)+1) of them), while the Lean proves local principality of the Hom level ideal. Change it to "unverified (orientation classification not in this run); only the cyclic-chain form at 9140-9142 is used".

## Verified clean
- **PkgI3.AbVar** has no data fields (Objects.lean:162-170).
  - dim is the Krull dimension, Hom is the IsMonHom scheme maps, and Pt is the K-points.
  - So IsSupersingular is geometric and junk objects cannot satisfy it.
  - No candidate is false or trivially true, and there is no free-quotient trap.
- **HomPlacement** fixes no embedding or basis. It is equivalent to invertibility, since B is a division algebra and M⊗ℚ ≅ B.
  - Placement independence and isomorphism invariance are proved.
  - The reference and order lemmas are about the explicit map, which levelEndEquivRight_apply pins.
- **Injectivity** is the real statement on Quotient enhancedSetoid (isomorphisms carrying C onto C′).
- **Part (1) preserves content:** it only inserts O and renames J.* to O.*. JetchevKane's arity is unchanged.
- **Part (2) avoids the excluded lemmas:** no hD lemma and no SupersingularTorsionRankFour.
  - EssSurj and SeparableIsogenyExists appear only at their definitions.
  - The one hCor use has an integral, prime-to-q ideal (exists_integral_primeTo).
- **Counts and hygiene:**
  - 34 axiom prints, all standard (Check.lean, axioms.txt).
  - INVENTORY A052 does read "N>1".
  - Hygiene is clean apart from em-dashes.

## Nits
- **Docstrings for the reading desk** should spell out two derivations: the bijective-map form of VoightThm4232Etale (lift F and F⁻¹, then use injectivity on ψφ and on id), and the HomPlacement equivalence.
- **The 42.2.4 sentence** is quoted only in the module docstring (VoightCandidates.lean:10-16), but report :189 says each candidate docstring quotes it.
- **levelEndEquivRight takes a frame of the non-reference E** (LevelOrderLemma.lean:434), which the brief advised against. It is harmless: the frame is used only for Tate injectivity.
- **Report wording at :206** on integrality should read: "some rational translate contains 1".
- **The v21f scope-error withdrawal is partial:** pm-adelic-join.md:115-121/:131, rc-pm-geometry.md:92-97 and rc-stage-kummer.md:55/:66 still assert it.
- **"All new declarations" (report :11)** is broader than the 34 checked.
- **Part (2) builds are not in builds.txt**, and the "nine docstring-edited" modules include code-edited ones.
- **Em-dashes** at Odd/Statements.lean:13, :15 and as empty table cells.
- **Jetchev–Kane online check:** not done. The §1.1/§2.5 claims rest on a reading of arXiv 0908.3905v1, not the journal version. The GLUE label stands for the stated reason.
