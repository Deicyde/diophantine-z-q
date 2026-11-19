# Projection and trace links of the support-change assembly

All exports below are in
`ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange`.
The new source is `StageLinks.lean`; earlier editions are unchanged.

## Proven without additional arithmetic inputs

`exists_stagePairing_trace_links` reconstructs the existing normalized local
retraction and split replacement, retaining both its projection homotopy
equivalence and the all-degree original local-cup trace transport.

`StageArithmeticInput.exists_linked_split` produces `LinkedSplitStage S`. Its
fields retain one split stage, one normalized local retraction, one original
compact trace and both original duality statements. In particular:

```lean
projection_retract : localRetract.p = toSplitStage.projection
projection_model : ∃ e : HomotopyEquiv (F.localCx i).toCC
  (splitLocalComplex (Acoef i)).toCC,
  e.hom = GHom.toCC toSplitStage.projection

trace_transport : ∀ (a b : ℤ) (hab : a + b = 2)
  (u : (splitLocalComplex (Acoef i)).X a)
  (v : (splitLocalComplex (Acoef i)).X b),
  toSplitStage.trace (0, toSplitStage.pairing.cupL.P a b 2 hab u v) =
    originalCupTrace S originalTrace localRetract a b hab u v
```

`originalCupTrace` is the original compact trace pulled through the existing
scalar-cone comparison, evaluated on the original retained local cup of the
same included split cochains. It is not a determinant table.

The three `LinkedSplitStage.htrace02`, `.htrace11`, `.htrace20` fields are proved
specializations of this single all-degree identity.

`StageArithmeticInput.chosen_links` fixes this strengthened record once.
`producedStageLinks'` retains that choice. `producedStages'` uses its split
stage at positive precision and the original zero-target stage at zero.
Consequently the following are proved for the chosen family:

- `producedStages'_projection_model`;
- `producedStages'_trace_transport`;
- `producedStages'_htrace02`, `_htrace11`, `_htrace20`.

The projection theorem has exactly the local homotopy-equivalence forward-map
link. The transport theorem retains the normalized retraction, its projection
equality, the original trace and boundary vanishing, both original dualities,
and the original trace identity. Its successor-stage specialization has the
same shape as the projection-model wiring interface.

## Realized assembly on the strengthened stages

`assemble_realized_on_stages` is the prior actual global-complex realization
construction on any supplied split-stage family. It produces one retained
complex, pairing, inverse homotopies and conditional certificates together.

`assemble_inner_limit_realized'` and
`assemble_from_support_change_realized'` use `producedStages'` and additionally
return `L.StageLinks`:

```lean
L.StageLinks =
  ((∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC
    (splitLocalComplex (Acoef i)).toCC,
    e.hom = GHom.toCC (L.stages i).projection) ∧
   ∀ i [NeZero i], OriginalStageTraceLinks a L.stages i)
```

In the same implicit arithmetic setting as the earlier assembler, the principal
statement is:

```lean
theorem assemble_from_support_change_realized' (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R) (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      ∃ L : AssembledLimit
          (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) U hU Cn hW,
        L.stages = producedStages'
          (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) p hK hS₀ h2 ∧
          L.Realized ∧ L.StageLinks
```

The local projection and original trace links hold at every positive stage;
`L.Realized` retains its required ultrafilter-large-set qualification for the
actual global-complex matrix coordinates. All refer to the same chosen stages
and retained witnesses. No equality with an earlier unconstrained stage choice
or earlier opaque retained output is claimed.

## The remaining residue-arithmetic identification is explicit

The transport to `originalCupTrace` is proved. Identification with the
independent `StageArithmeticData` representatives and their conjugated local
cups is still OPEN, as in the original residue-cochain input boundary.

For `B : LinkedSplitStage S` and `Y : StageArithmeticData i`, the named
`OriginalResidueTraceIdentification S B Y` fields are precisely:

```lean
identification02 : ∀ x y : Fin 2 → Acoef i,
  originalCupTrace S B.originalTrace B.localRetract 0 2 rfl x y = Y.cup02 x y
identification11 : ∀ x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i),
  originalCupTrace S B.originalTrace B.localRetract 1 1 rfl x y = Y.cup11 x y
identification20 : ∀ x y : Fin 2 → Acoef i,
  originalCupTrace S B.originalTrace B.localRetract 2 0 rfl x y = Y.cup20 x y
```

These compare original cochain trace cups, including their coefficient,
conjugation, representative and compact/scalar-trace dictionaries. They do not
assume a residue formula in terms of a prescribed determinant matrix or scalar.
They cannot be inferred from a normalized retract and arbitrary local cup data
alone; the existing stage input has no link to an arbitrary independently
supplied residue-arithmetic presentation.

`ResidueLinkedSplitStage` stores this explicit identification and the resulting
three consumer trace fields. `LinkedSplitStage.withResidueIdentification`
constructs that record. `producedResidueStageLinks'` and
`producedResidueStages'` preserve it. `producedResidueStages'_eq` proves that
adding the identification does not alter the already chosen split-stage family.

The three `producedStages'_htrace*_of_identification` theorems have exactly the
trace hypotheses required by `RetainedZeroTwo.of_splitStages` and
`RetainedLocalArithmetic.of_splitStages`.

`assemble_inner_limit_residue_realized'` and
`assemble_from_support_change_residue_realized'` add the corresponding
`L.ResidueTraceLinks Y` conclusion on the same assembled witnesses. The latter
has the one additional named input family:

```lean
h : ∀ i [NeZero i], OriginalResidueTraceIdentification (stage i)
  ((stage i).chosen_links p hK hS₀ h2) (Y i)
```

No discharge of this original-cochain identification or of the complete
height-one arithmetic family is claimed. Earlier support presentation,
old-condition flatness, original cups/isotropy and duality comparisons,
unmatched complements, derivative action, roots and local dimensions remain
exactly as before.

Manuscript: `diophantine_zq.tex`, lines 3483–3498, 4385–4451, 4859–4873 and
4976–5135. Verification and exact axiom reports are recorded separately.
