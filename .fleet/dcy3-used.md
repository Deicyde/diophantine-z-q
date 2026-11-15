# dcy3-used: done. `deligneComponentsY3PrintedAb` is removable with no new leaf (−1 GLUE)

**Verdict.** The chain reads the field only as `TSHecke.Y3Connected`: some fine witness `Y₃` is connected over `ℚ`.
The path is TailZ23, then TailZ13, then `heckeIrreducible_of_connected`. That used form follows from two fields
already in `OpenResearchLeaves22`:

- `shimuraMainThmIDeligneY3AbU`, Shimura's Main Theorem I in Deligne's adelic form on `Y₃`;
- `mumfordGroupLaw`.

The rest is proved material: Eichler class number one, Tau Ceti's absolute Artin map, Steinitz's extension to
`Aut(ℂ)`, and a `decide` table over `𝒪/3𝒪`.

`ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean` (namespace `DCY3Used`) proves:

```lean
y3ConnectedAb_of_U     : RayClassCFT.ShimuraMainThmIDeligneY3AbU → DCY3Used.Y3ConnectedAb
y3ConnectedAb_of_field : ShimuraGlue.DeligneComponentsY3PrintedAb → DCY3Used.Y3ConnectedAb   -- not stronger
y3Connected_of_leaves  : MumfordGroupLaw → ShimuraMainThmIDeligneY3AbU → HDec.TSHecke.Y3Connected
```

There is no sorry and the axioms are the standard three.

**How.** For a clopen `U`, `χ(g) = [Ψ(τ,g) ∈ U]` does not depend on `τ`, and it is invariant under `B^×_+` and `K₃`
by the uniformization. Let `s` be the `ℚ(i)`-idele equal to `1+i` above 3 and to `1` elsewhere. `χ` is invariant
under `h = q̂(s)` by the reciprocity law at the CM point `√2+i` of `i ↦ i+j`. Here `h ≡ 1+i+j mod 3`, with reduced
norm `≡ −1`. Class number one together with the table (`𝒪¹` reaches all 36 norm-1 classes of the 72 units mod 3)
makes `χ` constant.

**Compiles (VERIFIED).**
- `lake build +ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used` succeeds.
- `#discharges` (`scratch/dcy3-used/Discharges-output.txt`) matches no open field, as expected, because the used
  form is weaker than the field.
- The bypass fold dry run `scratch/dcy3-used/BypassFold.lean` compiles with standard axioms. It defines
  `OpenAddedLeaves18` (14 fields), `sixContactMin_of_open30` mapping to `sixContactMin_of_open10`, and a copy of
  `frozenTarget` on the new bundle.
- The spec is `scratch/dcy3-used/autofold.json`: a bypass with no leaves. In kinds.tsv the row is removed, so strict
  GLUE drops by 1 and strictest GLUE drops by 1.

**What remains.**
- The integrator has to do the hand fold.
- The pending reading does not go away. "Is the PEL moduli scheme with its uniformization the canonical model at
  level `K₃`?" now rests only on the already-open composite row `shimuraMainThmIDeligneY3AbU`. Report §4 lists the
  clauses of that row the proof reads.
- Deligne's bijection itself (the field as stated) is not derived; it needs a lower bound of two geometric
  components. It is not needed.

Report: `docs/research/dcy3-used.md`.
