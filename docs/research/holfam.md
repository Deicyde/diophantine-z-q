# holfam: the holomorphic moduli map on the fine witness, from the PEL family with its complex uniformization

Task holfam, 2026-11-15. Base: wip/composite-out 822da7b5 (composite-out's result on leaf-fold25). This is model work
with no human review.

Marks: **VERIFIED** means compiled, computed or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. **UNVERIFIED** means a locator recalled without a source; this host has no
network.

## 1. Result

`ShimuraSplit2.ShimuraHolFamilyAb` is not proved from the bundle fields alone (§3 explains why). It is reduced to one
new leaf, `HolFamilyPrinted.PELHolFamily`. This leaf is stated on the printed object only: Deligne's PEL moduli
scheme `M_{K₃}`, with its universal family and its complex uniformization. It mentions neither the project's fine
witness `(Y, Φ)` nor `PtEquiv` nor `R1fpPropsAb`.

The step that shimura-split2 left to a reading was the identification of the printed object with `Y₃`. That step is
now a Lean proof, `shimuraHolModAll_of_pel`. VERIFIED: the file compiles, and every theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

File: `ZInQKernel/Contrib/OneProof/HolFamilyPrinted.lean` (namespace `HolFamilyPrinted`, imports
`ZInQKernel.Contrib.OneProof.CompositeOut`).

```lean
def PELHolFamily : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom ∧ SmoothOfRelativeDimension 1 S.hom ∧
    ∃ 𝒜 : R1UnivRigid.QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜.toQMFamily s.left P) ∧
      ∃ sτ : UpperHalfPlane → (fieldPt ℂ ⟶ S),
        ShimuraSplit.IsHolFamily (X := S.left) (fun τ => (sτ τ).left) ∧
        ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily (sτ τ).left P ∧
          ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
            IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
            HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu

theorem shimuraHolModAll_of_pel (hP : PELHolFamily) : ShimuraSplit2.ShimuraHolModAll
theorem shimuraHolFamilyAb_of_pel (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : PELHolFamily) :
    ShimuraSplit2.ShimuraHolFamilyAb
theorem pelHolFamily_of_hol (hH : ShimuraSplit2.ShimuraHolFamilyAb) : PELHolFamily   -- not stronger
theorem pelHolFamily_iff_hol (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) :
    PELHolFamily ↔ ShimuraSplit2.ShimuraHolFamilyAb
theorem shimuraFamilyAb_of_pel (hR) (hP) : HDec.QMSplit.Moduli.ShimuraFamilyAb
theorem y3Connected_of_pel (hGL) (hR) (hP) (hM : QMRecPrinted.MainTheoremCM) (hUL) (hG) (hMum) :
    HDec.TSHecke.Y3Connected
theorem compositeUses_of_pel (hR) (hP) (hM) (hUL) (hG) (hMum) (hGL) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected
```

**The transport** (`shimuraHolModAll_of_pel`, GLUE, proved). Let `(Y, Φ)` be any fine witness.
1. Its clause `R1univAbProps` classifies the family `𝒜 → S` by a morphism `g : S → Y` over `ℚ`, with
   `Φ(s ≫ g) = [fibre at s]`.
2. `τ ↦ s_τ ≫ g` is holomorphic, because holomorphic families compose with morphisms of schemes
   (shimura-split2's `isHolFamily_comp`).
3. Its object at `τ` is the fibre of `𝒜` at `s_τ`, and that fibre is `ℂ²/Λ_τ` as a QM pair.

The fine witness itself is supplied by the existing leaf `deligneComponentsX6PrintedAb`, through its clause (R).

**The three uses of the composite** (`shimuraMainThmIDeligneY3AbU`) now follow from `PELHolFamily` and `MainTheoremCM`,
together with the fine witness of `deligneComponentsX6PrintedAb`, the textbook fields `uniformizationLeafAll`,
`gagaMorphism` and `mumfordTorsionAlgClosed`, and `mumfordGroupLaw`. composite-out's group-theoretic connectedness
proof is reused unchanged.

## 2. The new leaf and its rating

| leaf | kind | printed form? | reason |
|---|---|---|---|
| `HolFamilyPrinted.PELHolFamily` | published | **a consequence of the printed statement, not stronger**; locators UNVERIFIED | see below |

**Published statements**, all UNVERIFIED:
* Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4.9–4.17 and Example 5.8. This gives the PEL moduli
  scheme `M_K` over the reflex field (`ℚ` here), its universal abelian scheme, and `M_K(ℂ) = G(ℚ)\X × G(𝔸_f)/K` with
  `[x, g]` carrying `ℂ^g/Λ(x, g)`.
* Milne, *Introduction to Shimura varieties* (2005):
  - §8: PEL Shimura varieties are moduli varieties. The analytic family on `Sh_K(ℂ)` is algebraic, by Borel's
    extension theorem and Riemann's theorem in families, Deligne Hodge II 4.4.3.
  - §14: the model over the reflex field.
* Shimura, Ann. of Math. 78 (1963), the analytic families `τ ↦ ℂ²/ι(𝒪)(τ,1)ᵀ`, and Ann. of Math. 85 (1967),
  Main Theorem I.

**Why it is a consequence.** Take
* `G = B^×` with `B` of discriminant 6;
* `K₃ = ker((𝒪 ⊗ ℤ̂)^× → (𝒪/3𝒪)^×)`;
* `S = M_{K₃}`, which is proper because `B` is a division algebra;
* `𝒜` the universal family;
* `s_τ = [τ, 1]`.

The leaf also asks for less than that statement in three ways:
* one family, on the one component through `[τ, 1]`;
* the fibre is described only as a QM pair, with no level clause;
* nothing about the fine witness `Y`.

The converse is proved too (`pelHolFamily_of_hol`): `PELHolFamily` follows from `ShimuraHolFamilyAb`, so it is no
stronger than the leaf it replaces.

**Rating, compared with the existing leaves.**
* shimura-split2 flagged `ShimuraHolModAll` "pending reading". The reason was that the printed object (Shimura's
  `V_S` over `ℚ(ζ₃)`, or Deligne's model) has to be identified with the project's fine witness `Y₃`, and that step was
  not in the print. `PELHolFamily` leaves that step out; it is the Lean proof of §1.
* What remains in the leaf is the existence of `M_{K₃}` with its universal family in the project's conventions
  (`QMAbScheme`, with `QML3` fibres). That is the same moduli content as clause (R) of `deligneComponentsX6PrintedAb`,
  which kinds.tsv rates published, flag "locator UNVERIFIED", strict LEAF.
* The leaf adds one more clause: the complex uniformization, meaning `[τ, 1]` is holomorphic with fibre `ℂ²/Λ_τ`.

**Two possible ratings:**
* **Strict (in the spec, `scratch/holfam/autofold.json`):** published, flagged *pending reading of the analytic
  clause*. The open question is whether Deligne §4 / Example 5.8 (or Milne §§8, 14) states `M_K(ℂ) ≅ Γ\X` *as
  analytic spaces with the family* for this integral `𝒪`-linear level-3 datum over `ℚ`. The locators.md row R1 says
  §§4.9–4.17 were read, with a "qualified CONSEQUENCE" verdict on the conventions. Under this rating it counts as
  strict GLUE.
* **As `deligneComponentsX6PrintedAb` is rated:** published, flag "locator UNVERIFIED", strict LEAF. The
  convention caveats of row R1 are shared with (R), and the analytic description is part of Deligne's PEL section
  (SPECULATIVE until read).

**Count** (SPECULATIVE until the integrator applies it; it replaces composite-out's spec):
* Out: `shimuraMainThmIDeligneY3AbU` (composite, strict GLUE).
* In: `mainTheoremCM` (LEAF) and `pelHolFamily`.
* Strict rating: strict GLUE unchanged now, −1 when the reading clears.
* Rating as `deligneComponentsX6PrintedAb`: **−1 strict GLUE** right away.

Either way, the reading to be done is smaller than shimura-split2's: there is no `V_S → Y₃` step.

## 3. Why holomorphy is not proved from the bundle fields

The task asked first for a proof from the fields already in the bundles. Each of them was read (VERIFIED by reading
the definitions):
* `uniformizationLeafAll` speaks of single abelian varieties: `A^an ≅ ℂ^g/Λ`.
* `gagaMorphism` (`TailQ.lean:875`) speaks of single abelian varieties: an analytic map `ℂ^g/Λ → B(ℂ)` is
  algebraic.
* `HomLatticeCorr` is about homomorphisms of single abelian varieties.
* `MainTheoremCM` and the X6 leaves are about single points or objects.
* `mumfordGroupLaw` is about group laws on families.
* The R1fp clause lists (`R1univAbProps`) classify only algebraic families over proper smooth curves over `ℚ`.

None of these says how a point of `Y(ℂ)` depends on `τ`. The analytic family over `ℍ` is not an algebraic family over
a `ℚ`-curve, so `R1univAbProps` cannot be applied to it.

To derive holomorphy one would need a relative comparison: holomorphic dependence of periods on parameters for the
universal family over `Y^an`, or analytic representability of the moduli problem. Neither is in Mathlib or in the
repository. This is a judgement about what can be proved, not a statement that it is logically independent (all the
statements involved are true). It agrees with composite-out §2. SPECULATIVE.

The alternative "pure model" leaf was also considered and rejected. That leaf would be Shimura's `(V, φ)` with
Galois-compatible moduli on ℂ-points but no family. The bijection `V(ℂ) → Y(ℂ)` it induces is `Aut(ℂ)`-equivariant,
but such a bijection need not be algebraic. For example, swapping two `ℚ`-points of `ℙ¹` is equivariant. So the
transport would need continuity, which is the very thing missing. That is why the leaf has to carry the algebraic
family and the holomorphic uniformization together (SPECULATIVE argument; not formalized).

## 4. Checks (all VERIFIED)

* `lake env lean ZInQKernel/Contrib/OneProof/HolFamilyPrinted.lean`: 0 errors, 0 warnings, 1 min 32 s
  (`scratch/holfam/compile1.txt`, empty output).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.HolFamilyPrinted`:
  "Build completed successfully (12999 jobs)" (`scratch/holfam/build1.txt`). The build tree was copied from
  composite-out's worktree, which is at the same commit.
* `#discharges` (`scratch/holfam/Discharges.lean`, output `scratch/holfam/Discharges-output.txt`):
  - It reports "63 open hypotheses, 2223 theorems checked, 7 discharge one". The 7 are the same pre-existing
    contributions; none comes from `HolFamilyPrinted`.
  - No current open field is matched. This is expected, as in composite-out: the composite itself is not proved,
    only its three uses.
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all seven theorems of the file.
* Bypass fold dry run (`scratch/holfam/BypassFold.lean`, output `BypassFold-output.txt`):
  - It is composite-out's dry run with the field `shimuraHolModAll` replaced by
    `pelHolFamily : HolFamilyPrinted.PELHolFamily`.
  - Both uses become `HolFamilyPrinted.shimuraHolModAll_of_pel r.pelHolFamily`.
  - `HDec.HSyn.sixContactMin_of_open31` and `ZInQ.Contrib.TYZChain.frozenTarget_holfam` both depend on
    `[propext, Classical.choice, Quot.sound]`.
* Autofold spec (`scratch/holfam/autofold.json`):
  - It is a bypass, because the composite is not proved as stated.
  - Leaves: `mainTheoremCM` (published; same row as qmrec-printed's) and `pelHolFamily` (published, flagged pending
    reading of the analytic clause, as in §2).
  - Consumer terms:
    - `rayClassCMAb`: `QMRecPrinted.rayClassCMAb_of_mainCM …`
    - `shimuraFamilyAb`: `HolFamilyPrinted.shimuraFamilyAb_of_pel {l}.deligneComponentsX6PrintedAb {r}.pelHolFamily`
    - `y3Connected`: `HolFamilyPrinted.y3Connected_of_pel …`

## 5. Proposed row for `docs/research/locators.md` (not edited here)

| leaf | source | status |
|---|---|---|
| `pelHolFamily` | Deligne, Sém. Bourbaki 389 (1971) §§4.9–4.17, Example 5.8; Milne ISV (2005) §§8, 14; Shimura, Ann. of Math. 78 (1963), 85 (1967) MT I | UNVERIFIED. To check: (i) `M_K(ℂ) ≅ G(ℚ)\X × G(𝔸_f)/K` *as analytic spaces*, with the universal family pulling back to `ℂ²/Λ(x,g)`; (ii) the R1 conventions shared with (R) of `deligneComponentsX6PrintedAb`: lattice `𝒪`, level-3 structure, `E(G,h) = ℚ`. |

## 6. What remains

* **Hand fold:** apply `scratch/holfam/autofold.json` in place of composite-out's spec, after dcy3-used's bypass.
  The dry run compiles.
* **Readings:**
  - the analytic clause of `pelHolFamily` (§5);
  - the torsion clause of `MainTheoremCM`: Shimura 1998 §18 or Milne ISV §11, as before.
* **Coordination:** unif-printed (origin/wip/unif-printed) had no report commit when this task started, so nothing
  was merged. Its restatement of `uniformizationLeafAll` does not affect this file, which uses that field only through
  composite-out's theorems.
* No statement was changed. Nothing under `ZInQKernel/` was edited except the new file `HolFamilyPrinted.lean`.
