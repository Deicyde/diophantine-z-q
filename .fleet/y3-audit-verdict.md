# y3-audit: verdict of part (1), the consumer audit of the Y₃ fine-moduli leaf

Task y3-audit, 2026-11-17. Branch wip/y3-audit, with origin/main (27657ffb, top `sixContactMin_of_open58`) merged.
Full report: docs/research/y3-audit.md. Log: scratch/y3-audit/log.md.

## Verdict

1. **What the chain uses (VERIFIED: Lean probe over the closure of `ZInQ.OneProof.frozenTarget` plus reading).**
   It uses a **fine** moduli scheme `Y₃` for the moduli problem with **full 𝒪-linear level 3**, **over ℚ only**, with
   **no polarization**. "Fine" here has three parts:
   * `Φ_K : Y(K) ≃ M3 K` is a bijection for **every** field `K ⊇ ℚ`. The chain uses it at ℚ̄, at ℂ, at number fields
     `K ⊆ ℚ̄`, and at the residue fields `κ(x)` of points of `Y`.
   * Φ is natural under field maps.
   * A universal `QMAbScheme` lives over `Y`, and families over proper smooth ℚ-curves have classifying maps.

   The probe found no integral (ℤ[1/6] or ℤ_(p)) property of `Y₃` in the live closure: `SGRSplit.ShimuraIntegralModelRep`
   and the good-reduction model leaves are absent.
2. **The decisive uses are fine, not coarse.**
   * `rationalFibre_of_le` (TailC.lean:2361) takes a `K`-point, for `K ⊆ ℚ̄` a number field containing the residue
     field. It then needs an object `PK : QML3 K` over `K` itself, with its level-3 structure rational over `K`. This
     is N5 L528, "choose a fibre A/K".
   * The pinning of witnesses needs the universal family together with the classifying maps: `phi_part` (Pin.lean:235),
     `eq_id_of_Φ`, `exists_surjective_of_R1fp`.
   * The Hecke automorphisms are built the same way: `classify` and `heckeOfFine_proof` (TailU.lean:2202, 2220).
   * The forgetful map `Y₃ → X₆` is the classifying map of the universal family (`x6ModuliWitness_of_coarse`,
     GRX6AbPrint.lean:80).

   A coarse space would not supply these uses unless rigidity is added. With rigidity, coarse equals fine on field
   points, so the content is the same.
3. **The consumers cannot run at a Buzzard level (`U ⊆ V₁(N)`, `N ≥ 4` prime to 6, `U` maximal at 2 and 3) without
   rewriting the H chain.** Level 3 is built into the statements themselves:
   * the objects: `QML3`/`Level3`, with kernel `3𝒪`;
   * the action of `Γ' = Aut 𝒪 ⋉ 𝒪^×` on level-3 structures;
   * the degree bound `deg(Y₃ → P¹_j) ≤ 324` and `F₀ = 324!`;
   * the ray-class fields of conductor 3 in `RayClassCMAb`;
   * "unramified at `p ≥ 5`" at the CM points (R1rec, Lemma NV). At level 5 or 7 this fails at 5 or 7;
   * `π₀(Y₃) = (ℤ/3)^×`;
   * Raynaud's criterion with `m = 3`, applied to the rational 3-torsion of the rational fibre;
   * the Prop TS thresholds `p > 324`.

   Every consumer in the table of the full report is level-3-specific in its statement, or reaches the witness only
   through level-3 statements.
4. **Is the leaf true?**
   * `Y3Fix.Y3FineModuliAbP` is **true over ℚ (STANDARD argument; no print read)**:
     * rigidity holds at level 3: an automorphism of `(A, ι, η)` is a root of unity `u` in `End_𝒪(A)`, an order in
       ℚ or in an imaginary quadratic field, with `u − 1 ∈ 3·End_𝒪(A)`. Then `|u − 1|² ≤ 4 < 9` forces `u = 1`
       (Serre's lemma; Mumford, *Abelian varieties* §21 Thm 5, UNVERIFIED);
     * the fine level-3 space is then the free quotient of a fine space at an auxiliary level. N5 L441-478 itself
       does this with Buzzard's `V₁(5)`.
   * It is **not printed** in the form stated. Buzzard 1997 excludes level at `3 | D`.
   * The y3-fix rating "printed form (LEAF)" should change to: **true, with no verified print**. It is a consequence of
     either of these:
     * (a) a fine space at a Buzzard level, plus GLUE: the Isom scheme for the level-3 structures, a free quotient by
       `GL₂(𝔽₅)`, étale descent, and rigidity;
     * (b) Kottwitz 1992 §5 at an auxiliary prime `p ∤ 6`. There `K₃` is a neat prime-to-`p` level, so the level at
       3 is covered, and the generic fibre gives representability over ℚ. This needs the PEL comparison: Lemma P and
       the level classes (unread: locators.md R1).
5. **What would change at a Buzzard level** (not recommended):
   * the objects `QML3 → QML_U`;
   * every numerical constant above;
   * R1rec's prime threshold, which would also change T unless `N ∈ {5, 7, 11, 13}`;
   * RayClassCMAb's conductor;
   * the π₀ computation and Raynaud's `m`.

   That is a re-proof of the QM layer of H. **Recommended instead:** keep level 3 and make representability over ℚ the
   leaf (part 2, in progress).

## Consumer table

| consumer | file:line | property of Y₃ used | at a Buzzard level? |
|---|---|---|---|
| `shimuraFamilyAb_of_U` → `ShimuraFamilyAb` | Contrib/OneProof/RayClassShimura.lean:3049 | ℂ-points `Ψ(τ,1)` with lattice moduli clause, holomorphy; R1fpPropsAb carried | no: objects are `QML3` (level-3 `η_τ`) |
| `rayClassCMAb_of_leaves` / `obj_at` → `RayClassCMAb` | RayClassShimura.lean:3042, 1642 | `Φ` at ℚ̄ and ℂ, naturality ℚ̄→ℂ, Ψ; residue field of CM ℚ̄-points ⊆ ray class field **mod 3** | no: conductor 3 is the level |
| `y3ConnectedAb_of_U`, `y3Connected_of_leaves` → `Y3Connected` | DeligneComponentsY3Used.lean:681, 756 | ℂ-points via Ψ and reciprocity; `π₀ = (ℤ/3)^×` | no (level-3 component count) |
| `connectedSpace_of_R1fp`, `exists_surjective_of_R1fp` | OneProof/H/TailG.lean:8356, 8316 | `Φ` at residue fields `κ(x)`, R1univ + R1fam (pinning) | level-agnostic in form, but stated over `QML3` |
| `gonzalezRotgerX6Ab_of_print`, `x6ModuliWitness_of_coarse` | Contrib/OneProof/GRX6AbPrint.lean:115, 80 | universal `QMAbScheme` over Y (R1famAbProps) fed to X₆'s coarse universal property; ℚ̄-points | the X₆ leaf quantifies over level-3 families |
| `elkiesX6StarFunctionField_of_every` | Contrib/OneProof/ElkiesX6StarEvery.lean:91 | the X₆ witness above (fY : Y₃ → X₆) | as above |
| `phi_part`, `eq_id_of_Φ`, `mobiusGlue_of_curveFacts` | HDecomp/QM/Pin.lean:235; H/TailU.lean:2082; Contrib/Mobius/Glue.lean:257 | uniqueness of the witness: R1fam of one witness + R1univ of another on proper smooth ℚ-curves, field points | level-agnostic in form, over `QML3` |
| `classify`, `heckeOfFine_proof` → R1hecke | H/TailU.lean:2202, 2220 | twisted universal family classified by R1univ: `Aut 𝒪`, `𝒪^×` act on Y₃ over ℚ | no: `Γ'` acts on level-3 structures |
| `heckeBranch_of`, Hecke irreducibility (TSHecke) | H/TailG.lean:9014 | `Y₃ → P¹_j` Galois, group of order dividing 144 | no |
| `rationalFibre_of_le` (N5 L528), `fibreCoverOut_iff` | H/TailC.lean:2361 | **`Φ_K` at number fields `K ⊆ ℚ̄`**: an object `PK/K` with level 3 rational over K | no: rational 3-torsion → Raynaud `m = 3` |
| `conjTwist_of_rational`, `semilinearTwistIsos_of_descent`, `endTransport_of` (KernelField) | H/TailF.lean:1302, 1335; H/TailC.lean:6969 | `K`-points (`K ⊆ ℚ̄`) and conjugates of `PK` | no |
| `residueImage_comp_eq_of_pt`, `fieldOfModuli3_eq_residueImage` | H/TailG.lean:273; H/TailZ20.lean:1284 | residue field of a ℚ̄-point = field of moduli of the level-3 object | no (level-3 field of moduli) |
| `fieldDescentUnr`, `fibreDegree_of` (Lemma PR) | H/TailA.lean:2962; H/TailC.lean:2554 | `K`-points; degree ≤ 324 | no |
| `fibreQMPeriodAt_of`, period map (PeriodMapH) | H/TailC.lean:8301 | ℂ- and ℚ̄-points, naturality | over `QML3` |
| `elkies_coordinate`, `HeckeBranchFibreUnram` (SGRDirect) | Contrib/OneProof/SGRDirectElkies.lean:87 | ℚ̄-points, family, residue fields | no |
| `cm_pointW` (π₀/STQM) | Contrib/OneProof/Pi0FoldSTQM.lean:30 | CM ℚ̄-point of Y₃ | over `QML3` |
| every-witness leaves `GonzalezRotgerThm512X6`, `ElkiesX6StarEvery` | (definitions; probe) | hypothesis `R1fpPropsAb Y Φ` pins the witness | stated at level 3 |

Not a Y₃ consumer: `R16Split.R16CoreY`. Its "Y" is a variant name: Eichler–Shimura for `J₁(N)` (VERIFIED by reading,
R16Split.lean:534).
