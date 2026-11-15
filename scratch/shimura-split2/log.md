# shimura-split2 results log

Task: split `RayClassCFT.ShimuraMainThmIDeligneY3AbU` (gt-rayclass composite) faithfully; prove the fields
`rayClassCMAb`, `shimuraFamilyAb`.

## 2026-11-15

* 04:35 Build tree: copied `.lake/build`, `lean/.lake/build` from `~/dzq-wt/yu-prune-base` (HEAD c2ad4181 = gt-rayclass's
  base; `git diff --stat c2ad4181 HEAD -- ZInQKernel lean` = only RayClassShimura.lean). `lake build
  +ZInQKernel.Contrib.OneProof.RayClassShimura` replays the chain.
* Plan (finding, from reading RayClassShimura.lean): `embed_core` uses from the composite only clause 1 (onto, and the
  `DCRel → equal` direction), clause 4 at `g = u ∈ 𝒪̂^×`, and `ModuliAtUnits`. `shimuraFamilyAb` uses only clause 3
  with holomorphy at `g = 1`. VERIFIED (read).
* Design: state reciprocity on objects, not on a map `Ψ`: `MIsAt P τ g` = "`P : QML3 ℂ` has an `ι`-compatible
  uniformization with kernel `ι(L_g)(τ,1)ᵀ`, `L_g = B ∩ 𝒪̂g⁻¹`, and level structure `η(a) = [ι(x)(τ,1)ᵀ/3]` for
  `x g ≡ a mod 3𝒪̂`". Reciprocity `σ(MIsAt P z g) → MIsAt (P^σ) z (q̂(s)^ε g)` then has no normalization problem
  (no `Ψ`, no witness), so it is a separate leaf.
* 04:38 `lake build +ZInQKernel.Contrib.OneProof.RayClassShimura`: replayed 12226 jobs, built RayClassShimura (147 s).
  VERIFIED.
* 04:42 `ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean` part 1 compiles (`lake env lean`, 0 errors, 11 s):
  definitions `latB`, `vecLat`, `LevelAt`, `MIsAt`; leaves `QMReciprocityL3`, `ShimuraHolFamilyAb`; glue Props
  `DCRelTransport`, `UnifDetermines`, `ComplexUnifL3`; proved `vecLat_unit` (`L_u = 𝒪`), `embed_core_obj`,
  `rayClassCMAb_of_split : ShimuraHolFamilyAb → QMReciprocityL3 → DCRelTransport → UnifDetermines → ComplexUnifL3 →
  HomLinearLift → RayClassCMAb`, `shimuraFamilyAb_of_hol : ShimuraHolFamilyAb → ShimuraFamilyAb`. VERIFIED (compiled).
* 04:46 `dcRelTransport_proof : DCRelTransport` proved (LevelAt restated with ∃ representative x, equivalent since representatives differ by 3L_g). Compiles, 0 errors. VERIFIED.
* 04:49 `unifDetermines_of : HomLatticeCorr → UnifDetermines` proved (QML3.Iso from the unique lifts of id and of ι(a); level via `level_rep_eq`). Compiles. VERIFIED.
* 04:53 `complexUnifL3_of : QMComplexUnif → ComplexUnifL3` proved (η(1) = [ι(b)(τ,1)ᵀ/3], `nrd b ≢ 0 mod 3` from
  `ker η = 3𝒪` via `η(b̄)`, then a unit `ε ≡ b mod 3` from a 72-entry table checked by `decide +kernel` (`tab_spec`);
  `(𝒪/3𝒪)^×` has 72 elements since `B` is ramified at 3; table from `py/units.py`, VERIFIED computed).
  `complexUnifL3_of_textbook` from `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`.
* 04:53 Final: `rayClassCMAb_of_printed : ShimuraHolFamilyAb → QMReciprocityL3 → UniformizationLeafAll →
  GAGAMorphism → MumfordTorsionAlgClosed → RayClassCMAb`; `shimuraFamilyAb_of_printed : ShimuraHolFamilyAb →
  ShimuraFamilyAb`. `#print axioms` (in-file run): [propext, Classical.choice, Quot.sound] for both and for the glue
  proofs and `tab_spec`. VERIFIED (compiled, `lake env lean`, 12 s).
* 04:56 `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraSplit2`:
  `Build completed successfully (12981 jobs)`, 18 s (`build.txt`). VERIFIED.
* 04:57 `#discharges` (`Discharges.lean`, output `discharges_output.txt`): `rayClassCMAb` by
  `ShimuraSplit2.rayClassCMAb_of_printed`, still assumes [ShimuraHolFamilyAb, QMReciprocityL3, UniformizationLeafAll,
  GAGAMorphism, MumfordTorsionAlgClosed]; `shimuraFamilyAb` by `shimuraFamilyAb_of_printed`, still assumes
  [ShimuraHolFamilyAb]; axioms standard. `65 open hypotheses, 1558 theorems checked, 11 discharge one`. VERIFIED.
* 04:59 §12: `ShimuraHolModAll` (∀ fine witness form, no existence claim); proved `regVal_comp`, `isHolFamily_comp`, `exists_map_of_r1fp` (maps between fine witnesses from R1univAbProps), `shimuraHolModAll_of_hol` (∃ form ⇒ ∀ form) and `shimuraHolFamilyAb_of_all`; fields from (R) of deligneComponentsX6PrintedAb: `rayClassCMAb_of_leaves2`, `shimuraFamilyAb_of_leaves2`. Compiles. VERIFIED.
* 05:04 Rebuilt (`build.txt`); `#discharges` rerun (`discharges_output.txt`): `rayClassCMAb` by
  `rayClassCMAb_of_leaves2`, still assumes [DeligneComponentsX6PrintedAb, QMReciprocityL3, UniformizationLeafAll,
  GAGAMorphism, MumfordTorsionAlgClosed]; `shimuraFamilyAb` by `shimuraFamilyAb_of_leaves2`, still assumes
  [DeligneComponentsX6PrintedAb, ShimuraHolModAll]; all axioms standard; `65 open hypotheses, 1568 theorems
  checked, 14 discharge one`. VERIFIED.
* 05:04 Autofold dry run (`autofold-spec.json`, `autofold-dryrun.txt`): `strict count: 45/13 on 58 -> 45/13 on 58;
  strictest 44/14 -> 44/14` with qmReciprocityL3 entered as kind `consequence` and shimuraHolModAll as `published`,
  flag `pending reading` (both GLUE until read). Fold module (`FoldCheck.lean`, line 1 stripped) compiles;
  `sixContactMin_of_open27` axioms [propext, Classical.choice, Quot.sound] (`foldcheck_output.txt`). VERIFIED.
* 05:12 Report drafted (docs/research/shimura-split2.md). Independent model review of QMReciprocityL3/ShimuraHolModAll launched (adversarial, conventions).
