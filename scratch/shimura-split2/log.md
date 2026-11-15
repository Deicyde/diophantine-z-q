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
* 05:40 `ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean` part 1 compiles (`lake env lean`, 0 errors, 11 s):
  definitions `latB`, `vecLat`, `LevelAt`, `MIsAt`; leaves `QMReciprocityL3`, `ShimuraHolFamilyAb`; glue Props
  `DCRelTransport`, `UnifDetermines`, `ComplexUnifL3`; proved `vecLat_unit` (`L_u = 𝒪`), `embed_core_obj`,
  `rayClassCMAb_of_split : ShimuraHolFamilyAb → QMReciprocityL3 → DCRelTransport → UnifDetermines → ComplexUnifL3 →
  HomLinearLift → RayClassCMAb`, `shimuraFamilyAb_of_hol : ShimuraHolFamilyAb → ShimuraFamilyAb`. VERIFIED (compiled).
