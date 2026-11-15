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
