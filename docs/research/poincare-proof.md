# poincare-proof: the field `poincareComplement` is proved from five open fields (no new leaf)

**Result (VERIFIED, compiled).** `ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open`
(`ZInQKernel/Contrib/OneProof/PoincareComplement.lean`) has type

```lean
T09Pic.PicRepresentableAbVar → T09Pic.PicZeroAbVar → T09Pic.PhiAmpleIsogeny →
  AvSplit.MilneIsogenyQuasiInverse → AVGlue.CartierSmooth → ZInQ.Contrib.AVB1.PoincareComplement
```

The conclusion is exactly the field's statement: Poincaré's complete reducibility in complement form (Milne 1986,
Prop. 12.1; Mumford §19 Thm 1), over every field of characteristic 0, with no narrowing. The five hypotheses are all
fields of the current bundles (base 0caafe66, top `sixContactMin_of_open35`):
`{l}.picRepresentableAbVar`, `{l}.picZeroAbVar`, `{l}.phiAmpleIsogeny`, `{l}.milneIsogenyQuasiInverse`
(OpenAddedLeaves17) and `{t}.cartierSmooth` (OpenTextbookLeaves12). So the fold removes `poincareComplement` and
adds **no new leaf**: −1 hypothesis. The autofold dry-run gives strict 34/11 on 45 → 33/11 on 44 (strictest the same).

Checks (all on this host, base 0caafe66 with jp-compile's build tree copied in):

| check | outcome |
| --- | --- |
| `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PoincareComplement` | success, 13,699 jobs; the new module builds in 63 s |
| `#discharges` (`scratch/poincare-proof/Discharges.lean`, output in `discharges-output.txt`) | `DISCHARGES [OpenTextbookLeaves12.poincareComplement] by ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open`; still assumes the five fields above; axioms `[propext, Classical.choice, Quot.sound]` |
| `scripts/one_proof/autofold.py scratch/poincare-proof/autofold.json --dry-run` | the generated `TailZ43` text (`scratch/poincare-proof/FoldDryRun.lean`, first line stripped) compiles; `sixContactMin_of_open36` has standard axioms |
| code that runs at build time | none (no `#eval`, `run_cmd`, syntax, macros) |

## The proof

`i : B → J` is a homomorphism and a closed immersion, over a field `k` of characteristic 0.

**Polarization step (`exists_psi`).**
* `L` very ample on `J` (`T09Pic.exists_isVeryAmple`, proved in the tree from the vendored projectivity theorem).
  `L' = i^*L` is very ample on `B`: compose the immersion `J → ℙ^N` with `i`. It is ample by the proved
  `T09Pic.veryAmpleIsAmple`.
* `Pic_{B/k}` is represented by `P` (L1) and `Pic⁰ = (D, j)` is an abelian variety (L2).
* `ψ' : J → P` classifies the family `(i × 1)^*Λ(L)` on `B ×_k J`, where `Λ(L) = m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹`
  is `T09Pic.mumfordBundle`. It sends `0` to `0`: the restriction to `B × 0` factors through `Λ(L)|_{J × 0}`,
  which is trivial (`T09Pic.mumfordBundle_restrict_zero`). So `ψ'` factors through `Pic⁰` by a homomorphism
  `ψ : J → D` (`exists_hom_lift`, the proof of `T09Pic.exists_hom_comp_eq_phiL` written for any map that sends
  `0` to `0`: `J` is connected, `j` is an open immersion onto the identity component, then rigidity).
* `ψ' ∘ i = φ_{L'}`, by naturality of the Mumford bundle (`mumfordBundle_map`: `(i × i)^*Λ(L) = Λ(i^*L)`,
  since `i` is a homomorphism). L3 (`PhiAmpleIsogeny`, for `B` and the ample `L'`) then makes `ψ ∘ i` an
  isogeny.

**Algebraic step (`complement_of_psi`).** Put `φ = ψ ∘ i : B → D`. Milne's quasi-inverse (the field
`milneIsogenyQuasiInverse`) gives `d > 0` and `φ' : D → B` with `φ'φ = [d]_B` and `φφ' = [d]_D`. Let
`F = [d] − iφ'ψ ∈ End J`. Its image (`AVGlue.imageFactorization_of_cartier`, proved from Cartier) is
`F = g ∘ h`, with `h : J → C` surjective and `g : C → J` a closed immersion. Then:
* `i ≫ F = 0` and `F ≫ ψ = 0` (the identities above, written multiplicatively in the group `Hom(−, −)`);
* `g ≫ ψ = 0` and `g ≫ h = [d]_C` (`h` is an epimorphism: `C` is reduced, the targets are separated, and
  Mathlib's `ext_of_isDominant_of_isSeparated` applies); `i ≫ h = 0` (`g` is a monomorphism);
* `m = i·pr₁ + g·pr₂ : B × C → J` and `m' = (φ'ψ, h) : J → B × C` satisfy `m' ≫ m = [d]_J` and
  `m ≫ m' = [d]_B ⊗ [d]_C`.
* `[d]` is finite and surjective in characteristic 0 (`ZInQ.Contrib.AbVarBC.mulIsogeny`, already proved in the
  tree). So `m` is surjective (`Surjective.of_comp`), and `m` is finite: `[d]_B ⊗ [d]_C` is finite (base change),
  `m'` is separated, and Mathlib's `IsFinite.of_comp` applies. The output is `Z = C` with `g : C → J`.

## Consumers and narrowing

The only consumer is T8 (`PkgI3.PoincareReducibility`), through `AVGlue.poincareReducibility_of_published'`
(TailX:218). Step E1 in TailD uses T8 over a number field. No narrowing was needed, since the full statement is
proved.

## For the integrator

* Spec: `scratch/poincare-proof/autofold.json`. It discharges `poincareComplement` and has no leaves. The proof
  term takes `{l}.picRepresentableAbVar {l}.picZeroAbVar {l}.phiAmpleIsogeny {l}.milneIsogenyQuasiInverse
  {n}.cartierSmooth`, so the conversion theorem of the fold takes the added-leaves bundle `l` as an extra
  argument. The dry-run shows autofold handles this.
* New dependency: the t09-pic leaves L1-L3 (`picRepresentableAbVar`, `picZeroAbVar`, `phiAmpleIsogeny`) now have
  a second consumer, besides `t09SymmIsogenyExists`. Before, `milneIsogenyQuasiInverse` was consumed only on the
  points side. A later fold that drops any of these five fields by a route that no longer provides the statement
  has to keep it available to this proof.
* New leaves: none, so there are no printed-form ratings and no `locators.md` rows. The leaf row
  `poincareComplement` (Milne 1986 Prop. 12.1; Mumford §19 Thm 1) leaves kinds.tsv. Its locators were marked
  UNVERIFIED and no longer matter.

## Files

* `ZInQKernel/Contrib/OneProof/PoincareComplement.lean`: the proof. It imports `ZInQKernel.Contrib.AVB1.Poincare`
  (the statement), `ZInQKernel.OneProof.H.TailZ24` (T09Pic, AvSplit, AVGlue) and `ZInQKernel.Contrib.AbVarBC.Main`.
  It does not import `ZInQKernel.OneProof.Main`.
* `scratch/poincare-proof/`: `PoincareComplement.lean` (the same file), `Discharges.lean` and
  `discharges-output.txt`, `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean.txt`, `log.md`.
