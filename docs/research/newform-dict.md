# newform-dict: the kernel's `IsNewform` is the printed newform (proved)

Task newform-dict, 2026-11-15. Branch `wip/newform-dict`, base fork main 43513d87 (leaf-fold25). Contributor file
`ZInQKernel/Contrib/OneProof/NewformDict.lean` (17 KB). Scratch and log: `scratch/newform-dict/`.
Marks: **VERIFIED** (compiled, or read in the file named), **STANDARD** (published, reference given),
**SPECULATIVE**. Theorem numbers from memory are **UNVERIFIED** (no network).

## 0. Result

**The dictionary is proved in Lean in both directions, for the definitions as they stand.** For `N ≥ 1`, the
kernel's `IsNewform f χ` holds exactly when `f` is a newform of level `N` with nebentypus `χ` in the printed
sense (Atkin–Lehner 1970, Li 1975, Diamond–Shurman Def. 5.8.1, Miyake's primitive form), formalized as Tau Ceti's
`HeckeRing.GL2.Newform N k` (vendored in the kernel). The hard direction is strong multiplicity one. It follows
from Tau Ceti theorems already vendored in the kernel, with no new leaf. VERIFIED (compiled:
`lake build ZInQKernel.Contrib.OneProof.NewformDict`, no warnings in the file).

So no leaf has to be restated over `IsNormalizedEigenform` (the dsThm965 route), and no consumer has to be
restricted. Every statement over `IsNewform` is equivalent in Lean to the same statement over the printed
newform (`forall_isNewform_iff`).

### 0.1 Theorems (verbatim; namespace `NewformDict`; `open PkgI4 (CF coeff … IsNewform)`, `open HeckeRing.GL2`)

```lean
theorem exists_newform_of_isNewform [NeZero N] {f : CF N k} {χ : DirichletCharacter ℂ N}
    (hf : IsNewform f χ) :
    ∃ g : Newform N k, g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ

theorem isNewform_of_newform [NeZero N] (g : Newform N k) :
    IsNewform (g.toCuspForm : CF N k) (MulChar.ofUnitHom g.χ)

theorem isNewform_iff (hN : 0 < N) {f : CF N k} {χ : DirichletCharacter ℂ N} :
    IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ

-- the other two textual copies of IsNewform (same body, `Iff.rfl`)
theorem g9_isNewform_iff (hN : 0 < N) {f : ZInQ.Contrib.G9.PkgI4.CF N k} {χ : DirichletCharacter ℂ N} :
    ZInQ.Contrib.G9.PkgI4.IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ
theorem leafModCurves_isNewform_iff (hN : 0 < N) {f : HDec.LeafModCurves.CF N k}
    {χ : DirichletCharacter ℂ N} :
    HDec.LeafModCurves.IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ

theorem forall_isNewform_iff {k : ℤ} (P : (N : ℕ) → DirichletCharacter ℂ N → CF N k → Prop) :
    (∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N k), 0 < N → IsNewform f χ → P N χ f) ↔
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N k),
        f.χ = MulChar.toUnitHom χ → P N χ f.toCuspForm

-- the three bundle fields stated over IsNewform, restated over the printed newform (§3 of the file)
theorem carayolR17'_of_newform (h : CarayolR17Newform) : LadicCond.CarayolR17'
theorem newform_of_carayolR17' (h : LadicCond.CarayolR17') : CarayolR17Newform
theorem carayolR17'_iff_newform : LadicCond.CarayolR17' ↔ CarayolR17Newform
theorem r16CoreY_of_newform (h : R16CoreYNewform) : R16Split.R16CoreY
theorem newform_of_r16CoreY (h : R16Split.R16CoreY) : R16CoreYNewform
theorem r16CoreY_iff_newform : R16Split.R16CoreY ↔ R16CoreYNewform
theorem eigenformHTNew_of_newform (h : EigenformHTNewNewform) : ZInQ.Contrib.HodgeSplit.EigenformHTNew
theorem newform_of_eigenformHTNew (h : ZInQ.Contrib.HodgeSplit.EigenformHTNew) : EigenformHTNewNewform
theorem eigenformHTNew_iff_newform :
    ZInQ.Contrib.HodgeSplit.EigenformHTNew ↔ EigenformHTNewNewform
```

Each restatement is the field's text with one mechanical change. The binder `(f : CF N k)` and the hypotheses
`0 < N → IsNewform f χ →` become `[NeZero N] (f : Newform N k)` and `f.χ = MulChar.toUnitHom χ →`, and `f`
becomes `f.toCuspForm`. Nothing else changes. Example:

```lean
def CarayolR17Newform : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N 2) (ρ : GaloisRep ℓ 2)
    (p : ℕ) [Fact p.Prime],
    f.χ = MulChar.toUnitHom χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL (f.toCuspForm : CF N 2) →
      p ≠ ℓ → condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)
```

The texts of `R16CoreYNewform` and `EigenformHTNewNewform` are in the file, at lines 271 and 308.

`#print axioms` (VERIFIED: `scratch/newform-dict/Axioms.lean`, output `scratch/newform-dict/axioms.txt`):

```
'NewformDict.exists_newform_of_isNewform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.isNewform_of_newform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.isNewform_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.g9_isNewform_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.leafModCurves_isNewform_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.forall_isNewform_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.carayolR17'_iff_newform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.r16CoreY_iff_newform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NewformDict.eigenformHTNew_iff_newform' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 0.2 `#discharges` (VERIFIED: `scratch/newform-dict/Discharges.lean`, full output `discharges.txt`; lines for this file)

```
DISCHARGES [OpenResearchLeaves22.r17] by NewformDict.carayolR17'_of_newform
  still assumes: [NewformDict.CarayolR17Newform]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.eigenformHTNew] by NewformDict.eigenformHTNew_of_newform
  still assumes: [NewformDict.EigenformHTNewNewform]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.r16CoreY] by NewformDict.r16CoreY_of_newform
  still assumes: [NewformDict.R16CoreYNewform]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1833 theorems checked, 10 discharge one
```

### 0.3 Autofold spec

`scratch/newform-dict/autofold.json` replaces the three fields with their restatements. Each new leaf keeps the
kind of the field it replaces: `r17Newform` and `eigenformHTNewNewform` are consequence, `r16CoreYNewform` is
composite. None has a flag. The dry run (`python3 scripts/one_proof/autofold.py scratch/newform-dict/autofold.json
--dry-run`) reports `strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11`, so the fold is
count-neutral. The generated module, with line 1 stripped, is `scratch/newform-dict/AutofoldDryRun.lean`. It
compiles, and `'HDec.HSyn.sixContactMin_of_open30' depends on axioms: [propext, Classical.choice, Quot.sound]`
(VERIFIED).

The fold is optional. The fields as they stand are now certified to be equivalent to their printed-newform forms,
so nothing has to be rerouted. Folding would only make the bundle speak about printed newforms. The competing
folds of the same fields proposed by r17-bypass, ht-exists and r16-used are better combined with the restated
forms of §2.

## 1. What `IsNewform` means, compared with the sources

The kernel has three textual copies with the same body (VERIFIED, read):
`_root_.PkgI4.IsNewform` (`ZInQKernel/HDecomp/Conductor/LadicCond.lean:165`, used by `r17` and `r16CoreY`),
`ZInQ.Contrib.G9.PkgI4.IsNewform` (`ZInQKernel/Contrib/G9/I4Layer.lean:1273`, used by `eigenformHTNew`) and
`HDec.LeafModCurves.IsNewform` (`ZInQKernel/OneProof/H/LPrefix.lean:4480`). The body is:

```lean
def IsNewform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  IsNormalizedEigenform f χ ∧ (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k
```

* `IsNormalizedEigenform f χ` is the slash-form nebentypus `χ` on `Γ₀(N)`, together with `a₁ = 1` and
  `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` for all `m, n ≥ 1`. This says that `f` is an eigenform of
  every `T_n`, including `U_p` for `p ∣ N` (where `χ(p) = 0`).
* `oldSpace N k` is the ℂ-span, inside the functions `ℍ → ℂ`, of `τ ↦ g(dτ)` with `g ∈ S_k(Γ₁(M))`, `M ∣ N`,
  `M < N` and `dM ∣ N`.

**Printed newform** (STANDARD: Atkin–Lehner, Math. Ann. 185 (1970); W. Li, Math. Ann. 212 (1975);
Diamond–Shurman GTM 228 Def. 5.8.1; numbers UNVERIFIED). A newform is a normalized eigenform for all `T_n` and
`⟨d⟩` lying in `S_k(Γ₁(N))^new`, the Petersson orthogonal complement of the old space.

**Tau Ceti** `HeckeRing.GL2.Newform N k` (VERIFIED, read: vendored
`ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean:105` and `Newforms/Basic.lean:106,203`)
has four components:
* a nonzero cusp form on `Γ₁(N)` with a nebentypus `χ : (ZMod N)ˣ →* ℂˣ`;
* an eigenform of the good Hecke operators `heckeTCompositeGamma0 N n` for `(n, N) = 1`;
* lying in `cuspFormsNew N k := CuspForm.peterssonOrthogonal (cuspFormsOld N k)`, where `cuspFormsOld` is the
  span of the level raises `V_d` from `M` with `dM ∣ N`, `M ≠ N`;
* with `a₁ = 1`.

That a newform is an eigenform of every `T_n` is a theorem (`Newform.toEigenform`). This is Def. 5.8.1.

**Differences.** The kernel requires `f ∉ old`, which is a priori weaker than `f ∈ new`. It requires
eigenness at the bad primes too, which is a priori stronger. It encodes the character as a `DirichletCharacter`
(zero-extended), where Tau Ceti uses a unit homomorphism (`MulChar.ofUnitHom`/`toUnitHom` are inverse bijections).
`T25/Bridge.lean` proved new ⇒ `IsNewform`. The converse "eigenform for all `T_n` and not old ⇒ new" is the
content of strong multiplicity one (Li 1975 Thms 3 and 5; DS Thm 5.8.2; numbers UNVERIFIED). The docstring of
`ZInQ.Contrib.G9.PkgI4.IsNewform` already claims this equivalence; it is now proved.

## 2. Leaves freed of the dictionary step

* **On this base** (fields stated over `IsNewform`): `r17` (`LadicCond.CarayolR17'`), `r16CoreY`
  (`R16Split.R16CoreY`) and `eigenformHTNew` (`ZInQ.Contrib.HodgeSplit.EigenformHTNew`). Each is equivalent in Lean
  to its restatement over the printed newform (§0.1). All three are GLUE for other reasons, and stay GLUE:
  * `r17`: the transport to every semisimple attached `ρ`;
  * `r16CoreY`: a composite of two printed theorems about `A_f`, which has no Lean definition;
  * `eigenformHTNew`: Kato's `V_f` is not definable, so the theorem is transported and dualized.

  The newform notion is no longer one of those reasons.
* **GZ / TYZ hypotheses** (`hFH`, `hL3`, `h33`; also the proved `HeckeThetaNewform`): already stated over Tau
  Ceti's `Newform` (VERIFIED: `grep` finds no `IsNewform` in `ZInQKernel/Contrib/GZ*`,
  `Contrib/OneProof/FHNonvanishing`, `OneProof/TYZSplit.lean`). They never needed the dictionary.
* **New leaves proposed on other branches, not on this base.** All three are stated over `IsNewform` and are
  rated pending reading. The restated forms below compile (VERIFIED: `scratch/newform-dict/OffBase.lean`, output
  `offbase.txt`, standard axioms). Definitions were copied verbatim from the named commits.
  * `CarayolLevel.NewformRepConductor` (origin/wip/r17-bypass 3e6e5017, `CarayolLevel.lean:230`):
    `OffBase.CarayolLevel.iff_newform : NewformRepConductor ↔ NewformRepConductorNewform`.
  * `EigenformHTExists.KatoHTExists` (origin/wip/ht-exists 7088f9ed, `EigenformHTExists.lean:492`):
    `OffBase.EigenformHTExists.iff_newform : KatoHTExists ↔ KatoHTExistsNewform`.
  * `R16Used.AfTateCharPoly` and `R16Used.R16Trace` (origin/wip/r16-used dcf24ac6, `R16Used.lean:368, 388`) have
    the shape `∀ N χ f J, 0 < N → IsNewform f χ → IsJ1 N J → Q N χ f J`. `OffBase.R16Used.shapeJ_iff` proves that
    shape equivalent to its Newform form for arbitrary `Q`. Copying `AfTateCharPoly` itself would need R16Used's
    `tensorModule`.

  **Recommendation to the integrator.** When folding r17-bypass, ht-exists or r16-used, state their new leaf
  over the printed newform. For example, put `NewformRepConductorNewform` (the text in `OffBase.lean`) in the
  bundle, with proof `CarayolLevel.carayolR17'_of_newformRepConductor ((iff).mpr {n}.newformRepConductorNewform)`,
  where `iff` is the same two-line proof as `OffBase.CarayolLevel.iff_newform` (by
  `NewformDict.forall_isNewform_iff`). The `iff` theorem needs a module that imports both `NewformDict` and
  `CarayolLevel`; adding it to the contributor file `CarayolLevel.lean` is enough. Their leaves are then free of
  the newform dictionary.

### Ratings of the new leaves of this file

| leaf | printed form? | reason |
| --- | --- | --- |
| `CarayolR17Newform` | no (consequence, GLUE) | Carayol's Théorème (A) is about `ρ_{f,λ}`. The leaf is about every semisimple attached `ρ` (Chebotarev and Brauer–Nesbitt). The newform notion is now the printed one. |
| `R16CoreYNewform` | no (composite, GLUE) | two printed theorems about Shimura's `A_f`, over an existential `A`. Newform notion printed. |
| `EigenformHTNewNewform` | no (consequence, GLUE) | Kato's theorem for `V_{F_λ}(f)`, transported to every semisimple attached `ρ` and dualized. Newform notion printed. |
| `NewformRepConductorNewform`, `KatoHTExistsNewform`, `AfTateCharPoly` over `Newform` (§2, scratch) | possibly, pending the readings their tasks list | existence forms at the representation the print builds. With the restatement, the newform notion matches the print, so no dictionary step remains on that point. |

## 3. Method (proof of the hard direction)

The proof is `exists_newform_of_isNewform`, about 60 lines. Fix `N ≥ 1` and `f` with `IsNewform f χ`, and put
`χ₀ = toUnitHom χ`.
1. From `T25/Bridge.lean`: `f ∈ cuspFormCharSpace k χ₀`, and `T_p f = a_p(f) f` for `p ∤ N`.
2. Suppose `f` is not of the form `g.toCuspForm` with `g : Newform N k` and `g.χ = χ₀`. Tau Ceti's
   eigenvalue-refined spanning theorem `Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul` (DS Thm 5.8.3)
   writes `f` as a combination of `V_d g` with `g` a newform of level `M`, `dM ∣ N`, having the eigenvalues
   `a_p(f)` at `p ∤ N`. Sort each generator:
   * compatible character and `M = N`: then `d = 1`, and
     `Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul` (DS Thm 5.8.2 on the whole
     `χ`-space) gives `f = a₁(f) g = g`, against the assumption;
   * compatible character and `M < N`: the generator is in `cuspFormsOld`;
   * incompatible character: the generator is in another nebentypus space.

   So `f ∈ old ⊔ ⨆_{ψ ≠ χ₀} S_k(N, ψ)`.
3. The old space is diamond-stable (`diamondOpCusp_mem_cuspFormsOld`). By `iSup_inf_cuspFormCharSpace_of_invariant`
   it is the sum of its `χ`-parts, so `f = s + t` with `s ∈ old ∩ S_k(N, χ₀)` and `t ∈ ⨆_{ψ ≠ χ₀}`. Then
   `t = f − s ∈ S_k(N, χ₀)`, so `t = 0` by `iSupIndep_cuspFormCharSpace`.
4. So `f ∈ cuspFormsOld`. `map_cuspFormsOld_le_oldSpace` (new, the converse of Bridge's inclusion; Tau Ceti's
   `levelRaise_apply` is `(V_d g)(τ) = g(dτ)`) puts `⇑f ∈ oldSpace N k`, contradicting `IsNewform`.

Every Tau Ceti theorem used is in the vendored tree (`Newforms/Decomposition.lean`, `Newforms/Basic.lean`,
`CharacterDecomp.lean`, `Degeneracy.lean`) and is already compiled into the kernel.

## 4. What remains

* The fold (integrator): either the count-neutral autofold of §0.3, or, preferably, the Newform-form restatements
  of the new leaves from r17-bypass, ht-exists and r16-used when those are folded (§2).
* Ratings and readings of those leaves (their tasks' flags) are unaffected except that the newform dictionary is
  no longer among the open points.
