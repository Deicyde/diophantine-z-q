# t30-adelic fold notes

Fragment: `scratch/leaf-adopt3/fold/t30-adelic.lean` (2106 lines, section `T30Sec`).
- **Folded:** only the T30 part (`scratch/t30-adelic/SqrtCrit.lean`, namespace `T30`).
- **Not folded:** the G1-adelic part (`Adelic.lean`, 1066 lines; `G1Count.lean`, 52 lines). Reasons:
  - it needs the whole kernel file `ZInQKernel/HDecomp/Vigneras/Local.lean` (707 lines, namespace
    `GlueVigneras`, absent from Leaves.lean);
  - it changes no bundle field or glue Prop.

  Its statements are listed below.
- No `sorry` in SqrtCrit.lean. The kernel files contain the word only in docstrings.

## Bundle change

- Field `t30 : GlueDescent.B2Q.LeafSqrtCrit` of `HSyn.TextbookLeaves` becomes glue, proved from
  field `t16a`. Delete the field. Wherever `L.t30` is needed, use `T30.leafSqrtCrit_of_t16a L.t16a`.
- Grep shows no current use of `.t30` in Leaves.lean. The B2/B3 glue (`b2_of_leaves`,
  `b3_of_leaves`, `b3_degree_le_QM`) takes `LeafSqrtCrit` as a hypothesis, so the G0 assembly would
  feed it the bridge.
- Reclassification: T30 LEAF → GLUE (from T16a). The literature list loses T30.

## Bridging theorems (in the fragment, namespace `T30`, under `open GlueDescent.B2Q GlueSqrtDisj`)

```lean
theorem T30.leafSqrtCrit_of_t16a (h : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) :
    GlueDescent.B2Q.LeafSqrtCrit          -- written `LeafSqrtCrit` in the source
theorem T30.leafSqrtCrit_of_localKroneckerWeber
    (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber (p : ℕ)) : GlueDescent.B2Q.LeafSqrtCrit
theorem T30.sqrtCrit_at (p : Nat.Primes) (hLKW : PkgI6.LocalKroneckerWeber (p : ℕ)) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (hu1 …) (hu2 …) :
    (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1
```

- The hypothesis of `leafSqrtCrit_of_t16a` is syntactically the type of field `t16a`.
- The "if" direction needs no hypothesis: `T30.sqrt_of_chi'`.
- No new leaf Props and no new glue Props.

## Kernel declarations

**Already in Leaves.lean, text identical (checked declaration by declaration):**
- `GlueDescent.B2Q.{GQ, GQp, resp, resp_continuous, toRingAut, cyc, galChar, LeafSqrtCrit, act}`
  (Leaves.lean ~8731-8794 against `Descent/B2Glue.lean`);
- `PkgI6.LocalKroneckerWeber` (Leaves.lean ~4988 against `Conductor/I6Base.lean` 257).

Leaves.lean's `GlueDescent.B2Q` also has extra names: `b2_of_leaves`, `cast_cast_of_dvd`,
`chiLevel_pos`, `chi_toUnitHom_crt`, `exists_crt_unit`, `lev_eq_pow`. None of them clashes with an
identifier used by the fragment.

**Copied into the fragment** (namespaces absent from Leaves.lean). Each file is copied verbatim in
its own section, imports dropped, in dependency order:
1. `ZInQKernel/HDecomp/Conductor/SqrtChar.lean`, namespace `GlueI6Rest` (`exists_half_iff`, used by
   SqrtLocal). Section `T30KernelSqrtCharSec`.
2. `ZInQKernel/HDecomp/Sqrt/SqrtLocal.lean`, namespace `GlueSqrtLocal` (`redU_sq_eq_one`,
   `redU_val`, `galToProd`-related lemmas). Section `T30KernelSqrtLocalSec`. Top-level
   `open Polynomial`.
3. `ZInQKernel/HDecomp/Sqrt/Disj.lean`, namespaces `GlueSqrtLocal` and `GlueSqrtDisj`. It provides
   `muField`, `muField_mono`, `galToProd`, `galToProd_fst_spec/snd_spec/restrict/injective`,
   `range_galToProd`, `exists_tau`, `le_muField_of_lkw`, `coprime_pow_sub_one`,
   `orderOf_unit_pow_sub_one`, `dvd_pow_orderOf_sub_one`, `level_dvd`. Section
   `T30KernelDisjSec`. Top-level `open Polynomial IsLocalRing`, `open scoped Pointwise`, and a
   namespace-local notation `"N"` that ends with `end GlueSqrtLocal`, before T30's variables named
   `N`.

Disj.lean imports `Conductor/I6Base.lean` only for `PkgI6.LocalKroneckerWeber`, which Leaves.lean
already has. Its other import, `Dyadic.lean` (namespace `GlueConductor`), is not used by these
files. None of the other fold fragments declares these namespaces (grep of `fold/*.lean`).

## Statement differences

None. The kernel `LeafSqrtCrit` is identical to Leaves.lean's.

## Expected compile trouble spots

- Low risk overall: SqrtCrit and the kernel files all import full `Mathlib`, as Leaves.lean does.
- Global instances declared in Leaves.lean before this point could in principle change instance
  search in the copied proofs. Candidates: the `GlueDescent.B2Q` instance
  `IsTopologicalGroup GQ`, and `Algebra`/`Fact` instances from other sections.
- Kernel-timeout pitfall from the report: `coe_algebraMap_mu` deliberately goes through
  `IntermediateField.inclusion`. Do not "simplify" it to `rfl`.
- `T30` and `GlueDescent.B2Q` each have their own section-local `local instance (p : Nat.Primes) :
  Fact (p : ℕ).Prime`, as in the source.
- The source check took about 8 s.

## `#print axioms` dropped

`T30.leafSqrtCrit_of_localKroneckerWeber` and `T30.leafSqrtCrit_of_t16a`. Both were
`[propext, Classical.choice, Quot.sound]`. Suggested to keep: `T30.leafSqrtCrit_of_t16a`.

## G1-adelic: not copied. Main statements (namespace `G1Adelic`, `open GlueVigneras`)

Objects:
- `BA := Πʳ p : Nat.Primes, [Bp (p : ℕ), OpSub (p : ℕ)]`, i.e. `B̂ = B ⊗ 𝔸_f`;
- `Ohat : Set BA := {y | ∀ p, y p ∈ Op p}`;
- `Nhat : Subgroup BAˣ`, the normalizer of `𝒪̂`;
- `K0 : Subgroup BAˣ`, `𝒪̂^×`;
- `Zhat : Subgroup BAˣ`, the central scalars `𝔸_f^×`;
- `K3`, `{u ∈ K₀ : u_3 ≡ 1 mod 3𝒪_3}`;
- `Zint`, `ℤ̂^×`.

Theorems (all compiled in the scratch, standard axioms):
- `G1Adelic.relIndex_eq_four : (Zhat ⊔ K0).relIndex Nhat = 4`
- `G1Adelic.quotEquiv : Nhat ⧸ (Zhat ⊔ K0).subgroupOf Nhat ≃* ((Bp 2)ˣ ⧸ Hloc P2 hP2) × ((Bp 3)ˣ ⧸ Hloc P3 hP3)`
- `G1Adelic.gamma_count : (Zhat ⊔ K3).relIndex Nhat = 4 * ((Zhat ⊓ K0) ⊔ K3).relIndex K0`
- `G1Adelic.relIndex_K3 : ((Zhat ⊓ K0) ⊔ K3).relIndex K0 = 36`
- `G1Adelic.gamma_order : (Zhat ⊔ K3).relIndex Nhat = 144` (h-b1 M3: `|Γ'| = 144`)
- `G1Adelic.Zhat_inf_K0 : Zhat ⊓ K0 = Zint`
- `G1Adelic.gamma_count_Zint : (Zhat ⊔ K3).relIndex Nhat = (Zhat ⊔ K0).relIndex Nhat * (Zint ⊔ K3).relIndex K0 ∧ (Zhat ⊔ K0).relIndex Nhat = 4 ∧ (Zint ⊔ K3).relIndex K0 = 36`
- `G1Count.index_count` (generic): for `K₃ ≤ K₀`, `Z` normal and `Z ⊔ K₃` normal,
  `[G : Z ⊔ K₃] = [G : Z ⊔ K₀] · [K₀ : (Z ⊓ K₀) ⊔ K₃]`.

Kernel needs if it is folded later:
- `GlueVigneras` (all of `Vigneras/Local.lean`, not in Leaves.lean): `Bp`, `Op`, `combp`,
  `unramified_normalizer`, `exists_pi`, `normalizerOp_eq_univ`, `mem_OpUnits_iff`, …;
- `GlueRepo.A1.{combMul, mul3, one3, nrd3, isUnit3_iff, card_units_mod3}`. These are in Leaves.lean
  (section `RepoA1QuaternionSec`, ~9264); not text-diffed here.
