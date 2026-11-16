# weil-used: the added field `weilPairingMumford`

Task weil-used, base 43513d873 (leaf-fold25). Field `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford :
T09Pic.WeilPairingMumford` (statement `ZInQKernel/OneProof/H/TailZ24.lean:708`, bundle `TailZ34.lean:150`); kinds.tsv row
56: published, strict LEAF, strictest GLUE ("composite").

## 1. Result

1. **Consumers (VERIFIED, probe compiled).** The field's only consumer on the route is
   `T09Pic.t09SymmIsogenyExists_of_four` (in `addedLeaves12_of_open13`, `TailZ24.lean:821`). It never reads clause (6)
   (values = `weilScalar`) and reads clauses (1)-(5) only to fill the fields of `WeilPairing.WeilDual` and
   `WeilPairing.SymmIsogeny`. Below `T09_SymmIsogenyExists`, no constant in the closure of `ZInQ.OneProof.frozenTarget`
   reads `WeilDual.dualEnd` (clause 4) or the right half of `IsPerfect` (clause 1). Those two are inert.
2. **(a) Unread clauses.** Clause (6) can be dropped without touching anything else. The restatement is
   `T09Pic.WeilPairingPicZero`, which already exists in TailZ24: clause 6 dropped, an existential dual in clause 4, and
   clause 5 for very ample `L`. It is exactly what `t09SymmIsogenyExists_of_leaves` reads, and both implications are
   compiled (§2 of the file). Clauses (4) and (1, right half) can only be dropped by weakening the structure
   `WeilDual`. That would reroute the consumers of `T09_SymmIsogenyExists` back to `OpenAddedLeaves4` and older bundles,
   so it is recorded here (§3 of the file, `WeilPairingRead`) and not folded.
3. **(b) What remains is not one printed proposition.** Perfect, compatible and adjoint come from Mumford §20,
   alternating from §23, and Galois-equivariance from Milne 1986 §16. So the field is **split**, using t09-pic's
   six-way split L4a-f, which pins the pairing to Mumford's genuine `ē_n` (`weilScalar`). This does not raise the strict
   count. The autofold dry-run gives:
   `strict count: 46/10 on 56 -> 51/10 on 61; strictest 45/11 -> 51/10`.
   The strict GLUE count is unchanged (10) and the **strictest GLUE count goes down by 1 (11 -> 10)**. The bundle gains
   5 fields: 6 leaves replace 1 field.
4. **No split leaf is stronger than the field.** `split_of_weilPairingMumford` proves each of the six leaves from
   `WeilPairingMumford`. Because `constK` is injective, `IsMumfordPairing` pins `e n` for every `n ≥ 1` invertible in
   `K`. In the other direction, `weilPairingMumford_of_split` gives the field from the six leaves. The two directions
   together make the split equivalent to the field. **Caveat:** L4e (adjoint) is read only to fill the inert
   `WeilDual.dualEnd`.

### Theorems (`ZInQKernel/Contrib/OneProof/WeilPairingUsed.lean`, namespace `WeilUsed`, imports `ZInQKernel.OneProof.H.TailZ24`)

New leaves: t09-pic's L4a-f, copied verbatim from `scratch/t09-pic/Pic.lean:751-811` (commit 131fc43a1), with the
namespace changed to `WeilUsed`:

```lean
/-- `e` is Mumford's pairing: its values are `weilScalar` (as constants of `Γ(A_K̄, 𝒪)`) for every
`n ≥ 1` invertible in `K`. Since `constK` is injective, this pins `e n` for those `n`. -/
def IsMumfordPairing {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
    constK A ((e n x y).val : AlgebraicClosure K) =
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A)) (Additive.toMul (y : HDec.WeilPairing.P B))

/-- **LEAF L4a (`ē_n` is a bilinear `μ_n`-valued pairing).** Mumford §20 (definition of `ē_n`;
values in `μ_n`, bilinear), with Kleiman 9.2.5 and Mumford §8 (iv); UNVERIFIED numbering. -/
def WeilPairingExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∃ e : ∀ n : ℕ, Pairing A B n, IsMumfordPairing rep j e

/-- **LEAF L4b (`ē_n` is perfect).** Mumford §20 (n prime to the characteristic); UNVERIFIED. -/
def WeilPairingPerfect : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)

/-- **LEAF L4c (`ē_n` is Galois-equivariant).** `ē_n` is defined over `K` (Milne 1986 §16);
UNVERIFIED. -/
def WeilPairingGalois : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)

/-- **LEAF L4d (compatibility `ē_{mn}(x, y) = ē_n(mx, y)` for `y ∈ Â[n]`).** Mumford §20;
UNVERIFIED. -/
def WeilPairingCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
      ∀ (x : tors A (m * n)) (y : tors B n),
        (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val

/-- **LEAF L4e (adjunction `ē_n(x, f^∨ y) = ē_n(f x, y)`).** Mumford §20 (5) for isogenies;
Milne 1986 Lemma 16.2(c) for all homomorphisms; UNVERIFIED. -/
def WeilPairingDual : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
      (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y

/-- **LEAF L4f (`e^L_n(x, x) = 1`).** Mumford §23 (`e^L_n(x, y) = ē_n(x, φ_L(y))` is
skew-symmetric with `e^L_n(x, x) = 1`; stated for ample `L`); UNVERIFIED. -/
def WeilPairingAlternating : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0


```

```lean
theorem weilPairingMumford_of_split (ha : WeilPairingExists) (hb : WeilPairingPerfect)
    (hc : WeilPairingGalois) (hd : WeilPairingCompat) (he : WeilPairingDual)
    (hf : WeilPairingAlternating) : WeilPairingMumford
theorem constK_injective (A : AbVar K) : Function.Injective (constK A)
theorem split_of_weilPairingMumford (h : WeilPairingMumford) :
    WeilPairingExists ∧ WeilPairingPerfect ∧ WeilPairingGalois ∧ WeilPairingCompat ∧ WeilPairingDual ∧
      WeilPairingAlternating
theorem t09SymmIsogenyExists_of_split (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (ha : WeilPairingExists) (hb : WeilPairingPerfect) (hc : WeilPairingGalois)
    (hd : WeilPairingCompat) (he : WeilPairingDual) (hf : WeilPairingAlternating) :
    HDec.WeilPairing.T09_SymmIsogenyExists
-- §2, the restatement read by the consumer (T09Pic.WeilPairingPicZero, TailZ24)
theorem weilPairingPicZero_of_mumford (h : WeilPairingMumford) : WeilPairingPicZero
theorem t09SymmIsogenyExists_of_picZero (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (h4 : WeilPairingPicZero) : HDec.WeilPairing.T09_SymmIsogenyExists
-- §3, the read set below T09_SymmIsogenyExists
def WeilPairingRead : Prop  -- ∃ e, trivial left kernel ∧ Galois ∧ compatible ∧ e_n(x, λ_L x) = 0 (L very ample)
theorem weilPairingRead_of_picZero (h : WeilPairingPicZero) : WeilPairingRead
theorem weilPairingRead_of_mumford (h : WeilPairingMumford) : WeilPairingRead
```

`#print axioms` for each of the six main theorems prints `[propext, Classical.choice, Quot.sound]`
(`scratch/weil-used/discharges.txt`). The module builds (`lake build ZInQKernel.Contrib.OneProof.WeilPairingUsed`).

### `#discharges` (`scratch/weil-used/Discharges.lean`, output `scratch/weil-used/discharges.txt`)

```
'WeilUsed.weilPairingMumford_of_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilUsed.split_of_weilPairingMumford' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilUsed.t09SymmIsogenyExists_of_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilUsed.weilPairingPicZero_of_mumford' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilUsed.t09SymmIsogenyExists_of_picZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilUsed.weilPairingRead_of_mumford' depends on axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.neronBaseChangeStrictHenselization] by GapSHPair.neronBaseChangeStrictHenselization_of_unramified
  still assumes: [ReductGlue.NeronBaseChangeUnramifiedDVR]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.elkiesX6StarPrinted] by HDec.QMSplit.Moduli.ElkiesX6Star.elkiesX6StarPrinted_of_ab
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.r16CoreY] by R16Split.coreY_of_r16
  still assumes: [LeafModCurves.R16_EichlerShimuraJ1']
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.sga7_IX_3_3_SH] by SGA7PersistsNF.sga7_IX_3_3_SH_of_field
  still assumes: [CToPrinted.SGA7_IX_3_3]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.sga7_IX_3_5_ForwardGeom] by UnipotentForward.forwardGeom_of_forward
  still assumes: [UnipotentForward.SGA7_IX_3_5_Forward, UnipotentForward.SemiAbelianDescendsSepClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by WeilUsed.weilPairingMumford_of_split
  still assumes: [WeilUsed.WeilPairingExists,
 WeilUsed.WeilPairingPerfect,
 WeilUsed.WeilPairingGalois,
 WeilUsed.WeilPairingCompat,
 WeilUsed.WeilPairingDual,
 WeilUsed.WeilPairingAlternating]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.mumfordGroupLaw] by ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core
  still assumes: [LeafQM.AV.R1UnivRigid.MumfordRigidityCore]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1817 theorems checked, 8 discharge one
```

The line for this task is `DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by WeilUsed.weilPairingMumford_of_split`,
with the six leaves still assumed. The other lines come from contributions already in the tree.

### Autofold spec: `scratch/weil-used/autofold.json`

It discharges `weilPairingMumford` by
`_root_.WeilUsed.weilPairingMumford_of_split {n}.weilPairingExists {n}.weilPairingPerfect {n}.weilPairingGalois {n}.weilPairingCompat {n}.weilPairingDual {n}.weilPairingAlternating`,
with six published leaves (types `_root_.WeilUsed.WeilPairing*`).
- `python3 scripts/one_proof/autofold.py scratch/weil-used/autofold.json --dry-run` prints
  `strict count: 46/10 on 56 -> 51/10 on 61; strictest 45/11 -> 51/10`.
- The printed module (`scratch/weil-used/FoldDryRun.lean`, line 1 stripped) compiles with `lake env lean`.
  `HDec.HSyn.sixContactMin_of_open30` has the standard axioms.

### Rating of the new leaves

| leaf | printed form? | reason |
|---|---|---|
| L4a `WeilPairingExists` | yes, with a note | Mumford §20 defines `ē_n : X_n × X̂_n → μ_n` and states that it is bilinear. Reading its values as `weilScalar` on the Lean `Pic⁰` uses Kleiman 9.2.5 (the `K̄`-points of `Pic` are line bundles) and Mumford §8 (iv). This is the same bridging as in the field and as in `phiAmpleIsogeny` (flagged note). **If a reviewer reads this bridging as composite, L4a is strictest GLUE: the strictest count is then unchanged (11 -> 11) and the split only adds 5 fields, so the single-leaf form (or §2) is better.** |
| L4b `WeilPairingPerfect` | yes | Mumford §20, perfectness of `ē_n` (n prime to char). |
| L4c `WeilPairingGalois` | yes (locator weakest) | Mumford works over `k̄`. Milne 1986 §16 says `e_n` is defined over `K` (no numbered statement known to me; UNVERIFIED). |
| L4d `WeilPairingCompat` | yes | Mumford §20, `ē_{nm}(x, y) = ē_n(mx, y)`. |
| L4e `WeilPairingDual` | yes, with a note | Mumford §20 (5) states it for isogenies; Milne 1986 Lemma 16.2(c) states it for all homomorphisms (UNVERIFIED). Inert downstream (fills `WeilDual.dualEnd` only). |
| L4f `WeilPairingAlternating` | yes (consequence) | Mumford §23: `e^L` is skew-symmetric with `e^L(x, x) = 1` for every `L`. It is stated here for ample `L`, a special case. |

Every locator is UNVERIFIED (no network, no copy of Mumford or Milne on the host).

### Alternative: the single-leaf restatement (manual fold, not recommended over the split)

If the lead prefers one field, replace `weilPairingMumford : T09Pic.WeilPairingMumford` by
`weilPairingPicZero : T09Pic.WeilPairingPicZero` (kind published, strict LEAF, strictest GLUE: still composite). The
counts do not change; the gain is a weaker statement (no `weilScalar` clause, existential dual, very ample `L`). The
weaker field cannot fill the older generations, so this is a bypass fold (as in TailZ23):
- The field is passed unchanged by `openAddedLeaves16_of_OpenAddedLeaves17` (`TailZ34.lean:155`, field line 169),
  `openAddedLeaves15_of_OpenAddedLeaves16` (`TailZ31.lean:51`, line 66), `openAddedLeaves14_of_OpenAddedLeaves15`
  (`TailZ30.lean:54`, line 70) and `openAddedLeaves13_of_OpenAddedLeaves14` (`TailZ26.lean:173`, line 190).
- Its only consumer is `addedLeaves12_of_open13` (`TailZ24.lean:815`, field `t09SymmIsogenyExists` at line 821).
- The new generation `OpenAddedLeaves18` maps straight to `OpenAddedLeaves12`: compose the four maps above with the
  same field terms, and set
  `t09SymmIsogenyExists := _root_.WeilUsed.t09SymmIsogenyExists_of_picZero l.picRepresentableAbVar l.picZeroAbVar l.phiAmpleIsogeny l.weilPairingPicZero`.
- The new top theorem calls `sixContactMin_of_open17` (TailZ23) with `r` mapped 22 -> 14 by the research maps of
  TailZ35, TailZ34, TailZ33, TailZ29, TailZ28, TailZ27, TailZ26 and TailZ25, in that order. It maps `t` 11 -> 10 by
  `openTextbookLeaves10_of_OpenTextbookLeaves11`. The cross-bundle arguments `t` of
  `openResearchLeaves19_of_OpenResearchLeaves20 r t`, `openResearchLeaves20_of_OpenResearchLeaves21 r t`,
  `openResearchLeaves21_of_OpenResearchLeaves22 r t` and `openAddedLeaves14_of_OpenAddedLeaves15 l t` are the
  generation-11 or generation-10 `t`, as in the chain. It passes `g` unchanged and
  `hYu := QMLattice.yuB6Alg_of' t10.uniformizationLeafAll t10.gagaMorphism t10.mumfordTorsionAlgClosed` (TailZ30:75).

### Finding: the inert clauses (for a later change of `WeilDual`)

`WeilDual.dualEnd` has no reader in the closure of `frozenTarget` (244,312 constants). `WeilDual.perfect` has one
reader, `WeilPairing.weil_nondeg` (`TailB.lean:3704`), which uses `.1` only. `IsDualHom.unique` and
`weil_perfect_of_principal`, the users of `.2`, are not in the closure. So the route needs only `WeilPairingRead`:
trivial left kernel, Galois, compatible, and alternating on `λ_L`. That is still several printed properties (§20, §23,
Milne §16). Removing L4e and the right half of L4b would need a `WeilDual` without `dualEnd`, with only the left kernel
in `perfect`. That in turn means rerouting `tatePairingZl_of_leaves4` (`TailK.lean:250`) and `oldT9_of_symmIsogeny`
(`TailB.lean:3856`, through `t9_of_leaves5`, `TailN.lean:47`). Their bundle fields `t09SymmIsogenyExists` sit in
older generations (TailD:518, TailE:6537, TailI:158, TailK:196, TailN:181, TailZ13:24, TailZ17:192). That is a lead decision.

## 2. Method

- `scratch/weil-used/FieldUse.lean` imports `ZInQKernel.OneProof.Main`. It computes the constant closure of
  `ZInQ.OneProof.frozenTarget`. For every constant in it, it lists the projections, recursors and `.proj` nodes of
  `WeilDual`, `SymmIsogeny` and `Polarization` that its value mentions (a cached `Expr.find?`, so it is linear in the
  term DAG). The output is `FieldUse_out.txt` (3m34s). Clause readers inside `IsPerfect` were checked by reading
  `weil_nondeg`.
- The field's own path (`t09SymmIsogenyExists_of_four` -> `_of_mumford` -> `weilPairingPicZeroPrinted_of_mumford`
  discards clause 6 with `-`) was read in TailZ24.
- The split leaves come from t09-pic (compiled there). This task added `constK_injective`: `A ×_K K̄` is nonempty
  because `Spec K` is a point and both factors are nonempty, so `Γ` is a nonzero ring and a ring map from a field is
  injective. It also added `isMumfordPairing_eq` and `split_of_weilPairingMumford`.
- Lean runs: one at a time, after checking load and free memory. Build of the module: 21 s.
