# sga7-35-proof: the field `sga7_IX_3_5_ForwardGeom`

Base origin/main 0caafe66. Statement: `UnipotentForward.SGA7_IX_3_5_ForwardGeom`
(`ZInQKernel/Contrib/OneProof/UnipotentForward.lean`), a field of `OpenResearchLeaves26` (TailZ41); kinds.tsv
row: published, LEAF/LEAF, unverified-locator.

## 1. Verdict

**The field cannot be proved outright from Mathlib, the bundle fields and what ZInQKernel/ proves. It stays a leaf.
The target (field removed, -1, no new leaf) is not met.** (Mathematical argument, §3; not a Lean proof of
non-derivability.)

What was done instead (VERIFIED, compiled, standard axioms):

* `SGA7Orth.sga7_IX_3_5_ForwardGeom_of_orth` (`ZInQKernel/Contrib/OneProof/SGA7IX35Orth.lean`) proves the field,
  **statement unchanged**, from:
  * one new leaf, `SGA7Orth.GrothendieckOrthogonalitySS`: Grothendieck's orthogonality theorem in the semistable
    case, at finite level, over Mumford's Weil pairing. Rated **consequence** (GLUE), not printed form (§4);
  * three leaves already in the bundles (`OpenAddedLeaves17`): `picRepresentableAbVar`, `picZeroAbVar` and
    `weilPairingMumford`.
* Everything else in the standard proof is proved in Lean: `μ_N(K̄) ⊆ K` for `N` invertible in a strictly
  henselian `O`, the Weil-pairing argument that `σx - x` is orthogonal to the invariants of the dual, and the
  passage from `K̄` to the separable closure `Ω` of the statement.
* **The fold is not recommended.** It replaces a published leaf (LEAF) with a consequence (GLUE), so the strict
  and strictest GLUE counts each rise by one, and autofold refuses it without `--allow-rise` (§6). The reduction
  is useful only as a map: it isolates the geometric core of SGA 7 IX 3.5 (the orthogonality theorem) from its
  Galois and Weil-pairing glue, for whoever formalizes SGA 7 IX.
* Narrowing (§5): every live consumer works over number fields with abelian surfaces, and needs unipotence in
  general (wild `σ`; QM surfaces at `ℓ = 3`). No narrowing used by the consumers avoids the orthogonality theorem.

## 2. The statement (VERIFIED: read; `scratch/sga7-35-proof/Statements.lean` checks the verbatim copy by `rfl`)

For a strictly henselian DVR `O ⊆ K`, a separable closure `Ω` of `K`, `w` over `O`, an abelian variety `A` with
semistable reduction at `O` (`HasSemistableReduction`: some Néron model whose geometric special fibre has
semi-abelian identity component, in the genuine sense of `HasSemiAbelianIdentityComponent`), and a prime `ℓ`
invertible in `O`: every inertia element `σ` satisfies `(σ - 1)² = 0` on `T_ℓ A = lim A(Ω)[ℓⁿ]`. The definitions
are genuine (Néron mapping property; open connected subgroup with a flat surjection onto an abelian variety whose
kernel is `𝔾_m^r` in the functor of points). No falsity or vacuity was found.

## 3. Why the fields do not give it (mathematical argument; SPECULATIVE only as to which further leaves could help)

The standard proof (Grothendieck, SGA 7 I Exp. IX §§2-3; numbers UNVERIFIED) has these steps. `T = T_ℓ A`,
`T' = T_ℓ A'` (`A'` the dual), with the Weil pairing `T × T' → ℤ_ℓ(1)`. `T_f = T^I` is the fixed part, `T_t ⊆ T_f` the
toric part.

1. `T_f ≅ T_ℓ(N⁰_s)`, which has rank `2a + t` (Hensel, `[ℓⁿ]` étale on the Néron model, finite component group).
2. **Orthogonality theorem** (IX 2.4): `T_t` is the kernel of the pairing restricted to `T_f × T'_f`.
3. Semistable means `a + t = g`, so `(T'_f)^⊥` has rank `t` and equals `T_t`, hence lies in `T_f`.
4. `(σ - 1)T ⊆ (T'_f)^⊥` by Galois equivariance, since `I` acts trivially on `ℤ_ℓ(1)`. So
   `(σ - 1)T ⊆ T_f`, and `(σ - 1)² = 0`.

The fields that could feed this:
* `raynaudSemistableSH` is the converse direction (rational `A[m]` gives semistable). It says nothing about the
  action on `T_ℓ`.
* `sga7_IX_3_3_SH` (`N⁰` commutes with base change) and the Néron fields give step 1 and the equality
  `T^{I'} = T^I` for every open `I' ⊆ I`. Over a strictly henselian base there is no Frobenius, so this does not
  force unipotence: a semisimple `σ` whose eigenvalues are not roots of unity satisfies it too.
* `r7a` (Néron–Ogg–Shafarevich) concerns good reduction only.
* `weilPairingMumford` with `picZeroAbVar` gives the dual and the pairing (step 4). Step 2 is the deep input.
  It needs the biextension or Raynaud-extension theory of SGA 7 VII–IX, which no field and no library
  (Mathlib, the vendored FLT, Tau Ceti, Stacks ports, openai/math) provides.

Since step 4 is now proved in Lean, the smallest missing input is steps 1–3, stated as the new leaf (§4).

## 4. The new leaf and its rating

`SGA7Orth.GrothendieckOrthogonalitySS` (in `SGA7IX35Orth.lean`). `O` is a strictly henselian DVR, `A` is
semistable at `O`, `ℓ` is invertible in `O`, `(Pc, rep)` represents `Pic_{A/K}`, and `(B, j)` is its identity
component (`IsPicZero`). Let `e : A[ℓⁿ] × B[ℓⁿ] → μ_{ℓⁿ}` be pinned to Mumford's genuine `ē_n` by its values
(`constK (e x y) = weilScalar rep j ℓⁿ x y`). Then every `x ∈ A[ℓⁿ]` orthogonal to all `G_K`-invariant
`y ∈ B[ℓⁿ]` is `G_K`-invariant. Over a strictly henselian base, `I = G_K`.

* **Rating: consequence, not printed form.** It is SGA 7 IX Thm 2.4 (orthogonality) combined with:
  * the rank formulas for `T_f` of `A` and of its dual (step 1, and `a' = a`, `t' = t`);
  * the saturation argument of step 3;
  * the passage to finite level (`T'_f` is a direct summand of `T'`, so `x ⊥ B[ℓⁿ]^I` lifts into
    `(T'_f)^⊥ + ℓⁿT`);
  * the comparison of Mumford's `ē_n` with SGA 7's biextension pairing (up to sign, which does not matter).

  If the print of Prop. 3.5 contains an equivalent clause "`(T'_f)^⊥ ⊆ T_f`" (UNVERIFIED, recalled without
  network), a `T_ℓ`-level form of this leaf would be printed form; the finite-level form here would still be a
  consequence.
* Truth: true as stated (STANDARD content), in every characteristic and for imperfect residue fields. The
  argument only uses ranks, and these are geometric: `N⁰_k[ℓⁿ]` is étale, so its points over the separably closed
  `k` and over `κ̄` agree.
* Not vacuous: `e` is pinned to Mumford's pairing. `weilPairingMumford` asserts that a perfect, Galois-equivariant
  pairing with those values exists.

## 5. Consumers and narrowing (VERIFIED: read)

The field's one use is `UnipotentForward.semistableUnipotent_of_forwardGeom` (TailZ33), which gives
`ReductSplit.SemistableUnipotent`. That feeds `GapNeron.raynaudCriterion_leavesNF` (TailZ26), which gives r6 at
number fields (`RaynaudCriterionNF`). r6 is used in:

* TailH, `raynaudPlace_rational`, `raynaudPlace_of_R6`, `tateWildK_of_R6`, `localGlue_*`: `dim A = 2`, `σ` wild,
  after a base change to `K(A[m])`;
* `HDecomp/A6` `goodReduction_of_QM_rational3`, through TailF `qmModelG3_of` and `LeafQM.AV.QML3.goodReduction`:
  QM abelian surfaces with `A[3]` rational, `(σ - 1)² = 0` on `A[3^k]`, then the quaternion algebra forces a
  trivial action;
* TailI `linkedTateLocal_of_leaves3`.

All are at number fields. After strict henselization, `K` has characteristic 0 and its residue field is
algebraically closed. That narrowing removes the field's reading risk (`k(s)` versus `κ̄`; compare
`SGA7_IX_3_3_SHcp`). It does not make the statement provable: the unipotence of a general `σ`, or of a wild `σ`, on
a semistable abelian surface still needs steps 1–3. A route through potential good reduction of QM surfaces would
need its own published leaf, which is as deep. **No narrowing is proposed.**

## 6. Deliverables and checks

* `ZInQKernel/Contrib/OneProof/SGA7IX35Orth.lean`: the theorem `SGA7Orth.sga7_IX_3_5_ForwardGeom_of_orth`, the
  leaf `SGA7Orth.GrothendieckOrthogonalitySS`, and the glue `exists_isPrimitiveRoot_O`,
  `gal_fixes_rootsOfUnity`, `galMu_eq_self` and `unipSq_tors`. It imports `ZInQKernel.OneProof.H.TailZ24` and
  `ZInQKernel.Contrib.OneProof.UnipotentForward`, not Main.
* `#discharges` output: `scratch/sga7-35-proof/discharges.txt` (§7).
* `scratch/sga7-35-proof/autofold.json`: the spec. It uses `{l}` for the three added-bundle leaves. Dry run: §7.
* `scratch/sga7-35-proof/Orth.lean` (development copy), `Statements.lean` (`rfl` check), `log.md`.

## 7. Check outputs

(filled in from the runs below)
