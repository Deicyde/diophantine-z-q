# t5-torsion: T5 reduced to a count; T26 follows from T5; every use of T5 in the H proof follows from T35

Status: research note (task t5-torsion, 2026-11-13). The Lean is in `scratch/t5-torsion/`, the results
log is `scratch/t5-torsion/log.md`. No file under `ZInQKernel/` or `blueprint/` was edited, and no
other task's notes or scratch files were edited.

Marks: **VERIFIED** = compiled with `lake env lean`, or read in the repository or Mathlib. Every
compiled theorem below has no `sorry` and no `axiom`, and `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a locator recalled from memory (no network).

## 0. Main results

All items are VERIFIED. The single file `scratch/t5-torsion/T5Full.lean` contains all of them; it
compiles in about 10 s once the imported `ZInQKernel` modules are built. `T5Torsion.lean` (parts
1–4b) and `Tate.lean` (part 8) also compile on their own.

1. **T5 holds over every field that embeds in `ℂ`, from T35 alone.** T35 is
   `ZInQ.LeafPush2.UniformizationExists`, already `TextbookLeaves.t35`. The proof also uses
   Mathlib and the proved `ZInQ.Contrib.AbVarBC.mulIsogeny`.
   ```lean
   theorem T5Torsion.torsionStructureC_of_uniformization
       (hU : ZInQ.LeafPush2.UniformizationExists) : T5Torsion.TorsionStructureC
   theorem T5Torsion.torsionStructureAt (hU) {K} (σ : K →+* ℂ) (A) (g n) (hg) (hn) (hnK) : …
   ```
   `TorsionStructureC` is `PkgI2.TorsionStructure` with the hypothesis `(n : K) ≠ 0` replaced by
   `σ : K →+* ℂ` (hence characteristic 0). `torsionStructureAt` has exactly the shape of the
   kernel's use `hT K A g n hdim hn hnK`, plus `σ`.

2. **Every consumer of T5 in the H proof follows from T35.** Each one applies T5 only at `ℚ̄`, at
   a subfield of `ℚ̄`, or at a number field (§3):
   ```lean
   theorem LeafQM.AV.Pin.mobiusGlue_of_T35 (hU : ZInQ.LeafPush2.UniformizationExists) :
       LeafQM.AV.Pin.MobiusGlue                       -- closes GluePiecesPin.mobius
   theorem LeafQM.AV.QML3.goodReductionC (hNOS) (hRay) (hU) (τ : K →+* ℂ) (P : QML3 K) (Ov)
       [IsDiscreteValuationRing Ov] (h3 : IsUnit (3 : Ov)) : PkgI2.HasGoodReduction (toGrp P.A) Ov
   theorem GlueA6Alg.goodReduction_of_QM_rational3_C, …_C'   -- glue A6
   theorem T5Torsion.AssemblyCopies.torsionBound3_of_T35 (hU) : TorsionBound3
   theorem T5Torsion.AssemblyCopies.torsionCountPts_of_T35 (hU) : TorsionCountPts
   ```
   `TorsionBound3` and `TorsionCountPts` are verbatim copies of the assembly's Props (§3). After the
   rewiring in §3, the field `t5` of `TextbookLeaves` is used only to prove T26 (item 4).

3. **Full T5 (all fields, all characteristics) from a counting leaf.**
   ```lean
   theorem T5Torsion.torsionStructure_of_torsionCard (h : TorsionCard.{u}) :
       PkgI2.TorsionStructure.{u}
   theorem T5Torsion.torsionStructure_of_uniformization_of_nonC
       (hU : ZInQ.LeafPush2.UniformizationExists) (hN : TorsionCardNonC) :
       PkgI2.TorsionStructure.{0}
   ```
   - `TorsionCard`: `#A(K̄)[n] = n^{2g}` whenever `(n : K) ≠ 0`.
   - The group structure `A(K̄)[n] ≅ (ℤ/n)^{2g}` follows by pure algebra; that is proved here.
   - `TorsionCardNonC`: `TorsionCard` on the fields with no ring map to `ℂ`. These are the fields
     of positive characteristic, and those of characteristic 0 with transcendence degree above the
     continuum (STANDARD: a field of characteristic 0 embeds in `ℂ` iff its transcendence degree
     over `ℚ` is at most `𝔠`).

4. **T26 (`PkgI3.TateModuleFree`) is glue given T5.** T26 says `T_ℓ A` is free of rank `2 dim A`
   over `ℤ_ℓ`.
   ```lean
   theorem T5Torsion.TateFree.tate_linearEquiv (r : ℕ)
       (hcard : ∀ n, Nat.card (tb ℓ M n) = ℓ ^ (n * r)) :
       Nonempty (PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ]))
   theorem T5Torsion.TateFree.tateModuleFree_of_torsionStructure (hT : PkgI2.TorsionStructure.{0}) :
       PkgI3.TateModuleFree
   theorem T5Torsion.tateModuleFreeC_of_uniformization (hU) : TateModuleFreeC  -- k ↪ ℂ, T35 only
   theorem T5Torsion.tateModuleFree_of_uniformization_of_nonC (hU) (hN : TorsionCardNonC) :
       PkgI3.TateModuleFree
   ```

5. **The `GluePieces4` leaf `divisiblePoints` (#40, `WeilPairing.DivisiblePoints`) is not needed.**
   Its only use on the main chain is G0Assemble3's `tatePairingZl_of_leaves` (:49582, via
   `detTate_of_leaves`). There it supplies the surjectivity of `T_ℓ A → A(K̄)[ℓᵏ]` through
   `tate_surj (hD K A ℓ _)`, for `K` a number field. The same surjectivity follows from the torsion
   counts (part 11):
   ```lean
   theorem T5Torsion.TateFree.tate_surj_of_torsionStructure (hT : PkgI2.TorsionStructure.{0})
       (K) (A : PkgI3.AbVar K) (ℓ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
       ∀ m (t : Additive (A.Pt (AlgebraicClosure K))), ℓ ^ m • t = 0 → ∃ y : A.T ℓ, y.1 m = t
   theorem T5Torsion.tate_surj_numberField (hU : ZInQ.LeafPush2.UniformizationExists)
       (K) [NumberField K] (A) (ℓ) [Fact ℓ.Prime] : (same conclusion)
   ```
   Rewiring: in `tatePairingZl_of_leaves`, replace
   `(fun k t ht => WeilPairing.tate_surj (hD K A ℓ _) k t ht)` by
   `T5Torsion.tate_surj_numberField t.t35 K A ℓ`, and drop `hD` from `detTate_of_leaves`.

**Effect on the list of literature theorems** (SPECULATIVE: these are proposals, and the
integration is not done here):
- **(a) No rewiring.** Set `t26 := tateModuleFree_of_torsionStructure t.t5`. T26 stops being a
  leaf, so the list has one leaf fewer.
- **(b) No rewiring.** Set `t5 := torsionStructure_of_uniformization_of_nonC t.t35 nC` and
  `t26 := tateModuleFree_of_uniformization_of_nonC t.t35 nC`.
  - T5 and T26 are replaced by the single leaf `TorsionCardNonC`, which the H proof never uses in
    substance. The list again has one leaf fewer.
- **(d) Independently of (a)-(c): drop `GluePieces4.divisiblePoints` (item 5).** This needs one
  rewiring and adds no leaf.
- **(c) Rewiring T5's consumers (§3).** This makes the T5 count unnecessary for H. T26 is still
  needed in full generality, because its consumers apply it over general fields: for example
  `continuous_galRep_of_tateModuleFree {K}` and `tateBC_bijective_of_tateModuleFree`. So (c) only
  pays off together with (a) or (b).

## 1. What T5 demands (VERIFIED, ZInQKernel/HDecomp/Objects.lean:993, :1486)

`PkgI2.TorsionStructure.{u}` covers:
- every field `K : Type u`, of any characteristic;
- every `A : Grp (Over (Spec K))` with `[IsAbelianVariety A]` (Mathlib's proper, smooth, geometrically
  integral);
- all `g n : ℕ` with `topologicalKrullDim A.X.left = g`, `0 < n` and `(n : K) ≠ 0`.

For these it asserts an additive bijection `torsion A K̄ n ≃ (Fin (2g) → ZMod n)`. Here:
- `torsion A K̄ n = {x : Spec K̄ ⟶ A over K | x^n = 1}`;
- the group law on morphisms into a group object is Mathlib's;
- `K̄ = AlgebraicClosure K`.

`ObjBridge.TorsionStructure` is the `Type 0` instance (`torsionStructure_iff`, `Iff.rfl`). The bundle
field is `t5 : PkgI2.TorsionStructure.{0}`. So T5 is Mumford's full statement: positive
characteristic with `p ∤ n` is included, and there is no bound on the size of `K`. All its
consumers are in characteristic 0, at fields inside `ℚ̄`. The dimension is a natural number by
`PkgI3.AbVar.dim_finite` (Contrib/AbVarBC/Dim.lean); T26's proof uses this.

## 2. The proofs (part numbers refer to `T5Full.lean`)

**Part 1. Group theory (`GroupGlue.lean`).**
`nonempty_torsionBy_addEquiv_pi`: let `A` be an abelian group, `N ≠ 0` and `r` given. If
`#A[m] = m^r` for every `m ∣ N`, then `A[N] ≃+ (ZMod N)^r`.
- It generalizes Tau Ceti's rank-2 `nonempty_addEquiv_prod_zmod_primePow` and
  `torsion_addEquiv_prod` (vendored, Apache-2.0) to rank `r`.
- The proof splits `A[N]` into its primary parts over `N.primeFactors`.
- Each `p`-part is handled by the structure theorem `AddCommGroup.equiv_directSum_zmod_of_finite'`,
  using the counts at `p` and at `p^{v_p(N)}`.
- CRT (`ZMod.equivPi`) reassembles the parts.

**Part 2. Torsion of a uniformized group (`Torus.lean`).**
`natCard_pow_eq_one`: let `Φ : E → P` be surjective, with `Φ(z+w) = Φ z * Φ w`, and with kernel a
full `ℤ`-lattice `Λ` of a finite-dimensional real normed space `E`. Then `#{x | xⁿ = 1} = n^{dim_ℝ E}`.
- The bijection is `c ↦ Φ(∑ (c_i.val/n) b_i)` from `(ZMod n)^ι`.
- Here `b` is a `ℤ`-basis of `Λ`, and also an `ℝ`-basis of `E` (Mathlib's `Basis.ofZLatticeBasis`).

**Part 3. Torsion along `Ω → Ω₂` (`Descent.lean`).**
`natCard_torsion_eq_of_ext`: in characteristic 0, `#A(Ω)[n] = #A(Ω₂)[n]` for every `K`-embedding
`κ : Ω → Ω₂` with `Ω` algebraically closed.
- Injectivity: `Spec κ` is an epimorphism (Contrib/AbVarBC's `extPt_injective`).
- Surjectivity: `ker [n]` is finite over `K` (the proved `mulIsogeny`). So its `Ω₂`-points come
  from `Ω` (`exists_lift_of_isFinite`). The proof is adapted from AbVarBC's
  `torsionDescends_of_isFinite`.

**Part 4. Assembly.**
For `σ : K → ℂ`, extend it to `κ : K̄ → ℂ` (`IsAlgClosed.lift`) and apply part 3 with `Ω₂ = ℂ`.
- T35 at `σ` gives `Φ : ℂ^g → A(ℂ)_σ`, whose kernel is a full lattice. Part 2 then gives
  `#A(K̄)[n] = n^{2g}`, and part 1 gives the structure.
- Part 4b splits on `Nonempty (K →+* ℂ)`.

**Parts 5–7.** These are the copies of the consumers (§3).

**Part 8. T26 (`Tate.lean`).**
For an abelian group `M` with `#M[ℓⁿ] = ℓ^{nr}` for all `n`:
- Multiplication by `ℓ` maps `M[ℓ^{n+1}]` onto `M[ℓⁿ]`, by counting the image and the kernel `M[ℓ]`.
- So every element of `M[ℓ]` starts an element of `T_ℓ M`.
- Choose an `𝔽_ℓ`-basis of `M[ℓ]` (from `#M[ℓ] = ℓ^r`) and lift it to `X_1, …, X_r ∈ T_ℓ M`.
- By induction on `n`, `∑ c_i X_i(n) = 0` implies `ℓⁿ ∣ c_i`. So `c ↦ ∑ c_i X_i(n)` is injective
  on `(ℤ/ℓⁿ)^r`, and hence bijective onto `M[ℓⁿ]` by counting.
- `a ↦ ∑ a_i X_i` from `ℤ_ℓ^r` to `T_ℓ M` is injective (via `PadicInt.ext_of_toZModPow`).
- It is surjective: the level-`n` coefficients are compatible, so they define elements of `ℤ_ℓ`
  (Mathlib's `PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub`).
- T5 at `ℓⁿ` supplies the counts, with `r = 2g`.

**Part 9.** T26 corollaries.

**Part 10.** Embeddings `numberFieldToC`, `subfieldQbarToC`, and T5 at number fields and at
subfields of `ℚ̄` from T35.

**Part 11.** `T_ℓ A → A(K̄)[ℓᵏ]` is onto, from the counts (`exists_tate_lift_level`): the
successive `ℓ`-th roots of `t` stay in `A[ℓ^{k+j}]` because `ℓ : A[ℓ^{k+j+1}] → A[ℓ^{k+j}]` is onto.

## 3. The consumers of T5, and how to rewire them (VERIFIED by reading)

| use site | field `K` | n, g | replacement (compiled) |
|---|---|---|---|
| `Contrib/Mobius/Glue.lean` `level3_finite` ← `twistClassFinite_of` ← `mobiusGlue_of_curves`; assemblies `mobiusGlue_of_gp3`, `mobiusGlue_of_t5'` | `ℚ̄` (`TwistClassFinite` is over `QML3 Qbar`) | 3, 2 | `Pin.mobiusGlue_of_T35 t.t35` |
| `HDecomp/QM/Structures.lean` `Level3.onto`, `range_le`, `torsor`, `hrat` | the field of the `QML3` object | 3, 2 | `Level3.ontoC`, `range_leC`, `torsorC`, `hratC` (extra `σ : K →+* ℂ`) |
| `HDecomp/A6/A6.lean` `goodReduction_of_QM_rational3*` via `QM/Structures` `QML3.goodReduction` | G0Assemble2 `good_of_QML3` (:59730) and G0Assemble3 `qmModelG3_of` (:74743): `K : IntermediateField ℚ ℚ̄` | 3^{2k}, 2 | `QML3.goodReductionC … (qbarToC.comp K.val)` |
| G0Assemble2 `torsionBound3_of` (:56625, via `fibreCoverExists_of_propTSAll'`) | `ℚ̄` | 3, 2 | `AssemblyCopies.torsionBound3_of_T35 t.t35` |
| G0Assemble2 `torsionCountPts_of_leaf` (:59756, via `kernelFieldExists_of_split''`, `conjMapsNoCM_of`) | `L : IntermediateField ℚ ℚ̄` | n, 2 | `AssemblyCopies.torsionCountPts_of_T35 t.t35` |
| lt-local (`scratch/lt-local/LtLocal4.lean:3055`) `torsGL_of_leaf` (via `localGlue_of_descent`, `linkedTateLocal_of_tateBridge35`) | `K` a number field (`variable {K} [Field K] [NumberField K]`) | m, 2 | `T5Torsion.torsionStructure_numberField t.t35 K (toGrp A) 2 m _ hm` |

Drop-ins for the remaining shapes are `T5Torsion.torsionStructure_numberField` and
`T5Torsion.torsionStructure_subfieldQbar` (part 10). They are T5 at a number field and at a subfield
of `ℚ̄`, with the embeddings `numberFieldToC` and `subfieldQbarToC`.

`ConjTwistFromLeaves` (G0Assemble2:46560) has T5 among its hypotheses. It is a definition and is
not on the main chain.

The integrator's recipe (after the announcement), in the assembly files:
- **`mobiusGlue_of_gp3` / `mobiusGlue_of_t5'`.** Use `mobiusGlue_of_T35 t.t35`, or
  `mobiusGlue_of_curveFacts … (twistClassFinite_of_T35 t.t35)` to keep `gp`'s curve facts.
- **`fibreCoverExists_of_propTSAll`.** Replace `torsionBound3_of_t5 t5` by
  `torsionBound3_of_T35 t35`.
- **The kernel-field chain.** Replace `torsionCountPts_of_leaf hTors` by
  `torsionCountPts_of_T35 t35`.
- **`good_of_QML3` and `qmModelG3_of`.** Replace `QML3.goodReduction … hTors` by
  `QML3.goodReductionC … t35 (qbarToC.comp K.val)`.

## 4. What remains

- **`TorsionCardNonC`.** This is STANDARD: Mumford, *Abelian varieties* (1970), §4 after the
  theorem of the cube, and §6 Application 2 for `deg [n] = n^{2g}` and separability when `p ∤ n`
  (locators UNVERIFIED). The H proof never uses positive characteristic or fields larger than `ℂ`.
  An algebraic proof needs three inputs:
  1. `deg [n] = n^{2g}`, as the length of the fibre `ker [n]`;
  2. étaleness of `ker [n]` (`KerUnitOpen` is proved in characteristic 0 in Contrib/AbVarBC);
  3. the count of `K̄`-points of a finite étale `K`-scheme.

  Inputs 2 and 3 are glue, but they are substantial scheme theory. Large fields of characteristic 0
  would follow from T35 together with a Lefschetz-principle leaf: every abelian variety descends
  to a finitely generated subfield (EGA IV 8.8.2, 8.10.5, 17.7.8; UNVERIFIED).
- The rewiring of §3 and the bundle change (a)/(b) of §0 are integration work, not done here.
- Pitfalls found (in the log):
  - With `letI := AddCommGroup.zmodModule h`, instance search for `Module.finBasisOfFinrankEq` and
    `Module.natCard_eq_pow_finrank` gets stuck. The fix is to state the lemma with
    `[Module (ZMod ℓ) V]` as a binder.
  - A file-level `open … MonObj` makes `one_mul` resolve to `MonObj.one_mul`.
