# t5-torsion: the textbook leaf T5 (`PkgI2.TorsionStructure`) reduced; every use of T5 in the H proof follows from T35

Status: research note (task t5-torsion, 2026-11-13). Lean in `scratch/t5-torsion/`, results log
`scratch/t5-torsion/log.md`. No file under `ZInQKernel/` or `blueprint/` and no other task's notes or
scratch files were edited.

Marks: **VERIFIED** = compiled with `lake env lean` (no `sorry`, no `axiom`; `#print axioms` lists
only `propext`, `Classical.choice`, `Quot.sound`) or read in the repository/Mathlib.
**STANDARD** = published mathematics with a reference. **UNVERIFIED** = locator from memory (no
network).

## 0. Main results

All items are VERIFIED (compiled). The file `scratch/t5-torsion/T5Full.lean` holds them all.
`T5Torsion.lean` is the part that does not import `ZInQKernel.Contrib.Mobius`.

1. **T5 holds over every field that embeds in `ℂ`, from T35 alone.** T35 is
   `ZInQ.LeafPush2.UniformizationExists`, already `TextbookLeaves.t35`. The proof also uses
   Mathlib and the proved `ZInQ.Contrib.AbVarBC.mulIsogeny`:
   ```lean
   theorem T5Torsion.torsionStructureC_of_uniformization
       (hU : ZInQ.LeafPush2.UniformizationExists) : T5Torsion.TorsionStructureC
   ```
   `TorsionStructureC` is `PkgI2.TorsionStructure` with the hypothesis `(n : K) ≠ 0` replaced by
   a ring map `σ : K →+* ℂ` (hence characteristic 0). There is also a drop-in form
   `T5Torsion.torsionStructureAt hU σ A g n hdim hn hnK`, with the same shape as the kernel's
   `hT K A g n hdim hn hnK`.
2. **Every consumer of T5 in the H proof follows from T35.** Each one applies T5 only at `ℚ̄`, at
   a subfield of `ℚ̄`, or at a number field, and all of these embed in `ℂ`:
   ```lean
   theorem LeafQM.AV.Pin.mobiusGlue_of_T35 (hU : ZInQ.LeafPush2.UniformizationExists) :
       LeafQM.AV.Pin.MobiusGlue                                  -- GluePiecesPin.mobius
   theorem LeafQM.AV.QML3.goodReductionC (hNOS) (hRay) (hU) (τ : K →+* ℂ) (P : QML3 K) (Ov) …
       -- = QML3.goodReduction (glue A6) with T35 + τ in place of T5
   theorem GlueA6Alg.goodReduction_of_QM_rational3_C / _C'   -- A6, same
   theorem T5Torsion.AssemblyCopies.torsionBound3_of_T35 (hU) : TorsionBound3
   theorem T5Torsion.AssemblyCopies.torsionCountPts_of_T35 (hU) : TorsionCountPts
   ```
   The last two are verbatim copies of the assembly's Props `TorsionBound3` and
   `TorsionCountPts` (scratch/g0-assemble2/G0Assemble2.lean:56478, :59755), proved from T35.
   **Consequence (after rewiring, §3):** the field `t5` of `TextbookLeaves` is no longer used, so T5
   drops out of the list of literature theorems.
3. **Full T5 (all fields, all characteristics) from one counting leaf.**
   ```lean
   theorem T5Torsion.torsionStructure_of_torsionCard (h : TorsionCard.{u}) :
       PkgI2.TorsionStructure.{u}
   theorem T5Torsion.torsionStructure_of_uniformization_of_nonC
       (hU : ZInQ.LeafPush2.UniformizationExists) (hN : TorsionCardNonC) :
       PkgI2.TorsionStructure.{0}
   ```
   `TorsionCard` says `#A(K̄)[n] = n^{2g}` for `(n : K) ≠ 0`. The group structure
   `A[n] ≅ (ℤ/n)^{2g}` is pure algebra and is proved here. `TorsionCardNonC` is `TorsionCard` on
   the fields with no ring map to `ℂ`: positive characteristic, or characteristic 0 with
   transcendence degree above the continuum. Only that case still needs Mumford.

## 1. What T5 demands (VERIFIED, ZInQKernel/HDecomp/Objects.lean:993, :1486)

`PkgI2.TorsionStructure.{u}` reads: for every field `K : Type u` of any characteristic, every
`A : Grp (Over (Spec K))` with `[IsAbelianVariety A]` (Mathlib's proper, smooth, geometrically
integral), and all `g n : ℕ` with `topologicalKrullDim A.X.left = g`, `0 < n` and `(n : K) ≠ 0`,
there is an additive bijection `torsion A K̄ n ≃ (Fin (2g) → ZMod n)`. Here
`torsion A K̄ n = {x : Spec K̄ ⟶ A over K | x^n = 1}` with Mathlib's group structure on morphisms
into a group object, and `K̄ = AlgebraicClosure K`. `ObjBridge.TorsionStructure` is the `Type 0`
instance (`torsionStructure_iff`, `Iff.rfl`); the bundle field is `t5 : PkgI2.TorsionStructure.{0}`.

So T5 is the full Mumford statement: positive characteristic `p ∤ n` included, and no bound on the
size of `K`. Its consumers are all in characteristic 0, at fields embedded in `ℚ̄` (§3).

## 2. The proofs

**(a) Group theory (GroupGlue.lean, part 1).**
`T5Torsion.nonempty_torsionBy_addEquiv_pi`: for an abelian group `A`, `N ≠ 0` and `r`, if
`#A[m] = m^r` for every `m ∣ N`, then `A[N] ≃+ (ZMod N)^r`. This generalizes from rank 2 to rank `r`
Tau Ceti's `nonempty_addEquiv_prod_zmod_primePow` and `torsion_addEquiv_prod` (vendored,
Apache-2.0). The proof uses the primary decomposition over `N.primeFactors`, the structure theorem
`AddCommGroup.equiv_directSum_zmod_of_finite'` on each `p`-part with the counts at `p` and
`p^{v_p(N)}`, and CRT `ZMod.equivPi`.

**(b) Torsion of a uniformized group (Torus.lean, part 2).** `T5Torsion.natCard_pow_eq_one`:
suppose `Φ : E → P` sends `+` to `*`, is surjective, and has kernel a full `ℤ`-lattice `Λ` of a
finite-dimensional real normed space `E`. Then `#{x : P | xⁿ = 1} = n^{dim_ℝ E}`. The bijection
`(ZMod n)^ι → P[n]` is `c ↦ Φ(∑ (c_i.val/n) b_i)` for a `ℤ`-basis `b` of `Λ`, which is an `ℝ`-basis
of `E` (`Basis.ofZLatticeBasis`). Also `finrank ℝ (Fin g → ℂ) = 2g`.

**(c) Torsion along `K̄ → Ω₂` (Descent.lean, part 3).** `T5Torsion.natCard_torsion_eq_of_ext`: in
characteristic 0, `#A(Ω)[n] = #A(Ω₂)[n]` for every `K`-embedding `κ : Ω → Ω₂` with `Ω`
algebraically closed. The map is injective because `Spec κ` is an epimorphism (AbVarBC's
`extPt_injective`). It is surjective because `ker [n]` is finite over `K` (proved `mulIsogeny`), so
its `Ω₂`-points come from `Ω` (AbVarBC's `exists_lift_of_isFinite`; the proof is adapted from
`torsionDescends_of_isFinite`).

**(d) Assembly (part 4).** For `σ : K → ℂ`, extend to `κ : K̄ → ℂ` (`IsAlgClosed.lift`) and apply
(c) with `Ω₂ = ℂ`. T35 at `σ` gives `Φ : ℂ^g → A(ℂ)_σ` with a full-lattice kernel, so (b) gives
`#A(K̄)[n] = n^{2g}`, and (a) gives the structure. The case split on `Nonempty (K →+* ℂ)` gives
`torsionStructure_of_uniformization_of_nonC`.

## 3. The consumers of T5, and how to rewire them (VERIFIED by reading)

| use site | field `K` | n, g | replacement (compiled) |
|---|---|---|---|
| `Contrib/Mobius/Glue.lean` `level3_finite` ← `twistClassFinite_of` ← `mobiusGlue_of_curves` | `ℚ̄` (`TwistClassFinite` is over `QML3 Qbar`) | 3, 2 | `Pin.mobiusGlue_of_T35 t.t35` |
| `HDecomp/QM/Structures.lean` `Level3.onto`, `range_le`, `torsor`, `hrat` | the field of the `QML3` object | 3, 2 | `Level3.ontoC`, `range_leC`, `torsorC`, `hratC` (extra `σ : K →+* ℂ`) |
| `HDecomp/A6/A6.lean` `goodReduction_of_QM_rational3*`, `QM/Structures` `QML3.goodReduction` | in the assembly (`good_of_QML3`, G0Assemble2:59730) `K : IntermediateField ℚ ℚ̄`, finite over ℚ | 3^{2k}, 2 | `GlueA6Alg.goodReduction_of_QM_rational3_C'`, `QML3.goodReductionC … (qbarToC.comp K.val)` |
| G0Assemble2 `torsionBound3_of` (via `fibreCoverExists_of_propTSAll'`) | `ℚ̄` | 3, 2 | `AssemblyCopies.torsionBound3_of_T35 t.t35` |
| G0Assemble2 `torsionCountPts_of_leaf` (via `kernelFieldExists_of_split''`, `conjMapsNoCM_of`) | `L : IntermediateField ℚ ℚ̄` | n, 2 | `AssemblyCopies.torsionCountPts_of_T35 t.t35` |

The integrator's recipe (after the announcement), in `scratch/g0-assemble2/G0Assemble2.lean`:
* `mobiusGlue_of_gp3`: replace `t.t5` by `mobiusGlue_of_T35 t.t35` (`curveFacts` there come from
  `gp`; `mobiusGlue_of_curveFacts … (twistClassFinite_of_T35 t.t35)` is the exact analogue).
* `fibreCoverExists_of_propTSAll`: replace `torsionBound3_of_t5 t5` by `torsionBound3_of_T35 t35`.
* the kernel-field chain: replace `torsionCountPts_of_leaf hTors` by `torsionCountPts_of_T35 t35`,
  and `QML3.goodReduction … hTors` in `good_of_QML3` by `QML3.goodReductionC … t35 τ` with
  `τ = qbarToC.comp K.val`.

After this rewiring, `TextbookLeaves.t5` is unused and can be deleted. The full statement
`PkgI2.TorsionStructure` stays available as `torsionStructure_of_torsionCard` for anyone who needs
it in positive characteristic.

## 4. What remains

* **Positive characteristic and very large fields (`TorsionCardNonC`).** This is STANDARD: Mumford,
  *Abelian varieties* (1970), §4 after the theorem of the cube, and §6 Application 2 for
  `deg [n] = n^{2g}` and separability for `p ∤ n` (locators UNVERIFIED). The H proof never uses it.
  An algebraic proof would take
  1. the degree `deg [n] = n^{2g}` as the fibre length of `ker [n]`;
  2. étaleness of `ker [n]` (`KerUnitOpen` is proved in characteristic 0 in Contrib/AbVarBC);
  3. the count of `K̄`-points of a finite étale `K`-scheme.

  The second and third steps are glue, but substantial scheme theory.
* The rewiring of §3 is integration work and is not done here: ZInQKernel and G0Assemble2 are not
  edited.
