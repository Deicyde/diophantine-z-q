# gt-rigidity: `MumfordRigidityCore` reduced to *GIT* 6.14 (existence only) and `𝒪_S ≅ p_*𝒪_X`; Cor. 6.4 proved

Task gt-rigidity, 2026-11-14/15. Base a454ad64 (leaf-fold16). Lean: `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean`
(the contribution, 545 lines, imports only `ZInQKernel.OneProof.H.TailZ16`) and `scratch/gt-rigidity/`. Results
log: `scratch/gt-rigidity/log.md`. No other file under `ZInQKernel/`, `blueprint/`, or another task's notes or
scratch was edited. Model work, no human review.

Marks: **VERIFIED** (compiled, computed, or read in a file), **STANDARD** (published, with a reference),
**SPECULATIVE** (a judgement), **UNVERIFIED** (a theorem number recalled without a source; there is no network,
and neither *GIT* nor EGA is in the repository).

## 1. Main result

**`LeafQM.AV.R1UnivRigid.MumfordRigidityCore` is proved in two ways. Both compile with the standard axioms only
(VERIFIED).** In both, clause (a), *GIT* Cor. 6.4 ("every `S`-endomorphism fixing `e` is a homomorphism"), is now
a Lean proof.

```
theorem ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_pushforward
    (hG : MumfordGroupLaw) (hP : PushforwardStructureSheaf) : MumfordRigidityCore   -- recommended
theorem ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
    (hG : MumfordGroupLaw) (hR : RigidityLemma) : MumfordRigidityCore
```

`#discharges` (`scratch/gt-rigidity/Discharges.lean` imports `Main`, `Discharges` and the contribution, after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordRigidity`;
the full output is in `scratch/gt-rigidity/discharges-output.txt`), VERIFIED:

```
DISCHARGES [OpenResearchLeaves16.mumfordRigidityCore] by ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
  still assumes: [ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, ZInQ.Contrib.MumfordRigidity.RigidityLemma]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.mumfordRigidityCore] by ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_pushforward
  still assumes: [ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, ZInQ.Contrib.MumfordRigidity.PushforwardStructureSheaf]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 521 theorems checked, 2 discharge one
```

**Recommendation for the fold:** use `mumfordRigidityCore_of_pushforward`, which replaces the leaf
`mumfordRigidityCore` with two leaves:
* `MumfordGroupLaw`, the existence half of the old leaf, verbatim;
* `PushforwardStructureSheaf`, a textbook theorem (cohomology and base change in degree 0) with uses well
  beyond abelian schemes.

All the *GIT*-specific reasoning (the rigidity lemma's local half, and Cor. 6.4) is now Lean. The strict LEAF
count rises by one and no GLUE is added.

## 2. The leaves (stated in the contribution file, over Mathlib's definitions)

* **`MumfordGroupLaw`** (LEAF). *GIT* Thm. 6.14, number UNVERIFIED.
  * The hypotheses of `MumfordRigidityCore` verbatim: `S` locally noetherian; `F → S` proper, smooth and
    geometrically connected; a section `e`; every field fibre a `PkgI3.AbVar` with origin `e(s)`.
  * Conclusion: `∃ _ : GrpObj F, η[F].left = e`.
  * `mumfordGroupLaw_of_core : MumfordRigidityCore → MumfordGroupLaw` compiles, so it is strictly weaker than
    the old leaf.
  * Form: as r1univ-rigid explained, Thm. 6.14 on each connected component (open, since `S` is locally
    noetherian), glued; every fibre is assumed to be an abelian variety.
  * Out of reach in Lean 4.35 (SPECULATIVE): Grothendieck's proof deforms the group law over Artinian
    thickenings, then algebraizes (Grothendieck existence). None of this is in Mathlib.
* **`PushforwardStructureSheaf`** (LEAF). Statement: for `p : X → S` proper, smooth and geometrically
  connected over a locally noetherian `S`, `p.app U : Γ(S, U) → Γ(X, p⁻¹U)` is bijective for every open `U`.
  That is, `𝒪_S → p_*𝒪_X` is an isomorphism.
  * Sources, numbers UNVERIFIED: EGA III₂ (7.8.6); Stacks Project Tag 0E0L (proper, flat, finite presentation,
    geometrically connected and geometrically reduced fibres); Mumford, *Abelian varieties* §5 (cohomology and
    base change).
  * Form: a consequence. Smooth gives flat, finite presentation (with proper), and geometrically reduced
    fibres. With proper and geometrically connected, `H⁰(X_s, 𝒪) = k(s)` (Stacks 0BUG, UNVERIFIED tag).
  * Edge cases: `U = ∅` holds (both rings are zero); `X = ∅` cannot occur over a non-empty `S` (Mathlib's
    `GeometricallyConnected` implies surjective).
* **`RigidityLemma`** (LEAF, first route only). *GIT* Prop. 6.1, number UNVERIFIED.
  * Setup: `S` connected and locally noetherian; `p : X → S` proper, smooth, geometrically connected;
    `q : Y → S` separated and locally of finite type; `f : X → Y` over `S`.
  * Statement: if `f(X_s)` is a point for one `s`, then `f = p ≫ σ` for a section `σ`.
  * Form: a consequence of the printed statement (`p` proper and flat with `H⁰(X_s, 𝒪) = k(s)`): the
    hypotheses on `Y` and on `S` are extra.

None of these is vacuous or a disguised form of the conclusion. The last two say nothing about groups. All
are stated over Mathlib's `Scheme`, `IsProper`, `Smooth`, `GeometricallyConnected`, `IsSeparated`, `GrpObj`,
and the kernel's `PkgI3.AbVar` / `IsAbVarFibre`.

## 3. The proofs (all VERIFIED: compiled, standard axioms)

Cor. 6.4 is proved by Mumford's argument. For `f : F → F` with `f ∘ e = e`, take the defect

`d = (μ ≫ f) * ((fst ≫ f) * (snd ≫ f))⁻¹ : F ⊗ F ⟶ F`, i.e. `d(x, y) = f(xy) · (f(x) f(y))⁻¹`,

in the group `Hom(F ⊗ F, F)`. View `F ⊗ F = F ×_S F` as a family over `F` by `pr₂`; this is a base change of
`F → S`, so it is proper, smooth and geometrically connected, and `F` is locally noetherian. It suffices to show
`(d, pr₂) = pr₂ ≫ (x ↦ (1, x)) ≫ (d, pr₂)`; then `d = 1` (`defect_eq_one`, `defect_eq_one_of_pushforward`), and
`d = 1` is the `mul_hom` field of `IsMonHom f`.

**Second route** (`PushforwardStructureSheaf`):
* `eq_of_pushforward`, local rigidity: if `f'` is a map over `p` with a section `j`, and `f'(X_t)` is a point
  for **every** `t`, then `f' = p ≫ j ≫ f'`.
  * Near `x`, choose an affine `V ∋ f'(X_{p x})`, and an affine `U ∋ p x` with `p⁻¹U ⊆ f'⁻¹V`; it exists
    because `p` is a closed map.
  * The two maps `p⁻¹U → V` induce the same ring map `Γ(V) → Γ(p⁻¹U)` (`ext_of_isAffine`, `resLE_app_top`,
    `appLE_comp_appLE`). The reason: `p^#` is bijective (the leaf) and `j^# ∘ p^# = 1`, so `p^# ∘ j^# = 1`.
  * The pieces glue by `Scheme.hom_ext_of_forall`.
* `fibre_point_of_field`: `(d, pr₂)` is constant on every fibre `X_y`, `y ∈ F`.
  * Let `K = κ(y)`, `F_K = (Over.pullback s̄).obj F` with Mathlib's `Functor.grpObjObj`, and `f_K` the base
    change of `f`.
  * `f_K` fixes `1`, and `F_K` is proper and geometrically integral, so `f_K` is a homomorphism by the
    kernel's `MulRigidity.isMonHom_of_geometricallyIntegral`, and `d_K = 1`.
  * `μ_P ≫ P.map d = d_K` (`Functor.map_mul`, `Functor.map_inv'`, `Functor.Monoidal.μ_fst/μ_snd`).
  * The map `ψ : F_K → F ×_S F`, `x ↦ (x, ȳ)`, is the base change of `ȳ` along `pr₂` (`IsPullback.of_right`).
    So every point of `X_y` is `ψ(z)`, and `(d, pr₂) ∘ ψ` factors through the one-point `Spec K`.
  * Geometric integrality of `F_K` comes from the abelian-variety fibre hypothesis
    (`geometricallyIntegral_of_isAbVarFibre`).
* `isMonHom_of_pushforward`, then `mumfordRigidityCore_of_pushforward`.

**First route** (`RigidityLemma`):
* `isOpen_connectedComponent_of_noetherianSpace` and `isOpen_connectedComponent_of_isLocallyNoetherian`:
  connected components are open.
* `eq_of_rigidity`: the rigidity lemma on each open connected component of the base, via `morphismRestrict`,
  `resLE` and `Scheme.hom_ext_of_forall`.
* `isPullback_jr`: `x ↦ (x, 1)` is the base change of `η` along `pr₂`.
* `fibre_value`: `(d, pr₂)` sends the fibre over `η(s)` to one point.
* `eta_mem_connectedComponent`: each component of `F` contains such a point, because the fibres of `F → S`
  are connected.
* `isMonHom_of_rigidity`, then `mumfordRigidityCore_of_printed`.

## 4. What remains

* `MumfordGroupLaw`: a published leaf (*GIT* 6.14); not provable from Mathlib today.
* `PushforwardStructureSheaf`: a published leaf (EGA III 7.8.6 / Stacks 0E0L). Mathlib 4.35 has no cohomology
  and base change for coherent sheaves, so this is a leaf for the crowdsourcing list (SPECULATIVE: it is a
  natural Mathlib target, needed for any relative rigidity statement).
* `RigidityLemma` is needed only by the first route. Its local half follows from `PushforwardStructureSheaf`
  (`eq_of_pushforward`, compiled). The global half (`S` connected, one fibre) is not proved.
* Not done: a form of `MumfordGroupLaw` with the printed hypotheses (`S` connected, one fibre an abelian
  variety). Deriving the present form from it would need gluing `GrpObj` structures over the connected
  components in Lean.
