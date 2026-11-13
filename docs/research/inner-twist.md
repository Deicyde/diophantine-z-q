# inner-twist: `InnerTwistCount` and `UnramifiedConjugates` are proved

Task inner-twist, 2026-11-13. Base f90cf864 (`wip/integrate-w38b`). Lean: `scratch/inner-twist/`
(`InnerTwist.lean`, `UnramConj.lean`, `FibreCoverIT.lean`). Compiler outputs: `run_*.txt`. Results
log: `scratch/inner-twist/log.md`. No file under `ZInQKernel/`, under `blueprint/`, or in another
task's directory was edited. This is model work only; no human has reviewed it.

## 1. Result

Both glue Props that fibre-cover left open for this task are now **proved in Lean**. The proofs
need no leaf, no new glue Prop, and no change of statement.

The checks below were run with Lean 4.35.0 and Mathlib v4.35.0. All of them are VERIFIED (compiled).
Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

| Prop (verbatim from `scratch/fibre-cover/FibreCover.lean`) | theorem | file | depends on |
|---|---|---|---|
| `G0ModField.InnerTwistCount` | `G0ModField.innerTwistCount` | `InnerTwist.lean` | aut-o-finite's `Exact.autO_mod_inner_exact` (kernel Skolem–Noether, Mathlib) |
| `G0ModField.UnramifiedConjugates` | `G0ModField.unramifiedConjugates` | `UnramConj.lean` | Mathlib only |

**Composite.** `FibreCoverIT.lean` puts aut-o-finite's file, fibre-cover's file and both proofs into
one file, and proves two composites:

```lean
theorem fibreCoverExists_of_propTS' (Y₀ π₀) (t5 : PkgI2.TorsionStructure.{0})
    (hpin : CurvePinned Y₀ π₀) (hTS : PropTS Y₀ π₀) : FibreCoverExists
theorem fibreCoverExists_of_propTSAll' (t5 : PkgI2.TorsionStructure.{0}) (hTS : PropTSAll) :
    FibreCoverExists
```

So G2 (`FibreCoverExists`) now rests on three things:
- the bundle leaf T5;
- Prop. TS on the genuine cover;
- the pin `CurvePinned` (or `PropTSAll` in its place).

`InnerTwistCount` and `UnramifiedConjugates` are no longer inputs.

**Sharpness (extra).** `innerTwistCount_sharp`: every `W` with the covering property of
`InnerTwistCount` has at least 4 elements. So the bound `4` in Glazer's `4·81 = 324` is exact for
this order.

**Finding: fibre-cover's file does not compile on this base.** On f90cf864,
`scratch/fibre-cover/FibreCover.lean` does not compile as is. The cause is pin-apply, which added
two conjuncts to `R1fpProps` (`R1famProps`, `R1univProps`; `ZInQKernel/HDecomp/QM/Leaves.lean`
L74-79). As a result, `rationalFibre_of_le`'s pattern `obtain ⟨-, -, -, hnat⟩ := h1` binds a
conjunction.
- The fix is proof-only: `obtain ⟨-, -, -, hnat, -⟩ := h1`.
- A difflib check shows that this line is the only difference between `FibreCoverIT.lean` and
  fibre-cover's body (VERIFIED).
- Whoever integrates fibre-cover needs this one-line fix.

## 2. `InnerTwistCount`

The statement: there is a `W` with `|W| ≤ 4` such that every `α ∈ Aut(𝒪)` has the form
`α(a) = w(u a u⁻¹)` for some `w ∈ W` and `u ∈ 𝒪^×`. Here `𝒪 = LeafQM.O`, the kernel's maximal
order of `(2, −3)_ℚ`.

aut-o-finite proved the form `α = Ad v ∘ t_k`, where `t_k` is conjugation by `1, i, j, ij`
(`Exact.autO_mod_inner_exact`). The identity `Ad v ∘ t = t ∘ Ad(t⁻¹(v))` (`ad_comp_eq_comp_ad`)
turns this into the form `w ∘ Ad u` that `InnerTwistCount` asks for, with
`W = {t_0, …, t_3}`.

For sharpness: if `W` covers every `α`, then each representative `t_k = w_k ∘ Ad u_k` equals
`Ad(w_k(u_k)) ∘ w_k`. So `k ↦ w_k` is injective, since the four classes are distinct. Hence
`|W| ≥ 4`.

**Source check.** `InnerTwist.lean` is aut-o-finite's file, unchanged, plus §IT. A script checked
that §IT contains the 748-character block of FibreCover.lean (docstring and definition) verbatim
(VERIFIED).

## 3. `UnramifiedConjugates`

The statement: for `α ∈ ℚ̄` and `p : ℕ`, if `ℚ(α)` is unramified at `p`, then so is the splitting
field `L` of `minpoly α`. "Unramified at `p`" is glue-descent's `UnramifiedAt`: every prime of
`𝓞` containing `p` has ramification index 1 over `ℤ`.

Proof (STANDARD mathematics, now compiled). Let `G = Gal(L/ℚ)`, let `Q ∋ p` be a prime of `𝓞 L`,
and let `I = I(Q) ≤ G` be its inertia group.

1. **`inertia_le_fixing` (abstract number fields `K → L`).** Let `H ≤ G` be the fixing subgroup of
   the image of `𝓞 K`.
   - Mathlib's `IsGaloisGroup.of_isScalarTower` makes `H` a Galois group of `𝓞 L / 𝓞 K`.
   - Mathlib's `card_inertia_eq_ramificationIdxIn` gives `#(I ∩ H) = e(Q | Q∩𝓞K)` (applied to `H`)
     and `#I = e(Q | p)` (applied to `G`).
   - `ramificationIdx_tower` gives `e(Q | p) = e(Q∩𝓞K | p) · e(Q | Q∩𝓞K)`, and the first factor
     is 1 by hypothesis.
   - So `#(I ∩ H) = #I`, hence `I ≤ H`.
   - The separable-residue-field instance over `𝓞 K` comes from the one over `ℤ` by
     `HasSeparableResidueFieldsAt.tower_top`.
2. **`inertia_fixes_field`.** `I` fixes `K = Frac(𝓞 K)`, by `IsFractionRing.div_surjective`.
3. **`conj_mem_inertia`.** `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹Q)`, and `σ⁻¹Q` contains `p`. So `I(Q)` fixes every
   `σ(α)`, which runs over all roots of `minpoly α` (`Normal.minpoly_eq_iff_mem_orbit`).
4. Hence `I(Q)` fixes `L`, so `I(Q) = 1` and `e(Q | p) = #I(Q) = 1`. This last step follows
   unram-tate's `UnramifiedSup`.

The proof is uniform in `p : ℕ`. For `p = 0` the hypothesis says that every prime of `𝓞 ℚ(α)` is
unramified, and the statement remains true.

**Source check.**
- A script checked the 708-character block (VERIFIED).
- An `example … := rfl` in `UnramConj.lean` checks that the Prop unfolds to the statement over
  `AlgebraicClosure ℚ` and `GlueDescent.B2Q.UnramifiedAt` (VERIFIED).

## 4. Status of the statements

- Neither Prop is false, vacuous or inert.
- `InnerTwistCount` is a concrete statement about the kernel order, and it is sharp.
- `UnramifiedConjugates` is the textbook fact (Neukirch, *Algebraic Number Theory* I §9; UNVERIFIED
  locator) over genuine Mathlib definitions.
- Both are GLUE and are now proved; neither needs to stay a leaf.

## 5. What remains for G2 (unchanged by this task)

- `PropTS` on the genuine `(Y₃, π)`: Beckmann's theorem, or T1-T2 with R1(d).
- `CurvePinned` (qm-pin), or `PropTSAll`.
- The leaf T5 (`TextbookLeaves.t5`).

**Integration.** Append §2 of `FibreCoverIT.lean` after FibreCover's body, with the one-line
`rationalFibre_of_le` fix. Under FibreCover's `open MonObj`, write `_root_.one_mul`, as already done
in the file. `innerTwistCount` needs aut-o-finite's §7-§9, which import only
`HDecomp.QM.Structures` and `HDecomp.Textbook.SkolemNoether`. `unramifiedConjugates` needs only
`HDecomp.Descent.B2Glue`, which provides `UnramifiedAt`.
