# charpoly-port: `charPolyIndepOfEllAlgClosed` cannot be closed by porting Anthropic's degree polynomial alone

Findings note, 2026-11-17. Base read: fork `wip/leaf-fold33b` at `beafc63dc` (PR #59), `wip/deg-det` at
`ecf7da39c`, `anthropics/fermats-last-theorem` at `6e837e75355538c7f80bab5b956861e86c4eacc2`.

**Nothing here was built.** Every claim below comes from reading statements, definitions and import graphs.
READ = read in the source; COUNTED = computed from the module-level import graph; UNCHECKED = not verified.

## 1. Verdict

The route "port Anthropic's degree-polynomial theorem, then apply deg-det's reduction" does **not** prove
`ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` as stated. Two gaps remain after the port (§3, §4). The port
itself is small (§2). What the route can give is in §5.

## 2. What is cheap: the degree polynomial

deg-det's one missing geometric input is `DegDet.DegHomogPoly`
(`ZInQKernel/Contrib/OneProof/DegEqDetTate/Reduction.lean` on `wip/deg-det`): over an algebraically closed
field, `x ↦ deg(∑ xᵢ eᵢ)` is a homogeneous rational polynomial of degree `2g`.

Anthropic's FLT library has the same shape (READ):

```lean
theorem GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] {ι : Type*} [Fintype ι] (α : ι → SchemeHomOver f f)
    (hα : …each α i is a homomorphism…) :
    ∃ P : MvPolynomial ι ℚ, P.IsHomogeneous (2 * g) ∧
      ∀ n : ι → ℤ, ((L.endDegree (∏ i, α i ^ n i) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P
```

File `Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle.lean`,
Apache-2.0, Lean 4.33.1.

- Its import closure is 1,576 modules, 261,738 lines (COUNTED).
- 1,516 of those modules are already vendored under `ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/`
  on the PR #59 branch; the torsion theorem behind `mumfordTorsionAlgClosed_proof` has a 1,518-module closure
  and shares 1,516 of them (COUNTED).
- **New to vendor: about 60 modules, 10,367 lines** (COUNTED). They still need the Lean 4.33.1 → 4.35.0 port
  and the relocation rules of `CloudB3W16Torsion/NOTICE.md` (UNCHECKED: no module was ported).
- No `sorry` or `axiom` in code anywhere in the closure (COUNTED by text scan, comments stripped).

The AxiomMath/Stacks alternative (`Stacks.Groupoids.charpoly_tateModuleMap`, Mumford §19 Thm 4 itself) has a
10,874-module, 3.30M-line closure, of which the project vendors 281 modules. It also gives the polynomial over
`ℚ`, with no integer version in that directory (READ). Not recommended.

## 3. Gap 1: the reduction needs `homFreeFiniteAlgClosed`, which is proved only over fields mapping to `ℂ`

deg-det's theorem (READ, `docs/research/deg-det.md` on `wip/deg-det`):

```lean
theorem ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford
    (hP : DegDet.DegHomogPoly) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
```

- `hM` is available: `mumfordTorsionAlgClosed_proof` (`Contrib/OneProof/MumfordTorsionAlgClosed.lean`).
- `hH` is **not** available in full. `homFreeFiniteAlgClosed` left the open list through homfree-noemb's reroute,
  not through a proof. On the PR #59 branch (READ, `Contrib/OneProof/HomFreeFiniteAlgClosed.lean`):
  - `homFreeFiniteAlgClosedC` proves it for algebraically closed `k` with a ring hom `k →+* ℂ`, from
    `uniformizationLeafAll` and `mumfordTorsionAlgClosed` (both proved);
  - `homFreeFiniteAlgClosed_of_noEmb` gives the full statement only from `HomFreeFiniteAlgClosedNoEmb`
    (characteristic `p`, and characteristic `0` of large transcendence degree), which is unproved.
- The use is essential, not incidental. deg-det reads `deg` on `ℤ[X]/(R)` for a monic `R ∈ ℤ[X]` with
  `R(φ) = 0`, and that `R` comes from `Module.Finite ℤ (End A)` (deg-det.md §3).

One part needs no finiteness: in characteristic `0`, integrality of the coefficients follows from the charpoly
lying in `ℤ_ℓ[X]` for every prime `ℓ`. That does not remove the use above, and it does not cover
characteristic `p`.

## 4. Gap 2: the two degrees are different definitions

- Project (READ, `Contrib/OneProof/CharPolyIndepOfEllAlgClosed.lean` on `wip/deg-det`):
  `CharPolyEll.degEnd ψ` is `[K(A) : ψ^*K(A)]`, the `finrank` of stalks at the generic point, for `ψ` finite
  and surjective, and `0` otherwise.
- Anthropic (READ, `Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean`):
  `L.endDegree β` is the rank of the kernel group scheme, `(G.endKerStr β).finrank (closedPoint K)`, when the
  kernel is finite, and `0` otherwise.

They agree for isogenies, but that is a theorem. A partial bridge is already vendored on the PR #59 branch
(READ):

```lean
theorem GoodReductionJacobian.RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
    … (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧ ∀ x : A, L.endDegree β = Scheme.Hom.finrank β.1 x
```

What is still owed for `degEnd ψ = L.endDegree ψ` (UNCHECKED, my reading of what is missing):

1. an isogeny of abelian varieties is flat (finite surjective between regular schemes of equal dimension);
2. `Scheme.Hom.finrank β x` at the generic point equals the `finrank` of the stalk map that `degEnd` uses;
3. finite kernel implies finite and surjective, so the two `0` cases coincide.

deg-det's own lemmas are stated for `degEnd` (multiplicativity by the tower law, `#ker ψ ∣ deg ψ` by Artin's
theorem), so swapping the degree instead of comparing them would mean redoing `Reduction.lean`.

## 5. What this route can deliver

In order of cost:

1. **`DegHomogPoly` for Anthropic's degree**, transported to `PkgI3.AbVar` through
   `CloudB3W16Torsion/RelativeBridges.lean`: about 60 new vendored modules plus a short bridge.
2. **`DegHomogPoly` as deg-det states it**: item 1 plus the comparison of §4.
3. **`CharPolyIndepOfEllAlgClosed` for `k` with a ring hom to `ℂ`**, unconditionally, or the full statement from
   `HomFreeFiniteAlgClosedNoEmb`: item 2 plus deg-det's reduction with `homFreeFiniteAlgClosedC`.

None of these removes the open row by itself. Item 3 would, together with a reroute of the consumers to the
`ℂ` case, as homfree-noemb did for `homFreeFiniteAlgClosed`. Whether every use sits over a field mapping to
`ℂ` is UNCHECKED: the consumers found are `R16Split.rank_two_of_dim` (over `ℚ`) and
`HDecomp/C10/Link.lean` (`trace_T_of_frobCompare`, which charpoly-charp's note says is applied at a
characteristic-`p` field).

## 6. Cost to verify

The base that must build before any of this can be checked (deg-det's reduction, the torsion proof and the
`homFree` proof) is 4,321 modules, 911,693 lines on the PR #59 branch (COUNTED). No build was attempted.

## 7. State

This note comes with no Lean. `wip/deg-det` and `wip/leaf-fold33b` were read at the commits named at the top and
are not merged into `main` as of this note; no port was started.

Written by Claude Code, at Jack's request.
