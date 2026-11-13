# pi0-x6: `π₀(X₆) = 1` (rv-blueprints Q4) as glue

## Verdict

1. **rv-blueprints' sketch is not glue as written** (VERIFIED, read). Its last step argues that
   two components of degree 2 "would each be ramified over all three values", which is impossible
   because "a quadratic extension is branched at an even number of points". Parity forbids exactly
   three branch points; it does not forbid four. For the step to work, the cover `X₆ → P¹` must
   have **no branch values outside `{0, ∞, −16/27}`**. No clause of the bundle
   `LeafAdopt.R1R2fpRep` says this:
   - `R2X6PropsIff` describes the fibres as twist orbits and pins down only the fibres over the
     three values;
   - `R5fpCount` counts CM points by orders of conductor prime to 6.

   So the sketch also needs the leaf "a point with a nontrivial `W`-stabilizer lies over one of the
   three values". That follows from Baba–Granath 2008 §3.1 (the elliptic-order table, signature
   `(0; 2, 4, 6)`) through the uniformization, or from Ogg's fixed-point theorem for Atkin–Lehner
   involutions (UNVERIFIED locator).
2. **A different argument needs no branch-locus information** (checked here; SPECULATIVE until
   reviewed). It uses the Galois action on the geometric components, §2 below. Its literature
   inputs are clauses that are already in the bundle:
   - `R5ptProps` (González–Rotger Thm 5.12) at `ℚ(i)` and at `ℚ(√−3)`;
   - `R5fpCount` (González–Rotger Prop. 5.6) at `ℤ[i]`.

   It needs two more things:
   - (c) "CM **exactly** by `ℤ[i]`" (resp. `ℤ[ζ₃]`) at the points over `0` (resp. `∞`). The
     bundle's `HasCM4` says only that `com` contains some `φ` with `φ² = −1`.
   - (d) algebraic geometry over `ℚ̄`, which Mathlib does not have.
3. **Lean** (VERIFIED, compiled, standard axioms only). The arithmetic and Galois-theoretic core is
   proved from the bundle's clauses, in `scratch/pi0-x6/Core.lean`:
   `Pi0X6.subsingleton_of_bundle`. It assumes three things:
   - the closed facts about `ℚ(i)` and `ℚ(√−3)` (`b = 1`, `#Pic = 1`, conductor coprime to 6);
   - (c);
   - (d), which is three hypotheses on a Galois-compatible map `c : X(ℚ̄) → S`.

   For `S = π₀(X_ℚ̄)` the conclusion `Subsingleton S` is `π₀(X₆_ℚ̄) = 1`.
4. **The full clause `R1pi0Props X := GeometricallyConnected X.hom` cannot be proved in Lean
   today.** Step (d) needs:
   - connected components of `X ×_ℚ Spec ℚ̄` and the `Aut(ℚ̄/ℚ)`-action on them;
   - nonconstant maps from proper curves onto `P¹`;
   - the Nullstellensatz for closed points;
   - "connected over `ℚ̄` ⇒ connected over every field".

   All of this is standard (glue by the task's definition), but none of it is in Mathlib v4.35.

   **Recommendation:** keep `R1pi0Props` as a clause counted inside R1, as leaf-adopt did. The
   argument of §2 shows it is a consequence of González–Rotger and Baba–Granath (with R1 on points)
   plus standard algebraic geometry. It no longer rests only on Deligne 1971 §2, whose locator is
   UNVERIFIED.

## 1. The sketch, checked

The sketch's steps:
1. The generic fibre is a free `W`-orbit of 4 points.
2. The fibres over `0, ∞, −16/27` have 2 points each.
3. Four components of degree 1 would give 4 points over `0`.
4. Two components of degree 2 contradict parity.

Steps 1-3 are correct given standard facts:
- **Step 1.** `W = Aut(𝒪)/Inn(𝒪^×)`, of order 4. A non-CM pair has trivial stabilizer, because
  `(A, ι∘Ad w) ≅ (A, ι)` gives `φ = ι(w)c` with `c ∈ com ⊗ ℚ`, and `c ∉ ℚ` unless `w` is inner.
- **Step 2.** For `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]`, the values of `(b, h)` are `(1, 1)`, `(1, 1)` and
  `(0, 2)`, so `#CM = 2^b h = 2` for each.
  - For `ℚ(i)`: 2 is ramified and 3 is inert.
  - For `ℚ(√−3)`: 2 is inert and 3 is ramified.
  - For `ℚ(√−6)`: 2 and 3 are both ramified.
- **Step 3.** The components are disjoint and each one maps onto `P¹`.

**Step 4 fails.** Take a component `C` of degree 2 with deck group `H = ⟨w⟩`. Riemann–Hurwitz
gives `2g(C) − 2 = −4 + B`, where `B` is the number of ramification points. So `B = 2g + 2` is
even, and `B ≥ 3` allows `B = 4`. To exclude a fourth branch value one must know that every point
with a nontrivial stabilizer lies over `{0, ∞, −16/27}`. Two facts would give this:
- the three involutions of `W` each have exactly 2 fixed points, at `CM(−4)`, `CM(−3)` and
  `CM(−24)`, by Ogg's fixed-point count;
- `Γ*` has exactly three elliptic orbits (Baba–Granath).

Neither is a clause of `R1R2fpRep`. The step does not use the bundle's residue-field clause
`R5ptProps` at all.

## 2. The Galois-component argument

Notation:
- `X̄ = X₆ ×_ℚ Spec ℚ̄`;
- `G = Aut(ℚ̄/ℚ)`, acting on `X(ℚ̄)` by `x ↦ x ∘ Spec σ` and on `X̄` through the second factor;
- `π = π₆`.

The arithmetic inputs, all from the bundle:
- **(a)** `R5ptProps`. Take `k = ℚ(i)`, `R = ℤ[i]`, so `b = 1` and `h = 1`. A point over `0` with
  `com ≅ ℤ[i]` has `[ℚ(x):ℚ] = 2` and `ℚ(i) ↪ ℚ(x)`, so `ℚ(x) = ℚ(i)`. In the same way a point
  over `∞` (`k = ℚ(√−3)`, `R = ℤ[ζ₃]`, `b = 1`, `h = 1`) has `ℚ(x) = ℚ(√−3)`.
- **(b)** `R5fpCount` at `ℤ[i]`. There are exactly `2^1·1 = 2` points over `0`.
- **(c)** Every point over `0` has `com ≅ ℤ[i]` (`R2X6PropsIff` gives `HasCM4`), and every point
  over `∞` has `com ≅ ℤ[ζ₃]`.

The geometric input:
- **(d)** Every connected component of `X̄` contains a `ℚ̄`-point over `0` and one over `∞`, and
  `G` permutes the components compatibly with its action on `X(ℚ̄)`.

**Proof.**
- By (d), the number of components is at most the number of points over `0`, which is 2 by (b).
- Suppose there are two components, `C₁ ∋ x₁` and `C₂ ∋ x₂`, where `x₁, x₂` are the points over
  `0`.
- By (d), pick `y ∈ C₁` over `∞`.
- Pick `σ ∈ G` with `σ(√−3) = √−3` and `σ(i) = −i`. It exists because `i ∉ ℚ(√−3)`.
- The stabilizer of a `ℚ̄`-point is the fixing group of its residue field. So `σy = y`, since
  `ℚ(y) = ℚ(√−3)` by (a), and `σx₁ ≠ x₁`, since `ℚ(x₁) = ℚ(i)`.
- The fibre over `0` is `σ`-stable, so `σx₁ = x₂`.
- `σ` maps the component `C₁ ∋ y, x₁` to the component containing `σy = y` and `σx₁ = x₂`. Hence
  `C₁ = C₂`, a contradiction.
- So `X̄` is connected. Being connected over `ℚ̄` is equivalent to geometric connectedness
  (Stacks, Varieties, "geometrically connected"; UNVERIFIED tag).

What the argument does **not** use:
- the branch locus;
- Riemann–Hurwitz;
- `R1rec`;
- the connectedness of `X` over `ℚ`;
- the fibre over `−16/27`.

It uses `W` only to know that the fibres of `π` are finite, inside (d).

Consistency check (SPECULATIVE, from memory): Elkies' model of `X₀(6,1)` is the conic
`x² + y² + 3z² = 0`. It has the points `(i : 1 : 0)` over `ℚ(i)` and `(√−3 : 0 : 1)` over
`ℚ(√−3)`, which agrees with (a).

**Inputs (c) and (d), status.**
- **(c).** Two options:
  - (c1) Restate R2's CM clauses with "CM point by `R`" in its printed meaning, `End_𝒪(A) ≅ R`:
    `π₆(x) = 0 ↔ Nonempty (com P.q ≃+* ℤ[i])` (and the same at `∞` and `−16/27`). This is a
    consequence of Baba–Granath, exactly as the `HasCM` form is.
  - (c2) Derive it as glue from the leaf `PkgI3.QMDichotomyYu`: `End⁰(A) ≅ B` or `M₂(ℚ(√d))`, so
    the centralizer of `ι(B)` is `ℚ` or `ℚ(√d)`. Add `HomFreeFinite` (so `com` is integral over
    `ℤ`) and the maximality of `ℤ[i]` and `ℤ[ζ₃]`. This needs the double-centralizer theorem
    (not in Mathlib) and is not done.
- **(d).** This is glue at Mathlib scale and is not done. Its pieces, all STANDARD:
  - the components of `X̄` are smooth proper irreducible curves over `ℚ̄`, so each has infinitely
    many closed points, all of them `ℚ̄`-points;
  - `π` is nonconstant on each component, because its fibres are finite twist orbits: by
    Skolem–Noether (leaf T13), `Aut(𝒪) = N_B(𝒪)/ℚ^×`, and `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²`, a computation
    for the explicit `𝒪` (Vignéras, UNVERIFIED locator);
  - the image of a component is closed and irreducible and not a point, so it is all of `P¹`;
  - `G` acts on `X̄` by `id × Spec σ`, compatibly with `X̄(ℚ̄) = X(ℚ̄)`;
  - connected over `ℚ̄` implies connected over every field `K ⊇ ℚ`, which is what Mathlib's
    `GeometricallyConnected` asks.

## 3. Lean (`scratch/pi0-x6/`)

All results below are VERIFIED. `lake env lean scratch/pi0-x6/Core.lean` gives 0 errors and
0 warnings. `#print axioms` on the main declarations shows only `propext`, `Classical.choice` and
`Quot.sound`. The file imports `ZInQKernel.HDecomp.QM.Leaves` and uses its genuine definitions:
`R5ptProps`, `R5fpCount`, `ToP1`, `residueImage`, `fieldPt`, `fieldMap`, `com`, `inertCount6`,
`conductor`. `Field.lean` is the standalone copy of §1.

| Declaration | Statement |
| --- | --- |
| `sqrt_neg_one_not_mem` | `z² = −1`, `s² = −3` in `ℚ̄` ⇒ `z ∉ ℚ⟮s⟯` |
| `exists_fix_moves` | ∃ `σ : ℚ̄ ≃ₐ[ℚ] ℚ̄` with `σ s = s`, `σ z ≠ z` (via `InfiniteGalois.fixedField_fixingSubgroup`) |
| `galPt` | `σ · x = fieldMap σ ≫ x` on `X(ℚ̄)` |
| `spec_comp_eq_self_iff`, `galPt_eq_self_iff` | `σ · x = x` ↔ `σ` fixes `residueImage x` pointwise |
| `galPt_eq_self_iff_of_eq_adjoin` | if `ℚ(x) = ℚ⟮z⟯`: `σ · x = x ↔ σ z = z` |
| `val_galPt` | `π(σ · x) = σ(π x)` |
| `subsingleton_of_galois` | **core**, stated below |
| `eq_adjoin_of_finrank_two` | a degree-2 subfield of `ℚ̄` receiving `k ∋ w`, `w² = d` non-square, is `ℚ⟮z⟯`, `z² = d` |
| `residue_eq_adjoin_of_R5pt` | from `R5ptProps` with `inertCount6 k = 1`, `#Pic R = 1`: the residue field of a point with `com ≅ R` is `ℚ⟮z⟯`, `z² = d` |
| `fibre_le_two_of_R5count` | from `R5fpCount` and `hexact`: at most 2 `ℚ̄`-points over the value |
| `subsingleton_of_bundle` | the core with its arithmetic hypotheses discharged from `R5ptProps` and `R5fpCount` |

The core `subsingleton_of_galois` states: let `c : X(ℚ̄) → S` be Galois-compatible
(`c x = c x' → c(σx) = c(σx')`), and let every class contain a point over `0` and a point over
`∞`. Suppose there are at most 2 points over `0`, each with residue field `ℚ⟮z⟯`, `z² = −1`, and
every point over `∞` has residue field `ℚ⟮s⟯`, `s² = −3`. Then `Subsingleton S`.

The hypotheses of `subsingleton_of_bundle` that remain open are listed below. Each is either a
closed fact or one of the inputs (c) and (d) of §2:
- `hb₄ : inertCount6 k₄ = 1`, `hh₄ : Nat.card (Pic R₄) = 1`, `hc₄ : (conductor R₄).Coprime 6`,
  and the same at `k₃`. These are closed number theory for `ℚ(i)` and `ℚ(√−3)` with `R` the ring
  of integers. Mathlib has `three_pid` for `ℚ(ζ₃)` and inertia degrees in cyclotomic fields
  (`IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd`). It has no PID result for `ℚ(i)` as a
  cyclotomic field; `GaussianInt` is Euclidean, but it would have to be identified with
  `𝓞 ℚ(ζ₄)`. Not done.
- `hexact₄`, `hexact₃`: input (c).
- `hc`, `h0`, `hinf`: input (d), with `S = π₀(X_ℚ̄)`.

## 4. What remains

1. **(d)**: the algebraic geometry of §2 over `ℚ̄`, and the step from `π₀(X_ℚ̄) = 1` to
   `GeometricallyConnected X.hom`. This is large and needs Mathlib development.
2. **(c)**: either restate R2's CM clauses with `com ≃+* R` (option c1), or derive (c) from
   `QMDichotomyYu` (option c2).
3. The closed facts about `ℚ(i)` and `ℚ(√−3)`.
4. A human check of §2 (SPECULATIVE until reviewed).

Until items 1-3 are done, `R1pi0Props` stays a clause of the bundle.
