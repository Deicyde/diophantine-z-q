# pi0-x6 results log

Task: Q4 of docs/research/rv-blueprints.md, `π₀(X₆) = 1` as glue. Target Lean clause:
`LeafAdopt.R1pi0Props X := GeometricallyConnected X.hom` (scratch/h-decomposition/Leaves.lean
L18636), inside the bundle `LeafAdopt.R1R2fpRep`.

## Findings

F1 (VERIFIED, read) rv-blueprints Q4 sketch, step "two components of degree 2 would each be
ramified over all three values; impossible since a quadratic cover is branched at an even number
of points": parity (Riemann–Hurwitz `2g−2 = −4 + B`, `B` even) only forbids exactly three branch
points. The sketch needs "`π₆` has no branch values outside `{0, ∞, −16/27}`" (every `ℚ̄`-fibre
outside the three values has 4 points). No clause of `R1R2fpRep` gives this: `R2X6PropsIff`
fixes the fibres (twist orbits) and the CM clauses at the three values only; `R5fpCount`
counts CM points by orders of conductor prime to 6. So the sketch, as written, is NOT glue from
the bundle. It becomes correct with one more clause (fixed points of nontrivial `W`-elements lie
over the three values: Baba–Granath 2008 §3.1 elliptic-order table, signature `(0;2,4,6)`, via
the uniformization; or Ogg 1983 fixed points of Atkin–Lehner involutions, UNVERIFIED locator).

F2 (argument checked here; SPECULATIVE until reviewed) A different argument needs NO branch
information: Galois action on the geometric components. Inputs:
 (a) `R5ptProps` (in the bundle) at `k = ℚ(i)`, `R = ℤ[i]` (2 ramified, 3 inert: `b = 1`, `h = 1`):
     every `ℚ̄`-point over `0` has residue field `ℚ(i)`; at `k = ℚ(√−3)`, `R = ℤ[ζ₃]` (2 inert,
     3 ramified: `b = 1`, `h = 1`): every point over `∞` has residue field `ℚ(√−3)`.
 (b) `R5fpCount` (in the bundle) at `ℤ[i]`: exactly `2^1·1 = 2` points over `0`.
 (c) "CM by `ℤ[i]`" in the sense `com ≅ ℤ[i]` at the points over `0` (and `com ≅ ℤ[ζ₃]` over `∞`):
     the bundle's `HasCM4` only says `com ∋ φ, φ² = −1`. Either a textbook leaf (`com` is `ℤ` or an
     order in an imaginary quadratic field: Albert/Shimura, h-trust A9 dichotomy) or a restated R2
     CM clause with `Nonempty (com P.q ≃+* ℤ[i])` (the printed meaning of "CM point by `ℤ[i]`").
 (d) algebraic geometry over `ℚ̄` (Mathlib lacks it): every connected component of `X_ℚ̄` contains
     a `ℚ̄`-point over `0` and one over `∞` (components are smooth proper irreducible curves; `π₆`
     is nonconstant on each because fibres are finite twist orbits, `Aut(𝒪)/Inn(𝒪^×) ≅ W` finite;
     proper image is all of `P¹`; Nullstellensatz); `Aut(ℚ̄/ℚ)` permutes components compatibly
     with its action on `X(ℚ̄)`; `X_ℚ̄` connected ⇒ `GeometricallyConnected X.hom`
     (Stacks, Varieties, "geometrically connected" ⇔ connected over `k̄`; UNVERIFIED tag).
 Proof: components ≤ #(fibre over 0) = 2. If two, `C₁ ∋ x₁`, `C₂ ∋ x₂`. Pick `y ∈ C₁` over `∞` and
 `σ` with `σ(√−3) = √−3`, `σ(i) = −i`. Then `σy = y` (residue field `ℚ(√−3)`), `σx₁ ≠ x₁`
 (residue field `ℚ(i)`), so `σx₁ = x₂`. `σ` maps `C₁ ∋ y, x₁` to the component of `σy = y` and of
 `σx₁ = x₂`: `C₁ = C₂`. Contradiction.

## Lean (scratch/pi0-x6/)

(entries below as compiled)
- L1 (VERIFIED, compiled, `lake env lean scratch/pi0-x6/Field.lean`, no errors/warnings):
  `Pi0X6.sqrt_neg_one_not_mem` (`z² = −1`, `s² = −3` in `ℚ̄` ⇒ `z ∉ ℚ⟮s⟯`) and
  `Pi0X6.exists_fix_moves` (∃ `σ ∈ Aut(ℚ̄/ℚ)`, `σ s = s`, `σ z ≠ z`; via
  `InfiniteGalois.fixedField_fixingSubgroup`).
- L2 (VERIFIED, compiled, `lake env lean scratch/pi0-x6/Core.lean`, 0 errors, 0 warnings;
  axioms of the three main declarations: propext, Classical.choice, Quot.sound):
  `Pi0X6.galPt` (Galois action on `X(ℚ̄)`), `Pi0X6.spec_comp_eq_self_iff` /
  `Pi0X6.galPt_eq_self_iff` (σx = x ↔ σ fixes `residueImage x`),
  `Pi0X6.galPt_eq_self_iff_of_eq_adjoin`, `Pi0X6.val_galPt`, and the core
  `Pi0X6.subsingleton_of_galois` (Galois-compatible `c : X(ℚ̄) → S`, every class meets the fibres
  over 0 and ∞, ≤ 2 points over 0 with residue field ℚ⟮z⟯ (z² = −1), points over ∞ with residue
  field ℚ⟮s⟯ (s² = −3) ⇒ `Subsingleton S`).
- L3 (VERIFIED, compiled, `Core.lean`, 0 errors, 0 warnings; axioms of
  `subsingleton_of_bundle`: propext, Classical.choice, Quot.sound):
  `Pi0X6.eq_adjoin_of_finrank_two`, `Pi0X6.residue_eq_adjoin_of_R5pt` (from `R5ptProps` with
  `b(k) = 1`, `#Pic R = 1`, `k ∋ w`, `w² = d` non-square: residue field `ℚ⟮z⟯`, `z² = d`),
  `Pi0X6.fibre_le_two_of_R5count` (from `R5fpCount` + `hexact`: ≤ 2 points over the value),
  `Pi0X6.subsingleton_of_bundle` (R5ptProps + R5fpCount + the closed facts on ℚ(i), ℚ(√−3) as
  hypotheses + hexact₄/hexact₃ + the AG inputs hc/h0/hinf ⇒ Subsingleton S).
- L4 (VERIFIED, compiled, `lake env lean scratch/pi0-x6/ClosedQi.lean`, 0 errors, 0 warnings):
  closed facts for `k₄ = CyclotomicField 4 ℚ`: `gaussEquiv : GaussianInt ≃+* 𝓞 K4` (via
  `Zsqrtd.lift` and the integral power basis), `inertCount6_K4 : inertCount6 K4 = 1` (3 prime and
  2 not prime in `ℤ[i]`, Mathlib's `GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`),
  `pic_R4 : Nat.card (Pic R4) = 1` (PID), `conductor_R4 : conductor R4 = 1`, `finrank_K4`,
  `IsTotallyComplex K4`, `zeta4_sq' : ζ₄² = -1`.
- L5 (VERIFIED, compiled, `lake env lean scratch/pi0-x6/ClosedQ3.lean`, 0 errors, 0 warnings):
  closed facts for `k₃ = CyclotomicField 3 ℚ`: coordinates `a + bζ₃` on `𝓞 K3`
  (`exists_coord`, `coord_eq_zero`, `dvd_iff_coord`), `not_prime_three_O3` (`3 ∣ λ²`, `3 ∤ λ`),
  `prime_two_O3` (parity table over `ZMod 2` by `decide`), `inertCount6_K3 = 1`,
  `pic_R3 = 1` (Mathlib's `three_pid`), `conductor_R3 = 1`, `finrank_K3 = 2`,
  `sqrt3_sq : (2ζ₃+1)² = −3`.
- L6 (VERIFIED, compiled, `lake env lean scratch/pi0-x6/Pi0X6.lean`, 0 errors, 0 warnings; all
  8 audited declarations: propext, Classical.choice, Quot.sound): the single file combining
  Core + ClosedQi + ClosedQ3, plus §7: `R2X6CMExact` (exact-CM clause at 0, ∞), `Xbar`,
  `ptOf`, `compOf`, `AGInputs` (structure of the unproved algebraic-geometry inputs: galois,
  over0, overInf, descend), `subsingleton_components_of_bundle` and
  `r1pi0Props_of_bundle : R5ptProps X Ψ → R5fpCount → R2X6CMExact Ψ π₆ → AGInputs π₆ →
  GeometricallyConnected X.hom`.
- L7 (VERIFIED, compiled, `Pi0X6.lean`, 0 errors, 0 warnings; 9 audited declarations, standard
  axioms only): Galois compatibility of components PROVED: `galXbar σ := pullback.map … (𝟙)
  (Spec σ⁻¹)` on `X_ℚ̄`, `secOf_comp`, `ptOf_galPt : ptOf (σ·x) = galXbar σ (ptOf x)`,
  `compOf_galois` (via `Continuous.connectedComponentsMap_mk`). `AGInputs` reduced to `over0`,
  `overInf`, `descend`.
- L8 (VERIFIED): consolidated into the single file `scratch/pi0-x6/Pi0X6.lean` (the intermediate
  Field/Core/ClosedQi/ClosedQ3 files are removed, they are in git history). Final compile:
  `lake env lean scratch/pi0-x6/Pi0X6.lean`, exit 0, no errors, no warnings; output in
  `compile_out.txt` (9 `#print axioms`, all `[propext, Classical.choice, Quot.sound]`).
- L9 (VERIFIED, compiled, exit 0, no errors/warnings, 10 audited declarations standard axioms):
  `AGInputs.descend` restated as `ConnectedSpace (Xbar X) → GeometricallyConnected X.hom` (the
  Subsingleton form is false for empty `X`); `connectedSpace_of_subsingleton` proved;
  `r1pi0Props_of_bundle` takes a `ℚ̄`-point `x₀`; `r1pi0Props_of_X6Props` takes it from
  `X6Props` (clause 3).
