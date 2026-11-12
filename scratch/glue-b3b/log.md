# glue-b3b results log

- Prefix.lean = scratch/glue-conj/UnramConj.lean lines 1-910 (through `end Conj`), verbatim.
  Compiles (warnings only), 1m28s wall.
- Sec.lean part 1 (appended to Prefix as Dev.lean): `val_intCast` (integer has v=1 or ≤ v(p)),
  `val_sub_lt_one` (α²=±p, (a-b)α ∈ ℤ ⇒ v(a-b)<1), `smul_sq_cases`, `exists_int_of_fixed`,
  `exists_int_anti` ((a - σa)α ∈ ℤ when a fixed by Stab(α), σα=-α), `exists_frac`
  (x ∈ w ⇒ x = n/d, n,d integral, v(d)=1), `mem_inertia_of_center` (s•𝔓_w = 𝔓_w and s
  trivial on B/𝔓_w ⇒ s ∈ I_w). COMPILED, no errors. 11:49.
- Sec2.lean: `exists_inertia_neg` (α²=±p, ∃σ, σα=-α ⇒ ∃ s ∈ I_w, sα=-α), via H = Stab(α) (open,
  closed, compact), A = FixedPoints.subalgebra ℤ B H, Mathlib
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (A, H) and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite` (A, H). COMPILED, no errors. 11:52.
- Sec3.lean: `act_zeta` (sζ = ζ^cyc(s)), `gaussP` (quadratic Gauss sum in ℚ̄), `gaussP_transform`
  (s g = (cyc(s)/p) g), `gaussP_sq` (g² = ±p, Mathlib `gaussSum_sq`), `exists_neg_of_sq`
  (±p not a rational square), `leafB3b : LeafB3b` (LeafB3b text verbatim from
  glue-b3-unram / glue-conj). COMPILED; `#print axioms GlueB3Unram.leafB3b`:
  [propext, Classical.choice, Quot.sound]. 11:54.
- B3b.lean = glue-conj UnramConj.lean (through `end Conj`) + Sec/Sec2/Sec3 + glue-conj's
  `unramified_outside_final` + new `unramified_outside_b3a (hA : LeafB3a) ...` (same
  conclusion, calls `unramified_outside_final hA leafB3b`). COMPILED, no errors; all 11
  `#print axioms` lines: [propext, Classical.choice, Quot.sound]. 11:55.
- Generalization: `exists_inertia_neg` now takes `α² = c` (c : ℤ) with `v_w(c) = v_w(p)`;
  `exists_neg_of_sq` takes `¬ IsSquare (c : ℚ)`; `not_isSquare_of_squarefree`. leafB3b recompiled.
- T32Defs.lean: verbatim copies (namespace LeafPush) of leaf-push's `GQ`, `IsAtPrime`, `inertiaQ`,
  `T32b_QuadraticRamification` (diff-identical to scratch/h-decomposition/Leaves.lean
  L11877-11888, L11903-11916); `liesOver_of_isAtPrime`, `val_intCast_eq_one`,
  `t32b : LeafPush.T32b_QuadraticRamification`. (⇒) via t = (1+s)/2 integral, inertia gives
  v(σt - t) = v(s) < 1, contradicting v(s)² = v(d) = 1; (⇐) via `exists_inertia_neg`. COMPILED.
- Final B3b.lean (1617 lines) = all of the above. `lake env lean`: no errors, 20 s; 12
  `#print axioms` lines all [propext, Classical.choice, Quot.sound]; no `sorry`, no `axiom`. 12:04.
- Dev pieces Sec.lean, Sec2.lean, Sec3.lean, T32Defs.lean, Prefix.lean are fragments (not
  standalone files); B3b.lean is the checked file.
