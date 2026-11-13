# atkin-li: the leaf `HeckeThetaNewform` is proved

Status: research note (task atkin-li, 2026-11-13), branch `wip/atkin-li` (base fork main
57a7fa26, merged with `origin/wip/gz-theta` 9720252a). New Lean files:
`ZInQKernel/Contrib/GZTheta/{NewCMFinal,ALFricke,ALBasic,ALRep,ALArith,ALMain,ALFinal}.lean` and
the Tau Ceti backports listed in §3. Log `scratch/atkin-li/log.md`. No existing
file of the project was edited (the merge conflict in `ThirdParty/TauCeti/NOTICE` was resolved by
keeping both sides' entries).

Marks: **VERIFIED** (compiled, read in a source named here, or computed), **STANDARD** (published,
reference given), **SPECULATIVE**. No network on this host: literature locators are
**UNVERIFIED**.

## 0. Main result

**`ZInQ.GZDecomp.HeckeThetaNewform` is proved outright** (its exact type, no hypotheses), so
`Literature.GrossZagier` is down to gz-decomp's two leaves `FHNonvanishing` and
`GrossZagierHeegner`. VERIFIED (compiled; `lake build ZInQKernel.Contrib.GZTheta.NewCMFinal`).

```lean
-- ZInQKernel/Contrib/GZTheta/NewCMFinal.lean
theorem ZInQ.GZTheta.newCM : ZInQ.GZTheta.NewCM
theorem ZInQ.GZTheta.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner
    (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

`#print axioms` (VERIFIED: `scratch/atkin-li/Check.lean`, output
`scratch/atkin-li/out_check_axioms.txt`):

```
'ZInQ.GZTheta.newCM' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZTheta.heckeThetaNewform' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The leaf, verbatim (gz-decomp, `ZInQKernel/Contrib/GZDecomp/Decomp.lean`):

```lean
def ZInQ.GZDecomp.HeckeThetaNewform : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), f.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff f n = ZInQ.Contrib.HeckeFE.heckeCoeff d n
```

**Second result: Atkin–Li's twist theorem is proved outright** (gz-theta's Prop
`AtkinLiTwistNew`, Atkin–Li 1978 Thm 3.1, for weight 2, trivial nebentypus and `(·/r)`,
`r ≡ 1 mod 4` squarefree prime to the level), through strong multiplicity one across levels
(`NewformUniqueAcrossLevels`, Miyake Thm 4.6.19 / Cor. 4.6.20), which is proved by backporting
Tau Ceti main's `HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` (commit 4d91513e)
with its dependencies. This gives a second, independent proof of the leaf (gz-theta's route
`heckeThetaNewform_of_atkinLi`).

```lean
-- ZInQKernel/Contrib/GZTheta/ALFinal.lean
theorem ZInQ.GZTheta.newformUniqueAcrossLevels : ZInQ.GZTheta.NewformUniqueAcrossLevels
theorem ZInQ.GZTheta.atkinLiTwistNew : ZInQ.GZTheta.AtkinLiTwistNew
theorem ZInQ.GZTheta.heckeThetaNewform_via_atkinLi : ZInQ.GZDecomp.HeckeThetaNewform
-- ZInQKernel/Contrib/GZTheta/ALMain.lean
theorem ZInQ.GZTheta.atkinLiTwistNew_of_newformUniqueAcrossLevels :
    ZInQ.GZTheta.NewformUniqueAcrossLevels → ZInQ.GZTheta.AtkinLiTwistNew
```
```
'ZInQ.GZTheta.newformUniqueAcrossLevels' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZTheta.atkinLiTwistNew' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZTheta.heckeThetaNewform_via_atkinLi' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZTheta.atkinLiTwistNew_of_newformUniqueAcrossLevels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```
(VERIFIED: `scratch/atkin-li/Check3.lean`, `out_check_axioms3.txt`; `Check2.lean`,
`out_check_axioms2.txt`.)

The two Props, verbatim (`AtkinLiTwistNew` is gz-theta's, `Split.lean`; the named Prop is ours):

```lean
def AtkinLiTwistNew : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : Newform M 2), g.χ = 1 →
    ∀ (r : ℕ) [NeZero r], r % 4 = 1 → Squarefree r → Nat.Coprime r M →
      CuspForm.twist (jacobiChar r) (dvd_twist_left M r) (dvd_twist_right M r) g.toCuspForm ∈
        TauCeti.cuspFormsNew (M * r ^ 2) 2
```

```lean
-- ZInQKernel/Contrib/GZTheta/ALBasic.lean
def NewformUniqueAcrossLevels : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (M M' : ℕ) [NeZero M] [NeZero M'] (χ : (ZMod N)ˣ →* ℂˣ)
    (g : Newform M k) (g' : Newform M' k) (hM : M ∣ N) (hM' : M' ∣ N),
    g.χ.comp (ZMod.unitsMap hM) = χ → g'.χ.comp (ZMod.unitsMap hM') = χ →
    (∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) =
        g'.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM')) →
    M = M' ∧ ⇑g.toCuspForm = ⇑g'.toCuspForm
```

## 1. Proof of `NewCM` (`NewCMFinal.lean`)

`NewCM`: every `F ∈ S₂(Γ₁(32d²))` with coefficients `heckeCoeff d n` (`d ≡ 1 mod 4` squarefree) is
in Tau Ceti's new subspace. Proof:
1. `F = f_d := cmForm etaForm32 d` (gz-theta), as the `q`-expansion determines a cusp form.
2. `f_d` is a good eigenform with trivial nebentypus (gz-theta `exists_eigenformAway_cmForm`).
3. Tau Ceti's `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`
   (Diamond–Shurman 5.8.4) gives a newform `g` of level `M ∣ 32d²`, trivial nebentypus, with the
   eigenvalues of `f_d` at `p ∤ 32d²`, hence `a_p(g) = heckeCoeff d p` for `p ∤ 2d`.
4. gz-theta's `level_eq_of_assoc` (the Fricke-identity argument) gives `M = 32d²`.
5. Tau Ceti's `Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`
   (Diamond–Shurman 5.8.2) gives `f_d = a₁(f_d) g = g`, which is new.

Then `heckeThetaNewform := heckeThetaNewform_of_newCM newCM` (gz-theta `Final.lean`), and the
headline is gz-decomp's `frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` with it.

## 2. Proof of `AtkinLiTwistNew` from `NewformUniqueAcrossLevels`

Files `ALFricke.lean`, `ALBasic.lean`, `ALRep.lean`, `ALArith.lean`, `ALMain.lean` (all in
`ZInQKernel/Contrib/GZTheta/`). Let `g` be a newform of level `M`, weight 2, trivial nebentypus,
`r ≡ 1 (mod 4)` squarefree prime to `M`, `χ = (·/r)`, `N = M r²`, `h = g ⊗ χ` (Tau Ceti's
`CuspForm.twist`).

1. `h` is a good eigenform of level `N`, trivial nebentypus, `a_n(h) = χ(n) a_n(g)`
   (`exists_eigenformAway_twist`). Let `g'` be its associated newform, level `M' ∣ N`.
2. **Twist back.** `g' ⊗ χ` is a good eigenform of level `M' r²`; its newform `g''` has the
   eigenvalues `χ(p)² a_p(g) = a_p(g)`, so by `NewformUniqueAcrossLevels` `g'' = g` and
   `M ∣ M' r²`. Hence every prime of `P = N/M'` divides `r`.
3. **Representation** (`exists_coeff_rep`): by Tau Ceti's spanning theorem
   (`Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul`), the independence of the
   nebentypus spaces, and `NewformUniqueAcrossLevels`, `a_n(h) = ∑_{e ∣ P} c_e a_{n/e}(g')`, so
   `h(τ) = ∑_{e∣P} c_e g'(eτ)`.
4. **Fricke** (`twist_fricke`, generalizing gz-theta's level-32 computation): with
   `g(−1/(Mz)) = c_g z² g(z)` (`c_g = ±M ≠ 0`, Tau Ceti's Fricke sign),
   `h(−1/(Nτ)) = κ τ² h(τ)`, `κ = c_g r² χ(−M) ≠ 0`. With the Fricke identity of `g'` this gives
   `κ a_n(h) = c_{g'} ∑_{e∣P} c_e (P/e)² a_{n/(P/e)}(g')` (`fricke_sum`, `coeff_of_fun_identity`).
5. **Arithmetic** (`level_eq_of_reps`): `ν` (local factors `1 − b_p X + [p ∤ M'] p X²`) is the
   Dirichlet inverse of `b = a(g')`, so `c = a(h) ⋆ ν` is multiplicative, and `c(p^j) = ν(p^j)` at
   `p ∣ r` (where `a_{p^j}(h) = 0`). The two representations give `κ c_f = c_{g'} c_{P/f} f²`
   (`f ∣ P`), hence `c(p^v)² = p^{2v}`, `v = v_p(P) ∈ {1, 2}`. For `v = 2` (`p ∤ M'`),
   `c(p²) = p`; for `v = 1` (`p ∥ M'`), `c(p)² = a_p(g')² = 1` (Tau Ceti, Miyake 4.6.17). Both
   contradict, so `M' = N`, and multiplicity one at level `N` gives `h = g'`, new.

**Finding** (VERIFIED by computation in the proof): step 2 is needed. The Fricke identity alone is
consistent with `p ∥ M`, `p ∤ r`, `g'` unramified at `p` with `a_p(g') = ±(1+p)` and
`h = g'(τ) ∓ p g'(pτ)` (a `p`-stabilization). Only the Ramanujan bound (Deligne) or strong
multiplicity one across levels excludes it.

## 3. Tau Ceti backport (licence)

Backported by hand from Tau Ceti's main, commit 4d91513e (Apache-2.0), under
`ZInQKernel/Contrib/TauCeti/Backport/`, compiled against the commit-5a01f5fe modules vendored
here; each file keeps Tau Ceti's copyright header and carries a "Backported from Tau Ceti (...)"
line (the whole modules also a "Modified for the Z-in-Q kernel" line); NOTICE entry added
(`ThirdParty/TauCeti/NOTICE`). `python3 ~/dzq-runs/tc/diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0
(VERIFIED).

* whole modules (absent at 5a01f5fe): `NumberTheory/ModularForms/Newforms/OldAtPrime` (the
  `q`-new and `q`-old subspaces), `Newforms/PrimeDecomposition`, `Newforms/SupportAwayFromLevel`;
* declarations added after 5a01f5fe: `Data/Nat/Prime/Basic` (two `gcd`/`lcm` lemmas),
  `ModularForms/Basic` (`restrict_trace`), `ModularForms/Degeneracy` (`gamma1Conj`),
  `ModularForms/CongruenceSubgroups/Basic` (`Gamma1_lcm_eq_inf`,
  `exists_mul_eq_of_mem_Gamma1_gcd`), `Fricke/OldSpace` (`frickeOperatorCusp_mem_cuspFormsOldOf`),
  `Newforms/Basic` (`cuspFormsOldOf`), `Newforms/Descent/CharacterSpace`
  (`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd`), `Petersson/Trace`
  (`peterssonInnerCosets_restrict_restrict_eq_zero`), and the cross-level part of
  `Newforms/StrongMultiplicityOne/Basic` (`Newforms/StrongMultiplicityOne/Across.lean`; one call
  adapted to the 5a01f5fe signature of `CuspForm.qExpansion_levelRaise_coeff`).

## 4. What remains

Nothing for this task's target: `HeckeThetaNewform` and `AtkinLiTwistNew` are proved.
`Literature.GrossZagier` now rests on gz-decomp's two leaves `FHNonvanishing` and
`GrossZagierHeegner`; the headline needs `SixContactMin`, `TYZThm35ReadingA` and those two.
