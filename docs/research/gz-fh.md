# gz-fh: `FHNonvanishing` from Friedberg–Hoffstein Theorem B alone, with the twisted root number proved

Status: research note (task gz-fh, 2026-11-15). Branch `wip/gz-fh` (base `wip/w72` 24f97774).
Lean (new files only):
`ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` (the deliverable; final theorem),
`ZInQKernel/Contrib/OneProof/FHNonvanishing/Basic.lean` (leaf statements, arithmetic glue),
`ZInQKernel/Contrib/OneProof/FHNonvanishing/FE.lean` (functional-equation form, reductions),
`ZInQKernel/Contrib/OneProof/FHNonvanishing/TwistFE.lean` (the twisted functional equation, proved).
Scratch: `scratch/gz-fh/` (`Discharges.lean` + `Discharges-output.txt`: `#discharges`, the proposed
`Main.lean` edit and the `C_d` corollary; `FH.lean`, `TwistFricke.lean`: development copies;
`log.md`: results log).

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. No copy of Friedberg–Hoffstein,
Atkin–Li, Shimura or Iwaniec–Kowalski is on this host and there is no network: **every literature
locator in this note is UNVERIFIED**, and the statement of Friedberg–Hoffstein's theorem is
recalled from memory.

---

## 0. Main result

**`ZInQ.GZDecomp.FHNonvanishing` (hL2, rated composite) is proved from one printed leaf,
Friedberg–Hoffstein Theorem B, and the root number of the quadratic twists is proved in Lean.**

```lean
theorem ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) : ZInQ.GZDecomp.FHNonvanishing
theorem ZInQ.GZFH.twistFunctionalEquation : ZInQ.GZFH.TwistFunctionalEquation
```

All four files build (`lake build +ZInQKernel.Contrib.OneProof.FHNonvanishing`, VERIFIED), every
theorem has axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED), and `#discharges`
reports `DISCHARGES [hL2] by ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE, still assumes:
[ZInQ.GZFH.FriedbergHoffsteinB_FE]` (§4, VERIFIED).

| Name (`ZInQ.GZFH.`) | Kind | Source (UNVERIFIED locators) | Rating |
| --- | --- | --- | --- |
| `FriedbergHoffsteinB_FE` | **LEAF** (research) | Friedberg–Hoffstein, Ann. of Math. (2) 142 (1995) 385–423, Theorem B | **printed form up to a stated dictionary**: specialization (`F = ℚ`, `π = π_f`, `f` a weight-2 newform of trivial nebentypus, `χ₀ = χ_{D₀}` unramified at the finite places of `S ⊇ {p ∣ 2N}`), with `χ_v = χ₀,v` written as `D/D₀ ∈ (ℚ_v^×)²` (Mathlib's `ℚ_[p]`) and `ε(½, π ⊗ χ₀) = 1` written as the sign `+1` of the functional equation of the completed twisted L-function (§2). Flag: unread. |
| `twistFunctionalEquation` | GLUE, **proved** | Shimura 1971 Prop. 3.64; Iwaniec, *Topics* §7.3; Iwaniec–Kowalski Prop. 14.20 (root-number half) | `(f ⊗ χ_D) ∣ W_{N D²} = χ_D(−N) ε_N(f) · (f ⊗ χ_D)` for `D` odd fundamental, `(D, N) = 1`, hence `Λ(f⊗χ_D, 2 − s) = χ_D(−N) ε(f) Λ(f⊗χ_D, s)` (§3) |
| `fhNonvanishing_of_printed_fe` and helpers | GLUE, proved | Dirichlet's theorem (Mathlib); gz-statements' `heegnerHyp_iff_split`, `jacobiSym_neg_level`, `coprime_of_heegnerHyp`; reduction `ℤ_p → ℤ/p`, `ℤ_2 → ℤ/8` | (§4) |

The root-number computation the proof needs is therefore entirely in Lean: Dirichlet gives
`D₀ = −q`, `q ≡ −1 (mod 8N)` prime; `χ_{D₀}(−N) = −1`; the proved twisted functional equation
gives `Λ(f ⊗ χ_{D₀}, 2 − s) = (−1)(−1) Λ(f ⊗ χ_{D₀}, s)`, which is Friedberg–Hoffstein's
compatibility hypothesis `ε(½, π ⊗ χ₀) = 1`. Mathlib has no root numbers of elliptic curves, but
Tau Ceti's Fricke-eigenvector functional equation and `CuspForm.twist` suffice, and no newform
theory of twists is needed.

Two further reductions are kept in the files (both compile, both discharge hL2): the variant
leaf pair {`FriedbergHoffsteinB` (newform form of FH), `TwistNewformRootNumber` (Atkin–Li /
Iwaniec–Kowalski Prop. 14.20 as a printed leaf)} via `fhNonvanishing_of_printed`, and
{`FriedbergHoffsteinB_FE`, `TwistFunctionalEquation`} via `fhNonvanishing_of_printed_fe`. Proved
relations: `friedbergHoffsteinB_of_fe : FriedbergHoffsteinB_FE → FriedbergHoffsteinB`,
`twistFunctionalEquation_of_twistNewformRootNumber`. **Recommended for the fold: the single leaf
`FriedbergHoffsteinB_FE`.**

---

## 1. The statements (verbatim from the Lean files)

```lean
-- FHNonvanishing/Basic.lean
def IsOddFundDisc (D : ℤ) : Prop := D ≠ 1 ∧ D % 4 = 1 ∧ Squarefree D

-- FHNonvanishing/FE.lean
def FriedbergHoffsteinB_FE : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    (∃ G : ℂ → ℂ, IsEntireCont (twistCoeff f D₀) 2 G ∧
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G (2 - s) =
          ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G s) →
    ∀ B : ℕ, ∃ D : ℤ, B < D.natAbs ∧ IsOddFundDisc D ∧ 0 < D * D₀ ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p]))) ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

def TwistFunctionalEquation : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
  ∀ D : ℤ, IsOddFundDisc D → Nat.Coprime D.natAbs N →
    ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G →
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        ZInQ.Literature.completedL (N * D.natAbs ^ 2) G (2 - s) =
          (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) * rootNumber f hχ *
            ZInQ.Literature.completedL (N * D.natAbs ^ 2) G s
```

Objects (all genuine, none invented): Tau Ceti's `HeckeRing.GL2.Newform` (eigen away from the
level, Petersson-new, `a₁ = 1`); gz-decomp's `coeff`, `twistCoeff f D n = aₙ(f)·(n/|D|)`,
`rootNumber f hχ = i²·frickeSign` (the sign of Tau Ceti's proved
`Λ_N(2 − s) = rootNumber · Λ_N(s)`), `IsEntireCont`; the kernel's
`ZInQ.Literature.completedL M G s = M^{s/2}(2π)^{−s}Γ(s)G(s)` (`CR3Literature.lean`); Mathlib's
`jacobiSym`, `ℚ_[p]`, `Squarefree`. The strip `0 < Re s < 2` avoids Mathlib's junk values of `Γ`
at its poles, as in `FunctionalEquation5`. `chiD D = (· / |D|)` is the Kronecker character of
`ℚ(√D)` for `D ≡ 1 (mod 4)` (gz-statements: `chiD_prime`, `chiD_two`; quadratic reciprocity).

The variant statements `FriedbergHoffsteinB` (hypothesis: a newform `g` of level `N D₀²` with
`coeff g = twistCoeff f D₀` and `rootNumber g = 1`) and `TwistNewformRootNumber` are in
`FHNonvanishing/Basic.lean`.

## 2. The Friedberg–Hoffstein leaf against the printed theorem

**The printed theorem as recalled (UNVERIFIED in every detail; same recollection as
gz-statements §2.2).** S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic
L-functions on GL(2)*, Ann. of Math. (2) 142 (1995), 385–423, Theorem B: let `π` be a cuspidal
automorphic representation of `GL₂(𝔸_F)` (trivial central character, or self-contragredient: not
remembered), `S` a finite set of places containing the archimedean places, the places where `π`
ramifies (and possibly those above 2), and `χ₀` a quadratic idele class character with
`ε(½, π ⊗ χ₀) = 1`. Then there are infinitely many quadratic idele class characters `χ` with
`χ_v = χ₀,v` for all `v ∈ S` and `L(½, π ⊗ χ) ≠ 0`. Whether this is labelled A or B is not reliably
remembered (gz-statements §2.2); the task brief and gz-decomp say B.

**Clause by clause** (`F = ℚ`, `π = π_f`):

| Lean clause | Printed counterpart | Relation |
| --- | --- | --- |
| `f : Newform N 2`, `f.χ = 1` | `π` cuspidal, trivial central character | specialization |
| `S ⊇ {p ∣ 2N}` (with `∞` implicit) | `S` contains `∞`, the ramified places, (places above 2) | specialization (`2 ∈ S` imposed even if the print does not need it) |
| `IsOddFundDisc D₀`, `p ∤ D₀` for `p ∈ S` | `χ₀` quadratic; here unramified at the finite places of `S` | specialization; quadratic characters of `ℚ` ↔ fundamental discriminants (STANDARD), and `χ₀,2` unramified ↔ `D₀` odd |
| `FriedbergHoffsteinB_FE`: `∃ G`, entire continuation of `∑ aₙ(f) χ_{D₀}(n) n^{−s}`, with `Λ(2 − s) = Λ(s)` on `0 < Re s < 2`, `Λ(s) = (N D₀²)^{s/2}(2π)^{−s}Γ(s)G(s)` | `ε(½, π ⊗ χ₀) = 1` | for `(D₀, N) = 1` the finite `L(s − ½, π_f ⊗ χ₀)` is this Dirichlet series, its conductor is `N D₀²` and its archimedean factor `Γ_ℂ(s)`, so the global functional equation is `Λ(2 − s) = ε(½, π ⊗ χ₀) Λ(s)`; as `Λ ≢ 0` on the strip, the hypothesis says `ε(½, π ⊗ χ₀) = 1`. (In Lean the FE with sign `χ_{D₀}(−N) ε(f)` is now *proved*, `twistFunctionalEquation`, so the hypothesis is equivalent to `χ_{D₀}(−N) ε(f) = 1`.) |
| `FriedbergHoffsteinB` (variant): `∃ g` of level `N D₀²`, `coeff g = twistCoeff f D₀`, `rootNumber g = 1` | `ε(½, π ⊗ χ₀) = 1` | such a `g` has `π_g ≅ π_f ⊗ χ₀` (strong multiplicity one), and `rootNumber g` is the sign of the proved FE of `Λ(g, s)`. Implied by the FE form in Lean (`friedbergHoffsteinB_of_fe`). |
| `∀ B, ∃ D, B < |D|` | infinitely many `χ` | `χ = χ_D`, finitely many `D` per bound |
| `IsOddFundDisc D` | `χ` quadratic, `χ_2 = χ₀,2` unramified | `D` fundamental and odd |
| `0 < D * D₀` | `χ_∞ = χ₀,∞` | `χ_{D,∞} = sgn^{[D<0]}` |
| `IsSquare (D / D₀)` in `ℚ_p`, `p ∈ S` | `χ_p = χ₀,p` | `χ_{D,p}(x) = (D, x)_p` (Hilbert symbol), nondegenerate, so `χ_{D,p} = χ_{D₀,p}` iff `D/D₀ ∈ (ℚ_p^×)²` (Serre, *A course in arithmetic*, Ch. III Thm 2, UNVERIFIED number) |
| `∀ G, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0` | `L(½, π ⊗ χ) ≠ 0` | for `(D, N) = 1` (forced by `χ_p = χ₀,p` unramified at `p ∣ N`) the series `∑ aₙ(f) χ_D(n) n^{−s}` is the finite `L(s − ½, π ⊗ χ_D)`; `G` exists (G6) and is unique, so the clause is not vacuous; if the print uses `L^S`, the omitted Euler factors are finite and nonzero at the centre (gz-statements §2.3) |

**Rating (both forms): printed form up to the stated dictionary, a specialization, never
stronger** (provided the recalled statement is right). It inherits gz-statements' open human checks §6 H1 (a)-(f):
no level restriction, dihedral `π` allowed (the use is the CM newform of `C_d`), arbitrary local
data at `S ∋ 2`, the form of the root-number hypothesis, "infinitely many", the label and page.
The improvement over the composite `FHNonvanishing`: the root number of the twist is no longer
folded in (it is proved), and the leaf's hypothesis is the printed compatibility hypothesis,
applied to one explicit `χ₀`, instead of a consequence of it computed under the Heegner
conditions.


## 3. The twisted functional equation (proved): `FHNonvanishing/TwistFE.lean`

Statement proved (`slash_frickeGL_twist`): for `f : Newform N 2` with `f.χ = 1`, `D` an odd
fundamental discriminant `≠ 1` with `(D, N) = 1`, `r = |D|`, and `F = CuspForm.twist (chiDMod D)
f` (Tau Ceti; level `Γ₁(N r²)`, `q`-expansion `∑ aₙ(f) χ_D(n) qⁿ`),

```
⇑F ∣[2] frickeGL ℝ (N r r) = (χ_D(−N) · ε_N(f)) • ⇑F.
```

Then `normalizedFrickeOperatorCusp 2 F = χ_D(−N) ε_N(f) • F` (the normalizer is `1` in weight 2),
Tau Ceti's `CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul` gives the
functional equation of `frickeCompletedL F`, and `completedL_eq_frickeCompletedL_cusp` (proved:
`completedL M G = frickeCompletedL F M` on `Re s > 0` for the entire continuation `G` of `L(F, s)`)
turns it into `TwistFunctionalEquation`.

Proof of the eigenvalue (all VERIFIED by compilation), with Tau Ceti's
`F = r⁻¹ ∑_{a mod r} 𝓕χ(a) · f ∣ [1, a/r; 0, 1]` (`𝓕` = Mathlib's `ZMod.dft`):

1. `dft_chiDMod_nonunit`: `𝓕χ_D(a) = 0` for `a` not a unit of `ZMod r`. Witness
   (`exists_twist_witness`): for `p ∣ gcd(a, r)`, `r = p r'` with `(p, r') = 1` (squarefree), a unit
   `x ≡ 1 (mod r')`, `x ≡` non-residue `(mod p)` (CRT, `FiniteField.exists_nonsquare`); then
   `(x − 1) a = 0` and `χ_D(x) = (x/p)(x/r') = −1`, and substituting `j ↦ x j` gives
   `𝓕χ(a) = −𝓕χ(a)`. This is where `D` squarefree (primitivity of `χ_D`) enters.
2. `dft_chiDMod_unit`: `𝓕χ_D(u) = χ_D(u) 𝓕χ_D(1)` for a unit `u` (`χ_D(u)² = 1`).
3. `upperRightHom_mul_frickeGL`: for `r d₀ − N a b = 1`,
   `[1, a/r; 0, 1] · W_{N r²} = (r I) · W_N · [r, −b; −N a, d₀] · [1, b/r; 0, 1]`, the middle
   matrix in `Γ₀(N)` (`twistGamma_mem`). Scalars act trivially in weight 2
   (`ModularForm.slash_scalar`), `f ∣ W_N = ε_N(f) f` (`slash_frickeGL_newform`), `f ∣ γ = f` for
   `γ ∈ Γ₀(N)` (`slash_gamma0_newform`, from the nebentypus relation with `f.χ = 1`), and
   `f ∣ [1, x + m; 0, 1] = f ∣ [1, x; 0, 1]` for `m ∈ ℤ` (`slash_upperRightHom_add_intCast`). So
   (`slash_twist_unit`) `f ∣ [1, u/r] ∣ W_{N r²} = ε_N(f) · f ∣ [1, φ(u)/r]` with
   `φ(u) = −(N u)⁻¹` (Bezout gives `b ≡ φ(u)`).
4. `dft_twistInv`: `𝓕χ(u) = χ_D(−N) 𝓕χ(φ(u))`, since `(−N) φ(u) = u⁻¹` and `χ_D(u⁻¹) = χ_D(u)`.
5. `slash_frickeGL_twist`: drop the non-units (step 1), apply steps 3–4 termwise, and reindex
   by the involution `φ` of `(ZMod r)ˣ` (`twistInv_involutive`).

This proves, in Lean, the root-number half of Atkin–Li / Iwaniec–Kowalski Prop. 14.20 for
quadratic characters of odd conductor in weight 2 and trivial nebentypus, at the level `N D²`
(without the newform property of the twist, which is not needed).

## 4. The arithmetic glue and `#discharges`

Proof of `fhNonvanishing_of_printed_fe` (and of the variant `fhNonvanishing_of_printed`), all
VERIFIED by compilation:

1. `exists_aux_disc`: Dirichlet's theorem in Mathlib (`Nat.forall_exists_prime_gt_and_eq_mod`)
   gives a prime `q ≡ −1 (mod 8N)`, and `D₀ = −q` is an odd imaginary fundamental discriminant with
   the Heegner hypothesis for `N` and `D₀ ≡ 1 (mod 8N)` (`heegner_neg_prime`, via gz-statements'
   `heegnerHyp_iff_split`).
2. `χ_{D₀}(−N) = −1` (gz-statements' `jacobiSym_neg_level`), `(D₀, N) = 1`
   (`coprime_of_heegnerHyp`); `TwistFunctionalEquation` at `D₀` with `ε(f) = −1` gives the
   functional equation with sign `+1` for the entire continuation `G` of `L(f ⊗ χ_{D₀}, s)`
   (`exists_isEntireCont_twist`, gz-decomp G6).
3. `FriedbergHoffsteinB_FE` with `S = (2N).primeFactors` (`p ∤ D₀` for `p ∈ S`:
   `not_dvd_of_mem_primeFactors`) gives `D` with `|D| > B`, `IsOddFundDisc D`, `D·D₀ > 0`, `D/D₀`
   a square in every `ℚ_p`, `p ∣ 2N`, and the nonvanishing.
4. `heegner_of_local`: `D < 0`, and the local squares give the Heegner hypothesis:
   `exists_padicInt_of_isSquare_div` (`a/b = x²`, `p ∤ b` ⇒ `x ∈ ℤ_p`), `zmod_of_isSquare_div`
   (odd `p`: reduce mod `p`, `D ≡ ȳ²`, and `p ∤ D` since otherwise `p² ∣ D`),
   `mod_eight_of_isSquare_div` (`p = 2`: reduce `ℤ_2 → ℤ/8`; `5` is not a square mod 8).

`#discharges` (`scratch/gz-fh/Discharges.lean`, against the built `ZInQKernel.OneProof.Main` of
this base; full output `scratch/gz-fh/Discharges-output.txt`, VERIFIED). The other five DISCHARGES
lines of the output are the base's known contributions (as in the kit's worked example); the
lines for this task:

```
DISCHARGES [hL2] by ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE
  still assumes: [ZInQ.GZFH.FriedbergHoffsteinB_FE]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hL2] by ZInQ.GZFH.fhNonvanishing_of_printed
  still assumes: [ZInQ.GZFH.FriedbergHoffsteinB, ZInQ.GZFH.TwistNewformRootNumber]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hL2] by ZInQ.GZFH.fhNonvanishing_of_printed_fe
  still assumes: [ZInQ.GZFH.FriedbergHoffsteinB_FE, ZInQ.GZFH.TwistFunctionalEquation]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 65 open hypotheses, 1349 theorems checked, 8 discharge one
'gzfh_frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
'gzfh_fhNonvanishingCd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.twistFunctionalEquation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.fhNonvanishing_of_printed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.fhNonvanishing_of_printed_fe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.twistFunctionalEquation_of_twistNewformRootNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.GZFH.friedbergHoffsteinB_of_fe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`gzfh_frozenTarget` is `ZInQ.OneProof.frozenTarget` with `hL2` replaced by
`fhNonvanishing_of_friedbergHoffsteinB_FE hFH`, `hFH : FriedbergHoffsteinB_FE`: the proposed
`Main.lean` edit, checked without editing `Main.lean`.

**Main.lean edit (for the integrator; not made here).** `hL2` is a top-level hypothesis of
`ZInQ.OneProof.frozenTarget`, not a bundle field, so autofold does not cover it. The edit: add
`import ZInQKernel.Contrib.OneProof.FHNonvanishing`; replace the argument
`(hL2 : ZInQ.GZDecomp.FHNonvanishing)` by `(hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)`; pass
`(ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH)` where `hL2` was passed. kinds.tsv:
replace the composite row `FHNonvanishing` by `FriedbergHoffsteinB_FE` (LEAF, research, flagged
unread). Proposed locators.md row: Friedberg–Hoffstein 1995 Theorem B (label and page unread;
checks gz-statements §6 H1 (a)-(f), with (d) now "the root-number hypothesis is
`ε(½, π ⊗ χ₀) = 1`, read as the sign of the functional equation"). The GLUE count does not rise
(one composite becomes one leaf; all new glue is proved).

## 5. Would the `C_d` form (`FHNonvanishingCd`) make the split easier?

No longer relevant to the root number, which is now proved for every level. The same leaf implies
the `C_d` form (`gzfh_fhNonvanishingCd`, compiled, via
`GZStatements.fhNonvanishingCd_of_fhNonvanishing`), and the glue would be the same with `B = 4`.
What the `C_d` form would still buy (SPECULATIVE): the FH leaf could be narrowed to one dihedral
family (level `32 d²`, CM by `ℚ(i)`), which makes the statement check H1 (a), (b) narrower, and
"infinitely many" is then used only to avoid `D = −3`. The narrowing is a one-line change of the
leaf's quantifier; the glue in this task does not depend on it. Recommendation: keep the general
form (it is what the source states); switch to the `C_d` form only if the statement check of FH's
generality (H1 (a), (b)) fails.

## 6. The variant leaf `TwistNewformRootNumber` (not needed by the main result)

Printed (UNVERIFIED, from memory): Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloquium
Publ. 53 (2004), Prop. 14.20: if `f ∈ S_k(N, ψ)` is primitive and `χ` is a primitive character
mod `r` with `(r, N) = 1`, then `f ⊗ χ` is primitive in `S_k(N r², ψ χ²)` and
`η(f ⊗ χ) = ψ(r) χ(N) τ(χ)² r⁻¹ η(f)`, `η` the pseudo-eigenvalue of `W`. Also Atkin–Li,
*Twists of newforms and pseudo-eigenvalues of W-operators*, Invent. Math. 48 (1978) 221–243,
Thm 3.1 (UNVERIFIED number), and Shimura 1971 Prop. 3.64 for the twisted functional equation.

Specialization: `k = 2`, `ψ = 1`, `χ = χ_D` with `D` an odd fundamental discriminant, `r = |D|`;
`τ(χ_D)² = χ_D(−1)|D|` (Gauss), so `η(f ⊗ χ_D) = χ_D(−1)χ_D(N) η(f) = χ_D(−N) η(f)`, and
`rootNumber = i^k η` turns this into `rootNumber(g) = χ_D(−N) rootNumber(f)`. `χ_D(−N)` is
`jacobiSym (−N) |D|`, the Kronecker symbol `(D/·)` at `−N` for `D ≡ 1 mod 4`. The nebentypus
`χ_D²` is principal mod `|D|`, so `g.χ = 1` at level `N D²`. For real `χ` the possible readings
`χ(N)`, `χ̄(N)`, `χ(−N)` of the print agree after `τ(χ)²` is evaluated (gz-statements §6 H2).

**Rating: consequence of the printed form** (specialization plus the Gauss-sum evaluation), not
literal. Its root-number half is now proved (`twistFunctionalEquation`); its newform half (the
twist of a newform is new, the hard half of Atkin–Li) is not in Tau Ceti and is not needed by the
main result.


## 7. What remains

* Human statement check of Friedberg–Hoffstein Theorem B against the print (gz-statements §6 H1
  (a)-(f)); no locator here was read.
* The `Main.lean` edit and the kinds.tsv / locators.md rows (§4), for the integrator.
* Nothing else: the twisted root number, previously folded into the composite, is proved.
