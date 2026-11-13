# notes-fix: applying factcheck-w34b

Status: task notes-fix, 2026-11-13. Base 883c4ddf (origin/wip/integrate-w35c). Results log
`scratch/notes-fix/log.md`. Source: `docs/research/factcheck-w34b.md`. Its items about
`scratch/h-decomposition/Leaves.lean` and `h-decomposition.md` are left to leaf-adopt3.

## 1. Lean (ZInQKernel/HDecomp/QM/)

**Item 1: fixed in Lean.** `LeafQM.AV.fibre_conjugates_isomorphic` (QM/Leaves.lean) used to conclude
`∃ P : QML3 ℚ̄, ∀ σ, ∃ Q, IsBaseChangeOf σ P Q ∧ ∃ α, Nonempty (QMIso (P.q.twist α) Q.q)`. That
conclusion never mentions `j₀`. It now reads

```
∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
  ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) ∧
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ Q : QML3 Qbar, IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)
```

The proof is the old one: `exists_fibre_object` and then `conj_twist_of_rational`. The witness
`Y, π` comes with `R1fpProps` and `R2fpProps`, so "a point over `j₀`" means a point of the leaves'
`Y₃` under their `π`. Without these two conjuncts the clause `π(y) = j₀` could be met by any `π`.
The name is unchanged and nothing in the build used the old form, so `scripts/print_axioms.lean`
needed no change. The scratch copies (`scratch/leaf-qm-fp/QMLeaves.lean`,
`scratch/h-decomposition/Leaves.lean:15532`) still have the weak form. The second is
leaf-adopt3's file.

**Items 2-4: docstrings only, no statement changed.**
- `QML3` (QM/Structures.lean), `R1fp` and `QMLeaves` (QM/Leaves.lean) already said "in
  characteristic 0" at the base. "Lattice cores compiled" now reads "for N5's `μ` on `Λ = 𝒪`
  only", and the docstrings list what is not compiled: the passage to polarizations, `Λ = 𝒪v`,
  class number one and the descent from `ℂ`.
- `R5fp` and `R5fpCount` now say "in characteristic 0".
- The `R1R2fp` docstring (`R1heckeProps` paragraph) has rv-qm-polar's repair 3, retargeted per
  item 4. The kept `λ` has type `α⁻¹(μ)` relative to `ι∘α`; the matching
  `λ' = λ∘ι(εv)` has `v = μ⁻¹α(μ)` (`RvQMPolar.twist_type`, the algebra only); for `i` and `j + k`,
  `λ' = λ`. I checked the sign by hand: `α(μ) = −μ` gives `v = −1`, `ε = −1`, `εv = 1`.
- QM/Polar.lean (the kernel copy of QMPolar):
  - the header now says "New here (§§5-8)";
  - the §5 torus sentence is marked as argued;
  - the §8 header bullet, the §8 title and the `lemmaP_lattice` docstring now claim only the lattice
    statement for N5's `μ`, and list the steps that are argued, not compiled.

## 2. Notes (one commit per note, smallest edits)

| Note | Items |
| --- | --- |
| hdec-adopt2 | 7 (90 added, 182 before; checked with git at 9a826482), nit "eleven clusters" / ten rows |
| leaf-adopt | 8 (115 lines, 114 declarations), 9 (L19202), 14 (two of four files), nits 19,350 lines, five fields (checked at 01267822) |
| def-faltings | 10 (16th `#print axioms`, `omegaAt_genericPt`), 22 (H5, AT1a, M2), nits AN3's `g`, `IsMonHom`, `IsCommMonObj` |
| rv-jac-ext | 6 (`PkgI3.AbVar.baseChange` exists), 18 (`splitting_degree_le` is generic), 19 (axiom-bridge not on this branch), nits `routeW_*` rows, 5 of 8 printed |
| rv-qm-polar | 3, 4 (repair 3 retargeted), 5 (repair 2 locations), 15, 16, 17, nits `α⁻¹(μ)`, `pure_of_sq`, `Enu_int`; "Not in Lean" list extended |
| leaf-qm-fp | 1 (scratch vs kernel statement), 24 (`cm_of_val` + `R2X6Props`), 25 (integration done), nit `CategoryTheory.IsPullback`; pointers from the old SPECULATIVE premise to Lemma P |
| leaf-push2 | 11, 12, 13, nits (10 of 72 theorems; R3's scheme isomorphism) |
| rv-blueprints | 20, 21, 28, nits (`R5Repair`, `audit_tail`, R16Transfer header) |
| bp-analytic | 23 (linter, unbundled `analyticRep`, Liouville hypotheses), nits (94 lines, `QM.` namespace) |
| leaf-modcurves | 26 (integration done, MC9, `VSurjOfSurjective`, §A-§J), nit `rhoF_attached` |
| glue-t32a | 27 (2266 lines; verbatim range diffed), nit earlier-glue list |
| bp-qmmoduli | priority (c): §0 item 2 now has "abelian surface over `F`", characteristic 0 and the fixed `μ` |
| bp-hecke-fe | nits (`unitOf` 8 unit entries; `functionalEquation5_of_deuring_fourier` hypotheses) |
| hdec-adopt3 | pointer: the strengthened declaration now differs from the leaf-qm-fp draft (`same.py` QM count) |

## 3. Not done (outside this task's files)

- `scratch/hdec-adopt2/log.md:32` repeats "93". The fix is "90", but the file belongs to
  hdec-adopt2.
- The scratch originals `scratch/rv-qm-polar/QMPolar.lean` (`lemmaP_lattice` docstring and the
  `New here` line), `scratch/leaf-qm-fp/QMLeaves.lean` (`QML3` docstring, item 1 statement, repair
  3 text) and `scratch/rv-blueprints/R16Transfer.lean` (module header) are unchanged. Their kernel
  copies are fixed where they exist.
- The rename of the QM "Lemma P" to "Lemma QP", to avoid the clash with route AP's
  `ZInQ.Mult.lemmaP_*`, is recommended but not done. It would touch h-decomposition.md and
  Leaves.lean.
- Everything about `Leaves.lean` and `h-decomposition.md` is for leaf-adopt3: the duplicate
  `#print axioms` line, item 14's copy, the nit at h-decomposition.md:306, and the h-decomposition
  locations of item 5.

## 4. Build

VERIFIED (2026-11-13, 01:55 PST, after the last Lean change):
- `lake build ZInQKernel` exits 0: "Build completed successfully (9991 jobs)", 7m37s from a cold
  worktree, 0 errors. The QM modules took QM.Structures 21s, QM.Polar 11s and QM.Leaves 6.1s. Output:
  `scratch/notes-fix/build1.txt`.
- `lake env lean scripts/print_axioms.lean` exits 0 and prints 399 axiom lists for 399
  `#print axioms` lines. A Python check of the joined output finds every one exactly
  `[propext, Classical.choice, Quot.sound]`, including `LeafQM.AV.fibre_conjugates_isomorphic`.
  Output: `scratch/notes-fix/axioms.txt`.
