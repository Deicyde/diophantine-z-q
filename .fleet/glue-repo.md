# glue-repo (fleet report)

**Main result.** The elementary content of steps A1, A3, A5-A8 and A10 of `docs/research/h-trust.md`
(the quaternion datum, the degree bound, Lemma PR(i)-(ii), the conjugates, the Hom field, NoCM)
is now proved in Lean: `scratch/glue-repo/` has four files, about 1400 lines, with no `sorry`.
Every `#print axioms` gives propext, Classical.choice, Quot.sound (VERIFIED by compilation).
No new error was found in the notes. Details: `docs/research/glue-repo.md`; log:
`scratch/glue-repo/log.md`.

**Proved (glue).**
- A1: `𝒪` is a `Subring` of `ℍ[ℚ,2,0,−3]` with disc 6. N5's Gram matrix has det 1. The Rosati
  identity holds, and the Rosati involution is positive.
- A3: `|(𝒪/3𝒪)^*| = 72`, and `4·72 ≤ 324`.
- A5: `inertia_orders_eq_one_iff`. For p ≥ 17 and p ∉ S, Prop. TS's three inertia orders
  `e/gcd(e,m)` at 0, ∞, −16/27 are all 1 iff `p ∤ ZInQ.contactSupport S u`. Also `J(u)` is
  finite, nonzero and not a branch value, and `[K:ℚ] ≤ 324!`.
- A6: `1+3M_r(ℤ₃)` is torsion-free; `B` is a division algebra, so the toric part vanishes.
- A8: Minkowski (finite G ≤ GL_r(ℤ) has |G| ≤ 3^{r²}) and `[EK:ℚ] ≤ D`.
- A10: the fibre over `t(u)` is a free W-orbit with no real point; complex conjugation acts
  as w₃.
- M9: `ℚ(√−2)` does not embed in B; a type-(0,3) element x has `(1+x)/2 ∈ 𝒪`.

**Leaves (14, §3 of the report).**
- Shimura curve: Deligne's Hecke action; Baba–Granath `X₆/W = P¹_j`; the moduli interpretation
  (A4); Shimura reciprocity at CM points.
- Vignéras' local normalizers and embedding criterion.
- Prop. TS (Beckmann 1991, or SGA 1 purity and Abhyankar).
- Abelian varieties: SGA 7 IX semistable reduction with toric functoriality (or Morita);
  Serre–Tate Thms 1-2; Mumford §19 Thm 3; Baba–Granath / Lin–Yang on the moduli point.
- NoCM: Elkies' model and the W-action; González–Rotger Thm 5.12 and Prop. 5.6.

Only Vignéras (which is elementary, so really open glue) and Prop. TS can be stated faithfully
in Lean today.

**Biggest obstacle.** Every non-elementary input of Part A is about `Y₃`, `X₆` or the fibre
surface `A`. None of these is in Mathlib, so the leaves and the glue that connects them (Lemma NV,
the quotient in A3, PR(ii), A7, A8) cannot be stated over genuine definitions. The Lean glue here
does not yet connect to `SixContactMin`.
