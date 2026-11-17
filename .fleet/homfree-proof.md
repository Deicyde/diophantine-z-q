# homfree-proof (2026-11-16, base 0caafe66)

**Verdict.** `homFreeFiniteAlgClosed` (Mumford §19 Thm 3) is proved over every algebraically closed field that has a ring
homomorphism to `ℂ`. The proof uses only two other fields of the same bundle: `uniformizationLeafAll` and
`mumfordTorsionAlgClosed`. The field is discharged from those two fields plus one new leaf,
`HomFreeFiniteAlgClosedNoEmb`: the same statement restricted to fields with no embedding into `ℂ` (characteristic `p`,
or characteristic 0 of transcendence degree above the continuum). The new leaf is strictly weaker than the field. It is
published (a ∀-specialization of the print), not the printed form. The count is unchanged: 34/11 → 34/11.

**What compiles** (standard axioms, VERIFIED):
- `ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosed.lean`, with:
  - `homFreeConcl_of_emb`: free, finite, rank ≤ 4 dim A dim B, and `ℤ_ℓ ⊗ Hom ↪ Hom(T_ℓ, T_ℓ)`;
  - `homFreeFiniteC`: T6 over any `k` with `σ : k →+* ℂ`;
  - `homFreeFiniteAlgClosedC`, `homFreeFiniteAlgQ`, `homFreeFiniteNF`;
  - `homFreeFiniteAlgClosed_of_noEmb`.
- The proof: the lattice representation `Hom(A,B) ↪ Hom_ℤ(Λ_A,Λ_B)`, conj-twist's injective `ℤ_ℓ ⊗ Λ ↪ T_ℓ` with its
  naturality, and flatness of `ℤ_ℓ`.
- `#discharges` reports the field discharged, assuming the two fields and the new leaf.
- `scratch/homfree-proof/autofold.json`: the dry-run fold compiles.

**What remains.**
- The characteristic-`p` case (the new leaf) is out of reach of the bundles. It needs the quotient by `A[ℓ]` and
  §19 Thm 2 with Poincaré in characteristic `p`; ℓ-adic data alone cannot give finite generation.
- No consumer of T6 uses such a field. The closure call graph is VERIFIED; the fields are number fields and `ℚ̄`, from
  reading.
- So "-1, no new leaf" needs a re-assembly of the T6 branch onto `HomFreeFiniteC`/`AlgQ`. That is not an autofold;
  the plan is in docs/research/homfree-proof.md §5.3.
- Note for faltings-cm's pending r9b fold: use `homFreeFiniteNF` instead of `{t}.homFreeFiniteAlgClosed`.

Final commit of the task: report docs/research/homfree-proof.md, scratch/homfree-proof/ (log.md, checks), contribution ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosed.lean.
