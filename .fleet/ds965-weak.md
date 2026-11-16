# ds965-weak (fleet summary)

**Verdict: `dsThm965` is now reading-robust.** `DS965Weak.dsThm965_of_weak : DSThm965Weak → DSThm965` is proved in
Lean with no other leaf (standard axioms). `DSThm965Weak` is DS 9.6.5 in its weakest reading: `ρ(Frob_𝔭)`
*satisfies* `x² − a_p x + χ(p)p^{k−1}` (`aeval … = 0`), not "has it as characteristic polynomial". It is
printed under every reading: it is the print if DS says "satisfies", and otherwise follows by Cayley–Hamilton
(`dsThm965Weak_of_dsThm965`, compiled).

Glue, all proved: the kernel's Chebotarev (T18, `frobeniusDense_C9`) and hodge-split's `eps0`/`cycQ`.
* Non-scalar case: `det ρ = ε₀χ_ℓ^{k−1}` by density on the open non-scalar locus, then charpoly from
  `P(M) = 0` plus `det M = P(0)`.
* All-scalar case: replace `ρ = ψ·1` by `diag(ψ, ε₀χ_ℓ^{k−1}ψ⁻¹)`; new inertia lemmas for `ε₀` and `χ_ℓ`.
* No determinant leaf is needed (dsThm966, Weil pairing and Ribet are unused).

**Compiles:**
* `ZInQKernel/Contrib/OneProof/DSThm965Weak.lean` builds.
* `#discharges`: `DISCHARGES [OpenResearchLeaves22.dsThm965] by DS965Weak.dsThm965_of_weak`, still assumes
  `[DS965Weak.DSThm965Weak]`, standard axioms.
* `scratch/ds965-weak/autofold.json` dry run: strictest GLUE 43/13 → 44/12, strict unchanged. The generated
  fold compiles (`sixContactMin_of_open30`, standard axioms).

**R16Used.AfTateCharPoly (DS 9.5.4):** only partly repaired, analysis only.
* The density/determinant half transfers per ι-component.
* The scalar case does not: the representation is the Tate module of the existential `A` and cannot be
  swapped. It needs the determinant, Ribet's irreducibility, or the strong reading, stated about the same `A`.

**Remains:**
* A locators.md row for the new leaf (proposed in the report; shared doc not edited).
* The DS 9.6.5 page check, no longer needed for this field.

Report: `docs/research/ds965-weak.md`; log: `scratch/ds965-weak/log.md`.
