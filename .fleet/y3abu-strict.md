# y3abu-strict (fleet summary)

**Verdict.**
- **(b) is done.** y3abu-print's `DeligneCanonicalModelY3Every` is split into the two printed statements, and the glue
  is proved in Lean. Hence `shimuraMainThmIDeligneY3AbU_of_strict : Y3FineModuliAb → DeligneModuliY3Every →
  DeligneReciprocityY3Every → ShimuraMainThmIDeligneY3AbU`.
  - The moduli-interpretation leaf now pins the level structure at 𝒪̂^×: η(a) = (1/3)ι(a w)(τ,1)ᵀ with w ≡ u⁻¹ mod 3.
    The inverse is forced by DCRel. Without the pin, the split is false: right translation on one component breaks
    reciprocity.
  - The reciprocity leaf says: for every Ψ with that interpretation, reciprocity holds. It makes no existence claim
    and uses only the forgetful direction of the polarization, so it does not depend on Lemma P.
  - Both every-witness forms are proved equivalent to their one-witness forms.
- **(a) cannot be done as posed**, for the same reason sir-printed found. The polarized moduli problem and the relative
  Lemma P cannot be stated in Lean: there is no polarization or dual abelian scheme over a base. Consumer restriction
  does not help, because the field itself asserts the full R1fpPropsAb.
  - Proved instead, in `ShimuraY3StrictLemmaP.lean`:
    - Lemma P for the kernel's QM tori ℂ²/Λ_τ in Riemann-form language (`lemmaP_qmTorus`). The unique principal
      Riemann form of type μ is E₀ for every τ ∈ ℍ, via an explicit j_τ.
    - The level compatibility over char-0 fields (`eq_smul_E0K`).
  - Missing: Riemann's theorem, which needs a dual abelian variety.

**Ratings.**
- `deligneReciprocityY3Every`: printed form in both readings.
- `y3FineModuliAb` and `deligneModuliY3Every`: printed form only if a polarization-free print at level K₃ is
  confirmed (Boutot–Carayol, Astérisque 196-197, ch. III §1; Buzzard 1997 §1; UNVERIFIED). From PEL prints they are
  GLUE: the relative Lemma P (cannot be stated) and Lemma P over ℂ (its core is proved).

**Compiles (VERIFIED, standard axioms).**
- `ZInQKernel/Contrib/OneProof/ShimuraY3Strict.lean` and the helper `ShimuraY3StrictLemmaP.lean`.
- `#discharges` reports DISCHARGES shimuraMainThmIDeligneY3AbU with 3 leaves remaining.
- autofold dry run (flags state only locator questions):
  - alone: strict 16/21→19/20, −1 GLUE;
  - combined with grx6ab-print and elkies-print: 16/21→22/18, −3 GLUE.
- Both fold checks compile.

**Remains.**
- The locator readings. If only PEL prints are found, set the two flags to "pending reading" and keep the field
  unfolded, since the fold would then raise the count by 1.
- The mod-3 form of the level compatibility.

Report: docs/research/y3abu-strict.md. Scratch: scratch/y3abu-strict/ (log.md, autofold*.json, dry runs, fold checks).
