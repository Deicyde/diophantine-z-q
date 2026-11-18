Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: dsThm965Printed

Verdict: CONSEQUENCE. The Lean proposition follows from the weight-at-least-two theorem printed by Deligne and Serre in 1974, Theorem 6.1, with explicit elementary dictionary steps below. No stronger mathematical clause was found against that theorem. This is not a verification of Diamond–Shurman’s Theorem 9.6.5 locator or Definition 5.8.1: the relevant book pages were not obtained.

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.dsThm965Printed` (packet R7).
- Lean constant: `DSCoeffExt.DSThm965Printed`.
- Commit of OPEN read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- Recorded classification: published; strict GLUE; good-first; unread and unverified-locator.
- Entry: [OPEN, lines 334–346](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L334-L346).
- Binding: [bundle field `OpenResearchLeaves65.dsThm965Printed`, lines 24–25](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ91.lean#L24-L25) (corrected 2026-11-18: an earlier version linked the same proposition in an older bundle generation, `TailZ65.lean`).
- Checked definition and docstring: [lines 418–452](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L418-L452).

All code references below name this same commit. This was a read-only statement check, not a compilation or proof audit. No repository files, issue threads, or reading records were changed.

## Edition, page, display

Decisive substitute source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Annales scientifiques de l’École Normale Supérieure, fourth series, volume 7, no. 4 (1974), pp. 507–530. Despite the title, §6(a) explicitly states the theorem for k ≥ 2. Read Theorem 6.1 and display (6.1.1), printed p. 520 / PDF p. 15; the Frobenius convention is on printed p. 513 / PDF p. 8, footnote (1). Standing definitions were checked on printed pp. 508–509, §§1.2–1.6; the historical source qualification is Remark 6.2 on p. 521.

Recorded historical source: P. Deligne, *Formes modulaires et représentations ℓ-adiques*, Séminaire Bourbaki, exposé 355, February 1969, published in Lecture Notes in Mathematics 179 (1971), pp. 139–172. Read the §4 standing assumptions on p. 159 / PDF p. 22; the unramifiedness statement on p. 161 / PDF p. 24, whose label is actually “COROLLAIRE 3.2” in this scan; Proposition 4.8 on p. 166 / PDF p. 29; and Theorem 4.9 on p. 167 / PDF p. 30. These are cohomological/Hecke-operator statements, not a verbatim rank-two statement over the coefficient-field completion.

Inspected but not used to justify existence: P. Deligne, *Formes modulaires et représentations de GL(2)*, Lecture Notes in Mathematics 349 (1973), pp. 55–105, author-hosted scan. The introduction, printed p. 56 / PDF p. 2, identifies its scope; it was not substituted for the global Galois-representation theorem.

Book locator still not read: F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Theorem 9.6.5 and Definition 5.8.1. No edition/page/wording of these two items is certified here. Shimura’s 1971 Theorem 7.14 was likewise not read.

## Copy

Official freely accessible NUMDAM scans of the 1971 and 1974 publications; an author-hosted Institute for Advanced Study scan of the 1973 publication. The download URLs and SHA-256 digests are listed under Sources. No unauthorized book mirror was used.

## Quote

### Deligne–Serre, Theorem 6.1, p. 520

The following is the printed text, with its mathematical notation typeset from the page image and line-break hyphenation removed:

> Soit \(f\) une forme modulaire de type \((k,\varepsilon)\) sur \(\Gamma_0(N)\), non identiquement nulle. On suppose que \(k\geq 2\) et que \(f\) est fonction propre des \(T_p\), \(p\nmid N\), avec pour valeurs propres \(a_p\). Soit \(K\) une extension finie de \(Q\) contenant les \(a_p\) et les \(\varepsilon(p)\), cf. (2.7.3). Soit \(\lambda\) une place finie de \(K\), de caractéristique résiduelle \(l\), et soit \(K_\lambda\) le complété de \(K\) en \(\lambda\).
>
> Il existe alors une représentation linéaire semi-simple continue
>
> \[\rho_\lambda:G\longrightarrow\mathrm{GL}_2(K_\lambda),\qquad\text{où }G=\mathrm{Gal}(\overline Q/Q),\]
>
> qui est non ramifiée en dehors de \(Nl\) et telle que
>
> \[(6.1.1)\qquad\mathrm{Tr}(F_{\rho_\lambda,p})=a_p\quad\text{et}\quad\det(F_{\rho_\lambda,p})=\varepsilon(p)p^{k-1}\quad\text{si }p\nmid Nl.\]

The convention on p. 513, footnote (1), is explicit:

> Nous adoptons ici les conventions d’Artin [1]. Notre « substitution de Frobenius » est donc l’élément noté \(\varphi\) dans [5]; son inverse est le « Frobenius géométrique ».

### Deligne, Proposition 4.8 and Theorem 4.9, pp. 166–167

Proposition 4.8(i) identifies \(F\) as follows; the ellipsis omits the specified cohomology group, not a condition:

> \(F\) s’identifie à l’inverse de l’élément de Frobenius ("arithmétique") \(\varphi_p\) du groupe de Galois […]

Theorem 4.9 prints the identities

> \[T_p=F+I_p^*V,\qquad FV=p^{k+1},\]
> \[1-T_pX+pR_pX^2=(1-FX)(1-I_p^*VX).\]

The p. 161 corollary ends:

> Il est non ramifié en dehors de \(n\) et de \(\ell\).

### Deligne 1973, introduction, p. 56: excluded as an existence source

> Il ne sera pas question ici des théorèmes globaux fondamentaux […]

OCR fixes: the extracted 1974 text misrecognized ε as `s`/`c`, λ as `X`, ρ as `p`, nondivisibility as `)(`, and several subscripts/exponents. The quotes above restore these symbols from the scanned images, particularly k ≥ 2, p ∤ N, p ∤ Nl, and ε(p)p^(k−1). The 1971 scan was also checked visually for the inverse Frobenius and FV = p^(k+1). No mathematical correction to the print is being proposed. Its p. 161 corollary number was left as printed rather than silently changed to 4.2.

## Standing hypotheses

1. In the 1974 paper, N is a positive integer. A form of type (k, ε) is a weight-k modular form on Γ₁(N) with the Γ₀(N) transformation law `f|ₖγ = ε(d)f`, where d is γ’s lower-right entry. Its expansion at infinity uses q = exp(2πiz). Holomorphy at all cusps is part of “modular”; vanishing there defines “parabolic”.
2. Type (k, ε) includes ε(−1) = (−1)^k. The paper explicitly observes that the opposite parity forces f = 0. The Lean normalization gives f ≠ 0, so this parity is automatic, not a missing hypothesis.
3. Theorem 6.1 assumes eigenvectors only for T_p with p ∤ N. It does not assume newness or a primitive character. It applies to noncuspidal forms as well; the Lean cusp-form case is a restriction.
4. K is a finite extension of Q containing the Hecke eigenvalues and character values. λ is a finite place with residual characteristic l. The representation uses the usual local-field topology, not the discrete topology. Neither l ∤ N nor l > 2 is required.
5. Section 3 uses the absolute Galois group. Unramifiedness is triviality on an inertia group of a place above p. The Frobenius image is defined up to conjugacy, and the adopted convention is arithmetic, as the p. 513 footnote says.
6. In Deligne’s 1971 §4, the standing parameters are k ≥ 0, n ≥ 3, and primes p, ℓ with p prime to nℓ. This k is the symmetric-power parameter; for a weight-k form in the Lean statement it is k − 2. The module in Theorem 4.9 is the parabolic cohomological Galois module constructed earlier, with Hecke operators and a pairing. It is not simply declared to be a two-dimensional K_f,λ-vector space.
7. Theorem 4.9 is unconditional. The subsequent §5 statements invoking the Weil conjectures concern bounds/Ramanujan and are not used here.

## Lean definition inventory

The following unfolds the project-defined notions to Mathlib objects or to the concrete formulas indicated. Links give the requested committed source locations without depending on a working copy.

- `CF N k` and `coeff f m`: [G9, lines 1233–1238](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L1233-L1238). `CF` is Mathlib `CuspForm` on Γ₁(N), and `coeff` is `(UpperHalfPlane.qExpansion 1 f).coeff m`. There is no separate coefficient oracle.
- `IsNormalizedEigenformDS`: [lines 50–52](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L50-L52). It asserts existence of a full `Eigenform` with underlying cusp form f, character `MulChar.toUnitHom χ`, and a₁(f) = 1. `DirichletCharacter` and restriction to units are Mathlib notions.
- Full `Eigenform`: [lines 77–91](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Eigenform.lean#L77-L91). It extends Mathlib `CuspForm`, carries a unit-group character, membership in its character space, an eigenvalue at every positive index, the corresponding T_n equation, and nonvanishing. Bad primes are included; newness is not. Its [lines 251–256](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Eigenform.lean#L251-L256) identify normalized coefficients with eigenvalues.
- Character space: [lines 280–296](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L280-L296). It is the intersection of the Mathlib eigenspaces of all diamond operators. The operators are [translation by Γ₀(N) representatives, lines 202–240](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L202-L240), with index given by the lower-right entry. Thus the character is χ(d), not its inverse in the transformation law.
- Hecke action: [lines 308–310 and 394–405](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Action.lean#L308-L405). This is a Mathlib `Finsupp.linearCombination` of concrete twisted double-coset operators, packaged as a ring homomorphism into `Module.End` of the cusp character space. The [cusp operator, lines 175–195](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/ModularForm.lean#L175-L195) has the stated slash sum as its underlying function.
- Concrete slash sum: [lines 92–124](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Basic.lean#L92-L124). It is a finite sum `Σᵥ χ(aᵥ,upper-left) · (f|ₖaᵥ)`. The character is [the composition in lines 69–70](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/NebentypusChar.lean#L69-L70); the integral witness and its upper-left unit are [lines 133–160](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Delta0.lean#L133-L160). Γ₀(N), Γ₁(N), matrices, and eigenspaces stop at Mathlib; rational slashing crosses the following explicit bridge.
- Rational slash action: [lines 95–110](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/SlashActionRat.lean#L95-L110) define the scoped `ratSlashAction` by Mathlib `monoidHomSlashAction` along `Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)`. It is definitionally the Mathlib real slash at the entrywise real image. The [positive-determinant formula, lines 132–138](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/SlashActionRat.lean#L132-L138), is `f(gz) |det g|^(k−1) (cz+d)^(−k)`. In the prime Hecke sum, this gives the `1/p` translated terms and the `χ(p)p^(k−1) f(pz)` term, matching the printed (1.6.1), with no extra weight normalization.
- Coset indexing: [lines 421–422](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/Basic.lean#L421-L422) give a subgroup quotient, and [lines 695–697](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/Basic.lean#L695-L697) give aᵥ = δτᵥ⁻¹. `HeckeCoset` itself is imported from Mathlib’s Hecke-ring definitions, rather than being a new project hypothesis. The concrete semigroup Δ₀(N) is [lines 77–80](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Delta0.lean#L77-L80): positive-determinant integral matrices, lower-left entry divisible by N, upper-left entry a unit modulo N.
- T_n: [lines 119–120](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/Diagonal/Composite.lean#L119-L120) form the product of prime-power blocks. The product is [lines 111–112](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/Data/Nat/Factorization/PrimePowerProd/Basic.lean#L111-L112), using Mathlib’s prime-power recursion. The blocks are [lines 179–184](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/Diagonal/PrimePower.lean#L179-L184): 1, T_p, then `T_p T_{p^(r+1)} − p S_p T_{p^r}`. T_p and S_p are the diagonal classes [lines 94–107](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/Diagonal/PrimePower.lean#L94-L107).
- Diagonal classes: [lines 69–72](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/Diagonal/Elem.lean#L69-L72) and [lines 93–95](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/Diagonal/Coset.lean#L93-L95) construct the single double-coset class with positivity/coprimality guards. The actual rational diagonal matrix is [lines 72–80](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/HeckeRing/GLn/DiagonalCosets.lean#L72-L80). Positive-index eigenconditions do not use the junk zero-index branch.
- Coefficient-form dictionary: [lines 124–126](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L124-L126) prove equivalence with the coefficient predicate at [G9, lines 1241–1252](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L1241-L1252): the nebentypus transformation law, a₁ = 1, and the usual divisor-sum Hecke coefficient relation. The prime-square identity used below is [lines 497–505](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L497-L505).
- `coeffField f`: [lines 350–354](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L350-L354). It is Mathlib `IntermediateField.adjoin ℚ (Set.range (coeff f))`, a subfield of ℂ, with explicit membership of each a_n. The zero coefficient does not enlarge this field for a cusp form. `NumberField`, its ring of integers, `HeightOneSpectrum`, `asIdeal`, and `adicCompletion` stop at Mathlib. Finiteness is an assumption in this particular proposition, not an additional conclusion being attributed to the theorem.
- Absolute Galois group: [G9, lines 736–739](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L736-L739). `Qbar` is Mathlib `AlgebraicClosure ℚ`; `GQ` is its ℚ-algebra automorphism group with the Krull topology.
- Place and Frobenius: [G9, lines 743–747](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L743-L747). `LiesOver v p` means p belongs to the nonunits of the valuation subring v. `IsArithFrob σ v p` means σ belongs to its decomposition group and σ(x) − x^p belongs to those nonunits for every x in v. These are concrete predicates, with decomposition/inertia subgroups and nonunits supplied by Mathlib.
- Representation and unramifiedness: [lines 439–442](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L439-L442). The proposition uses a raw group homomorphism `GQ →* GL (Fin 2) K_f,λ`, not an opaque attachment predicate or the separate `GaloisRep` bundle. GL is the units of the matrix ring; continuity and identity are Mathlib notions. Every inertia element above a good p must map to 1.
- Polynomial conclusion: [lines 443–452](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L443-L452). `Matrix.charpoly`, `Polynomial.X`, `Polynomial.C`, `algebraMap`, and `Polynomial.aeval` stop at Mathlib. The two alternatives are literally characteristic-polynomial equality and matrix annihilation by the displayed polynomial; there is no additional project-defined characteristic polynomial.

## Comparison

### 1. Quantifier order and the representation

The Lean chooses one continuous representation for fixed N, k, χ, f, l, λ, before quantifying over p, valuation subrings, Frobenius lifts, or b. Theorem 6.1 likewise supplies one representation for each form, coefficient field, and finite place, with its properties at all good primes. It even supplies semisimplicity, which the Lean does not demand. There is no hidden choice of a different representation for each p or each polynomial coefficient.

### 2. Level, weight, character, and eigenform

`[NeZero N]` means N > 0 for natural N, matching positive level. `k : ℤ` with `2 ≤ k` matches the weight range. The full eigenform and a₁ = 1 imply nonvanishing, the correct nebentypus, and the T_p eigenrelations required by the print. Requiring all T_n, including U_p at p dividing N, restricts the allowed forms compared with Theorem 6.1; it does not strengthen its conclusion. The prime eigenvalue is a_p(f), because a₁ = 1. The good-prime coefficient formula in the paper’s (1.6.1) is the same normalization as the checked coefficient dictionary. No newform or character-primitivity hypothesis is missing.

The parity convention is not dropped: slashing by −I and nonvanishing force χ(−1) = (−1)^k. This agrees with the paper’s §1.5, including small levels.

### 3. The apparently smaller coefficient field

The print permits any finite K containing a_p and ε(p). Taking K = `coeffField f` is justified, not an unexplained descent from an algebraic closure. Each a_n belongs to K by definition. The already proved coefficient dictionary and prime-square identity give

\[a_p(f)^2-a_{p^2}(f)=\chi(p)p^{k-1}.\]

Consequently χ(p)p^(k−1) belongs to K. Since p ≠ 0 and K contains Q, division by p^(k−1) gives χ(p) in K for every good prime. At a bad prime the zero-extended character is zero. If all unit-group character values are desired, represent a unit class by a positive integer prime to N and factor it into primes prime to N. Multiplicativity gives those values in K as well.

The Lean explicitly assumes that K is a number field. This is stronger input than merely having the abstract coefficient subfield, and is exactly what licenses the finite-place/completion constructions. No extra coefficient-field existence or Schur-index hypothesis is needed to apply Theorem 6.1.

### 4. λ and the completion

A member of `HeightOneSpectrum (𝓞 K)` is a nonzero prime ideal; for the ring of integers of a number field it is maximal. Containing the rational prime l says that its finite place has residual characteristic l. Mathlib’s adic completion is the completion of K at this place, with its valuation topology. Identifying the concrete Mathlib completion with the printed K_λ is the usual completion dictionary; a change in normalization of the valuation does not change its topology. Both statements are over K_λ itself, not merely over Q̄_l or an unspecified larger extension.

### 5. Good primes

For prime p and prime l, `¬ p ∣ N * l` is exactly p ∤ N and p ≠ l, the print’s p ∤ Nl. The same set is excluded for both unramifiedness and the polynomial. Neither statement imposes l ∤ N, l odd, or a condition at p = l. Levels 1 and 2 are allowed in the decisive Theorem 6.1; the auxiliary n ≥ 3 used in the 1969 cohomological construction must not be mistaken for a hypothesis on this Lean level.

### 6. Every valuation subring and every Frobenius lift

For a valuation subring of Q̄, having p as a nonunit is the algebraic description of a place above p. Its restriction to Q is the p-adic place, and these places correspond to primes of the algebraic integers above p. Thus this quantifier does not introduce unrelated valuations.

Inertia groups above a fixed rational prime are conjugate. Triviality on one gives triviality on each. At one place, two arithmetic Frobenius lifts differ by inertia, so an unramified representation has the same image for them; changing the place conjugates the image. Characteristic polynomials and annihilating polynomial identities are conjugacy invariant. This explains the Lean’s universal quantification over v and σ without an extra ramification assumption.

### 7. Arithmetic versus geometric Frobenius

The Lean residue action is x ↦ x^p: arithmetic Frobenius. This agrees exactly with Deligne–Serre’s p. 513 footnote. There is no convention mismatch with Theorem 6.1 and no need to invert its matrix.

There is a normalization difference if one uses Deligne 1969/1971 literally: his F in Theorem 4.9 is φ_p^(-1), geometric Frobenius on cohomology. It is not legitimate simply to rename that F as the Lean’s σ. A contragredient representation converts a geometric-Frobenius matrix into the transpose of the arithmetic-Frobenius matrix on the dual: if ϱ is the cohomological representation, then ϱ^∨(φ_p) = ϱ(φ_p^(-1))^t. This is a further dictionary step, alongside extraction of the relevant rank-two coefficient-field representation. Theorem 6.1 already packages the appropriate arithmetic normalization and coefficient field.

### 8. Polynomial, power, sign, and the conditional b

For a two-by-two matrix M,

\[\operatorname{charpoly}(M)=X^2-\operatorname{Tr}(M)X+\det(M).\]

Inserting (6.1.1) gives exactly the Lean’s X² − a_p X + χ(p)p^(k−1) after the canonical map K → K_λ. The paper’s Euler-polynomial notation `det(1 − MT)` is reciprocal to the characteristic polynomial: `X² det(1 − M/X)`. It must not be compared as if it were already `det(XI − M)`. There is no sign error, reciprocal determinant, or off-by-one power in the Lean.

In the 1971 congruence formula, substituting the symmetric-power parameter k − 2 turns p^(r+1) into p^(k−1), as required. Its operator-valued polynomial is not itself a declaration of a rank-two characteristic polynomial.

The Lean’s b quantifier is conditional on `(b : ℂ) = χ(p)p^(k−1)`. Such a b exists, by the prime-square identity, and is unique, because K is a subfield of ℂ. This is not a vacuous workaround for a coefficient that might fail to belong to K. The quantifier does not require selecting unrelated constants for different lifts.

### 9. The disjunction is weaker than the printed trace/determinant statement

Theorem 6.1 yields characteristic-polynomial equality by the two-by-two identity. The left disjunct then gives the Lean conclusion by `Or.inl`. Cayley–Hamilton is not needed for this direction. The right disjunct, matrix annihilation alone, is generally weaker than characteristic-polynomial equality; no converse is asserted here.

## Verdict

CONSEQUENCE, with the further steps named explicitly:

1. Use the checked full-eigenform/coefficient dictionary to identify the good T_p eigenvalues as a_p(f) and obtain χ(p) in K_f by the prime-square identity.
2. Apply the printed Deligne–Serre Theorem 6.1 with K = K_f and the finite place corresponding to λ.
3. Translate the completion, valuation-subring, inertia, and Frobenius-lift notation as above.
4. Use the elementary two-by-two characteristic-polynomial formula and introduce the left disjunct.

These steps do not require a new research assertion. The 1974 theorem is a suitable precise printed citation for the mathematical content of this leaf. The actual Diamond–Shurman locator remains unverified; this report does not manufacture a YES for a book page it did not read. Deligne’s 1971 Theorem 4.9 alone is not the docstring’s claimed verbatim K_f,λ statement obtainable merely by or-introduction.

## False, incomplete or unclear

No false Lean clause or omitted hypothesis was found against Theorem 6.1. The incompleteness is bibliographic and certificate-level: the exact Diamond–Shurman pages remain unread, and the 1969/1971 congruence theorem requires more than or-introduction to supply a rank-two coefficient-field representation in the arithmetic normalization.

The 1974 introduction and Remark 6.2 explicitly discuss the then-incomplete publication of proofs of the general construction. Theorem 6.1 itself is printed unconditionally. This report compares its statement and does not claim to audit or replace its proof, or to settle historical proof-publication questions.

## Not read

- Diamond–Shurman Theorem 9.6.5, Definition 5.8.1, and their chapter proofs; Shimura 1971 Theorem 7.14.
- The full constructions and proofs in Deligne 1969/1971; the page readings used here are specified above. In particular, a rank-two coefficient-field extraction was not certified directly from its bulk cohomological module.
- Deligne–Serre’s §2.7 proof and the systematic proofs in §§5–9; the coefficient field’s finiteness is an input to this Lean proposition, and no reliance on §2.7 to prove it was needed.
- Deligne 1973 beyond the introduction/scope check and a search of its extracted text; it was not used as the global existence theorem.
- Mathlib’s implementation proofs beyond the named stopping points, or any compiler verification of the project’s already proved dictionary lemmas. The target’s downstream uses and the proof of the final theorem were outside this one-row check.

## AI use

An AI language model located the sources, read the committed Lean text and scanned pages, produced the transcriptions, performed the comparison, and wrote this report. `curl` downloaded the legitimate PDFs; `pdftotext` supplied searchable extraction. Mathematical symbols and relevant wording were checked against rendered scan images rather than accepted from OCR alone. No human reading is asserted.

## Evidence

AI-READ. The substitute theorem and cited historical pages were read as specified. This report is not HUMAN-READ evidence, does not certify the unread Diamond–Shurman page, and makes no claim to clear a reading or locator flag. Any effect on the project’s reading ledger or classification is for its reviewer/maintainer.

## Sources and acquisition record

1. Deligne–Serre 1974 — decisive theorem and conventions
   - PDF: https://www.numdam.org/item/ASENS_1974_4_7_4_507_0.pdf
   - SHA-256: `65b390f6d33e827e30c6c66bbc15421eca51db3180bdf5996dcee19047be97fc`
   - Quote: Theorem 6.1/(6.1.1), printed p. 520; Frobenius footnote (1), p. 513. PDF includes a cover page.
   - Its bibliography [4], p. 530, identifies Deligne’s Bourbaki 355 as the historical source of the construction.
2. Deligne 1969/1971 — recorded historical print and convention contrast
   - Landing page: https://www.numdam.org/item/SB_1968-1969__11__139_0/
   - PDF: https://www.numdam.org/item/SB_1968-1969__11__139_0.pdf
   - SHA-256: `19509c19b0cb056f4a5eba83a48a99f54bb6df0c7a96ab7f4018b0765e1ed98c`
   - Quotes: p. 161, printed Corollaire 3.2; p. 166, Proposition 4.8(i); p. 167, Theorem 4.9. PDF includes a cover page.
3. Deligne 1973 — inspected, excluded as the existence citation
   - Author’s publication page: https://publications.ias.edu/deligne/paper/366
   - PDF: https://publications.ias.edu/sites/default/files/Number21.pdf
   - SHA-256: `4e735ca05197f215f4d45cf485d45c1f646b3b1efd1f4a4a5a399524a02e624b`
   - Scope quote: introduction, printed p. 56 / PDF p. 2. This hash is recorded for acquisition completeness, not as additional evidence of the target theorem.

Attempts to obtain the book legitimately: the author’s page https://people.reed.edu/~jerry/ links the Springer volume and printing-specific errata, not a free volume. The publisher’s book page https://link.springer.com/book/10.1007/978-0-387-27226-9 and chapter page https://link.springer.com/chapter/10.1007/978-0-387-27226-9_9 were checked. Its free preview, https://page-one.springer.com/pdf/preview/10.1007/978-0-387-27226-9_9, exposes the beginning of the chapter, not Theorem 9.6.5. Author errata were inspected but did not supply the target statement. The older Diamond author-page link returned an unavailable response, and a candidate newer author address returned 404. A Google Books preview request did not expose the target page text. These attempts did not establish a legitimate obtainable copy of the required book pages; no book PDF hash or book-page quote is invented. Unrelated mirrors appearing in searches were not downloaded.
