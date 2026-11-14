# shimura-glue: Deligne's `π₀` leaves in printed form, with the reduced-norm computation in Lean

Task shimura-glue, 2026-11-14. Base 15fc1527 (wip/w60). Lean: `scratch/shimura-glue/`, results log `log.md`.
No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model work, no human
review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (there is no
network on this host).

## 1. Main result

**Both Deligne leaves of shimura-split are now theorems from Deligne's theorem in printed form, plus an
exact computation that is compiled.** VERIFIED: compiled, standard axioms.

* **The printed form.** `ShimuraGlue.DelignePi0 Y K` is the display of Deligne's theorem on connected
  components for `G = B^×`, `B = (2, −3 | ℚ)`:
  * a bijection `π₀(Y ×_ℚ ℚ̄) ≃ ℚ^×_{>0} \ 𝔸_f^× / nrd(K)`;
  * under it, `σ ∈ Aut(ℚ̄/ℚ)` acts by multiplication by `[u]^ε`, for every idele `u` whose `p`-components are
    the `p`-adic cyclotomic characters `χ_p(σ)`, with a fixed sign `ε = ±1`.

  It is stated over Mathlib's own objects:
  * `FiniteAdeleRing ℤ ℚ` for `𝔸_f`;
  * `QuaternionAlgebra 𝔸_f 2 0 (−3)` for `B ⊗ 𝔸_f`, with `nrd(x) = x x̄`;
  * `𝒪̂ = 𝒪 ⊗ ℤ̂`, the `ℤ̂`-span of the kernel's basis `1, i, (1+j)/2, (i+k)/2`;
  * Mathlib's `cyclotomicCharacter` and `padicEquiv : ℚ_v ≅ ℚ_p`;
  * Mathlib's `ConnectedComponents` of the scheme `Y ×_{Spec ℚ} Spec ℚ̄`, with `σ` acting by `id × Spec σ`.
* **The two leaves** (`Deligne.lean`, §4):
  * `DeligneComponentsY3Printed`: some fine witness `(Y, Φ)` (`R1fpProps`, the canonical model `Y₃ = Sh_{K₃}`)
    satisfies `DelignePi0 Y K3`. Here `K3 = ker(𝒪̂^× → (𝒪̂/3𝒪̂)^×)` is the level of the kernel's `Level3`.
  * `DeligneComponentsX6Printed`: some coarse witness (`X6Props`, `X₆ = Sh_{𝒪̂^×}`) satisfies
    `DelignePi0 X Kfull`, where `Kfull = 𝒪̂^×`.
* **The computations** (`Adelic.lean`, Mathlib only; §3):
  * `nrd(𝒪̂^×) = ℤ̂^×` and `nrd(K₃) = U₃ := ℤ̂^× ∩ (1 + 3ℤ̂)`. These are the local representations of every
    unit of `ℤ_p` by the reduced norm of `𝒪_p`, at every prime `p`, by Hensel's lemma. At `p = 3` a unit
    `≡ 1 mod 3` is the square of an element `≡ 1 mod 3`. The local pieces are assembled into ideles.
  * `𝔸_f^× = ℚ^×_{>0} · ℤ̂^×`, with `ℚ^×_{>0} ∩ ℤ̂^× = 1`.
  * Hence:
    * `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×)` is a point (`pi0_Kfull_eq_one`);
    * `ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×` by `q·u ↦ u₃ mod 3` (`pi0K3Equiv`);
    * the cyclotomic idele of `σ` maps to Mathlib's `modularCyclotomicCharacter` at 3 (`chi_cycU`).
* **The theorems** (`Deligne.lean`):
  * `deligneComponentsY3_of_printed : DeligneComponentsY3Printed → ShimuraSplit.DeligneComponentsY3`;
  * `deligneComponentsX6_of_printed : DeligneComponentsX6Printed → HDec.QMSplit.Moduli.DeligneComponentsX6`.

  The targets are shimura-split's statements, copied verbatim (`mk_deligne.py`).
* **The bundle** (`RowsGlue.lean`, over `TailK`). `ShimuraGlueLeaves` is `ShimuraSplitLeaves` with the two
  printed Deligne leaves in place of the old two. `rows_of_shimuraGlueLeaves` gives the same six rows: `r1r2`,
  `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel`. The file has 59 `#print axioms` lines, all
  `[propext, Classical.choice, Quot.sound]`.
* **Not changed: the other four leaves.** `ReciprocityCanonical`, `ElkiesConicX6`, `BabaGranathX6'` and
  `ShimuraHolFamily` remain consequences of one printed theorem each. §5 gives, for each, the printed
  statement, the step from it to the leaf, and the definitions that a printed-form Lean statement would need.
  None of these definitions exists in Mathlib 4.35 or in the kernel, except the class-field part of
  `ReciprocityCanonical`, which the vendored Tau Ceti now supplies (§5.1).
* **`r3`** (`R03_LinYang`, over `ℂ`). Two definitions are missing (§6):
  * a principal polarization on `PkgI3.AbVar`, which needs the dual abelian variety;
  * the coarse moduli bijection on `ℂ`-points (`X6Props` is over `ℚ̄` only).

## 2. The six leaves of the task

| leaf (shimura-split) | new leaf (form; source) | glue (status) | Lean name of the proof |
|---|---|---|---|
| `DeligneComponentsY3` | `DeligneComponentsY3Printed` (**printed form**, reading in §4: Deligne, Bourbaki 389 (1971), Thm 2.4 and §3; PSPM 33 (1979), 2.1.3 and 2.6.3; Milne 2005, Thms 5.17, 13.6; UNVERIFIED) | `ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×`, `χ(χ_cyc(σ)) = χ₃(σ)` (**proved**) | `ShimuraGlue.deligneComponentsY3_of_printed` |
| `DeligneComponentsX6` | `DeligneComponentsX6Printed` (**printed form**, same source, level `𝒪̂^×`) | `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` and "π₀ a point ⇒ connected" (**proved**) | `ShimuraGlue.deligneComponentsX6_of_printed` |
| `ReciprocityCanonical` | unchanged (consequence; §5.1) | — | — |
| `ElkiesConicX6` | unchanged (consequence; §5.2) | — | — |
| `BabaGranathX6'` | unchanged (consequence, or printed form if Baba–Granath's `j` is the coordinate normalized by the three CM values; §5.3) | — | — |
| `ShimuraHolFamily` | unchanged (consequence; §5.4) | — | — |
| `r3` | not split; missing definitions in §6 | — | — |

## 3. The computation in Lean (`Adelic.lean`, Mathlib imports only)

### 3.1 Objects (all over Mathlib definitions)

| Lean | meaning |
|---|---|
| `Af := FiniteAdeleRing ℤ ℚ`, `Place := HeightOneSpectrum ℤ` | `𝔸_f`, the finite places |
| `BR R := QuaternionAlgebra R 2 0 (-3)`, `BAf := BR Af` | `B ⊗_ℚ R` (for `R = ℚ` this is the kernel's `LeafQM.B`) |
| `nrdQ R : BR R →* R`, `nrdQ_eq_mul_star : ↑(nrdQ x) = x * star x` | the reduced norm |
| `ofQ n = n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2`, `mulCoordR`, `ofQ_mul` | the kernel's `LeafQM.ofInt` and `mulCoord`, over any `ℚ`-algebra |
| `Zhat : Subring Af` | `ℤ̂`: integral at every place |
| `Ohat : Subring BAf` | `𝒪̂ = 𝒪 ⊗ ℤ̂` |
| `ZhatU`, `U3` | `ℤ̂^×`, `{u ∈ ℤ̂^× : u ∈ 1 + 3ℤ̂}` |
| `Kfull`, `K3` | `𝒪̂^×`, `{k ∈ 𝒪̂^× : k ∈ 1 + 3𝒪̂}` |
| `posRat`, `nrdU`, `Pi0 K := Afˣ ⧸ (posRat ⊔ K.map nrdU)` | `ℚ^×_{>0}`, `nrd` on units, `ℚ^×_{>0}\𝔸_f^×/nrd(K)` |
| `cycU g` | the idele `(cyclotomicCharacter L p g)_p ∈ ℤ̂^×` |

### 3.2 Local part (`ℤ_p`, Mathlib's Hensel lemma)

In the coordinates of `ofQ`, `nrd = N4(n) = (n₀² + n₀n₂ + n₂²) − 2(n₁² + n₁n₃ + n₃²)` (`nrdQ_ofQ`). Then:

* `rep_unit`: every unit of `ℤ_p` is `N4(n)` for some `n ∈ ℤ_p⁴`, at every prime `p`.
  * `p = 2`: `a² + a + 1`, Hensel at `a = 0`.
  * `p = 3`: `x² − 2y²`, with `y ∈ {0, 1}` by the residue, then Hensel in `x`.
  * `p ≥ 5`: `4(a² + ab + b²) = (2a + b)² + 3b²`. Solve `x² + 3y² = 4u` mod `p` by Mathlib's
    `FiniteField.exists_root_sum_quadratic`, then lift in a variable with nonzero residue.
* `sq_three`: a unit `u ≡ 1 mod 3` of `ℤ_3` is `x²` with `x ≡ 1 mod 3`.
* `rep_unit3`: every unit (`≡ 1 mod 3` if `p = 3`) is `N4(e₀ + 3n')`, where `e₀` are the coordinates of 1.

### 3.3 Global part

* `nrd_Kfull_le`, `ZhatU_le`: `nrd(𝒪̂^×) = ℤ̂^×`. Local representations at every place, transported by Mathlib's
  `padicIntEquiv` and assembled by the ring hom `adeleHom : ∏_v ℤ_p → 𝔸_f` (`exists_unit_of_nrd`: an element
  of `𝒪̂` with reduced norm in `ℤ̂^×` is a unit of `𝒪̂`, with inverse `x̄ · nrd(x)⁻¹`).
* `nrd_K3_le`, `U3_le`: `nrd(K₃) = U₃`. The inclusion `⊆` is the identity
  `nrd(1 + 3y) = 1 + 3(tr y + 3 nrd y)`.
* `exists_decomp`, `posQ_ZhatU`, `decomp_unique`: `𝔸_f^× = ℚ^×_{>0} ℤ̂^×` with unique factors.
  * The rational factor is `∏_{v ∈ S} p_v^{v(s_v)}` over the finite set `S` of places where `s` is not a local
    unit. The `p`-adic norms then show that the quotient is a unit everywhere.
  * Uniqueness: a positive rational that is a `p`-adic unit at every `p` has numerator and denominator 1.
* `chi : 𝔸_f^× →* (ℤ/3)^×`, `q·u ↦ u₃ mod 3`. It is a hom by uniqueness of the factors.
  * `chi_ker : ker chi = ℚ^×_{>0} ⊔ nrd(K₃)`.
  * `chi_surjective`: `chi(−1) = −1`.
  * `pi0K3Equiv : Pi0 K3 ≃* (ℤ/3)^×`, with `pi0K3Equiv (mk s) = chi s` by `rfl`.
* `pi0_Kfull_eq_one` (so `Subsingleton (Pi0 Kfull)`): `s = q·u` with `u ∈ ℤ̂^× = nrd(𝒪̂^×)`.
* `chi_cycU : chi (cycU g) = modularCyclotomicCharacter L hn g`.
  * The 3-component of `cycU g` is Mathlib's `cyclotomicCharacter L 3 g`.
  * Its residue mod 3 is the mod-3 character. This uses `cyclotomicCharacter.spec` at `n = 1`,
    `modularCyclotomicCharacter.unique`, and the congruence of `toZMod` and `toZModPow 1` modulo the maximal ideal
    (`toZMod_cyc_three`).

## 4. The printed leaves and their reading (`parts/DeligneNew.lean`)

```lean
def DelignePi0 (Y : Over (Spec (CommRingCat.of ℚ))) (K : Subgroup BAfˣ) : Prop :=
  ∃ (c : ConnectedComponents (ShimuraSplit.baseQbar Y) ≃ Pi0 K) (ε : ℤˣ),
    ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (u : Afˣ),
      (∀ v : Place, (u : Af) v = (adicCompletion.padicEquiv v).symm
        (cyclotomicCharacter Qbar (primesEquiv v) σ.toRingEquiv : ℚ_[primesEquiv v])) →
      ∀ z, c (ShimuraSplit.galActπ₀ Y σ z) = (QuotientGroup.mk u : Pi0 K) ^ (ε : ℤ) * c z

def DeligneComponentsY3Printed : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ DelignePi0 Y K3

def DeligneComponentsX6Printed : Prop :=
  ∃ Y Φ X Ψ fY, R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull
```

### 4.1 The printed statement

STANDARD; locators UNVERIFIED (no network):
* Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), Thm 2.4 and §3;
* Deligne, *Variétés de Shimura*, PSPM 33 (1979), Part 2, 2.1.3 and Thm 2.6.3;
* Milne, *Introduction to Shimura varieties* (2005), Thm 5.17 and Thm 13.6.

For `G^der` simply connected, `π₀(Sh_K(G,X)_ℂ) = G(ℚ)_+\G(𝔸_f)/K ≅ T(ℚ)^†\T(𝔸_f)/ν(K)`, with `T = G/G^der`, and
`Aut(ℂ/ℚ)` acts on it through the reciprocity map.

For `G = B^×`: `G^der = SL₁(B)` is simply connected, `ν = nrd`, `T = 𝔾_m` and `T(ℚ)^† = ℚ^×_{>0}`.

### 4.2 Reading (SPECULATIVE judgements; the reasons are standard)

1. **The witness is `Sh_K`.** The canonical models are rendered, as in every leaf of the bundle, as "some
   witness of the moduli clause lists".
   * Fine witnesses are unique up to unique isomorphism (qm-split's `compare_iso`), and so are coarse witnesses
     (`CoarseCompare`), so the existential is not stronger than the print together with R1.
   * `K3` is the level of the kernel's `Level3`: `η : 𝒪/3𝒪 ≅ A[3]`, `𝒪`-linear. The automorphisms of the left
     module `𝒪/3𝒪` are right multiplications by `(𝒪/3𝒪)^×`, so the level group is
     `ker(𝒪̂^× → (𝒪̂/3𝒪̂)^×)`.
2. **The reciprocity map of `ℚ` is written through the cyclotomic character.**
   * `art_ℚ(u)`, for `u ∈ ℤ̂^×`, acts on `μ_∞` by `ζ ↦ ζ^{u^{∓1}}`, the sign depending on the normalization. So
     the ideles `s` with `art(s) = σ|ℚ^ab` are `ℚ^×_{>0} u^{±1}`, where `u = (χ_p(σ))_p`.
   * The fixed sign `ε` absorbs both the normalization of `art` and the left/right convention of `galActπ₀`.
   * The idele `u` is determined by `σ` (by its components), so the quantifier `∀ u` ranges over one element.
     The derivation instantiates `u := cycU σ`.
3. **`π₀` is the Zariski `π₀` of the scheme `Sh_K ⊗ ℚ̄`.** For a scheme of finite type over an algebraically
   closed field this equals `π₀(Sh_K(ℂ))` (base change of algebraically closed fields, then GAGA).
4. **Consistency checks (VERIFIED by the computation).**
   * `Pi0 K3` has 2 elements and `σ` acts through `χ₃`, so the geometric components of `Y₃` are defined over
     `ℚ(ζ₃)` and swapped by complex conjugation. This matches ts-hecke's `pi0_check.py` (two orbits in
     Shimura's uniformization).
   * `Pi0 Kfull` is a point, so `X₆` is geometrically connected.

The leaves are therefore the printed display for this `G`, in the explicit form (2) of the reciprocity law, and
are not stronger than the print.

### 4.3 Proofs (`Deligne.lean`)

* `deligneComponentsY3_of_printed`. Compose `c` with `pi0K3Equiv`. Then
  `pi0K3Equiv([u]^ε · w) = chi(u)^ε · pi0K3Equiv(w)`, and `chi(cycU σ) = chi3 σ` (`chi_cycU` with shimura-split's
  `card_mu3`). Finally `x^ε = x` on `(ℤ/3)^×` (`zmod3_zpow`).
* `deligneComponentsX6_of_printed`. `Pi0 Kfull` is a subsingleton, so `π₀(X_ℚ̄)` is too. `X_ℚ̄` is nonempty,
  from the `ℚ̄`-point of `X6Props` and `pullback.lift`. A nonempty space with subsingleton `π₀` is connected
  (`connectedSpace_of_subsingleton`).

## 5. The other four leaves: printed statements and what is missing

Each remains a consequence of one printed theorem. For each, below: what is printed, what the leaf adds, and
what a printed-form statement in Lean would need.

### 5.1 `ReciprocityCanonical` (Shimura reciprocity at three CM points)

* **Printed.** Shimura, Ann. of Math. 85 (1967), Main Thm I. Also Deligne 1971, §3, and Milne 2005, §12-13, the
  reciprocity law at special points (locators UNVERIFIED).
  * For a CM point `x = [h_k, g]` of `Sh_K` with `k ↪ B`, `k(x)` is the class field of `k` attached to
    `k^× · {s ∈ 𝔸_{k,f}^× : ι(s) ∈ gKg^{-1}}`.
  * `σ = art_k(s)` acts by `[h_k, g] ↦ [h_k, ι(s)g]`.
* **The step to the leaf.** The leaf says that `ℚ(y)` is unramified above every `p ≥ 5`, for `y` with CM by
  `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`. It takes three further steps:
  1. A computation: `ι^{-1}(gK₃g^{-1}) ⊇ 1 + 3𝒪̂_k` for an optimal embedding of the maximal order. Hence
     `k(y) ⊆` the ray class field of `k` of conductor 3.
  2. Ray class fields are unramified outside the modulus.
  3. `disc(k) ∈ {−4, −3, −24}`, and discriminants behave in towers.
* **Missing for a printed form.**
  * The adelic uniformization `Y₃(ℂ) ≅ B^×\(ℍ^± × (B ⊗ 𝔸_f)^×/K₃)`. It is not in Lean; the kernel has only
    ShimuraFam's holomorphic families.
  * The Artin map of an imaginary quadratic field. Mathlib 4.35 has none.
* **Available now (VERIFIED by reading the files).** The kernel's vendored Tau Ceti has
  `TauCeti.ClassFieldTheory.rayClassField`, `rayClassArtinEquiv`, and `IsAdmissibleModulus.isUnramifiedAway`
  (ray class fields are unramified away from the modulus)
  (`ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/ClassFields/RayClassField.lean`). Mathlib has
  `NumberField.discr_dvd_discr` and `not_dvd_discr_iff_isUnramifiedIn`.
* **What these would give.** A smaller consequence leaf, "`k·ℚ(y)` embeds in `rayClassField k (3)`", from
  which steps 2-3 are provable glue. That leaf is the classical form of Shimura's theorem on CM points: the
  printed law, with the class field identified.

  Not attempted in this run (see §8).

### 5.2 `ElkiesConicX6` (the conic model of `X₆`)

* **Printed.** Elkies, ANTS-III, LNCS 1423 (1998), §3 (locators UNVERIFIED):
  * `X*(6) = X₆/W` has a coordinate `t` with `t = 0, 1, ∞` at the CM points of discriminants −24, −4, −3;
  * `X₆` is the `(ℤ/2)²`-cover `X*(6)(√−t, √(3(t−1)))`.

  Kurihara 1979 gives `X₀(6,1) : x² + y² + 3 = 0`.
* **The step to the leaf.** The leaf uses Baba–Granath's `j` and the conic `Y² + 3X² + 3Z² = 0`. It takes two
  computations:
  * the substitution `X/Z = √−t`, `Y/Z = √(3(t−1))`, which gives `t = −X²/Z²`;
  * the Möbius map `j = 16(t−1)/27`, fixed by the three CM values.
* **Missing for a printed form.**
  * Elkies' statement is about function fields: `ℚ(X₆) = ℚ(t)(√−t, √(3(t−1)))`. Mathlib has
    `Scheme.functionField`, but there is no comparison between `ℚ̄`-points of a proper smooth curve and places
    of its function field. The kernel's curve-glue results do not include it. Without that comparison, the
    function-field statement does not give `X₆(ℚ̄) ≃ C(ℚ̄)`.
  * A Möbius action on the kernel's `ToP1`, that is, new charts for `a t + b`. It is not in the kernel.
    (SPECULATIVE: a few hours of work; it would let the leaf be stated in Elkies' `t`, removing its dependence
    on Baba–Granath's normalization.)

### 5.3 `BabaGranathX6'`

* **Printed.** Baba–Granath, Canad. J. Math. 60 (2008) (audit YES for these three):
  * Thm 2.1, p. 737: the polarized moduli space is `V/W`;
  * Lemma 3.1, pp. 739-740: `V/W ≅ P¹_ℚ`, and the three distinguished images are rational;
  * the §3.1 table, p. 740: each of `CM(−4)`, `CM(−3)`, `CM(−24)` is one `W`-orbit.

  The values `j = 0, ∞, −16/27` are located by the audit only near Prop. 3.9/Thm 3.10 and Cor. 3.11,
  pp. 744-745 (locators.md: "Theorem 2.1/Lemma 3.1 alone also do not locate the numerical j-normalization").
* **Form.** The leaf is the conjunction of these printed statements, on one witness and one coordinate.
  * If Baba–Granath's `j` is the coordinate of `V/W` normalized by those values, the leaf is in printed form
    (a conjunction).
  * If instead `j` is defined through Igusa invariants (Prop. 3.6), the leaf is a consequence: it pins `j` by
    the CM values, which is the same coordinate by the uniqueness of the Hauptmodul (`MobiusGlue`).

  Which of the two holds is SPECULATIVE until the paper is read.
* **Missing for a printed form in the second case.** Igusa invariants of the curve attached to a point of
  `X₆`, which needs the polarization (§6).

### 5.4 `ShimuraHolFamily`

* **Printed.** Shimura, Ann. of Math. 85 (1967), Main Thm I, and Shimura, Ann. of Math. 78 (1963) for the
  analytic family `A_τ = ℂ²/Λ_τ` (locators UNVERIFIED).
  * Main Thm I concerns the canonical model of one geometric component, over `ℚ(ζ₃)` for the level-3 group.
* **The step to the leaf.** The leaf asks for one holomorphic `φ : ℍ → Y₃(ℂ)` on the `ℚ`-model, with the
  moduli clause (`IsShimuraHolFamily`: the lattice `qmLattice τ` uniformizes the QM pair of `φ(τ)`). It uses
  Deligne 1971 §4 (the `ℚ`-model as the union of the conjugate components), R1 and Lemma QP.
* **Missing for a printed form.**
  * The canonical model of the component over `ℚ(ζ₃)`, with its own moduli interpretation.
  * The comparison `Sh_K ⊗ ℚ(ζ₃) = ⊔` of components, which is the content of Deligne §4.

  Neither is stated in the kernel. The holomorphy part is already concrete (`IsHolFamily`, review §7 of
  shimura-split).

## 6. `r3` (`R03_LinYang`): which definitions are missing

`R03_LinYang` (kernel `ZInQKernel/HDecomp/LeafPush2/R3.lean`) is stated over `ℂ` and without polarizations:
every QM abelian surface over `ℂ` is the Jacobian of a curve on the Lin–Yang family at some `j ≠ 0`, or a product
of elliptic curves.

**The printed statement.** Lin–Yang, arXiv:1807.00466v1 Example 29 (read by the audit), or Baba–Granath
Prop. 3.6 (read): the *principally polarized* QM surface over the point `j` of `X₆/W`, for `j ≠ 0, ∞`, is the
Jacobian of a genus-2 curve with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.

**Missing definitions** (VERIFIED by reading the kernel: none of them is defined):
1. **A principal polarization on `PkgI3.AbVar`.** This means the dual abelian variety `Â` (`Pic⁰`), and a
   polarization `λ : A → Â` coming from an ample line bundle, with "principal" meaning `λ` is an isomorphism.
   * Mathlib 4.35 has no Picard scheme and no dual abelian variety. The kernel's `RvQMPolar` treats
     polarizations only as Riemann forms on the lattice `𝒪` (`QM/Polar.lean`).
   * Without this, neither "principally polarized" nor Weil's dichotomy (a principally polarized abelian
     surface is a Jacobian or a product with the product polarization) can be stated.
2. **The coarse moduli bijection on `ℂ`-points**, `Ψ_ℂ : X₆(ℂ) ≃ {QM pairs over ℂ}/≅`. `X6Props` gives `Ψ` only on
   `ℚ̄`-points.
   * Without it, "the `j` of `A`" (`π₆(Ψ_ℂ⁻¹[A, ι])`) cannot be stated for `A/ℂ`.
   * Most QM surfaces over `ℂ` have transcendental `j` and are not base changes from `ℚ̄`, so the `ℚ̄`-form plus
     base change does not suffice. A spreading-out argument over `X₆` (the chain's glue target
     `R03_LinYang_algClosed`) would be needed instead.

**The split these would allow.** With (1) and (2), `r3` would split into three leaves and coordinate glue:
* Lin–Yang Ex. 29 on the coarse witness over `ℂ` (printed);
* Weil's dichotomy (printed);
* Lemma QP (existence of the principal polarization of type `μ`);
* the coordinate glue `j = π₆(x)`.

## 7. Files and checks (all VERIFIED: `lake env lean`, one Lean process at a time)

| file | content | check |
|---|---|---|
| `Local.lean` | §3.2 (Mathlib only) | 0 errors, ~4 s |
| `Adelic.lean` | `Local.lean` + §3.1-3.3 (Mathlib only) | 0 errors, ~8 s |
| `parts/DeligneNew.lean` | `DelignePi0`, the two printed leaves, the two derivations (§4) | via `Deligne.lean` |
| `Deligne.lean` | generated by `mk_deligne.py`: kernel import `ZInQKernel.HDecomp.QM.Leaves` + `Adelic.lean` + shimura-split's `Y3Conn.lean` (verbatim) + shimura-split's `DeligneComponentsX6` (verbatim) + `parts/DeligneNew.lean` | 0 errors, ~12 s; `deligne_result.txt`: 3 axiom lines, all standard |
| `parts/BundleNew.lean` | `ShimuraGlueLeaves`, `shimuraSplitLeaves_of_glue`, `rows_of_shimuraGlueLeaves` | via `RowsGlue.lean` |
| `RowsGlue.lean` | generated by `mk_rowsglue.py`: shimura-split's `Rows.lean` (verbatim, over `TailK`) + `Adelic.lean` + `parts/DeligneNew.lean` + `parts/BundleNew.lean` | 0 errors, ~1 min 45 s; `rowsglue_result.txt`: 59 axiom lines, all standard |

**Build note.** `.lake/build` and `lean/.lake/build` were reflink-copied from `~/dzq-check2` (commit 5da857b0;
from this base only `ZInQKernel/OneProof/TYZSplit.lean` differs, in a docstring).

**Instance finding** (VERIFIED). Over `TailK`, `Algebra ℚ (v.adicCompletion ℚ)` resolves to
`DivisionRing.toRatAlgebra`. That is not reducibly defeq to `instAlgebraAdicCompletion`, the instance in the type
of Mathlib's `padicEquiv`. Any statement mentioning `padicEquiv` then fails to elaborate.
`attribute [local instance 2000] instAlgebraAdicCompletion` fixes it. It is used in `Adelic.lean` and
`DeligneNew.lean`; the kernel's `BaseChange2` instead removes the other instance.

**Integration notes.**
* `Adelic.lean` imports only Mathlib and could move to `ZInQKernel/Contrib/` unchanged.
* `Deligne.lean` needs only `ZInQKernel.HDecomp.QM.Leaves` plus shimura-split's `Y3Conn.lean` (also kernel-only).
* `RowsGlue.lean` shows the fold over `TailK`. Over `TailU` the remark of shimura-split §6 applies (drop Part 1's
  qm-split prefix).

## 8. Counts and what remains

**Bundle.** `ShimuraSplitLeaves` had 9 fields; `ShimuraGlueLeaves` has the same 9.

| | published form | consequences |
|---|---|---|
| before (shimura-split) | 3: `GonzalezRotgerX6`, `GonzalezRotgerCountX6`, `GeomConnOfAlgClosure` (weakened textbook) | 5: both Deligne leaves, `BabaGranathX6'`, `ReciprocityCanonical`, `ElkiesConicX6` |
| after | 5: the above and `DeligneComponentsX6Printed`, `DeligneComponentsY3Printed` | 3: `BabaGranathX6'`, `ReciprocityCanonical`, `ElkiesConicX6` |

T5 is a textbook leaf in both rows. `ShimuraHolFamily` (in `ShimuraFam.lean`, over `TailU`) remains a
consequence. The two Deligne leaves are two specializations of one theorem.

**Remaining (unchecked or unproved):**
* §5.1, the Tau Ceti reduction of `ReciprocityCanonical` to the ray-class form: not attempted.
* §5.2, the Möbius action on `ToP1` for Elkies' `t`: not attempted.
* §6, the polarization and `ℂ`-moduli definitions for `r3`: not attempted.
* The reading of Baba–Granath's `j` (§5.3): unchecked.
* No independent model review of the new leaves was run.
