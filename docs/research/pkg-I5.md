# pkg-I5: the Arakelov package (steps E2-E4, F3) as literature leaves

Status: research note (task pkg-I5, 2026-11-11). It works out interface package I5 of
`docs/research/wk-h.md` §2: Javanpeykar 2014 Thm 1.1.1, Gaudron–Rémond 2014 Thm 1.4, Faltings
1983 Lemma 5 with additivity, Bost's lower bound, and Pazuki 2012 Cor. 1.3(2). For each input it
gives the statement N5 uses, the most concrete faithful leaf, the Lean objects the leaf needs
and which of them exist. It then settles the central question: can the Faltings height be
defined concretely, or replaced by an elementary height? Drafts: `scratch/pkg-I5/I5.lean`
(compiles, no `sorry`). Log: `scratch/pkg-I5/log.md`. No file under `ZInQKernel/`, `blueprint/`
or other notes was edited.

Marks:

- **VERIFIED**: read in a source in the repository, computed (script and output in
  `scratch/pkg-I5/`), or compiled.
- **STANDARD**: a published theorem with a reference. Locators recalled from memory are marked
  UNVERIFIED. There was no network access.
- **SPECULATIVE**: an assessment or a sketch.
- **ASTRA-READ** (h-trust §2.5): a model opened the primary source; no human has.

## 0. Summary

1. **The Faltings height cannot be removed from I5 (VERIFIED as an argument, §2.2).** The
   transfer E2-E4 runs through `J = J₁(N)` and its complement `Z`, abelian varieties of
   dimension up to `N² ≤ Q²M⁴`. Every published theorem used there (Javanpeykar, GR14, Faltings
   Lemma 5, Bost) is an inequality in `h_F` of these large-dimensional varieties.
   - No explicit formula covers them. `X₁(N)` is hyperelliptic for only three `N` (STANDARD,
     Ishii–Momose 1991, UNVERIFIED), and the hyperelliptic formula is all §2.4 gives beyond
     genus 2.
   - Replacing `h_F(J₁(N))` or `h_F(Z)` by an elementary height would need a published theorem
     bounding the elementary height of an abelian variety in terms of its conductor or level.
     For a general abelian variety with bounded bad primes such a bound is the open effective
     Shafarevich conjecture; for `J₁(N)` itself, Javanpeykar's theorem is the bound, and it is
     about `h_F`.
   So a faithful I5 needs a **Lean definition of the stable Faltings height of an abelian
   variety over a number field**, together with abelian varieties, isogenies and their degrees,
   products, the Jacobian of `X₁(N)` and Belyi degrees. None of these exists in Mathlib, Tau
   Ceti or the FLT projects in the required form (prereq-survey; §3 here).
2. **For the abelian surface `A` alone, much can be made concrete (VERIFIED: compiled and
   checked numerically).**
   - *Theta height.* By Thomae's formula, the eighth powers of the ten even theta constants of
     `Jac C`, for `C : y² = c∏(x − aᵢ)`, are proportional to the polynomials
     `Θ_T = (∏_{i<j∈T}(aᵢ−aⱼ)·∏_{i<j∈Tᶜ}(aᵢ−aⱼ))²`, one for each splitting of the branch points
     into two triples (`thomaePoint`). The theta height of F3 becomes `h([Θ_T])/8`, an
     elementary height (`thetaHeightThomae`; exact since `h(z⁸) = 8h(z)` for sup norms).
     `∑Θ_T` is the Igusa–Clebsch `I₄`, and `∏Θ_T = (disc/a₀¹⁰)⁴` (`thomae_check.py`).
   - *Archimedean part of `h_F`.* For hyperelliptic Jacobians it is a Lebesgue integral over `ℂ`
     (`hypGram`, `hypVol`). The factor 2 was checked against PARI periods (`area_check.py`).
   - *Elliptic curves.* There is a closed formula for the stable Faltings height
     (`faltingsHeightEC`), checked numerically (`ec_height_check.py`):
     - it agrees with Silverman's τ-formula on 7 curves;
     - at `j = 0` it gives `−1.321117`, Deligne's minimum `−0.748752` shifted by `−½ log π`;
     - 11a1 and 11a3 differ by `½ log 5`, Faltings Lemma 5 with equality for the 5-isogeny.
   - *Genus 2 with a smooth Weierstrass model over `𝓞_K`.* The non-archimedean term vanishes,
     and `h_F(Jac C)` is the archimedean formula (`faltingsHeightGood`).
3. **Leaves statable today (VERIFIED: compiled).**
   - `BostEC`: Bost at `g = 1`.
   - `BostGoodGenus2`: Bost for genus-2 Jacobians with a good model.
   - `PazukiGoodGenus2`: Pazuki Cor. 1.3(2) with Thomae's theta height and the good-model
     Faltings height.

   All three are faithful special cases. `PazukiGoodGenus2` is a composite: Pazuki read through
   Thomae's formula and the good-model identification of `h_F`. None of the three is enough for
   H: the QM surface's curve need not have everywhere good reduction (§2.4), and E2-E4 are out
   of reach anyway (item 1).
4. **Glue proved (VERIFIED).** `f3_numerics` (N5 L934-947: from Pazuki's bound to
   `h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F)`), and the model-independence lemmas `thomaePoint_add_const`
   and `thomaePoint_smul`. Each depends on `propext`, `Classical.choice`, `Quot.sound`. Together
   with wk-h's `transfer_numerics` (E3-E4 arithmetic), all of N5's Arakelov bookkeeping is now
   machine-checked as real-number lemmas.
5. **Recommendation (§5).** State I5 as five leaves over one new **object layer**, and make
   that layer a crowdsourced sub-project with acceptance tests:
   - the five leaves: Javanpeykar, GR14, Faltings Lemma 5, Bost, Pazuki;
   - the object layer: abelian varieties over number fields, isogeny degree, stable Faltings
     height, Jacobians, `X₁(N)`, Belyi degree, theta height;
   - acceptance tests: the general `h_F` must agree with `faltingsHeightEC` and
     `faltingsHeightGood` (they pin down normalizations), and `thetaHeight` with
     `thetaHeightThomae` on Jacobians.

   Additivity of `h_F` and the dimension bookkeeping become glue once the layer exists. The CM
   branch (BCCGM eq. (6.2), Fowler) is not needed (h-cm).

## 1. The five inputs: the statements N5 uses

N5's transfer for `u ∉ 𝒞` (L860-905). From A1-E1 there are:

- `L'` with `d' = [L':ℚ] ≤ QM`;
- the QM surface `A/L'`;
- `Z/L'` and `N ≤ QM²`;
- an `L'`-isogeny `A × Z → J = J₁(N)_{L'}`.

| # | Input | Statement used (N5 form) | Read status |
| --- | --- | --- | --- |
| E2 | Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014) 89-140, Thm 1.1.1 and §2.3 | For a smooth projective geometrically connected curve `X` over a number field (equivalently over `ℚ̄`) of genus `g ≥ 1`: `h_F(Jac X) ≤ 13·10⁶·g·deg_B(X)⁵`. `deg_B` is the Belyi degree, the minimal degree of a morphism `X_ℚ̄ → P¹` unramified outside `{0, 1, ∞}`. §2.1 uses the metric `(i/2)∫ω∧ω̄`; §2.3 identifies the curve's height with the stable Faltings height of `Jac X`. Applied at `X = X₁(N)`, with `g, deg_B ≤ [PSL₂(ℤ):±Γ₁(N)] ≤ N²` (pp. 92-93) | ASTRA-READ (height/AUDIT item 3). Whether 1.1.1 is phrased over `ℚ̄`: UNVERIFIED |
| E3 | Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014) 2057-2108, Thm 1.4 | `A, B` abelian varieties over a number field `k`, `k`-isogenous, `g = dim A`. Then there is an isogeny `A → B` (and one `B → A`) of degree `≤ κ(A) = ((14g)^{64g²}[k:ℚ]·max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`, original stable Faltings normalization, no polarization hypothesis. Applied with source `J`, target `A × Z` | ASTRA-READ (item 4) |
| E4a | Faltings, *Endlichkeitssätze…*, Invent. Math. 73 (1983), Lemma 5; alternative Raynaud, Astérisque 127, Exp. VII Cor. 2.1.3 | `φ : A → B` an isogeny over `K`: `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Lemma 5 itself is the exact formula `h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹_{G/𝓞}` (`G` the kernel, semistable case). The inequality follows since `1 ≤ #s*Ω¹ ≤ deg φ` | UNVERIFIED locators (h-trust §2.5 item 7) |
| E4b | additivity | `h_F(A × B) = h_F(A) + h_F(B)` (Néron model and metric of a product). A basic property, stated in Faltings 1983 §1 and Deligne, Sém. Bourbaki 616 (UNVERIFIED) | uncited in N5 (L896) |
| E4c | Bost, Duke Math. J. 82 (1996); as recorded in GR14 §9 (and CMH 89 (2014) §2.3) | `h_F(A) ≥ −(3/2)·dim A`, original normalization. (CMH: `≥ −log(π√2)·dim`) | ASTRA-READ (GR14 §9) |
| F3 | Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012), Cor. 1.3(2) and §§2.2-2.3 | `g = 2`, level `r = 2` (the sixteen half-characteristic theta constants, the six odd ones zero), Deligne metric (`h_F + log π` for `g = 2`): `h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`, `X_D = max(1, h_F(A) + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵`. `h_Θ` uses Euclidean norms at infinity | ASTRA-READ (whole/REPORT L59) |

N5's arithmetic between them: E3-E4 is `transfer_numerics` (wk-h, proved), and F3 is
`f3_numerics` (here, proved).

## 2. The Faltings height

### 2.1 Definition and what it needs (STANDARD)

For `A/K` with semistable reduction, let `𝒜/𝓞_K` be the Néron model and
`ω_𝒜 = e*Ω^g_{𝒜/𝓞_K}`, an invertible `𝓞_K`-module. For `0 ≠ η ∈ ω_𝒜`:

`h_F(A) = [K:ℚ]⁻¹ ( log #(ω_𝒜/𝓞_K η) − ½ ∑_{σ:K→ℂ} log ((i/2)^g ∫_{A_σ(ℂ)} η∧η̄) )`.

The stable height is this quantity after any extension over which `A` is semistable
(Grothendieck, SGA 7 IX 3.6). Faltings' original normalization is `(i/2)^g`; Deligne's is
`(i/2π)^g`, which shifts by `(g/2) log π` (Pazuki uses Deligne's).

A Lean definition needs four things:

1. abelian varieties over number fields;
2. a semistable model, or the Néron model, and its invariant differentials;
3. the complex points `A_σ(ℂ)` with integration of top forms, or a period lattice;
4. for the stable version, field extensions together with invariance under base change.

Items 2 and 3 are absent from every library (prereq-survey §1, row "Basic"; log Step 2).

**A definition without constructing Néron models (SPECULATIVE).** By the Néron mapping property,
every smooth separated finite-type group-scheme model `𝒢` of `A_L` maps to the Néron model. So
`ω_𝒩 ⊆ ω_𝒢`, and the Néron lattice gives the smallest value of the model height. Moreover
`h(A_L) ≥ h^st(A)`, with equality for semistable `L`. Hence

`h_F^st(A) = inf over (L/K finite, 𝒢/𝓞_L smooth group model of A_L, η) of the model height`.

This needs only smooth group schemes over `𝓞_L`, which Mathlib can express. Néron existence and
semistable reduction become theorems about the definition, not parts of it. The archimedean
term (item 3) is still needed. A route to it: `A_σ(ℂ)` with the analytic topology from étale
coordinates (inverse function theorem), and `|η∧η̄|` as a measure patched from charts. Estimated
at several thousand lines (SPECULATIVE).

### 2.2 Why the large-dimensional heights cannot be avoided

E2-E4 bound `h_F(A)` through `h_F(J₁(N))` (Javanpeykar), the degree of an isogeny out of
`J₁(N)` (GR14, whose bound itself contains `h_F(J₁(N))`), height variation along that isogeny,
and `h_F(Z) ≥ −(3/2)dim Z` for a complement of dimension `≤ N²`.

- *No explicit formula.* Javanpeykar's theorem has one hypothesis and one conclusion, both
  about `h_F(Jac X)` with `g(X) ~ N²/24`. `X₁(N)` is hyperelliptic only for `N ∈ {13, 16, 18}`
  (Ishii–Momose 1991, UNVERIFIED), so the hyperelliptic integral formula (§2.4) does not reach
  it.
- *No elementary replacement.* The leaves are inequalities in `h_F` of `J` and `Z`. To restate
  any of them with an elementary height `h'`, one needs a published comparison between `h'` and
  `h_F` in dimension `N²`. Pazuki's Cor. 1.3 is such a comparison for theta heights in every
  dimension. But the theta height of `J₁(N)` needs a theta structure on `J₁(N)`, which is no
  more elementary than `h_F`. A bound for `h_F(A)` from the level and bad primes of `A` alone,
  with no modular curve, would be an effective Shafarevich theorem; that is open for abelian
  surfaces.
- *The CM branch is not needed.* N5 L581-631 uses `h_F` of a CM elliptic curve (BCCGM (6.2)) and
  GR14 at `E² → A`. h-cm shows the branch is empty for rational `u`. The closed formula
  `faltingsHeightEC` would make (6.2) concrete if the branch were ever restored.

### 2.3 Elliptic curves: a closed formula (VERIFIED)

For `W/K` elliptic with `ω = dx/(2y + a₁x + a₃)`, `P = 4x³ + b₂x² + 2b₄x + b₆`:

`h_F^st(E) = (12[K:ℚ])⁻¹ (∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|) − (2[K:ℚ])⁻¹ ∑_σ log (2∫_ℂ dλ/|P^σ|)`.

Derivation, three steps:

1. At a semistable place, `ord_v(ω/ω_Néron) = (ord_v Δ_min − ord_v Δ)/12` and
   `ord_v Δ_min = max(0, −ord_v j)`.
2. The product formula turns `∑_v ord_v(Δ) log Nv` into `∑_σ log|σΔ|`.
3. `(i/2)∫_{E_σ}ω∧ω̄` is the covolume of the period lattice, which equals `2∫_ℂ dλ/|P^σ|`
   (the two sheets).

Every term is base-change invariant after normalization, so the formula holds over any `K`
without passing to a semistable field. It is equivalent to Silverman 1986 Prop. 1.1 and to
BCCGM (6.2) (both cited by N5; height/AUDIT item 2). Numerical checks: log Step 3.

### 2.4 Genus 2

**Archimedean part (VERIFIED as a definition; STANDARD identity).** Let
`C : y² + h(x)y = f(x)`, `P = 4f + h²`, `ωᵢ = xⁱdx/(2y + h)`. Then:

- `(i/2)∫_C ωᵢ∧ω̄ⱼ = 2∫_ℂ xⁱx̄ʲ/|P(x)| dλ` (`hypGram`);
- `(i/2)²∫_{Jac C}|ω₀∧ω₁|² = det(hypGram)` (`hypVol`). Both sides equal `|det Ω₁|² det Im τ`
  (Riemann bilinear relations).

**Good models (VERIFIED as a definition).** If Liu's discriminant `2⁻¹²disc₆(P)` is a unit of
`𝓞_K` (`Genus2Eq.Good`), the Weierstrass model is smooth. Then `Jac C` has Néron model
`Pic⁰_{𝒞/𝓞_K}`, an abelian scheme (BLR 9.5 Thm 4), with invariant differentials `𝓞_K·ω₀∧ω₁`
(Lockhart 1994, Liu 1996; locators UNVERIFIED). So
`h_F(Jac C) = −(2[K:ℚ])⁻¹ ∑_σ log hypVol(P^σ)` (`faltingsHeightGood`).

**General genus-2 curves (SPECULATIVE sketch).** `Λ = Δ_eq·(ω₀∧ω₁)^{⊗10}` is a section of
`(det ω)^{⊗10}` independent of the equation, with `‖Λ‖_σ = |σΔ_eq|·hypVol(P^σ)⁵`. For semistable
`C`, Mumford's relation `10λ = δ₀ + 2δ₁` on `M̄₂` (STANDARD, UNVERIFIED locator) gives
`ord_𝔭 Λ = δ₀(𝔭) + 2δ₁(𝔭)`, counting non-separating and separating nodes with thickness. This
agrees with the shape of the Bost–Mestre–Moret-Bailly, Ueno and Saito formulas (Astérisque 183
(1990); Ueno 1988; Saito 1989; UNVERIFIED). The result:

`10[K:ℚ]h_F(Jac C) = ∑_𝔭 (δ₀ + 2δ₁)(𝔭) log N𝔭 − ∑_σ log ‖Λ‖_σ`.

For the QM surfaces of H, two facts simplify this:

- `A` has potentially good reduction everywhere: the character group of a toric part would be
  a `ℚ`-space of dimension `≤ 2` carrying an action of the division algebra `B`, which forces
  dimension 0. So `δ₀ = 0`.
- The local terms come only from separating nodes, where `C` degenerates to two elliptic curves
  while `Jac C` stays good. For `p ≥ 5` they should be
  `ord_𝔭(I₁₀) − 10 min_k ord_𝔭(I_k)/k`, from Igusa invariants.

This would give a closed Igusa-invariant formula for `h_F(A)`, with care needed at 2 and 3.
Not drafted: the identification is not checkable here.

**The good-model restriction is real.** The reduction of a QM surface can be a product of
elliptic curves with the product polarization. At such a prime, `C` has bad (compact-type)
reduction although `A` is good, and then `faltingsHeightGood` does not apply. Over the field
`L'` there is in general no reason for every prime to be of the good kind (SPECULATIVE).

### 2.5 Theta height via Thomae (VERIFIED as a definition and by computation)

The Thomae point and its properties (`thomaePoint`; Thomae 1870, Mumford *Tata Lectures on
Theta II* Ch. IIIa §8, UNVERIFIED):

- Even characteristics in genus 2 correspond to the 10 splittings of the six branch points
  into two triples. Thomae gives `θ_T⁴ = ±κ·∏_{i<j∈T}(aᵢ−aⱼ)∏_{i<j∈Tᶜ}(aᵢ−aⱼ)` with one
  `κ ≠ 0`. So `[θ_T⁸] = [Θ_T]` in `P⁹`, with no sign ambiguity.
- The projective point is independent of the model. It is translation invariant, and scaling
  the branch points multiplies it by `λ¹²` (both proved in Lean); together with `x ↦ 1/x` this
  gives `PGL₂`-invariance (each root occurs to degree 4 in every `Θ_T`).
- `∑_T Θ_T = I₄/a₀⁴` and `∏_T Θ_T = (disc/a₀¹⁰)⁴` (`thomae_check.py`). So N5's
  `j = 3779136(∏z_m)⁴/(∑z_m⁸)⁵` becomes `j² = 3779136²·I₁₀⁴/I₄¹⁰` in Igusa–Clebsch invariants
  (`I₁₀ = disc`). This makes F1's theta-to-Igusa step (LNY §2.2, Igusa 1967) elementary
  algebra, a remark for package I1.
- The height: `h([θ_T]) = h([Θ_T])/8` exactly for sup norms (`Height.logHeight_pow`). Pazuki
  uses Euclidean norms, which dominate.

### 2.6 Why `h_F(A)` cannot be traded for an elementary height in the leaves

The chain needs `h_F(A)` only as an intermediate: E gives `h_F(A) ≤ B`, and F3 gives
`h_Θ(A) ≤ f(h_F(A))` with `f` increasing.

- Restating F3 with `h' ≥ h_F` in place of `h_F` gives a consequence of Pazuki (faithful). But
  then E must bound `h'`, and the published E theorems bound only `h_F`.
- Restating with `h' ≤ h_F` makes F3 stronger than Pazuki (not faithful).

So `h_F(A)` can be eliminated only by composing E with F3. That composite is not one published
theorem. The genus-2 objects of §§2.4-2.5 serve instead as specifications of the general
definitions (§5).

## 3. Per input: faithful leaf, objects, statability

Lean-shaped templates over the missing object layer (not compiled). Names are proposals.

```lean
-- object layer (absent)
AbelianVariety K                         -- K a number field
dim A : ℕ;  A ×ₖ B;  A.baseChange L
Isogeny A B, Isogeny.deg φ : ℕ           -- finite surjective homomorphism; rank of φ_* O
faltingsHeight A : ℝ                     -- stable, Faltings' original normalization
SmoothProjCurve K, genus X, jacobian X : AbelianVariety K
belyiDegree X : ℕ
modularCurveX1 N : SmoothProjCurve ℚ
PPAV K, thetaHeightLevel2 (A : PPAV K) : ℝ  -- Pazuki's h_Θ, r = 2

def Javanpeykar : Prop := ∀ K X, 1 ≤ genus X →
  faltingsHeight (jacobian X) ≤ 13 * 10^6 * genus X * belyiDegree X ^ 5
def GaudronRemond : Prop := ∀ K (A B : AbelianVariety K), Nonempty (Isogeny A B) →
  ∃ φ : Isogeny A B, (φ.deg : ℝ) ≤ κ (dim A) (finrank ℚ K) (faltingsHeight A)
def FaltingsLemma5 : Prop := ∀ K A B (φ : Isogeny A B),
  |faltingsHeight A - faltingsHeight B| ≤ log φ.deg / 2
def Bost : Prop := ∀ K A, -(3/2) * dim A ≤ faltingsHeight A
def Pazuki : Prop := ∀ K (A : PPAV K), dim A = 2 →
  thetaHeightLevel2 A ≤ XD A / 2 + pazukiC2 * log (XD A + 2)   -- XD = max 1 (h_F + log π)
```

| Input | Faithful leaf | Objects needed | Exists today (Mathlib / Tau Ceti / FLT) | Statable now? |
| --- | --- | --- | --- | --- |
| E2 Javanpeykar | as above; the application to `X₁(N)` (`g, deg_B ≤ N²`, `dim J₁(N) = g`, base change to `L'`) is glue | curves over `K`, genus, Jacobian, Belyi degree, `X₁(N)` over `ℚ`, `h_F` | Mathlib: function fields, `Γ₁(N)` and its index. Lean Pool: function field of `X₀(N)`. Anthropic FLT: Jacobians in a special case. No Belyi maps, no `X₁(N)` as a scheme, no `h_F` | no |
| E3 GR14 | as above; N5 uses the direction "source `J`" | abelian varieties, isogenies, degree, `h_F`, `[K:ℚ]` | Tau Ceti: `AbelianVariety`, `IsIsogeny` (definitions only). No degree API, no `h_F` | no |
| E4a Faltings Lemma 5 | as above (the inequality form; the exact formula needs the kernel's finite flat model) | same as E3 | same | no; only numerical evidence (11a1 → 11a3 attains `½ log 5`) |
| E4b additivity | `h_F(A ×ₖ B) = h_F A + h_F B` | products, `h_F` | Mathlib pullbacks | glue once `h_F` exists |
| E4c Bost | as above | `h_F`, `dim` | — | **special cases now**: `BostEC`, `BostGoodGenus2` (compiled) |
| F3 Pazuki | as above | principally polarized surfaces, level-2 theta structure, `h_Θ`, `h_F` | none | **special case now**: `PazukiGoodGenus2` (compiled; composite with Thomae and the good-model bridge) |

Glue of the package (to be proved by the project):

| Glue | Content | Status |
| --- | --- | --- |
| G1 | `genus X₁(N) ≤ N²`, `deg_B X₁(N) ≤ N²`, `dim J₁(N) = genus`, `h_F` base-change invariant | needs the object layer |
| G2 | E3-E4 arithmetic (`transfer_numerics`) | **proved** (wk-h) |
| G3 | F3 arithmetic (`f3_numerics`) | **proved** (here) |
| G4 | `dim` additive on products, preserved by isogenies; `deg ≥ 1` | needs the object layer |
| G5 | heights independent of the field; Thomae point model-independent | partly proved (`thomaePoint_add_const`, `thomaePoint_smul`) |

## 4. What compiles (`scratch/pkg-I5/I5.lean`, VERIFIED)

`lake env lean scratch/pkg-I5/I5.lean`: no errors, no `sorry`. `#print axioms` on the three
proved theorems lists `propext`, `Classical.choice`, `Quot.sound`. Mathlib-only.

- Definitions:
  - `thomaePoint`, `absLogHeight`, `thetaHeightThomae`;
  - `hypGram`, `hypVol`;
  - `finiteHeightPart`, `faltingsHeightEC`;
  - `Genus2Eq` with `P`, `binDisc`, `Good`; `faltingsHeightGood`, `pazukiC2`.
- Leaves: `BostEC`, `BostGoodGenus2`, `PazukiGoodGenus2`.
- Proved: `thomaePoint_add_const`, `tripleProd_mul`, `card_evenTriple`, `thomaePoint_smul`,
  `f3_numerics`.

Scripts, with outputs saved beside them: `ec_height_check.py`, `area_check.py`,
`thomae_check.py`.

## 5. Obstacle and recommendation

**Biggest obstacle.** No library has a definition of the stable Faltings height of an abelian
variety over a number field. It needs Néron (or semistable smooth group) models with their
invariant differentials, and integration over `A_σ(ℂ)`. Next in size: the Jacobian of `X₁(N)`
as an abelian variety over `ℚ`, with Belyi degrees, for Javanpeykar.

**Recommended form of I5 for the decomposition.**

1. Five leaves: Javanpeykar, GR14, Faltings Lemma 5 (inequality form), Bost, Pazuki
   (`g = r = 2`). Each is stated over the object layer as in §3 and is exactly the published
   statement (Lemma 5: its standard corollary).
2. An object layer, as a crowdsourced sub-project. It is a prerequisite, not a leaf.
   **Acceptance tests** guard against vacuous or mis-normalized definitions:
   - `faltingsHeight (ellipticCurve W) = faltingsHeightEC W`;
   - `faltingsHeight (jacobian C) = faltingsHeightGood E` for good genus-2 equations;
   - `thetaHeightLevel2 (jacobian C) ≥ thetaHeightThomae a` (sup norms below Euclidean
     norms).

   Their right-hand sides compile today, and the first was checked numerically against known
   values.
3. Glue G1-G5, two items of which are already proved.
4. Fallback while the object layer does not exist: wk-h's `ArakelovSig` (compiled). Its limits
   must be stated next to it: over abstract types the fields can be satisfied by a fake model
   (wk-h §4.3), so it is attribution only, not a faithful reduction.

**What this package does not change.** As a Lean Prop, H still enters through
`JHeightBound`/`SixContactMin`. I5's leaves become faithful Lean statements only together with
the object layer.

## 6. Checks to make with library access (UNVERIFIED items, by weight)

1. Javanpeykar Thm 1.1.1: the field (`ℚ̄` or number field) and the hypothesis `g ≥ 1`.
2. Faltings 1983 Lemma 5 (and the 1984 erratum), or Raynaud Exp. VII Cor. 2.1.3, for the
   inequality form.
3. Pazuki Cor. 1.3(2): whether `X_D` carries `max(1, ·)`, and the exact `C₂` at `g = r = 2`.
4. Thomae's formula in the six-finite-branch-point form; Lockhart 1994 Def. 1.6 (Liu's
   discriminant `2⁻¹²disc(4f + h²)`) and the basis `xⁱdx/(2y + h)` of `H⁰(𝒞, ω)` for smooth
   models.
5. Mumford's `10λ = δ₀ + 2δ₁` and its arithmetic form (Ueno 1988, Saito 1989, BMMB 1990), and
   Ishii–Momose 1991 (hyperelliptic `X₁(N)`).
