# cm-points: CM points on X₀(32) = A, Shimura reciprocity, and TYZ's genus-point package split into genuine leaves

Task cm-points, 2026-11-13. Lean: `ZInQKernel/Contrib/TYZGenus/CM.lean` and
`ZInQKernel/Contrib/TYZGenus/Package.lean` (new files owned by this task; `lake build
ZInQKernel.Contrib.TYZGenus.Package` builds both, VERIFIED). Results log: `scratch/cm-points/log.md`.
Drafts: `scratch/cm-points/T1.lean`–`T9.lean`; axiom audit `scratch/cm-points/Audit.lean`
(output `audit-out.txt`). No `sorry`, no `axiom`; no existing file edited. Merged into this branch:
`origin/wip/x0-32` (`TYZGenus/X0.lean`, the modular parametrization `X0.phiC`) and
`origin/wip/ring-class` (`TYZGenus/RingClass.lean`, `H_{d,4}`, `H'_d`, `ℍ'_n` from Tau Ceti's ring class
fields).

Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD** (published, reference
given), **SPECULATIVE**, **UNVERIFIED** (theorem numbers from memory; this host has no network).

Caveats that stay attached (from `tyz-decomp.md`): (1) reading A is not printed in any refereed text;
(2) TYZ (Tian–Yuan–Zhang, arXiv:1411.4728v1; Asian J. Math. 21 (2017), refereed) was read in arXiv v1
only, and `Period7.tex` is **not on this host**: every TYZ line number here is quoted from `nt-tyz.md`,
`rv-tyz-inputs.md`, `tyz-t1.md`, `pn-design.md`, `rv-pn-encoding.md`, not re-read; (3) Proposition N is
AI-reviewed only; (4) Theorem 3.3's constant rests on a computation TYZ do not print (`tyz-t1.md`, AI).
Added here: (5) the translation of TYZ's `z_n = f_n(P_n)` (a CM point on TYZ's curve `X_U`) to
`(1 − [i])·f₀(P_n)` with `f₀(P_n)` the Heegner point of `[16(n+1), −8, 1]` on `X₀(32)` is `tyz-t1.md`
§3.1's (AI-derived, checked numerically there), not a printed statement.

## 0. Main result

`TYZGenusPackage` (an existential over the *abstract* `PropN.GenusData`: abstract `ℤ[i]`-module `M`,
abstract `τ`, `β`, `Z`, `P`, `ε`) is derived from leaves in which `M`, `τ`, `β`, `ℍ'_n` and the class-5
genus points are **pinned by genuine definitions**:

* `M := A(ℍ'_n) ⊂ A(ℚ̄)` (`CM.ptsOver (RingClass.HHprime n)`, a `ℤ[i]`-submodule via `[i]`);
* `τ(y/2) := y • (2, −4)` on `A : y² = x³ + 4x` (`Package.tauG`; TYZ's cusp dictionary);
* `β := galPt σ`, the Galois action of an automorphism `σ` of `ℚ̄` acting on every quadratic field
  as the idele `β₁ = r_∞(−1)r₂(−2)` (`Package.IsBetaOneLift`);
* `P := Package.Pseq`, TYZ's recursion as a definition;
* `Z(e) = Σ_{t∈Φ} t(z_e)` for `e ≡ 5 (mod 8)`, with `z_e = (1 − [i]) f₀(P_e)` and `f₀(P_e)` the Heegner
  point of `[16(e+1), −8, 1]` (`CM.heegnerPt`), defined through x0-32's modular parametrization
  `X0.phiC` and a fixed embedding `ιC : ℚ̄ → ℂ`, `ιC i = I`.

**Theorem** (`Package.tyzThm35ReadingA_of_cmLeaves`, VERIFIED compiled, standard axioms):

```lean
theorem tyzThm35ReadingA_of_cmLeaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA
```

(through `genusPackage_of_cm`, `tyzZnOverHprime_of`, `lemma318_iff_literal`, `genusData_of`). The
leaves, all `def … : Prop` closed over pinned objects except the last:

| leaf | statement | source (numbers UNVERIFIED unless noted) | refereed? |
|---|---|---|---|
| `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2` | (tyz-decomp, unchanged) | TYZ Thm 1.1, L1082, Lemma 2.9 | yes |
| `CMFieldOfDefinitionTYZ` | `f₀(P_n) ∈ A(H_{n,4})` (ring-class's `H4bar n`) | main theorem of CM / Shimura reciprocity for `X₀(N)`: Shimura 1971 Thm 5.4, Ch. 6; Gross, *Heegner points on X₀(N)* (1984) §3; TYZ Prop 3.2 | yes (textbook) |
| `IInH4` | `i ∈ H_{n,4}` | genus theory: `K(i) = K(√n)` ⊂ genus field ⊂ `H_n ⊆ H_{n,4}` (Cox Thm 6.1; ring-class's `hilbertLeH4`) | yes (textbook) |
| `TYZSigmaFixesZn` | every `ρ` acting on `H_{n,4}` as Tau Ceti's Artin symbol of `sigmaClass n` (`σ_{1+2ϖ}`) fixes `z_n` | TYZ Cor 3.9 / Thm 3.6 with Shimura reciprocity on `P_n = [h,1]` (rv-tyz-inputs §1.5); caveat (5) | yes (+ caveat 5) |
| `HprimeNormal` | `H'_d/ℚ` normal (`d ≡ 5`, squarefree), ring-class's `Hprimebar d` | TYZ Prop 3.2(1) (L1253–1260) + Cox Lemma 9.3 | yes |
| `Lemma318Literal HHprime` | every torsion point `P` of `A(ℍ'_n)` has `2(P + [i]P) = 0` | TYZ Lemma 3.18 (L2230–2232), literally | yes |
| `GenusPointLeafCM ℓ` | for each `n`: ∃ a choice `Φ` of TYZ's `Φ₀`, class-7 genus points `Z7 e ∈ A(L_e(i))`, `ε`, a lift `σ`, with Thm 3.3/3.5 (first assertion) and Lemma 3.21(1),(4) for `tyzGenusPt Φ Z7` | TYZ Thm 3.3, 3.5, Lemma 3.21, L2558; "Lemma 3.21 holds for any choice of `Φ₀`" (L2547–2554, VERIFIED by rv-pn-encoding against the source) | yes; **bundled** (existential over `Φ₀`-choice, class-7 genus points, `ε`, `σ`) |

Proved here, not leaves: `i ∈ ℍ'_n` (`iContained_HHprime`); `L_n(i)/ℚ` normal (`normal_Lni`);
`ℍ'_n/ℚ` normal from `HprimeNormal` (`normalFields_HHprime`); for the pinned `τ`,
`τ(y/2) = 0 ↔ (2+2i) ∣ y` (`tauG_eq_zero`, TYZ L1386) and `τ(½ℤ[i]) = A[(1+i)³]`
(`isTorsI3_mem_range`, `lemma318_iff_literal`, with x0-32's explicit list of `A[(1+i)³]`), so Lemma
3.18 needs no fact about `τ`; `β'` fixes `τ(½ℤ[i])` (`galPt_tauG`); F4, `σ` fixing `i` commutes with
`[i]` (`CM.galPt_iPt`); a `β₁`-lift fixes `i` (`fixes_i_of_isBetaOneLift`, TYZ L2581); every element of
`Gal(H_{d,4}/K_d)` extends to `ℚ̄` (`exists_actsAsArtin4`) and Galois descent `H_{d,4} → H'_d`
(`mem_Hprimebar_of_fixed`), giving `z_n ∈ A(H'_n)` (`tyzZnOverHprime_of`); the class-5 genus points lie in
`A(ℍ'_n)` for every `Φ` (`tyzGenusSum_mem`); complex conjugation on Heegner points (`CM.cmComplexConj`,
from `η(−z̄) = conj η(z)`; formerly leaf CM-4); and the core `genusData_of`, which builds
`PropN.GenusData ℓ n` from the pinned objects.

**What this buys over `TYZGenusPackage`.** There every object is existential and the TYZ statements are
fields of one structure. Here Lemma 3.18, the normality F5, the field of definition of `z_n` (itself
split into Shimura's theorem, genus theory and TYZ's Corollary 3.9 with a proved Galois descent) are
separate leaves about pinned objects; `τ_eq_zero`, `β_τ`, F4, `i ∈ ℍ'_n` and "`τ(½ℤ[i]) = A[(1+i)³]`" are
theorems; and the existential of the remaining bundled leaf shrinks from `(M, τ, β, Z, P, ε)` to
`(Φ₀-choice, class-7 genus points, ε, σ)`. The class-5 genus points are pinned up to the choice of
`Φ₀`, which TYZ allow to be arbitrary.

**What remains bundled, and why.** TYZ's class-7 genus point `Z(e) = Σ_{t ∈ 2Cl_e} f_e(P_e)^t`
(`e ≡ 7 mod 8`) needs TYZ's base CM point for `n ≡ 7` (the fixed point of an embedding `M`,
`M² = −n`, rv-tyz-inputs §1.5), which no note on this host records; pinning it by a guessed Heegner
form could make Lemma 3.21(4) (an exact equality) false. With `Z7` pinned, `GenusPointLeafCM` splits by
`genusPointLeaf_of_split` into `GenusPtsDefined`, `Thm35First`, `Lemma321` (stated, with `Z` a
parameter; see the soundness note in Package.lean §5: those three are closed leaves only for a pinned
`Z`).

Independent review (AI subagent, 2026-11-13, statements only): no false leaf; findings on
free parameters applied as docstring notes (log 09:00).

### 0.1 Declarations proved (exact types; `open ZInQ.Contrib.TYZGenus`)

CM.lean (namespace `CM`):

```lean
theorem mem_ptsOver_iff (K : IntermediateField ℚ Qbar) (P : PtA) : P ∈ ptsOver K ↔ IsDefinedOver K P
theorem iPt_mem {K} (hi : iQ ∈ K) {P : PtA} (hP : P ∈ ptsOver K) : iPt P ∈ ptsOver K
theorem galPt_mem {K} (σ : GalQ) (hσ : ∀ x ∈ K, σ x ∈ K) {P : PtA} (hP : P ∈ ptsOver K) :
    galPt σ P ∈ ptsOver K
theorem galPt_iPt (σ : GalQ) (hσ : σ iQ = iQ) (P : PtA) : galPt σ (iPt P) = iPt (galPt σ P)
theorem ιC_iQ : ιC iQ = I
theorem toC_injective : Function.Injective toC
theorem toC_heegnerPt {D} (Q : HeegnerForm 32 D) (h : ∃ P : PtA, toC P = X0.phiC Q.tauH) :
    toC (heegnerPt Q) = X0.phiC Q.tauH
theorem heegnerPt_eq {D} (Q : HeegnerForm 32 D) {P : PtA} (hP : toC P = X0.phiC Q.tauH) :
    heegnerPt Q = P
theorem cmPoint_im (A B D : ℤ) : (cmPoint A B D).im = Real.sqrt (-(D : ℝ)) / (2 * A)
theorem genusSum_mem {F K} {Φ : Finset GalQ} {z : PtA} (hΦ : ∀ t ∈ Φ, ∀ x ∈ F, t x ∈ K)
    (hz : z ∈ ptsOver F) : genusSum Φ z ∈ ptsOver K
theorem eta_conj (z : ℂ) : ModularForm.eta (-conj z) = conj (ModularForm.eta z)
theorem xC_conj (z : ℂ) : X0.xC (-conj z) = conj (X0.xC z)      -- also yC_conj, etaD_conj
theorem phiC_conj (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = -conj (τ : ℂ)) :
    X0.phiC τ' = conjPt (X0.phiC τ)
theorem toC_galPt (σ : GalQ) (hσ : ∀ x : Qbar, ιC (σ x) = conj (ιC x)) (P : PtA) :
    toC (galPt σ P) = conjPt (toC P)
theorem cmComplexConj : CMComplexConj
```

Package.lean (namespace `Package`):

```lean
instance : Module GaussianInt PtA                      -- (a+bi)•P = a•P + b•[i]P
theorem ptT_add_self : ptT + ptT = pt00                -- (2,−4) + (2,−4) = (0,0)
theorem four_zsmul_ptT : (4 : ℤ) • ptT = 0
theorem tauG_eq_zero (y : GaussianInt) : tauG y = 0 ↔ twoTwoI ∣ y
theorem galPt_tauG (σ : GalQ) (hσ : σ iQ = iQ) (y : GaussianInt) : galPt σ (tauG y) = tauG y
theorem fixes_i_of_isBetaOneLift {σ : GalQ} (hσ : IsBetaOneLift σ) : σ iQ = iQ
theorem Pseq_eq (ℓ ε Z d) : Pseq ℓ ε Z d = Z d - ∑ d₁ ∈ d.divisors.filter (…), (ε (d/d₁) d₁ * ℓ d₁) • Pseq ℓ ε Z (d/d₁)
theorem genusData_of {ℓ n} (hn : n % 8 = 5) (K) (hi : iQ ∈ K) (hN : Normal ℚ K)
    (h318 : ∀ P ∈ ptsOver K, IsOfFinAddOrder P → ∃ y, tauG y = P) (Z)
    (hZ : ∀ e ∈ n.divisors, e % 8 = 5 ∨ e % 8 = 7 → Z e ∈ ptsOver K) (ε) (hε : EpsClasses n ε)
    (htors : ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n)) (σ : GalQ) (hσ : IsBetaOneLift σ)
    (h5 : ∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
      galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2)
    (h7 : ∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1) :
    Nonempty (GenusData ℓ n)
theorem genusPackage_of_genusPointLeaf (Hn) (hI : IContained Hn) (hN : NormalFields Hn)
    (h318 : Lemma318 Hn) (hG : ∀ ℓ, IsTYZLcal ℓ → GenusPointLeaf ℓ Hn) : TYZGenusPackage
theorem genusPointLeaf_of_split (hZ : GenusPtsDefined Hn Z) (h35 : Thm35First ℓ Z)
    (h321 : Lemma321 Z) : GenusPointLeaf ℓ Hn
theorem genusPackage_of_split (Hn Z) (hI) (hN) (h318) (hZ : GenusPtsDefined Hn Z)
    (h35 : ∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ Z) (h321 : Lemma321 Z) : TYZGenusPackage
theorem tyzThm35ReadingA_of_split (h11 h1 h29) (Hn Z hI hN h318 hZ h35 h321) : TYZThm35ReadingA
theorem iQ_mem_Lni (n : ℕ) : iQ ∈ Lni n
theorem iContained_HHprime : IContained HHprime
theorem normal_Lni (n : ℕ) : Normal ℚ (Lni n)
theorem normalFields_HHprime (hH : ∀ d, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d)) :
    NormalFields HHprime
theorem Hprimebar_le_HHprime {n e} (he : e ∈ n.divisors) (he5 : e % 8 = 5) : Hprimebar e ≤ HHprime n
theorem genusSum_mem_HHprime … : genusSum Φ z ∈ ptsOver (HHprime n)
theorem genusPackage_of_ringClass (Z) (hHp : HprimeNormal) (h318 : Lemma318 HHprime)
    (hZ : GenusPtsDefined HHprime Z) (h35 : ∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ Z) (h321 : Lemma321 Z) :
    TYZGenusPackage
theorem tyzThm35ReadingA_of_ringClass (h11 h1 h29) (Z hHp h318 hZ h35 h321) : TYZThm35ReadingA
theorem cmFieldTYZ_of {H} (h : CMFieldOfDefinition H)
    (hH : ∀ n, n % 8 = 5 → Squarefree n → H (-64 * n) ≤ H4bar n) : CMFieldOfDefinitionTYZ
theorem Lni_mono {e n} (h : e ∣ n) (hn : n ≠ 0) : Lni e ≤ Lni n
theorem tyzGenusSum_mem (hz : TYZZnOverHprime) (hN : HprimeNormal) {n e} (hsq : Squarefree n)
    (he : e ∈ n.divisors) (he5 : e % 8 = 5) (Φ : Finset GalQ) :
    genusSum Φ (tyzZn e) ∈ ptsOver (HHprime n)
theorem genusPtsDefined_of (hz hN) (Φ Z) (h5 : ∀ e, e % 8 = 5 → Z e = genusSum (Φ e) (tyzZn e))
    (h7 : ∀ e, e % 8 = 7 → Squarefree e → Z e ∈ ptsOver (Lni e)) : GenusPtsDefined HHprime Z
theorem genusPackage_of_cm (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318 HHprime)
    (hG : ∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : TYZGenusPackage
theorem tyzThm35ReadingA_of_cm (h11 h1 h29 hz hN h318 hG) : TYZThm35ReadingA
theorem ptT_add_iPt_ptT : ptT + iPt ptT = .some (-2 * iQ) 0 _      -- τ((1+i)/2) = (−2i, 0)
theorem isTorsI3_mem_range (P : PtA) (h : X0.IsTorsI3 P) : ∃ y : GaussianInt, tauG y = P
theorem lemma318_iff_literal (Hn) : Lemma318 Hn ↔ Lemma318Literal Hn
theorem tyzThm35ReadingA_of_cm' (h11 h1 h29 hz hN) (h318 : Lemma318Literal HHprime) (hG) :
    TYZThm35ReadingA
theorem exists_actsAsArtin4 (d : ℕ) [NeZero d] (c : Pic (O4 d)) : ∃ ρ : GalQ, ActsAsArtin4 ρ d c
theorem mem_Hprimebar_of_fixed (d : ℕ) [NeZero d] {x : Qbar} (hx : x ∈ H4bar d)
    (hfix : ∀ ρ : GalQ, ActsAsArtin4 ρ d (sigmaClass d) → ρ x = x) : x ∈ Hprimebar d
theorem tyzZnOverHprime_of (h1 : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn) :
    TYZZnOverHprime
theorem tyzThm35ReadingA_of_cmLeaves (h11 h1 h29) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4)
    (hs : TYZSigmaFixesZn) (hN : HprimeNormal) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : TYZThm35ReadingA
```

`#print axioms` (VERIFIED, `lake env lean scratch/cm-points/Audit.lean`, 2026-11-13): every one of
`CM.mem_ptsOver_iff, CM.galPt_iPt, CM.ιC_iQ, CM.heegnerPt_eq, CM.genusSum_mem, Package.tauG_eq_zero,
Package.galPt_tauG, Package.fixes_i_of_isBetaOneLift, Package.genusData_of,
Package.genusPackage_of_genusPointLeaf, Package.genusPackage_of_split, Package.tyzThm35ReadingA_of_split,
Package.iContained_HHprime, Package.normal_Lni, Package.normalFields_HHprime,
Package.genusPackage_of_ringClass, Package.tyzThm35ReadingA_of_ringClass, Package.cmFieldTYZ_of,
Package.tyzGenusSum_mem, Package.genusPtsDefined_of, Package.genusPackage_of_cm,
Package.tyzThm35ReadingA_of_cm, CM.eta_conj, CM.phiC_conj, CM.cmComplexConj,
Package.ptT_add_iPt_ptT, Package.isTorsI3_mem_range, Package.lemma318_iff_literal,
Package.tyzThm35ReadingA_of_cm', Package.exists_actsAsArtin4, Package.mem_Hprimebar_of_fixed,
Package.tyzZnOverHprime_of, Package.tyzThm35ReadingA_of_cmLeaves` (33 declarations) depends on axioms:
`[propext, Classical.choice, Quot.sound]`.

No TYZ or CM leaf of the main theorem is proved; they are `def … : Prop`. The former leaf CM-4
(`CMComplexConj`) and the former leaf `TYZZnOverHprime` are now theorems / glue.

## 1. CM points (CM.lean)

**Objects** (all genuine definitions):

* `galPt σ : A(ℚ̄) →+ A(ℚ̄)`, the coordinatewise action of `σ ∈ Gal(ℚ̄/ℚ)` (Mathlib `Point.map`);
  `ptsOver K = A(K)` for `K ⊆ ℚ̄` (range of `A(K) → A(ℚ̄)`; `mem_ptsOver_iff`: coordinates in `K`).
* `ιCA : ℚ̄ →ₐ[ℚ] ℂ` with `ιC iQ = I` (proved), `toC : A(ℚ̄) →+ A(ℂ)` (injective, proved).
* `HeegnerForm N D`: primitive `[A, B, C]`, `A > 0`, `N ∣ A`, `B² − 4AC = D < 0`; `τ_Q = (−B + i√|D|)/2A ∈ ℍ`
  (`tauH`, positivity proved); `lat = ⟨1, τ_Q⟩`, `latN = ⟨1/N, τ_Q⟩` (the cyclic `N`-isogeny);
  `conj = [A, −B, C]`.
* `heegnerPt Q`: the unique `P ∈ A(ℚ̄)` with `toC P = X0.phiC τ_Q` (`heegnerPt_eq`), `X0.phiC` the
  eta-quotient parametrization of x0-32 (whose leaves `X0.X0AnalyticModel` say it is the modular
  parametrization `X₀(32) ≅ A`, `dx/2y = 2πi f dτ`). An earlier draft (commit 6b9a10f1) pinned the
  parametrization by `Σ a_m q^m/m` and the lattice with `g₂ = −16`, `g₃ = 0` (`y = ℘'/2` on
  `y² = x³ + 4x`); replaced by x0-32's model to avoid two parallel models.
* `sqrtD D` (`√D` with `ιC √D = i√|D|`), `IsFrobAbove σ p b D` (arithmetic Frobenius at a prime `𝔓` of
  the algebraic integers containing `p` and `(−b+√D)/2`), `conjPrimeLat p b D = ⟨p, (−b − i√|D|)/2⟩ = 𝔭̄`.
* `tyzForm n = [16(n+1), −8, 1]` (disc `−64n`, `n ≡ 5`), `tyzHeegnerPt n`, `tyzZn n = (1 − [i]) f₀(P_n)`,
  `genusSum Φ z = Σ_{t∈Φ} t(z)`.

**Leaves** (the main theorem consumes `CMFieldOfDefinitionTYZ` and `TYZSigmaFixesZn`; the others are
stated as the CM input of TYZ §3):

| leaf | content | source (numbers UNVERIFIED) |
|---|---|---|
| `CMAlgebraic` | `X0.phiC τ_Q ∈ toC(A(ℚ̄))` for every Heegner form of level 32 | Shimura 1971 Ch. 5–7 (modular parametrization over `ℚ`, CM values algebraic); Gross 1984 |
| `CMFieldOfDefinition H` | `heegnerPt Q ∈ A(H D)` (`H D` = ring class field of disc `D`) | Gross, *Heegner points on X₀(N)* (1984) §3; Shimura 1971 Thm 5.7 |
| `CMFieldOfDefinitionTYZ` | `f₀(P_n) ∈ A(H_{n,4})`, ring-class's `H4bar n` (from CM-2: `cmFieldTYZ_of`) | as above; TYZ Prop 3.2 |
| `ShimuraReciprocity` | for odd `p ∤ D` split, `b² ≡ D (4p)`, `σ` Frobenius above `𝔭 = (p, (−b+√D)/2)`: `σ(P_Q) = P_{Q'}` whenever `B' ≡ B (64)` and `(lat Q', latN Q') = c·𝔭̄·(lat Q, latN Q)` | main theorem of CM (Shimura 1971 Thm 5.4; Silverman, *Advanced topics* II.8.2); Gross 1984 `σ_𝔟(𝒪,𝔫,[𝔞]) = (𝒪,𝔫,[𝔞𝔟⁻¹])` |
| `CMComplexConj` | the automorphism inducing complex conjugation maps `P_{[A,B,C]}` to `P_{[A,−B,C]}` | **proved** (`cmComplexConj`) |
| `TYZSigmaFixesZn` | every `ρ` acting on `H_{n,4}` as Tau Ceti's Artin symbol of ring-class's `sigmaClass n` fixes `z_n` (Shimura reciprocity in TYZ's form) | TYZ Cor 3.9 / Thm 3.6, Shimura reciprocity on `P_n = [h, 1]` (rv-tyz-inputs §1.5) |
| `IInH4` | `i ∈ H_{n,4}` | genus theory (Cox Thm 6.1) |
| `TYZZnOverHprime` | `z_n ∈ A(H'_n)` | **glue** (`tyzZnOverHprime_of`) from `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn` |

Direction in `ShimuraReciprocity`: `Art(𝔭)` maps the lattice class `[𝔞]` to `[𝔭⁻¹𝔞] = [𝔭̄𝔞]`
(arithmetic Frobenius; `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)`). STANDARD; **not checked numerically**: PARI is not
installed on this host (`cypari2` absent; installing it needs the network, which this task may not use).
The Frobenius form determines the whole Galois action on CM points since every class of `Pic(𝒪_D)`
contains split primes; a class-group form needs an action of `Pic(𝒪_D)` on Heegner forms, which no
file provides (Tau Ceti's `ringClassArtinEquiv` is used instead in `ActsAsArtin4`).

## 2. Package.lean, layer by layer

1. §1–§2: `Module GaussianInt PtA`; `ptT = (2, −4)`; `tauG y = y • ptT`; `tauG_eq_zero` (proof: `2T = (0,0)`,
   `4T = 0`, `2[i]T = (0,0)`, and `[i]T = (−2, −4i)` differs in `x`-coordinate from every `kT`).
2. §3–§4: `Pseq` (well-founded recursion), `EpsClasses`, `betaOneSign` (`sgn D · (−2, D)₂`, Serre,
   *Course in arithmetic* III Thm 1, UNVERIFIED number), `IsBetaOneLift`.
3. §5: leaves with parameters `Hn` (`ℍ'_n`) and `Z`: `IContained`, `NormalFields`, `Lemma318`,
   `GenusPtsDefined`, `Thm35First`, `Lemma321`, bundled `GenusPointLeaf`.
4. §6: glue `genusData_of`, `genusPackage_of_genusPointLeaf`, `genusPointLeaf_of_split`,
   `genusPackage_of_split`, `tyzThm35ReadingA_of_split`.
5. §7: ring-class's `HHprime`: `iContained_HHprime`, `normal_Lni`, `normalFields_HHprime`,
   `HprimeNormal`, `genusPackage_of_ringClass`, `tyzThm35ReadingA_of_ringClass`.
6. §8: CM bridge: `ActsAsArtin4`, `CMFieldOfDefinitionTYZ`, `TYZSigmaFixesZn`, `TYZZnOverHprime`,
   `tyzGenusPt`, `GenusPointLeafCM`, `genusPackage_of_cm`, `tyzThm35ReadingA_of_cm`.

`IsBetaOneLift` versus TYZ's "lifting of `β₁`": a lifting satisfies `IsBetaOneLift` (quadratic
characters, normalization-free); the converse would need `ℍ'_n ∩ ℚ^{ab}` multiquadratic (UNVERIFIED), so
the leaves only assert the *existence* of a `σ` with `IsBetaOneLift` (weaker than TYZ's "for any
lifting", hence implied by it). TYZ's proof of Lemma 3.21 uses the lift only through its action on the
multiquadratic `L_n(i)` (rv-tyz-inputs §1.5), so the stronger "for every `σ` with `IsBetaOneLift`"
would also be supported (SPECULATIVE; not used).

## 3. Proposals for the other files (not applied)

* ring-class: prove `HprimeNormal` (normality of `Hprimebar d` over `ℚ`; generalized dihedral
  structure, Cox Lemma 9.3), and a `hilbertbar`/`Kbar` (images of `H_d`, `K_d` in `ℚ̄`) so that
  TYZ's admissible `Φ₀` (lifts of `2Cl_e` into `2Cl'_e`) can be defined.
* x0-32: nothing needed; `X0.phiC`, `X0.PtAC` are used as they are. If `phiC` is renamed, `CM.heegnerPt`
  and `CMAlgebraic` must follow.

## 4. What remains

* TYZ's class-7 genus points (base CM point for `n ≡ 7`) are not pinned; with them,
  `GenusPointLeafCM` splits into three genuine leaves (`genusPointLeaf_of_split`).
* `HprimeNormal` and `IInH4` (ring class field facts) are leaves; Tau Ceti's norm-group description
  might prove `IInH4`; `HprimeNormal` needs that ring class fields are Galois over `ℚ`.
* `CMAlgebraic`, `CMFieldOfDefinition(TYZ)`, `ShimuraReciprocity`, `TYZSigmaFixesZn` are not proved;
  `ShimuraReciprocity`'s direction is not checked numerically (no PARI), but was re-derived by the
  independent review (Cox Cor. 11.37, Shimura Thm 5.4).
* Duplicates: x0-32 independently proved `X0.cmComplexConj` and `X0.lemma318_iff` (files
  `X0CM.lean`, `X0Pkg.lean`) after merging this branch; both versions compile together (VERIFIED,
  `lake build … X0CM X0Pkg`). The integrator may keep either.
