# bst-regular: `G_K`-regularity of `B_st` and Fontaine's dimension form vs basis form

**Result.** All three target theorems compile, but each is **conditional** on two Props, (c) and (d). The tree
does not prove (c) or (d). The abstract step (a) and step (b) are proved unconditionally. **No count change:** this
task retires no frozen field and edits no existing file.

| target | status | Lean name |
|---|---|---|
| 1. dimension form ⇒ basis form over `G_K` | proved from `BstFracInvariants`, `BstLineUnits` | `BstRegular.isAdmissibleT_of_isAdmissible` |
| 2. `IsPstFBasis ↔ IsPstF`, `LocalIsPstFBasis ↔ LocalIsPstF` | proved from the same two Props | `BstRegular.isPstFBasis_iff_isPstF`, `BstRegular.localIsPstFBasis_iff_localIsPstF` |
| 3. `ColmezThm01 ↔ BergerSurveyF` | proved from the same two Props (the forward direction needs neither: it is `bergerSurveyF_of_colmez`) | `BstRegular.colmezThm01_iff_bergerSurveyF` |
| (a) for every `H`-regular `B ⊆ B_dR`: dimension form ⇒ basis form | **proved, unconditional** | `BstRegular.isAdmissibleT_of_isAdmissible_of_regular` |
| (b) every `ℚ_p`-subalgebra of `B_dR` is a domain | **proved, unconditional** | `BstRegular.isDomain_sub` |

Base `182e3388b7416a1d625b1786b945b2e2b77b2e4e` (confirmed with `git rev-parse HEAD`). Files:
`ZInQKernel/Contrib/OneProof/BstRegular/Abstract.lean` and `ZInQKernel/Contrib/OneProof/BstRegular/Bst.lean`. Both
build with `lake build`. Results log: `scratch/bst-regular/log.md`. Axiom check: `scratch/bst-regular/Axioms.lean`.

Marks: **VERIFIED** means compiled here or read in the tree. **STANDARD** means published, with an exact
reference. **UNVERIFIED** means a locator given from memory (there was no network access).

## 1. Exact types (VERIFIED, `#check` output; namespace `HDec.PkgI4.BstRegular`)

```
isAdmissibleT_of_isAdmissible_of_regular : ∀ (p : ℕ) [Fact (Nat.Prime p)] {E : Type u_1} [Field E] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] {n : ℕ} (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)),
  IsRegularB p B H → ∀ (ρ : GQp p →* GL (Fin n) E), BergerBst.IsAdmissible p B H ρ → BmaxOne.IsAdmissibleT p B H ρ

isAdmissibleT_of_isAdmissible : ∀ (p : ℕ) [Fact (Nat.Prime p)] {E : Type u_1} [Field E] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] {n : ℕ}, BstFracInvariants → BstLineUnits →
  ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] ↥K] {ε₀ : PreTilt 𝓞_ℂ_[p] p}
    (h : IsGenEps p ε₀) {w : Ainf p} (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} → ∀ (ρ : GQp p →* GL (Fin n) E),
    IsAdmissible p (BstFOf p h w hw) K.fixingSubgroup ρ → IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ

isPstFBasis_iff_isPstF : ∀ (p : ℕ) [Fact (Nat.Prime p)] {E : Type u_1} [Field E] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] {n : ℕ}, BstFracInvariants → BstLineUnits →
  ∀ {ε₀} (h : IsGenEps p ε₀) {w : Ainf p} (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} → ∀ (ρ : GQp p →* GL (Fin n) E),
    IsPstFBasis p h w hw ρ ↔ IsPstF p h w hw ρ

localIsPstFBasis_iff_localIsPstF : ∀ (p : ℕ) [Fact (Nat.Prime p)], BstFracInvariants → BstLineUnits →
  ∀ {ε₀} (h : IsGenEps p ε₀) {w : Ainf p} (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    LocalIsPstFBasis p h w hw n ρ ↔ LocalIsPstF p h w hw n ρ

colmezThm01_iff_bergerSurveyF : BstFracInvariants → BstLineUnits →
  (PanBergerRefereed.ColmezThm01 ↔ PanDict.BergerSurveyF)
```

`#print axioms`: every theorem above, plus `isDomain_sub` and `isRegularB_bst`, depends on
`[propext, Classical.choice, Quot.sound]` only. The output is pasted in `scratch/bst-regular/log.md`.

## 2. The two open Props (unproved; Lean text from `BstRegular/Bst.lean`)

Here `B_st = BstFOf p h ξ (theta_xi' p)`. The targets are stated for every generator `w` of `ker θ` and reduce to
`ξ` through `bstFOf_eq_xi`.

```
def BstFracInvariants : Prop :=            -- (c): (Frac B_st)^{G_K} ⊆ B_st
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ x ∈ BstFOf p h (xi p) (theta_xi' p), ∀ y ∈ BstFOf p h (xi p) (theta_xi' p), y ≠ 0 →
    ∀ z : BdR p, z * y = x → (∀ σ ∈ K.fixingSubgroup, bdrAct p σ z = z) → z ∈ BstFOf p h (xi p) (theta_xi' p)

def BstLineUnits : Prop :=                 -- (d): G_K-stable ℚ_p-lines of B_st are spanned by units
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ b ∈ BstFOf p h (xi p) (theta_xi' p), b ≠ 0 →
    (∀ σ ∈ K.fixingSubgroup, ∃ c : ℚ_[p], bdrAct p σ b = algebraMap ℚ_[p] (BdR p) c * b) →
    ∃ b' ∈ BstFOf p h (xi p) (theta_xi' p), b * b' = 1
```

Printed source for both: Fontaine proves that `B_st` is `G_K`-regular, with `(Frac B_st)^{G_K} = B_st^{G_K} = K_0`
(Astérisque 223 (1994), Exp. II §5 / Exp. III §1; locators UNVERIFIED). The route guide is Brinon–Conrad, CMI
notes, §9.1–9.2. Those notes are unrefereed and are not a source.

**Which targets each Prop blocks:** all three targets (1, 2a, 2b and the backward direction of 3) need both (c)
and (d), through `isRegularB_bst`. The forward direction of 3 needs neither.

## 3. What was proved

**(a) Abstract step** (`Abstract.lean`). `IsRegularB p B H` has three fields:
* `stable`: `H` maps `B` into `B`.
* `frac`: `(Frac B)^H = B^H` with fractions cleared. For `x, y ∈ B` with `y ≠ 0` and `σ(x)·y = x·σ(y)` for all
  `σ ∈ H`, there is `c ∈ B^H` with `x = c·y`.
* `line`: a nonzero `b ∈ B` with `σ b ∈ ℚ_p·b` for all `σ ∈ H` is a unit of `B`.

`B` being a domain is not a field, because it is automatic (step (b)). `IsRegularB.inv_fixed` shows that `B^H` is a
field.

The proof of `isAdmissibleT_of_isAdmissible_of_regular` (VERIFIED):
1. `dim_{B^H} D = N := dim_{ℚ_p} V` gives `N` elements `d_j ∈ D` that are independent over `B^H`. This uses
   `exists_linearIndependent_of_le_finrank` and needs no field structure on `B^H`.
2. Let `M ∈ M_N(B)` be the matrix of their coordinates in the basis `1 ⊗ e_i`.
3. Suppose `det M = 0`. Then there is a kernel vector of minimal support (`Matrix.exists_mulVec_eq_zero_iff`, `B`
   a domain). Fix an index `j₀` where it is nonzero. For each `σ ∈ H`, the vector `σ(v_{j₀})v − v_{j₀}σ(v)` is a
   kernel vector with smaller support, so it is zero. Then `frac` gives `v = v_{j₀}·c` with `c` in `(B^H)^N`. Torsion
   freeness then gives `Σ c_j d_j = 0` with `c_{j₀} = 1`, which contradicts step 1.
4. `M = R(σ)·σ(M)`, where `R(σ)` is the `ℚ_p`-matrix of `ρ(σ)`. So `σ(det M) = det R(σ)^{-1}·det M`.
5. By `line`, `det M` is a unit. Then `M` is invertible, and the `d_j` are the image of the standard basis under
   `Matrix.toLinearEquiv'`.

**(b)** `isDomain_sub`: every `ℚ_p`-subalgebra of `B_dR` is a domain, because `B_dR` is a field
(`isField_BDeRham`).

**From (c), (d) to regularity** (`Bst.lean`): `isRegularB_bst`. Stability is `FontaineSt.bstF_stable`. `frac`
writes `z = x·y⁻¹` in `B_dR` and cancels `y·σ(y) ≠ 0`. `line` is (d) as stated.

## 4. Plan for (c) and (d): tree inventory and what is missing

Before writing the Props I searched the tree for each step under its usual names. No regularity statement for
`B_cris`, `B_st` or `B_max` is proved under another name. The only named input on invariants,
`BergerBst.FontaineBstInvariants` (`dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]`, BergerBst.lean §11), is a Prop and is not
proved.

### (c) `(Frac B_st)^{G_K} ⊆ B_st`
The printed route: a `G_K`-invariant `z ∈ Frac(B_st)` lies in `B_dR^{G_K} = K`, and `K ∩ Frac(B_st) = K_0 ⊆ B_st`.

| sub-step | tree status |
|---|---|
| c1. `z ∈ B_dR^{G_K}` ⇒ `z` is the image of some `a ∈ K` | **Partial.** `BdRInv.bdRInvariantsPrinted_proof` gives the dimension form only. The element form exists at `K = ℚ_p` only (`LogPTransc.bdr_invariant_eq_algebraMap`, LogPTranscendenceBdR.lean). For general `K`, the proof in BdRInvariants.lean (steps 2–3: an invariant `x` is `0` or a unit of `B_dR^+`; `θ(x) ∈ K` by `axSenTate_proof`; `x` equals the Hensel lift from G9 `exists_hensel_lift`) contains the element form but does not state it. Missing: an exported lemma. |
| c2. `K ∩ Frac(B_st) ⊆ K_0`, i.e. `K ⊗_{K_0} B_st → B_dR` injective (Fontaine) | **Missing, deep.** The printed proof uses the Frobenius of `B_cris^+`. The tree has no Frobenius on `A_cris` or `B_cris`: `AcrisImagePhi.lean`'s `phi` is the divided-power series map, not Frobenius, and `BcrisOf ⊆ B_dR` is not Frobenius-stable inside `B_dR`, so the abstract model `AbstractAcris` / `PanBergerSplit.Acris` would be needed. Transcendence of `log [p̃]` over `B_cris` is proved at `K = ℚ_p` (`LogPFontaine.logPTildeTranscendental_proof`, `LogPTransc.transcendental_bcrisOf`, `bcrisPolyEquiv`), but not over `K ⊗_{K_0} B_cris`. |
| c3. `K_0 = W(k_K)[1/p] ⊆ B_st` | **Partial.** PanBergerSanity.lean has Teichmüller lifts of prime-to-`p` roots of unity in `B_st^{G_K}` (`teichB_pow_mem_bstInv`, `natDegree_minpoly_le_finrank_bstInv`). Missing: `W(k̄) → A_inf` and its image in `B_cris^{G_K}`. |

### (d) lines in `B_st` are units
The printed route: a line `b` lies in `B_cris` (degree argument in `X = log [p̃]`), and a line in `B_cris` is
`t^m·u` with `u` a unit.

| sub-step | tree status |
|---|---|
| d1. a line `b ∈ B_st = B_cris[X]` has `X`-degree 0 | **Missing, moderate.** Compare the `X^d` and `X^{d−1}` coefficients, using `σ(X) = X + log [u_σ]` and `bcrisPolyEquiv`. If `d ≥ 1`, then `r + dX ∈ B_dR^{G_K}` with `r ∈ Frac(B_cris)`. To rule this out at general `K` one needs `log [p̃] ∉ Frac(B_cris) + B_dR^{G_K}`. The tree proves this only for `G_{ℚ_p}` (`LogPTransc` LogCore, `notInFrac_bmax_logPTilde`). At general `K` it needs c1 and c2. |
| d2. a line in `B_cris` is a unit | **Missing, deep.** Write `b = t^m·b₀` with `b₀ ∈ (B_dR^+)^×`, so that `θ(b₀)` spans a `C_p(ηχ^{−m})` line. Sen's theorem on `C_p`-admissible characters and the Frobenius eigenvalue argument (`B_cris^{φ=1} ∩ B_dR^+ = ℚ_p`, the fundamental exact sequence) finish the proof. In the tree: `t⁻¹ ∈ B_cris` (by definition, `Ring.inverse (tOf p h)` is adjoined), the filtration `filB`, `theta0`, `theta1` (DeRhamScholzeHT.lean), Tate's `C_p(i)^{G_K} = 0` for `i ≠ 0` (`tateTwistInvariants_proof`), and Ax–Sen–Tate (`axSenTate_proof`). Missing: Frobenius on `B_cris`, the fundamental exact sequence, and Sen's theorem. |

Recommendation for the fold desk: the swap `BergerSurveyF → ColmezThm01` is equivalence-preserving only after (c)
and (d) are proved. Until then, `colmezThm01_iff_bergerSurveyF` turns the swap into "add (c) and (d) as leaves". That
is a count change unless (c) and (d) can be cited as one printed statement (`B_st` is `G_K`-regular, Fontaine).
Whether the page reading admits that citation is for the fold desk.
