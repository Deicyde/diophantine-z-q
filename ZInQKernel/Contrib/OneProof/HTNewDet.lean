import ZInQKernel.OneProof.H.TailB

/-! # htnew-det: can determinants replace `eigenformHTNew`? (No: the twist is not known to be finite.)

Task htnew-det (2026-11-16), report `docs/research/htnew-det.md`. Nothing here proves a research
field, and no statement of the chain is changed.

The research field `eigenformHTNew` is read only as `r13 : PkgI4.EigenformHT`, and `r13` only by
`G0Galois.g12` (through `g8_g12`), which hands it to the glue `G0Galois.G12Weight`. There it is used
only to rule out eigenforms of weight `k ≥ 3` (ht-bypass). The suggested replacement compares
determinants: `det r₅ = ψ² · det ρ_g = ψ² ε χ^{k−1}` and `(det r₅)² = χ²` on `G_K`
(Weil pairing). This file proves in Lean exactly what that comparison yields, and that it is
sharp:

* `twist_sq_mul_cyc_finite`: the determinant data in weight `k` give that `ψ² χ^{k−2}` has finite
  image, and nothing more about `ψ`. At `k = 2` this is the chain's `GlueAssembly.twist_finite`.
* `det_data_weight_shift`, `charpoly_smul_fin_two`, `frobPoly_weight_shift`,
  `traceTwist_weight_shift`: every determinant, trace and Frobenius characteristic-polynomial
  identity that the chain's leaves (DS 9.6.5, R14's determinant clause, Pan's trace form, the
  Weil-pairing determinant) state is unchanged under `(k, ψ, a_q) ↦ (k + 2m, ψ χ^{−m}, q^m a_q)`
  (the `θ^m`-twist: `θ^m f = Σ n^m a_n qⁿ` is a `p`-adic eigenform of weight `2 + 2m` with
  Galois representation `ρ_f ⊗ χ^m`, not a classical one).
* `twist_shift_not_finite`: after the shift by `m ≠ 0` the twist has infinite image whenever
  `χ^m` does (the cyclotomic character), so the finiteness of `ψ` that the proposed argument
  presupposes is not a consequence of the determinant data; in `g12` it is derived only *after*
  `k = 2` is known, from the weight comparison that reads `r13`.

So the determinant comparison is circular: it needs `ψ` of finite order to get `k = 2`, and
`k = 2` to get `ψ` of finite order. The smallest input `g12` needs instead is
`NoHighWeightTwist5` (§2): the `k ≥ 3` half of `G12Weight`'s content, with no `R13` hypothesis;
`G12Weight` follows from it with the proved pieces and the leaves `SenTwist`, `FiniteImageHT`
(`g12WeightNoR13_of`, `g12Weight_of_noR13`), and it follows from the chain's own route through
`r13` (`noHighWeightTwist5_of_g12Weight`). It is GLUE (a corollary of Kato's theorem with Sen's
twist theorem), not a printed-form leaf, so it is not added.
-/

noncomputable section

namespace ZInQ.Contrib.HTNewDet

open Polynomial

/-! ## 1. What the determinant data give, and why it is not enough -/

section Det

variable {G E : Type*} [Group G] [Field E]

/-- **The determinant argument in weight `k`** (generalizes `GlueAssembly.twist_finite`, which is the
case `k = 2`). With `r = det r₅`, `ε` the nebentypus as a Galois character, `χ` the cyclotomic
character, `ψ` the twist: if `r = ε χ^{k−1} ψ²` (R14's determinant clause, `det ρ_g = ε χ^{k−1}`,
times `ψ²`), `r² = χ²` on a finite-index `H` (Weil pairing: `det V₅(A) = χ²` on `G_K`,
`V₅(A) ≅ r₅ ⊕ r₅`), and `ε` has finite image, then `ψ² χ^{k−2}` has finite image. -/
theorem twist_sq_mul_cyc_finite (H : Subgroup G) [H.FiniteIndex] (r ε χ ψ : G →* Eˣ) (k : ℤ)
    (hdet : ∀ g, r g = ε g * χ g ^ (k - 1) * ψ g ^ 2)
    (hH : ∀ h ∈ H, r h ^ 2 = χ h ^ 2) (hε : (Set.range ε).Finite) :
    (Set.range fun g => ψ g ^ 2 * χ g ^ (k - 2)).Finite := by
  classical
  let α : G →* Eˣ := r * χ⁻¹
  have hαH : (α '' H).Finite := by
    refine Set.Finite.subset ((Polynomial.nthRoots 2 (1 : E)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn) ?_
    rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (by norm_num)]
    have := hH h hh
    have e : (α h) ^ 2 = 1 := by
      simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, this,
        mul_inv_cancel]
    have := congrArg Units.val e
    simpa using this
  have hα := GlueAssembly.finite_range_of_finiteIndex α H hαH
  have hsq : (Set.range fun g => ψ g ^ 2 * χ g ^ (k - 2)) ⊆
      (fun p : Eˣ × Eˣ => p.1 * p.2⁻¹) '' (Set.range α ×ˢ Set.range ε) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(α g, ε g), ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, ?_⟩
    simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, hdet]
    have hk : χ g ^ (k - 1) = χ g ^ (k - 2) * χ g := by
      rw [← zpow_add_one]; ring_nf
    rw [hk, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  exact ((hα.prod hε).image _).subset hsq

/-- **The determinant identity is invariant under the weight shift** `(k, ψ) ↦ (k + 2m, ψ χ^{−m})`.
So no argument that reads only `r = ε χ^{k−1} ψ²` (with `r² = χ²` on `H`, `ε` finite, which do not
mention `k` or `ψ`) can tell `k = 2` from `k = 2 + 2m`. -/
theorem det_data_weight_shift {G E : Type*} [Group G] [CommGroup E] (r ε χ ψ : G →* E) (k m : ℤ)
    (hdet : ∀ g, r g = ε g * χ g ^ (k - 1) * ψ g ^ 2) :
    ∀ g, r g = ε g * χ g ^ (k + 2 * m - 1) * (ψ g * χ g ^ (-m)) ^ 2 := by
  intro g
  have hc : ∀ a b c d : E, a * b * d = a * (b * c) * (d * c⁻¹) := by
    intro a b c d
    rw [show d * c⁻¹ = c⁻¹ * d from mul_comm _ _]
    group
  have : χ g ^ (k + 2 * m - 1) = χ g ^ (k - 1) * χ g ^ (2 * m) := by
    rw [← zpow_add]; ring_nf
  have h2 : (χ g ^ (-m)) ^ 2 = (χ g ^ (2 * m))⁻¹ := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]; ring_nf
  rw [hdet g, mul_pow, this, h2]
  exact hc _ _ _ _

/-- After the shift by `m`, a finite-image twist becomes an infinite-image one as soon as `χ^m`
has infinite image (the cyclotomic character, `m ≠ 0`). Hence "`ψ` has finite image" is not a
consequence of the determinant data in weight `k` (it holds for `(2, ψ)` and fails for
`(2 + 2m, ψ χ^{−m})`, which satisfy the same identities). -/
theorem twist_shift_not_finite {G E : Type*} [CommGroup E] (ψ χ : G → E) (m : ℤ)
    (hψ : (Set.range ψ).Finite) (hχ : ¬ (Set.range fun g => χ g ^ m).Finite) :
    ¬ (Set.range fun g => ψ g * χ g ^ (-m)).Finite := by
  intro h
  apply hχ
  refine ((hψ.prod h).image fun p : E × E => p.1 * p.2⁻¹).subset ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨(ψ g, ψ g * χ g ^ (-m)), ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, ?_⟩
  simp [zpow_neg]

end Det

section Frob

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- **Frobenius characteristic polynomials under a scalar twist** (`2 × 2`): if `M` has
characteristic polynomial `X² − a X + b`, then `c • M` has `X² − (c a) X + c² b`. -/
theorem charpoly_smul_fin_two (M : Matrix (Fin 2) (Fin 2) R) (c a b : R)
    (h : M.charpoly = X ^ 2 - C a * X + C b) :
    (c • M).charpoly = X ^ 2 - C (c * a) * X + C (c ^ 2 * b) := by
  rw [Matrix.charpoly_fin_two] at h ⊢
  have h1 := congrArg (fun P : R[X] => P.coeff 1) h
  have h0 := congrArg (fun P : R[X] => P.coeff 0) h
  simp [coeff_X, coeff_C] at h1 h0
  rw [Matrix.trace_smul, Matrix.det_smul, h1, h0]
  simp [smul_eq_mul]

/-- **DS 9.6.5's Frobenius polynomial under the `θ^m`-twist.** If `ρ(Frob_q)` has
characteristic polynomial `X² − a_q X + e q^{k−1}` (Diamond–Shurman 9.6.5 for a weight-`k` form
with `e = χ(q)`; `k − 1 = j`), then `(χ_cyc^m ⊗ ρ)(Frob_q) = q^m ρ(Frob_q)` has
`X² − (q^m a_q) X + e q^{(k + 2m) − 1}`: the polynomial DS 9.6.5 attaches to a weight-`(k + 2m)`
form with coefficients `q^m a_q` and the same nebentypus. -/
theorem frobPoly_weight_shift (M : Matrix (Fin 2) (Fin 2) R) (q : R) (a e : R) (j m : ℕ)
    (h : M.charpoly = X ^ 2 - C a * X + C (e * q ^ j)) :
    ((q ^ m) • M).charpoly = X ^ 2 - C (q ^ m * a) * X + C (e * q ^ (j + 2 * m)) := by
  rw [charpoly_smul_fin_two M (q ^ m) a _ h]
  have : (q ^ m) ^ 2 * (e * q ^ j) = e * q ^ (j + 2 * m) := by ring
  rw [this]

/-- **Pan's trace form under the shift**: `tr r(σ) = ψ(σ) x` iff `tr r(σ) = (ψ(σ) χ(σ)^{−m}) (χ(σ)^m x)`;
at an arithmetic Frobenius `χ(σ) = q`, so the "coefficient" becomes `q^m a_q`. -/
theorem traceTwist_weight_shift {K : Type*} [Field K] (t ψσ χσ x : K) (hχ : χσ ≠ 0) (m : ℤ)
    (h : t = ψσ * x) : t = (ψσ * χσ ^ (-m)) * (χσ ^ m * x) := by
  rw [h, zpow_neg]
  field_simp

end Frob

/-! ## 2. The smallest input `g12` needs, and `G12Weight` without `R13` -/

open _root_.PkgI4 (GaloisRep GaloisChar)

/-- **No eigenform of weight `≥ 3` is attached, up to a twist, to an irreducible `r` with
Hodge–Tate weights `{0, −1}` at 5 (GLUE; the `k ≥ 3` content of `G12Weight`, h-trust C8).**
Exactly what `G0Galois.g12` needs beyond the proved pieces, at the one place it is used (`ℓ = 5`,
Pan∘Berger's `g` for G8's `r₅`). Consequence of Kato, Astérisque 295 (2004) §§9.2-9.4 (de Rham with
Hodge–Tate weights `{0, k − 1}`, cohomological normalization, every level; newforms) with Sen's
twist theorem (`SenTwist`), Chebotarev and Brauer–Nesbitt; see `noHighWeightTwist5_of_g12Weight`.
Not a printed-form leaf (the printed object `V_{F_λ}(f)` is not definable in Mathlib, and the
statement mixes Kato's theorem with Sen's), so it is not added as a leaf. §1 shows the
determinant data cannot prove it. -/
def NoHighWeightTwist5 : Prop :=
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 3 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    HDec.PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    False

/-- `HDec.G0Galois.G12Weight` without its `PkgI4.EigenformHT` (= `r13`) hypothesis. -/
def G12WeightNoR13 : Prop :=
  HDec.HSyn.EigenformRepExists → HDec.HSyn.DeligneSerreConseq → HDec.HSyn.FrobeniusDense →
  HDec.HSyn.BrauerNesbitt →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    HDec.PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}

/-- `G12Weight` from its `R13`-free form (the `R13` hypothesis is discarded). -/
theorem g12Weight_of_noR13 (h : G12WeightNoR13) : HDec.G0Galois.G12Weight :=
  fun hR _ hDS hFD hBN => h hR hDS hFD hBN

/-- **`G12WeightNoR13` from `NoHighWeightTwist5`** with the leaves `SenTwist`, `FiniteImageHT` and
the proved glue (`twistExists`, `twistConj_of`, `htConj_of htExtend`): `k = 1` by Deligne–Serre
as in `g12Weight_of`, `k = 2` with `n = 0`, `k ≥ 3` excluded by `NoHighWeightTwist5`. -/
theorem g12WeightNoR13_of (hSen : HDec.G0Galois.SenTwist) (hFI : HDec.G0Galois.FiniteImageHT)
    (hNo : NoHighWeightTwist5) : G12WeightNoR13 := by
  intro hR hDS hFD hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  rcases lt_trichotomy k 2 with hlt | rfl | hgt
  · -- weight one: `ρ_g` has finite image, so `ψ ⊗ ρ_g` would have equal weights
    exfalso
    have h1 : k = 1 := by omega
    subst h1
    obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N 1 χ g hN le_rfl hg
    let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
    have hss' : ρ.IsSemisimple := hss
    have hatt' : ρ.AttachedTo ιC ιL g := hρatt
    obtain ⟨ρ', htw⟩ := HDec.G0Galois.twistExists 5 2 ρ ψ
    have hconj : HDec.G0Galois.IsConj r ρ' :=
      HDec.G0Galois.twistConj_of hFD hBN 5 r ρ ρ' ψ ιC ιL N 1 g S hN hirr hss' hatt' hatt htw
    have hw' : HDec.PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ') 5 {0, -1} :=
      HDec.G0Galois.htConj_of HDec.G0Galois.htExtend 5 2 r ρ' _ hconj hw
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
    have h0 : HDec.PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 (Multiset.replicate 2 0) :=
      hFI 5 2 ρ hfin
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h0 hw'
    have ha : (0 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    have hb : (-1 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    rw [hs] at ha hb
    simp only [Multiset.mem_map, Multiset.mem_replicate] at ha hb
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := ha
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hb
    omega
  · exact ⟨0, by norm_num⟩
  · exact (hNo r N k χ g ψ ιC ιL S hN (by omega) hg hirr hw hatt).elim

/-- **`G12Weight` with no `R13`** from `NoHighWeightTwist5` and the leaves `SenTwist`,
`FiniteImageHT` (those `g12Weight_of_senTwist` takes). -/
theorem g12Weight_of_noHighWeight (hSen : HDec.G0Galois.SenTwist)
    (hFI : HDec.G0Galois.FiniteImageHT) (hNo : NoHighWeightTwist5) : HDec.G0Galois.G12Weight :=
  g12Weight_of_noR13 (g12WeightNoR13_of hSen hFI hNo)

/-- **`NoHighWeightTwist5` is implied by the chain's route through `r13`**: `G12Weight` with the
leaves it takes (R14, R13, R15, T18, T19) gives it, by `g12Weight_concl_iff`. So it is no stronger
than what `g12` already uses. -/
theorem noHighWeightTwist5_of_g12Weight (hW : HDec.G0Galois.G12Weight)
    (hR14 : HDec.HSyn.EigenformRepExists) (hR13 : HDec.PkgI4.EigenformHT)
    (hR15 : HDec.HSyn.DeligneSerreConseq) (hT18 : HDec.HSyn.FrobeniusDense)
    (hT19 : HDec.HSyn.BrauerNesbitt) : NoHighWeightTwist5 := by
  intro r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  have h := hW hR14 hR13 hR15 hT18 hT19 r N k χ g ψ ιC ιL S hN (by omega) hg hirr hw hatt
  have := (HDec.G0Galois.g12Weight_concl_iff k (by omega)).mp h
  omega

end ZInQ.Contrib.HTNewDet
