import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.RationalTate
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaT
import ZInQKernel.Contrib.OneProof.RC.Skeleton.Steps

/-!
# Lane RC30 (base zero), part 3: central dimensions `(1,1)` at the base from full Selmer corank one

Lemma `ex:arith-base-zero` (`diophantine_zq.tex`, 11/5 version, tex 4350–4352):

> Full Selmer corank one gives central dimensions `(1,1)` in degrees one and two and zero in every
> other degree. This uses the full Selmer group, including a possible divisible part of `Ш`.

Lanes RC15, RC25 carry this as the field `hcentral : (Dm.map ρ).rank = m` (ELLIOT) of the base
model: for the two-term model `[A^{m+1} --Dm--> A^{m+1}]` (degrees one and two) of the primitive
complex over `A = Λ_(t)`, the central fibre `[ℚ₂^{m+1} --D̄--> ℚ₂^{m+1}]` (`D̄ = ρ(Dm)`) has
cohomology `ker D̄` and `coker D̄`, and `hcentral` says both are one-dimensional.

The text's step has three parts.

1. **The central degree-one cohomology is the rational full Selmer group.** The central fibre of
   the model computes the central cohomology of the primitive complex (it is the actual complex
   after cancelling unit disks, a homotopy equivalence over `A` that specializes), which the
   comparison `i : K₀ → R₀` identifies with the cohomology of the ordinary rational Kummer complex
   (tex 3952–3962: "All three maps are quasi-isomorphisms"). Its degree-one cohomology is the
   rational `2`-adic Selmer group `V₂ Sel_{2^∞}(E/K)` of the full Selmer group, divisible part of
   `Ш` included (universal coefficients with `ℚ₂/ℤ₂`, tex 5305–5311:
   `0 → H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K) → H²(C_K)_tors → 0`). Over `K = ℚ(√k)` it splits, after
   inverting two, into the `Gal(K/ℚ)`-eigenspaces `V₂ Sel_{2^∞}(E/ℚ) ⊕ V₂ Sel_{2^∞}(E^{(k)}/ℚ)`
   (the sum-and-difference identity behind `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`, tex 2616–2626).
   This identification is the input `CentralSelmerComparison` (one `ℚ₂`-linear isomorphism).
2. **Full Selmer corank one**: `corank Sel_{2^∞}(E/ℚ) = 1` and `corank Sel_{2^∞}(E^{(k)}/ℚ) = 0`,
   the hypothesis `SelmerCorankOneOverK ℓ k` of the lemma (lane RC0's form of `s₂(E/K) = 1`), over
   the genuine Selmer groups `selmerTwoPower`.
3. **The count** (PROVED): the rational Tate module of a group of `ℤ₂`-corank `r` has dimension
   `r` (`finrank_ratTate_of_Z2Corank`, file `RationalTate.lean`), so `dim ker D̄ = 1 + 0 = 1`, and
   by rank–nullity `rank D̄ = m` and `dim coker D̄ = 1`: central dimensions `(1,1)`.

The model has no terms outside degrees one and two and is square (Euler characteristic zero);
those are properties of the model fields `m`, `Dm`, unchanged from lanes RC15/RC25. Given them,
the degree-two count follows from the degree-one count, so no separate duality input is needed for
`hcentral`.

Contents (every theorem `PROVED`):
* `CentralSelmerComparison S₁ S₂ Dm` (the input of part 1);
* `rank_eq_of_finrank_ker`, `finrank_coker_of_rank_eq` (rank–nullity at the centre);
* `CentralSelmerComparison.finrank_ker`, `.hcentral`, `.finrank_coker` (parts 2–3 for groups
  `S₁`, `S₂` of coranks `1`, `0`);
* `hcentral_of_selmer`: lane RC25's field `hcentral` from `SelmerCorankOneOverK ℓ k` and the
  comparison for the genuine Selmer groups of `E_ℓ` and `E_ℓ^{(k)}` (the bridge);
* transparency: `nonempty_centralSelmerComparison_iff` (the comparison exists iff the central
  degree-one dimension is `r₁ + r₂`) and `nonempty_centralSelmerComparison_iff_hcentral` (under
  `SelmerCorankOneOverK` it is equivalent to `hcentral`): what is gained is that the remaining
  input is the identification of the central cohomology with the rational full Selmer group (the
  meaning of the text's "gives"), stated over the genuine Selmer groups, while the corank
  arithmetic and rank–nullity are proved.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
open Matrix Module

/-! ## The comparison input -/

/-- **The central degree-one cohomology of the base model is the rational full Selmer group**
(tex 4350–4352, with tex 3952–3962 and 5305–5311). For the two-term model `Dm` of the primitive
complex at the base over `A = Λ_(t)`, an isomorphism of `ℚ₂`-vector spaces between the central
degree-one cohomology `ker ρ(Dm)` and `V₂S₁ × V₂S₂` (`RatTate`: the rational Tate modules), where
`S₁`, `S₂` are the Selmer groups `Sel_{2^∞}(E/ℚ)`, `Sel_{2^∞}(E^{(k)}/ℚ)` in the application.
Kind: ELLIOT (the comparison `i : K₀ → R₀` is a quasi-isomorphism, tex 3961–3962) + GLUE (the
cancellation of unit disks is a homotopy equivalence over `A` and commutes with `A → ℚ₂`; the
degree-one cohomology of the rational Kummer complex is `V₂ Sel_{2^∞}(E/K)` by universal
coefficients, tex 5305–5311, the full Selmer group with the divisible part of `Ш`; after inverting
two it is the sum of the `Gal(K/ℚ)`-eigenspaces `V₂ Sel_{2^∞}(E/ℚ)` and
`V₂ Sel_{2^∞}(E^{(k)}/ℚ)`). DEPARTURE (form): the Selmer group over `K` is not defined in the
library; as in lane RC0's `SelmerCorankOneOverK`, it enters through the two rational Selmer
groups. -/
structure CentralSelmerComparison (S₁ S₂ : Type*) [AddCommGroup S₁] [AddCommGroup S₂] {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT) where
  /-- the identification of the central degree-one cohomology -/
  cmp : LinearMap.ker (Dm.map Rings.rhoT).mulVecLin ≃ₗ[ℚ_[2]] RatTate S₁ × RatTate S₂

/-! ## Rank–nullity at the centre -/

/-- **`rank D̄ = m` from `dim ker D̄ = 1`** for a square matrix of size `m + 1` over a field
(rank–nullity). PROVED. -/
theorem rank_eq_of_finrank_ker {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜)
    (h : finrank 𝕜 (LinearMap.ker D.mulVecLin) = 1) : D.rank = m := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  rw [h, finrank_fin_fun] at hrn
  unfold Matrix.rank
  omega

/-- **`dim coker D̄ = 1` from `rank D̄ = m`** for a square matrix of size `m + 1` over a field: the
degree-two cohomology of the central fibre is one-dimensional. PROVED. -/
theorem finrank_coker_of_rank_eq {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) (h : D.rank = m) :
    finrank 𝕜 ((Fin (m + 1) → 𝕜) ⧸ LinearMap.range D.mulVecLin) = 1 := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range D.mulVecLin)
  rw [finrank_fin_fun] at hq
  unfold Matrix.rank at h
  omega

/-- **`dim ker D̄ = 1` from `rank D̄ = m`** for a square matrix of size `m + 1` over a field
(rank–nullity; the converse of `rank_eq_of_finrank_ker`). PROVED. -/
theorem finrank_ker_of_rank_eq {𝕜 : Type*} [Field 𝕜] {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) (h : D.rank = m) :
    finrank 𝕜 (LinearMap.ker D.mulVecLin) = 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  rw [finrank_fin_fun] at hrn
  unfold Matrix.rank at h
  omega

/-! ## The count -/

namespace CentralSelmerComparison

variable {S₁ S₂ : Type*} [AddCommGroup S₁] [AddCommGroup S₂] {m : ℕ}
  {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT}

/-- **The central degree-one dimension is `1`** when `corank S₁ = 1` and `corank S₂ = 0`. PROVED
(`finrank_ratTate_prod_of_Z2Corank`). -/
theorem finrank_ker (C : CentralSelmerComparison S₁ S₂ Dm) (h₁ : Z2Corank S₁ 1)
    (h₂ : Z2Corank S₂ 0) : finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = 1 := by
  have := finiteDimensional_ratTate_prod_of_Z2Corank h₁ h₂
  rw [C.cmp.finrank_eq, finrank_ratTate_prod_of_Z2Corank h₁ h₂]

/-- **Lane RC25's `hcentral` from the comparison and the coranks** (tex 4350–4352): central
dimensions `(1,1)`, in the form `rank ρ(Dm) = m`. PROVED. -/
theorem hcentral (C : CentralSelmerComparison S₁ S₂ Dm) (h₁ : Z2Corank S₁ 1)
    (h₂ : Z2Corank S₂ 0) : (Dm.map Rings.rhoT).rank = m :=
  rank_eq_of_finrank_ker _ (C.finrank_ker h₁ h₂)

/-- **The central degree-two dimension is `1`** (the other half of "central dimensions `(1,1)`",
tex 4350–4351). PROVED. -/
theorem finrank_coker (C : CentralSelmerComparison S₁ S₂ Dm) (h₁ : Z2Corank S₁ 1)
    (h₂ : Z2Corank S₂ 0) :
    finrank ℚ_[2] ((Fin (m + 1) → ℚ_[2]) ⧸ LinearMap.range (Dm.map Rings.rhoT).mulVecLin) = 1 :=
  finrank_coker_of_rank_eq _ (C.hcentral h₁ h₂)

end CentralSelmerComparison

/-- **What the comparison amounts to**: for groups `S₁`, `S₂` of coranks `r₁`, `r₂`, a comparison
exists exactly when `dim ker ρ(Dm) = r₁ + r₂` (both sides are finite-dimensional). So, as an
abstract input, `CentralSelmerComparison` carries the dimension statement "the central degree-one
dimension is the corank of the full Selmer group" (tex 4350–4351), and nothing more. PROVED. -/
theorem nonempty_centralSelmerComparison_iff {S₁ S₂ : Type*} [AddCommGroup S₁] [AddCommGroup S₂]
    {r₁ r₂ m : ℕ} {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT} (h₁ : Z2Corank S₁ r₁)
    (h₂ : Z2Corank S₂ r₂) :
    Nonempty (CentralSelmerComparison S₁ S₂ Dm) ↔
      finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = r₁ + r₂ := by
  have := finiteDimensional_ratTate_prod_of_Z2Corank h₁ h₂
  constructor
  · rintro ⟨C⟩
    rw [C.cmp.finrank_eq, finrank_ratTate_prod_of_Z2Corank h₁ h₂]
  · intro h
    exact ⟨⟨LinearEquiv.ofFinrankEq _ _ (h.trans (finrank_ratTate_prod_of_Z2Corank h₁ h₂).symm)⟩⟩

/-- **Under full Selmer corank one the comparison is equivalent to `hcentral`** (transparency, as
`nonempty_innerLimit45Base_iff` for the inner-limit field): `CentralSelmerComparison` for the
genuine Selmer groups of `E_ℓ`, `E_ℓ^{(k)}` exists iff `rank ρ(Dm) = m`. PROVED. -/
theorem nonempty_centralSelmerComparison_iff_hcentral {ℓ : ℕ} {k : ℤ} {m : ℕ}
    {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT} (hSel : SelmerCorankOneOverK ℓ k) :
    Nonempty (CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm) ↔
      (Dm.map Rings.rhoT).rank = m := by
  rw [nonempty_centralSelmerComparison_iff hSel.1 hSel.2]
  exact ⟨rank_eq_of_finrank_ker _, finrank_ker_of_rank_eq _⟩

/-- **Bridge to lane RC25: the field `hcentral` of the base model** (tex 4350–4352) from the
lemma's hypothesis "full two-primary Selmer corank one for `E/K`" (`SelmerCorankOneOverK ℓ k`:
`corank Sel_{2^∞}(E_ℓ/ℚ) = 1` and `corank Sel_{2^∞}(E_ℓ^{(k)}/ℚ) = 0`, over the genuine Selmer
groups) and the comparison of the central degree-one cohomology with
`V₂ Sel_{2^∞}(E_ℓ/ℚ) × V₂ Sel_{2^∞}(E_ℓ^{(k)}/ℚ)`. PROVED. -/
theorem hcentral_of_selmer {ℓ : ℕ} {k : ℤ} {m : ℕ}
    {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT} (hSel : SelmerCorankOneOverK ℓ k)
    (C : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm) :
    (Dm.map Rings.rhoT).rank = m :=
  C.hcentral hSel.1 hSel.2

end ZInQ.Manuscript.RC.BaseZeroLimit
