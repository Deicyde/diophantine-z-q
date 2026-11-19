import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Chain

/-!
# The common-coordinate leaf from a chain of support triangles at the leaf's values

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194).

A `TriangleChain` over `F = Frac Λ` (for instance `ChainData.toTriangleChain` of a presentation of
the support complexes, `CommonCoordinate13Chain.lean`) whose Frobenius data at step `i` are the
leaf's values at the `i`-th unused prime, and whose two end coordinates have the primitive and
corrected expansions, gives the leaf's chain values (`ChainValues`), hence the current leaf
`CommonCoordinateInputsNF` and (4.7) (`CommonCoordinateTarget`).

* `TriangleChain.AtLeaf C Fam x ps H`: the Frobenius data of the steps of `H` are the leaf's values
  at `p_i`: `Fr_i = ρ_T(Fr_{p_i})` over `F`, `q_i = p_i`, `q_i⁻¹ = p_i⁻¹`, `a_i = a_{p_i}`,
  `z_i = z_{p_i}(x)`, `z_i⁻¹ = z_{p_i}(x)⁻¹`, with `n = |ps|`.
* `chainValues_of_triangleChain`: the chain values of such a chain (`v = H.v`, `σ = H.sign`, the
  steps' (4.7) from `TriangleChain.h47`).
* `CommonCoordinateInputsTC`, **`commonCoordinateInputsNF_of_TC`**,
  **`commonCoordinateTarget_of_TC`**: the leaf from such chains at every address.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- **A chain of support triangles at the leaf's values** (tex 4142–4194): the length is the
number of unused primes in the order `ps`, and the Frobenius data at step `i` are those of the
`i`-th prime: `ρ_T(Fr_{p_i})` over `F`, `p_i`, `p_i⁻¹`, `a_{p_i}`, `z_{p_i}(x)^{±1}`.
Kind: definition. -/
def TriangleChain.AtLeaf (ps : List ℕ) (H : TriangleChain FracLam) : Prop :=
  H.n = ps.length ∧ ∀ i (hi : i < ps.length),
    H.Fr i = (frobMat C ps[i]).map zTwoToF ∧ H.q i = (ps[i] : FracLam) ∧
      H.qi i = (ps[i] : FracLam)⁻¹ ∧ H.a i = (apE ℓ ps[i] : FracLam) ∧
      H.z i = lamToF (zAt Fam x ps[i] : Lambda) ∧
      H.zi i = lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)

/-- **The leaf's chain values from a chain of support triangles at the leaf's values**
(tex 4142–4194): `v = H.v`, `σ = H.sign`, and (4.7) at every step from `TriangleChain.h47`.
Kind: definition. -/
def chainValues_of_triangleChain (D : RCData ℓ) (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) (ps : List ℕ) (hnd : ps.Nodup)
    (hps : ps.toFinset = unusedAt Fam x) (H : TriangleChain FracLam)
    (hH : H.AtLeaf C Fam x ps)
    (hprim : IsTExpansion (H.v 0) (D.uPrim Fam x))
    (htilde : IsTExpansion (etaF ℓ Fam x * H.v ps.length) (D.uTilde Fam x)) :
    ChainValues C D Fam x where
  hprime := hprime
  hgood := hgood
  ps := ps
  hnd := hnd
  hps := hps
  v := H.v
  σ := H.sign
  h47 := fun i hi => by
    obtain ⟨hn, hv⟩ := hH
    obtain ⟨hFr, hq, hqi, ha, hz, hzi⟩ := hv i hi
    have h := H.h47 i (hn ▸ hi)
    rw [hFr, hqi, ha, hz, hzi] at h
    exact h
  hprim := hprim
  htilde := htilde

/-- **The common-coordinate inputs from chains of support triangles** (tex 4142–4194): `E_ℓ`
elliptic, a coefficient datum, and at every address of every final family a chain of support
triangles over `F` at the leaf's values with the primitive and corrected expansions at its ends.
Kind: definition. -/
def CommonCoordinateInputsTC {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      (∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) ∧ (∀ q ∈ F.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) ∧
      ∃ (ps : List ℕ) (H : TriangleChain FracLam), ps.Nodup ∧ ps.toFinset = unusedAt F x ∧
        @TriangleChain.AtLeaf ℓ hE C F x ps H ∧ IsTExpansion (H.v 0) (D.uPrim F x) ∧
        IsTExpansion (etaF ℓ F x * H.v ps.length) (D.uTilde F x)

/-- **The current leaf from chains of support triangles** (tex 4142–4194). Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_TC {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsTC D) :
    CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  refine commonCoordinateInputsNF_of_chainValues ⟨hE, C, fun Co Ce F hF x => ?_⟩
  obtain ⟨hprime, hgood, ps, H, hnd, hps, hH, hprim, htilde⟩ := hT Co Ce F hF x
  exact ⟨@chainValues_of_triangleChain ℓ hE C F x D hprime hgood ps hnd hps H hH hprim htilde⟩

/-- **(4.7) from chains of support triangles** (tex 4142–4194): `RCSteps.common_coordinate`.
Kind: PROVED. -/
theorem commonCoordinateTarget_of_TC {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsTC D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_TC h)

end ZInQ.Manuscript.RC.Wiring
