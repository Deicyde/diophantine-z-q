import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Unit

/-!
# Theorem 5.3, Lane RC0 round 3: (4.7) from the support-triangle models

The leaf `PostLeaves.common_coordinate` asked, at every address of a final family, for a
`CommonCoordinateModel`, whose fields `h47` (the multi-prime (4.7), ELLIOT + GLUE Nekovář
6.4.1–6.4.3) and `hunit` (`ε_q ∈ Λ^×`) were inputs. Batch 3's `commonCoordinateModel_of_actual_models`
(CommonCoordinate) produces both from the support triangle at each relaxation step in the original
integral bases (`ActualStep`: a triangular model whose basis comparisons have `Λ`-unit
determinants), with the full unit `ε_p` of (4.7). This file records its inputs as the structure
`CommonCoordinateTriangles`
and proves `commonCoordinateInputs_of_triangles : CommonCoordinateInputsT D → CommonCoordinateInputs D`
(PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-- **The support-triangle data at one address** (tex 4142–4328; the inputs of batch 3's
`commonCoordinateModel_of_models`). Kinds and owners:
* `R`, `chi`, `Q`, `v`, `g`, `l`, `e`, `ei`, `hsign`, `urel`, `U`, `hU`, `hutilde`: the coefficient
  ring `𝒪[G]`, the character at the address, the graph primes and their factors, the unused primes,
  `ũ = η u_rel` (definition; tex 4151–4226; owner RC15 / RC7);
* `hratio`, `hinv`: the Euler-factor identity `l_q/e_q² = 1 + 2v_q` at the character and the
  invertibility of `e_q` (ELLIOT, the Frobenius model at `q`; tex 4194–4219; owner RC15 / RC4);
* `qn`, `hodd`, `F`, `a`, `z`, `zi`, `ha`, `hd`, `hl`, `he`: for each unused prime `p` the odd residue
  cardinality, a Frobenius matrix over `ℚ₂[[t]]` with trace `a_p` and determinant `q_p`, and the
  identifications of `l_p`, `e_p` with the factors of the model (definition / ELLIOT; tex 4151–4222;
  owner RC15 / RC4);
* `u`, `hrel`, `hprim`, `eps`, `hstep`: the coordinates relaxed at `T ⊆ U` (`u U = u_rel`,
  `u ∅ = u_prim,x`) related at each step by the support triangle in the original integral bases,
  with basis comparisons of `Λ`-unit determinant, and the resulting full unit `ε_p` (ELLIOT;
  tex 4166–4193; owner RC15 / batch 3 CommonCoordinate). -/
structure CommonCoordinateTriangles {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type 1 where
  R : Type
  [commR : CommRing R]
  chi : R →+* PowerSeries ℚ_[2]
  Q : Finset ℕ
  v : ℕ → R
  g : ℕ → R
  l : ℕ → R
  e : ℕ → R
  ei : ℕ → R
  hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1
  hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q)
  hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1
  urel : PowerSeries ℚ_[2]
  U : Finset ℕ
  hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1)
  hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel
  qn : ℕ → ℕ
  hodd : ∀ p ∈ U, Odd (qn p)
  F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  a : ℕ → PowerSeries ℚ_[2]
  z : ℕ → PowerSeries ℚ_[2]
  zi : ℕ → PowerSeries ℚ_[2]
  ha : ∀ p ∈ U, (F p).trace = a p
  hd : ∀ p ∈ U, (F p).det = PowerSeries.C (qn p : ℚ_[2])
  hl : ∀ p ∈ U, chi (l p) =
    quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p)
  he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p)
  u : Finset ℕ → PowerSeries ℚ_[2]
  hrel : u U = urel
  hprim : u ∅ = D.uPrim Fam x
  eps : ℕ → PowerSeries ℚ_[2]
  hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
    ActualStep (F p) (PowerSeries.C (qn p : ℚ_[2])) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (a p)
      (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit

attribute [instance] CommonCoordinateTriangles.commR

/-- The model of (4.7) at the address from the support-triangle data (PROVED: batch 3's
`commonCoordinateModel_of_actual_models`). -/
def CommonCoordinateTriangles.toModel {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
    (M : CommonCoordinateTriangles D Fam x) : CommonCoordinateModel D Fam x :=
  commonCoordinateModel_of_actual_models D Fam x M.R M.chi M.Q M.v M.g M.l M.e M.ei M.hsign
    M.hratio M.hinv M.urel M.U M.hU M.hutilde M.qn M.hodd M.F M.a M.z M.zi M.eps M.ha M.hd M.hl M.he
    M.u M.hrel M.hprim M.hstep

/-- **The inputs of (4.7) as support-triangle data** (tex 4142–4328): at every address of a final
family, one `CommonCoordinateTriangles`. -/
def CommonCoordinateInputsT {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateTriangles D F x)

/-- `CommonCoordinateInputs` from the support-triangle data (PROVED). -/
theorem commonCoordinateInputs_of_triangles {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsT D) : CommonCoordinateInputs D := fun Co Ce F hF x => by
  obtain ⟨M⟩ := h Co Ce F hF x
  exact ⟨M.toModel⟩

end ZInQ.Manuscript.RC.Wiring
