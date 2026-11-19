import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Leaf

/-!
# The common-coordinate leaf from the values along one chain of relaxations

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate`, proof (tex 4142–4193). The
text relaxes the unused primes `U_x` of the address one at a time, along one chain
`p₀, p₁, …, p_{n−1}` enumerating `U_x`; each step is a support triangle and gives (4.7) at the
step, and the retained bases of consecutive steps are compared by a sign (tex 4185–4193). With
`v_i` the coordinate after `i` steps and `σ_i = ±1` that sign (for the limit chain `σ = 1`
identically, `chainSign_eq_one`; the orientations are compatible by construction), the chain's
data are
`l_{p_i} v_{i+1} = e_{p_i}² p_i⁻⁴ σ_i v_i` for `i < n`, `v₀` with `t`-expansion `u_{prim,x}`, and
`η_x v_n` with `t`-expansion `ũ_x`.

The current leaf `CommonCoordinateTrianglesLF` (`CommonCoordinate6.lean`) asks instead for one
coordinate `u T` for every support `T ⊆ U_x` and a step at every pair `(T, p)` with `p ∉ T`. This
file builds it from the values along one chain:

* `chainFactor`: `c_p = s_p e_p² p⁻⁴ l_p⁻¹`, with `s_p` the sign of the step of the chain that
  relaxes `p`; `chainCoord`: the product formula `u T = (∏_{p ∈ T} c_p) v₀`;
* `chainCoord_empty`, `chainCoord_insert`: `u ∅ = v₀` and `u (T ∪ {p}) = c_p u T`;
  `chainValues_eq_prod`: the chain's (4.7) forces `v_i = (∏_{j < i} c_{p_j}) v₀`;
  `chainCoord_take`, `chainCoord_unusedAt`: `u {p₀, …, p_{i−1}} = v_i` and `u U_x = v_n`;
* `naturalStep_chainCoord`: the leaf's step at `(T, p)`, with step unit `ε = p⁻⁴ s_p`;
* `trianglesLF_of_chainValues`: the leaf from one chain;
* `ChainValues`, `ChainValues.toLF`, `CommonCoordinateInputsCV`,
  `commonCoordinateInputsNF_of_chainValues`, `commonCoordinateTarget_of_chainValues`: the same
  at every address of every final family, hence (4.7) (`commonCoordinateTarget_of_NF`).

What the leaf built here says, plainly. The leaf's per-step content is (4.7) at the step: at a
good odd prime an actual support triangle with coordinates `u_R, u_P` exists exactly when
`l_p u_R = e_p² p⁻⁴ u_P` (`supportTriangleAt_iff_h47`, `CommonCoordinate10Collapse.lean`), and
the leaf's `NaturalStep` is met by any coordinates with `δ u' = c e² u` (`naturalStepF_of`). So
the coordinates of the intermediate supports in the leaf are the product-formula values
`(∏_{p ∈ T} c_p) v₀`, one for every `T ⊆ U_x`, initial segment of the chain or not; nothing here
identifies them with coordinates of the Selmer complexes of those supports. Only the endpoints
are the chain's: `u ∅ = v 0` (the primitive expansion) and `u U_x = v n` with `n = |U_x|` (the
corrected expansion). The intermediate values `v i` are themselves forced by `v 0` and (4.7)
along the chain (`chainValues_eq_prod`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! ## Two identities in a field, and signs as units -/

/-- **(4.7) at one step, solved for the new coordinate** (tex 4185–4193): if `l ≠ 0` and
`l w' = e² qi⁴ s w`, then `w' = s e² qi⁴ l⁻¹ w`. Kind: PROVED. -/
theorem chainStep_solve {K : Type*} [Field K] {l e qi s w w' : K} (hl : l ≠ 0)
    (h : l * w' = e ^ 2 * qi ^ 4 * s * w) : w' = s * e ^ 2 * qi ^ 4 * l⁻¹ * w := by
  rw [← inv_mul_cancel_left₀ hl w', h]
  ring

/-- **(4.7) at one step in determinant form** (tex 4178–4182, 4185–4193): with `q qi = 1` and
`l ≠ 0`, the determinant `q⁴ l` of the new block times `s e² qi⁴ l⁻¹ w` is `s e² w`.
Kind: PROVED. -/
theorem chainStep_det {K : Type*} [Field K] {q qi l e s w : K} (hq : q * qi = 1) (hl : l ≠ 0) :
    q ^ 4 * l * (s * e ^ 2 * qi ^ 4 * l⁻¹ * w) = s * e ^ 2 * w := by
  have hq4 : q ^ 4 * qi ^ 4 = 1 := by rw [← mul_pow, hq, one_pow]
  have hll : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  linear_combination (s * e ^ 2 * w * l * l⁻¹) * hq4 + (s * e ^ 2 * w) * hll

/-- **A sign is a `Λ`-unit** (tex 4185–4193: the comparison of the retained bases is a sign):
for `s ∈ ℤˣ`, the element `(s : F)` is the image of a unit of `Λ`. Kind: PROVED. -/
theorem lamUnitF_intUnit (s : ℤˣ) : LamUnitF ((s : ℤ) : FracLam) :=
  ⟨Units.map (Int.castRingHom Lambda).toMonoidHom s, by simp⟩

/-! ## The product formula along one chain -/

section Chain

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- **The factor of a step at `p`** (tex 4185–4193): for a chain `ps` with signs `σ`,
`c_p = s_p e_p(x)² p⁻⁴ l_p(x)⁻¹`, where `s_p = σ (idx p)` is the sign of the step at which the
chain relaxes `p`, and `e_p(x)`, `l_p(x)` are the point factor and the two-place factor at the
leaf's values (the actual Frobenius `frobMat C p`). Kind: definition. -/
def chainFactor (ps : List ℕ) (σ : ℕ → ℤˣ) (p : ℕ) : FracLam :=
  ((σ (ps.idxOf p) : ℤ) : FracLam) *
      pointFactor (apE ℓ p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ^ 2 * (p : FracLam)⁻¹ ^ 4 *
    (quotientFactor ((frobMat C p).map zTwoToF) (p : FracLam)⁻¹ (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)))⁻¹

/-- **The coordinate of a support by the product formula** (tex 4185–4193):
`u T = (∏_{p ∈ T} c_p) v₀`. Kind: definition. -/
def chainCoord (ps : List ℕ) (σ : ℕ → ℤˣ) (v : ℕ → FracLam) (T : Finset ℕ) : FracLam :=
  (∏ p ∈ T, chainFactor C Fam x ps σ p) * v 0

/-- The product formula at the empty support is `v₀` (tex 4185–4193). Kind: PROVED. -/
theorem chainCoord_empty (ps : List ℕ) (σ : ℕ → ℤˣ) (v : ℕ → FracLam) :
    chainCoord C Fam x ps σ v ∅ = v 0 := by
  simp [chainCoord]

/-- One more prime multiplies the product formula by its factor: `u (T ∪ {p}) = c_p u T` for
`p ∉ T` (tex 4185–4193). Kind: PROVED. -/
theorem chainCoord_insert (ps : List ℕ) (σ : ℕ → ℤˣ) (v : ℕ → FracLam) {T : Finset ℕ} {p : ℕ}
    (hpT : p ∉ T) :
    chainCoord C Fam x ps σ v (insert p T) =
      chainFactor C Fam x ps σ p * chainCoord C Fam x ps σ v T := by
  rw [chainCoord, chainCoord, Finset.prod_insert hpT, mul_assoc]

/-- **The values along the chain are forced by (4.7) along the chain** (tex 4185–4193): if the
graph primes are good odd primes, the chain `ps` enumerates `U_x` without repetition and each step
satisfies `l_{p_i} v_{i+1} = e_{p_i}² p_i⁻⁴ σ_i v_i`, then `v_i = (∏_{j < i} c_{p_j}) v₀` for
`i ≤ n` (as `l_{p_i}(x) ≠ 0`, `leaf_quotientFactor_ne_zero`). Kind: PROVED. -/
theorem chainValues_eq_prod (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) (ps : List ℕ) (hnd : ps.Nodup)
    (hps : ps.toFinset = unusedAt Fam x) (v : ℕ → FracLam) (σ : ℕ → ℤˣ)
    (h47 : ∀ i (hi : i < ps.length),
      quotientFactor ((frobMat C ps[i]).map zTwoToF) (ps[i] : FracLam)⁻¹
          (lamToF (zAt Fam x ps[i] : Lambda)) (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) *
          v (i + 1) =
        pointFactor (apE ℓ ps[i] : FracLam) (lamToF (zAt Fam x ps[i] : Lambda))
            (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) ^ 2 *
          (ps[i] : FracLam)⁻¹ ^ 4 * ((σ i : ℤ) : FracLam) * v i) :
    ∀ i, i ≤ ps.length → v i = ((ps.take i).map (chainFactor C Fam x ps σ)).prod * v 0 := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hi' : i < ps.length := hi
    have hQ : ps[i] ∈ Fam.Q := by
      have h : ps[i] ∈ ps.toFinset := List.mem_toFinset.mpr (List.getElem_mem hi')
      rw [hps] at h
      exact (mem_unusedAt.mp h).1
    obtain ⟨hpr, hp2⟩ := hprime ps[i] hQ
    have hv : v (i + 1) = chainFactor C Fam x ps σ ps[i] * v i := by
      rw [chainFactor, hnd.idxOf_getElem i hi']
      exact chainStep_solve (leaf_quotientFactor_ne_zero C Fam x hpr hp2 (hgood ps[i] hQ))
        (h47 i hi')
    rw [hv, ih hi'.le, ← List.take_concat_get' ps i hi', List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring

/-- **The product formula on the initial segments of the chain** (tex 4185–4193): under the
hypotheses of `chainValues_eq_prod`, the support `{p₀, …, p_{i−1}}` gets the value `v i`.
Kind: PROVED. -/
theorem chainCoord_take (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) (ps : List ℕ) (hnd : ps.Nodup)
    (hps : ps.toFinset = unusedAt Fam x) (v : ℕ → FracLam) (σ : ℕ → ℤˣ)
    (h47 : ∀ i (hi : i < ps.length),
      quotientFactor ((frobMat C ps[i]).map zTwoToF) (ps[i] : FracLam)⁻¹
          (lamToF (zAt Fam x ps[i] : Lambda)) (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) *
          v (i + 1) =
        pointFactor (apE ℓ ps[i] : FracLam) (lamToF (zAt Fam x ps[i] : Lambda))
            (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) ^ 2 *
          (ps[i] : FracLam)⁻¹ ^ 4 * ((σ i : ℤ) : FracLam) * v i)
    {i : ℕ} (hi : i ≤ ps.length) :
    chainCoord C Fam x ps σ v (ps.take i).toFinset = v i := by
  rw [chainValues_eq_prod C Fam x hprime hgood ps hnd hps v σ h47 i hi, chainCoord,
    List.prod_toFinset _ (hnd.sublist (List.take_sublist i ps))]

/-- **The product formula at the full support is the chain's last value** (tex 4185–4193): under
the hypotheses of `chainValues_eq_prod`, `u U_x = v n` with `n = |U_x|`. Kind: PROVED. -/
theorem chainCoord_unusedAt (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) (ps : List ℕ) (hnd : ps.Nodup)
    (hps : ps.toFinset = unusedAt Fam x) (v : ℕ → FracLam) (σ : ℕ → ℤˣ)
    (h47 : ∀ i (hi : i < ps.length),
      quotientFactor ((frobMat C ps[i]).map zTwoToF) (ps[i] : FracLam)⁻¹
          (lamToF (zAt Fam x ps[i] : Lambda)) (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) *
          v (i + 1) =
        pointFactor (apE ℓ ps[i] : FracLam) (lamToF (zAt Fam x ps[i] : Lambda))
            (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) ^ 2 *
          (ps[i] : FracLam)⁻¹ ^ 4 * ((σ i : ℤ) : FracLam) * v i) :
    chainCoord C Fam x ps σ v (unusedAt Fam x) = v ps.length := by
  have h := chainCoord_take C Fam x hprime hgood ps hnd hps v σ h47 (le_refl ps.length)
  rwa [List.take_length, hps] at h

/-- **The leaf's step at `(T, p)` from the product formula** (tex 4142–4193, 4185–4193): at a good
odd prime `p ∉ T`, `u (T ∪ {p}) = c_p u T` gives `det B · u (T ∪ {p}) = s_p e_p² u T` with
`det B = p⁴ l_p` (`det_twoPlaceBlock`, `quotientDet_eq`), and round one's `naturalStepF_of` gives
the `NaturalStep` with step unit `p⁻⁴ s_p`. Kind: PROVED. -/
theorem naturalStep_chainCoord (ps : List ℕ) (σ : ℕ → ℤˣ) (v : ℕ → FracLam) {T : Finset ℕ}
    {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2) (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p)
    (hpT : p ∉ T) :
    NaturalStep ((frobMat C p).map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))
      (chainCoord C Fam x ps σ v T) (chainCoord C Fam x ps σ v (insert p T))
      ((p : FracLam)⁻¹ ^ 4 * ((σ (ps.idxOf p) : ℤ) : FracLam)) LamUnitF LamUnitF := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  refine naturalStepF_of (lamUnitF_intUnit _)
    (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 hgood) ?_
  rw [det_twoPlaceBlock, quotientDet_eq _ _ (mul_inv_cancel₀ hp0) ha hd,
    chainCoord_insert C Fam x ps σ v hpT, chainFactor]
  exact chainStep_det (mul_inv_cancel₀ hp0) (leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood)

end Chain

/-! ## The leaf from one chain -/

/-- **The common-coordinate leaf from the values along one chain** (tex 4142–4193, 4185–4193):
from a chain `ps` enumerating `U_x` without repetition, values `v` and signs `σ` with (4.7) at
each step of the chain, the leaf `CommonCoordinateTrianglesLF` with coordinates the product
formula `u T = (∏_{p ∈ T} c_p) v 0` (`chainCoord`) and step units `ε T p = p⁻⁴ s_p`: `hprim`
from `u ∅ = v 0`, `htilde` from `u U_x = v n` (`chainCoord_unusedAt`), and each step from
`u (T ∪ {p}) = c_p u T` (`naturalStep_chainCoord`). A definition whose proof fields are proved
here. Kind: PROVED. -/
def trianglesLF_of_chainValues {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q)
    (ps : List ℕ) (hnd : ps.Nodup) (hps : ps.toFinset = unusedAt Fam x)
    (v : ℕ → FracLam) (σ : ℕ → ℤˣ)
    (h47 : ∀ i (hi : i < ps.length),
      quotientFactor ((frobMat C ps[i]).map zTwoToF) (ps[i] : FracLam)⁻¹
          (lamToF (zAt Fam x ps[i] : Lambda)) (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) *
          v (i + 1) =
        pointFactor (apE ℓ ps[i] : FracLam) (lamToF (zAt Fam x ps[i] : Lambda))
            (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) ^ 2 *
          (ps[i] : FracLam)⁻¹ ^ 4 * ((σ i : ℤ) : FracLam) * v i)
    (hprim : IsTExpansion (v 0) (D.uPrim Fam x))
    (htilde : IsTExpansion (etaF ℓ Fam x * v ps.length) (D.uTilde Fam x)) :
    CommonCoordinateTrianglesLF C D Fam x where
  hgood := hgood
  u := chainCoord C Fam x ps σ v
  hprim := by rw [chainCoord_empty]; exact hprim
  eps := fun _ p => (p : FracLam)⁻¹ ^ 4 * ((σ (ps.idxOf p) : ℤ) : FracLam)
  hstep := fun _ _ p hp hpT =>
    naturalStep_chainCoord C Fam x ps σ v (hprime p (mem_unusedAt.mp hp).1).1
      (hprime p (mem_unusedAt.mp hp).1).2 (hgood p (mem_unusedAt.mp hp).1) hpT
  htilde := by
    rw [chainCoord_unusedAt C Fam x hprime hgood ps hnd hps v σ h47]
    exact htilde

/-- **The values along one chain of relaxations at one address** (tex 4142–4193, 4185–4193): the
graph primes are good odd primes; a chain `ps = p₀, …, p_{n−1}` enumerating the unused primes
`U_x` without repetition; values `v i ∈ F` and signs `σ i = ±1` with (4.7) at each step of the
chain, `l_{p_i} v_{i+1} = e_{p_i}² p_i⁻⁴ σ_i v_i` (`l`, `e` at the leaf's values, with the actual
Frobenius `frobMat C p_i`); `v 0` with `t`-expansion `u_{prim,x}` and `η_x v n` with
`t`-expansion `ũ_x`. The values are data: nothing here ties them to the Selmer complexes of the
supports. Kind: definition. -/
structure ChainValues {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ)
    (Fam : Family) (x : Addr Fam.b) : Type where
  /-- the graph primes are odd primes (tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction of `E_ℓ` (tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the chain: the order in which the unused primes are relaxed (tex 4185–4193) -/
  ps : List ℕ
  /-- no prime is relaxed twice -/
  hnd : ps.Nodup
  /-- the chain enumerates the unused primes `U_x` (tex 4142–4143) -/
  hps : ps.toFinset = unusedAt Fam x
  /-- the values along the chain (`v i` after `i` steps; any elements of `F`) -/
  v : ℕ → FracLam
  /-- the signs of the steps (the comparison of the retained bases, tex 4185–4193) -/
  σ : ℕ → ℤˣ
  /-- (4.7) at each step of the chain (tex 4142–4193, 4185–4193) -/
  h47 : ∀ i (hi : i < ps.length),
    quotientFactor ((frobMat C ps[i]).map zTwoToF) (ps[i] : FracLam)⁻¹
        (lamToF (zAt Fam x ps[i] : Lambda)) (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) *
        v (i + 1) =
      pointFactor (apE ℓ ps[i] : FracLam) (lamToF (zAt Fam x ps[i] : Lambda))
          (lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)) ^ 2 *
        (ps[i] : FracLam)⁻¹ ^ 4 * ((σ i : ℤ) : FracLam) * v i
  /-- the value before the first step has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion (v 0) (D.uPrim Fam x)
  /-- `η_x` times the value after the last step has `t`-expansion `ũ_x` (tex 4150–4151) -/
  htilde : IsTExpansion (etaF ℓ Fam x * v ps.length) (D.uTilde Fam x)

/-- **The leaf from the bundled values along one chain** (tex 4142–4193, 4185–4193):
`trianglesLF_of_chainValues` applied to the fields. Kind: PROVED. -/
def ChainValues.toLF {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
    {Fam : Family} {x : Addr Fam.b} (h : ChainValues C D Fam x) :
    CommonCoordinateTrianglesLF C D Fam x :=
  trianglesLF_of_chainValues C D Fam x h.hprime h.hgood h.ps h.hnd h.hps h.v h.σ h.h47 h.hprim
    h.htilde

/-- **The common-coordinate inputs from chain values** (tex 4142–4193, 4185–4193): `E_ℓ`
elliptic, a coefficient datum `C` (one for all families), and at every address of every final
family the values along one chain (`ChainValues`). Kind: definition. -/
def CommonCoordinateInputsCV {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@ChainValues ℓ hE C D F x)

/-- **The current leaf from chain values** (tex 4142–4193, 4185–4193): `ChainValues.toLF` at
every address of every final family gives `CommonCoordinateInputsNF`. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_chainValues {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsCV D) : CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact ⟨hE, C, fun Co Ce F hF x => (hT Co Ce F hF x).map fun t => t.toLF⟩

/-- **(4.7) from chain values** (tex 4142–4193, 4185–4193): through
`commonCoordinateInputsNF_of_chainValues` and `commonCoordinateTarget_of_NF`. Kind: PROVED. -/
theorem commonCoordinateTarget_of_chainValues {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsCV D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_chainValues h)

end ZInQ.Manuscript.RC.Wiring
