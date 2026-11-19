import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Leaf

/-!
# The text's unit in (4.7) and the corrected coordinate, and one ultrafilter per family

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): the steps
satisfy (4.7) with `ε_q ∈ Λ^×`, and `ũ_x = ε_x u_{prim,x}` with `ε_x ∈ Λ^×` (tex 4147,
4151–4152); the units come from the comparison of the retained cone bases, a sign, and from
determinants of unit disks of the retained models (tex 4187–4194). The inner limit fixes one
nonprincipal ultrafilter for one active support and binary family (tex 4401–4404).

* The cone sign is one (proofs from the final review, round nine). `linkOrient_apply_eq`: the
  orientation of a link is the block orientation; hence `linkSign_eq_one`, `chainSign_eq_one`,
  and `fracChain_v_end_one`: the last value of the limit chain is the coordinate of the model of
  the full support, with no sign.
* The text's unit at the end (tex 4151–4152, 4187–4194). `ChainValuesE`: the values along one
  chain as in `ChainValues`, with the corrected expansion asked only up to a unit `ε ∈ Λ^×`
  (`ε = 1` when there is no unused prime). `ChainValuesE.toLF`: the current leaf, with the
  coordinate of the full support multiplied by `ε` and the last step carrying the unit;
  `ChainValues.toE`: the form with `ε = 1` is a special case; `CommonCoordinateInputsCVE`,
  `commonCoordinateInputsNF_of_chainValuesE`.
* One ultrafilter per family (tex 4401–4404). `CommonCoordinateLimitSTE C D Fam x U hU`: the
  inner-limit data at one address for a GIVEN nonprincipal ultrafilter `U`, with the corrected
  expansion up to a unit; `CommonCoordinateLimitSTE.toChainValuesE`;
  `CommonCoordinateInputsLimitE`: one ultrafilter for each final family, the same at all its
  addresses; `commonCoordinateInputsNF_of_limitE`, `commonCoordinateTarget_of_limitE`; and
  `CommonCoordinateLimitST.toE`: the per-address form with the pinned unit is the special case
  at its own ultrafilter.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal)
open scoped PowerSeries.WithPiTopology

/-! ### The cone sign is one -/

section SignOne

open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.CoordLink

/-- The comparison of the cone bases fixes an old basis vector (tex 4189–4191: "Their comparison
is a sign"). Proof from the final review, round nine. Kind: PROVED. -/
theorem chE2_symm_old (m1 m2 i : ℕ) (a : Fin (m1 + 4 * i)) :
    (chE2 m1 m2 i).symm (Sum.inl (joinF m1 i (Sum.inl a))) = Sum.inl (Sum.inl a) := by
  rw [Equiv.symm_apply_eq]; rfl

/-- The comparison of the cone bases fixes a new basis vector (tex 4189–4191: "Their comparison
is a sign"). Proof from the final review, round nine. Kind: PROVED. -/
theorem chE2_symm_new (m1 m2 i : ℕ) (n : NS) :
    (chE2 m1 m2 i).symm (Sum.inl (joinF m1 i (Sum.inr n))) = Sum.inr n := by
  rw [Equiv.symm_apply_eq]; rfl

/-- **The orientation of a link is the block orientation** (tex 4189–4191: "Their comparison is
a sign"). Proof from the final review, round nine. Kind: PROVED. -/
theorem linkOrient_apply_eq (m0 m1 m2 i : ℕ) (x) :
    linkOrient m0 m1 m2 i x = σBlock m0 (m1 + 4 * (i + 1)) m2 x := by
  rcases x with ((e | u) | (b | (u | c)))
  · rfl
  · rfl
  · obtain ⟨y, rfl⟩ := (joinF m1 i).surjective b
    rcases y with a | n
    · show (Equiv.sumCongr (chE1 m0 m1 i)
          (Equiv.sumCongr (Equiv.refl (Fin m2)) (Equiv.refl Unit)))
          (σFull m0 (m1 + 4 * i) m2 NS
            (Sum.inr ((chE2 m1 m2 i).symm (Sum.inl (joinF m1 i (Sum.inl a)))))) = _
      rw [chE2_symm_old]
      rfl
    · show (Equiv.sumCongr (chE1 m0 m1 i)
          (Equiv.sumCongr (Equiv.refl (Fin m2)) (Equiv.refl Unit)))
          (σFull m0 (m1 + 4 * i) m2 NS
            (Sum.inr ((chE2 m1 m2 i).symm (Sum.inl (joinF m1 i (Sum.inr n)))))) = _
      rw [chE2_symm_new]
      rfl
  · rfl
  · rfl

/-- **Every link sign is one** (tex 4189–4191: "Their comparison is a sign"; here the sign is
`1`). Proof from the final review, round nine. Kind: PROVED. -/
theorem linkSign_eq_one (m0 m1 m2 i : ℕ) : linkSign m0 m1 m2 i = 1 := by
  have h : (σBlock m0 (m1 + 4 * (i + 1)) m2).trans (linkOrient m0 m1 m2 i).symm =
      Equiv.refl _ := by
    ext x
    simp only [Equiv.trans_apply, Equiv.refl_apply]
    rw [Equiv.symm_apply_eq, linkOrient_apply_eq]
  unfold linkSign
  rw [h]
  exact Equiv.Perm.sign_refl

/-- **The sign of the comparison of the cone bases is one** along every chain (tex 4189–4191:
"Their comparison is a sign"). Proof from the final review, round nine. Kind: PROVED. -/
theorem chainSign_eq_one (m0 m1 m2 n : ℕ) : chainSign m0 m1 m2 n = 1 := by
  cases n with
  | zero => rfl
  | succ i => exact linkSign_eq_one m0 m1 m2 i

/-- **The last value is the coordinate of the full support** (tex 4185–4193, 4189–4191): on the
limit chain over `Frac Λ`, `v_n = vPrim n`, the sign `σ_n` of `fracChain_v_end` being `1`.
Proof from the final review, round nine. Kind: PROVED. -/
theorem fracChain_v_end_one {m0 m1 m2 : ℕ} (c : ℕ → ChainMat LamI m0 m1 m2) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) (f : FrobSeq LamI) (n : ℕ)
    (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (ZInQ.Manuscript.RC.Limits.stageIdeal s) f n) :
    (fracChain c U).chainV (fracChain_holds c hU f n hs) n =
      (fracChain c U).vPrim (fracChain_holds c hU f n hs) n le_rfl := by
  rw [fracChain_v_end c hU f n hs, chainSign_eq_one]
  simp

end SignOne

/-! ### The values along one chain with the text's unit -/

section UnitE

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

/-- **The values along one chain, with the corrected expansion up to a unit** (tex 4142–4194,
4151–4152, 4187–4194): as `ChainValues`, with `htilde` replaced by: for some `ε ∈ Λ^×`, equal
to `1` when there is no unused prime, `ε η_x v n` has `t`-expansion `ũ_x` (the text's
`ũ_x = ε_x u_{prim,x}`). Kind: definition (data). -/
structure ChainValuesE (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) : Type where
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
  /-- the values along the chain -/
  v : ℕ → FracLam
  /-- the signs of the steps (tex 4189–4191) -/
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
  /-- up to a unit `ε ∈ Λ^×` (`ε = 1` if `U_x = ∅`), `η_x` times the value after the last step
  has `t`-expansion `ũ_x` (tex 4150–4152, 4187–4194) -/
  htildeE : ∃ ε : Lambdaˣ, (ps = [] → ε = 1) ∧
    IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x * v ps.length)) (D.uTilde Fam x)

variable {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- The unit `ε` of the corrected expansion (tex 4151–4152, 4187–4194). Kind: definition. -/
def ChainValuesE.unitE (h : ChainValuesE C D Fam x) : Lambdaˣ := Classical.choose h.htildeE

/-- The unit is `1` when there is no unused prime, and the corrected expansion holds with it
(tex 4151–4152, 4187–4194). Kind: PROVED. -/
theorem ChainValuesE.unitE_spec (h : ChainValuesE C D Fam x) :
    (h.ps = [] → h.unitE = 1) ∧ IsTExpansion (lamToF (h.unitE : Lambda) *
      (etaF ℓ Fam x * h.v h.ps.length)) (D.uTilde Fam x) :=
  Classical.choose_spec h.htildeE

/-- The coordinates of the supports: the product formula `chainCoord`, multiplied by the unit
`ε` at the full support `U_x` (tex 4151–4152, 4185–4194). Kind: definition. -/
def ChainValuesE.coord (h : ChainValuesE C D Fam x) (T : Finset ℕ) : FracLam :=
  if T = unusedAt Fam x then lamToF (h.unitE : Lambda) * chainCoord C Fam x h.ps h.σ h.v T
  else chainCoord C Fam x h.ps h.σ h.v T

/-- The step units: `p⁻⁴ s_p`, times `ε` for the step into the full support `U_x`
(tex 4187–4194). Kind: definition. -/
def ChainValuesE.stepUnit (h : ChainValuesE C D Fam x) (T : Finset ℕ) (p : ℕ) : FracLam :=
  if insert p T = unusedAt Fam x then
    (p : FracLam)⁻¹ ^ 4 * (lamToF (h.unitE : Lambda) * ((h.σ (h.ps.idxOf p) : ℤ) : FracLam))
  else (p : FracLam)⁻¹ ^ 4 * ((h.σ (h.ps.idxOf p) : ℤ) : FracLam)

/-- (4.7) for the product formula in determinant form: `det B · u (T ∪ {p}) = s_p e_p² u T` at a
good odd prime `p ∉ T` (tex 4178–4193). Kind: PROVED. -/
theorem ChainValuesE.det_mul_chainCoord (h : ChainValuesE C D Fam x) {T : Finset ℕ} {p : ℕ}
    (hpr : p.Prime) (hp2 : p ≠ 2) (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (hpT : p ∉ T) :
    (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).det *
        chainCoord C Fam x h.ps h.σ h.v (insert p T) =
      ((h.σ (h.ps.idxOf p) : ℤ) : FracLam) * pointFactor (apE ℓ p : FracLam)
        (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ^ 2 *
        chainCoord C Fam x h.ps h.σ h.v T := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  rw [det_twoPlaceBlock, quotientDet_eq _ _ (mul_inv_cancel₀ hp0) ha hd,
    chainCoord_insert C Fam x h.ps h.σ h.v hpT, chainFactor]
  exact chainStep_det (mul_inv_cancel₀ hp0) (leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood)

/-- **The current leaf from the values along one chain with the text's unit** (tex 4142–4194,
4151–4152, 4187–4194): coordinates `coord` (the product formula, times `ε` at `U_x`), step units
`stepUnit`; each step from `naturalStep_chainCoord`, or, for the step into `U_x`, from
`naturalStepF_of` with the `Λ`-unit `ε s_p`; `hprim` from `u ∅ = v 0` (if `U_x = ∅` then the
chain is empty and `ε = 1`); `htilde` from `u U_x = ε v n`. Kind: definition. -/
def ChainValuesE.toLF (h : ChainValuesE C D Fam x) : CommonCoordinateTrianglesLF C D Fam x where
  hgood := h.hgood
  u := h.coord
  hprim := by
    by_cases h0 : (∅ : Finset ℕ) = unusedAt Fam x
    · have hps0 : h.ps = [] := by
        rw [← List.toFinset_eq_empty_iff, h.hps]
        exact h0.symm
      rw [ChainValuesE.coord, ite_eq_left h0, h.unitE_spec.1 hps0, Units.val_one, map_one, one_mul,
        chainCoord_empty]
      exact h.hprim
    · rw [ChainValuesE.coord, ite_eq_right h0, chainCoord_empty]
      exact h.hprim
  eps := h.stepUnit
  hstep := fun T _ p hp hpT => by
    have hpQ : p ∈ Fam.Q := (mem_unusedAt.mp hp).1
    obtain ⟨hpr, hp2⟩ := h.hprime p hpQ
    have hT : T ≠ unusedAt Fam x := fun e => hpT (e ▸ hp)
    by_cases hins : insert p T = unusedAt Fam x
    · simp only [ChainValuesE.coord, ChainValuesE.stepUnit, ite_eq_right hT, ite_eq_left hins]
      refine naturalStepF_of (LamUnitF.mul ⟨h.unitE, rfl⟩ (lamUnitF_intUnit _))
        (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 (h.hgood p hpQ)) ?_
      linear_combination (lamToF (h.unitE : Lambda)) *
        h.det_mul_chainCoord hpr hp2 (h.hgood p hpQ) hpT
    · simp only [ChainValuesE.coord, ChainValuesE.stepUnit, ite_eq_right hT, ite_eq_right hins]
      exact naturalStep_chainCoord C Fam x h.ps h.σ h.v hpr hp2 (h.hgood p hpQ) hpT
  htilde := by
    rw [ChainValuesE.coord, ite_eq_left rfl,
      chainCoord_unusedAt C Fam x h.hprime h.hgood h.ps h.hnd h.hps h.v h.σ h.h47,
      mul_left_comm]
    exact h.unitE_spec.2

/-- **The pinned form is a special case** (tex 4151–4152): chain values with the corrected
expansion exactly (`ChainValues`) are chain values with the unit `ε = 1`. Kind: definition. -/
def ChainValues.toE (h : ChainValues C D Fam x) : ChainValuesE C D Fam x where
  hprime := h.hprime
  hgood := h.hgood
  ps := h.ps
  hnd := h.hnd
  hps := h.hps
  v := h.v
  σ := h.σ
  h47 := h.h47
  hprim := h.hprim
  htildeE := ⟨1, fun _ => rfl, by rw [Units.val_one, map_one, one_mul]; exact h.htilde⟩

end UnitE

/-- **The common-coordinate inputs from chain values with the text's unit** (tex 4142–4194,
4151–4152): `E_ℓ` elliptic, a coefficient datum `C`, and at every address of every final family
the values along one chain with the corrected expansion up to a unit (`ChainValuesE`).
Kind: definition. -/
def CommonCoordinateInputsCVE {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@ChainValuesE ℓ hE C D F x)

/-- **The current leaf from chain values with the text's unit** (tex 4142–4194, 4151–4152):
`ChainValuesE.toLF` at every address of every final family. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_chainValuesE {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsCVE D) : CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact ⟨hE, C, fun Co Ce F hF x => (hT Co Ce F hF x).map fun t => t.toLF⟩

/-! ### The inner limit with one ultrafilter per family -/

section LimitE

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

/-- **The inner-limit data at one address for a given ultrafilter, with the text's unit**
(tex 4142–4194, 4385–4451, 4401–4404): as `CommonCoordinateLimitST`, with the nonprincipal
ultrafilter `U` a parameter (so that one ultrafilter serves all addresses of a family), and the
corrected expansion of the limit asked up to a unit `ε ∈ Λ^×` (`ε = 1` if `U_x = ∅`; tex
4151–4152, 4187–4194). Kind: definition (data). -/
structure CommonCoordinateLimitSTE (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) : Type where
  /-- the graph primes are odd primes (tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction (tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the order in which the unused primes are relaxed -/
  ps : List ℕ
  /-- each unused prime is relaxed once -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes -/
  hps : ps.toFinset = unusedAt Fam x
  /-- the Frobenius data over `Λ` -/
  f : FrobSeq LamI
  /-- they are the leaf's values -/
  hf : LeafFrob C Fam x ps f
  /-- the rank of the model of `C_∅` in degree `0` -/
  m0 : ℕ
  /-- the rank of the model of `C_∅` in degree `1` (besides the class) -/
  m1 : ℕ
  /-- the rank of the model of `C_∅` in degree `3` -/
  m2 : ℕ
  /-- the matrix data of the chain at the stages (lifts to `Λ`) -/
  c : ℕ → ChainMat LamI m0 m1 m2
  /-- the identities hold modulo the stage ideals at `U`-many stages -/
  hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f ps.length
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion ((fracChain c U).chainV (fracChain_holds c hU f ps.length hs) 0)
    (D.uPrim Fam x)
  /-- up to a unit, the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x`
  (tex 4150–4152, 4187–4194) -/
  htildeE : ∃ ε : Lambdaˣ, (ps = [] → ε = 1) ∧ IsTExpansion (lamToF (ε : Lambda) *
    (etaF ℓ Fam x * (fracChain c U).chainV (fracChain_holds c hU f ps.length hs) ps.length))
    (D.uTilde Fam x)

variable {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
  {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}

/-- **The chain values with the text's unit from the inner limit** (tex 4142–4194, 4385–4451):
as `CommonCoordinateLimitST.toChainValues`: the values are the coordinates of the limit chain
over `Frac Λ`, the signs those of the comparison of the cone bases (all `1`,
`chainSign_eq_one`), and (4.7) holds at every step (`ChainMat.chain_h47`). Kind: definition. -/
def CommonCoordinateLimitSTE.toChainValuesE (H : CommonCoordinateLimitSTE C D Fam x U hU) :
    ChainValuesE C D Fam x where
  hprime := H.hprime
  hgood := H.hgood
  ps := H.ps
  hnd := H.hnd
  hps := H.hps
  v := (fracChain H.c U).chainV (fracChain_holds H.c hU H.f H.ps.length H.hs)
  σ := chainSign H.m0 H.m1 H.m2
  h47 := fun i hi => by
    obtain ⟨hFr, hq, hqi, ha, hz, hzi⟩ := H.hf i hi
    have hmem : H.ps[i] ∈ unusedAt Fam x := by
      rw [← H.hps, List.mem_toFinset]
      exact List.getElem_mem hi
    have hpQ : H.ps[i] ∈ Fam.Q := (mem_unusedAt.mp hmem).1
    obtain ⟨hpr, hp2⟩ := H.hprime _ hpQ
    obtain ⟨hta, hde⟩ := leafFr_trace_det C hpr hp2 (H.hgood _ hpQ)
    have hp0 : (H.ps[i] : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
    have h := ChainMat.chain_h47 (fracChain H.c U)
      (fracChain_holds H.c hU H.f H.ps.length H.hs) i hi
      (by rw [hq, hqi]; exact mul_inv_cancel₀ hp0)
      (by rw [hFr, ha]; exact hta)
      (by rw [hFr, hq]; exact hde)
      (by
        rw [hFr, hq, hz, hzi]
        exact isUnit_iff_ne_zero.2 (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2
          (H.hgood _ hpQ)))
    rw [hFr, hqi, hz, hzi, ha] at h
    exact h
  hprim := H.hprim
  htildeE := H.htildeE

/-- **The per-address form with the pinned unit is a special case** (tex 4385–4451): the data
`CommonCoordinateLimitST` (its own ultrafilter `H.U`, the corrected expansion exactly) give
`CommonCoordinateLimitSTE` at the ultrafilter `H.U` with `ε = 1`. Kind: definition. -/
def CommonCoordinateLimitST.toE (H : CommonCoordinateLimitST C D Fam x) :
    CommonCoordinateLimitSTE C D Fam x H.U H.hU where
  hprime := H.hprime
  hgood := H.hgood
  ps := H.ps
  hnd := H.hnd
  hps := H.hps
  f := H.f
  hf := H.hf
  m0 := H.m0
  m1 := H.m1
  m2 := H.m2
  c := H.c
  hs := H.hs
  hprim := H.hprim
  htildeE := ⟨1, fun _ => rfl, by rw [Units.val_one, map_one, one_mul]; exact H.htilde⟩

end LimitE

/-- **The common-coordinate inputs from the inner limit with one ultrafilter per family**
(tex 4142–4194, 4385–4451, 4401–4404): `E_ℓ` elliptic, a coefficient datum, and for every final
family one nonprincipal ultrafilter `U` such that at every address of the family the inner-limit
data for `U` exist, with the corrected expansion up to a unit (`CommonCoordinateLimitSTE`).
Kind: definition. -/
def CommonCoordinateInputsLimitE {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite), ∀ x : Addr F.b,
        Nonempty (@CommonCoordinateLimitSTE ℓ hE C D F x U hU)

/-- **The current leaf from the inner limit with one ultrafilter per family** (tex 4142–4194,
4385–4451, 4401–4404): through `CommonCoordinateLimitSTE.toChainValuesE` and
`commonCoordinateInputsNF_of_chainValuesE`. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_limitE {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsLimitE D) : CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  refine commonCoordinateInputsNF_of_chainValuesE ⟨hE, C, fun Co Ce F hF x => ?_⟩
  obtain ⟨U, hU, hx⟩ := hT Co Ce F hF
  exact (hx x).map fun t => t.toChainValuesE

/-- **(4.7) from the inner limit with one ultrafilter per family** (tex 4142–4194, 4385–4451):
through `commonCoordinateInputsNF_of_limitE` and `commonCoordinateTarget_of_NF`.
Kind: PROVED. -/
theorem commonCoordinateTarget_of_limitE {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsLimitE D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_limitE h)

end ZInQ.Manuscript.RC.Wiring
