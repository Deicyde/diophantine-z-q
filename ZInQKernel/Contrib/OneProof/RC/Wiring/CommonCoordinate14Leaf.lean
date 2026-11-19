import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Limit
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Field
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Values

/-!
# The common-coordinate leaf from the inner limit of the stage chains

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) after the
inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451).

The matrix data of a chain of relaxations at the finite coefficient stages (lifts to `Λ` whose
identities hold modulo `(2^s, t^s)` at `U`-many stages) pass to exact data over `Λ`
(`limitChain`, `limit_holds`), hence over `F = Frac Λ` (`fracChain`, `fracChain_holds`). There
every step is a `KmStep` and (4.7) holds between consecutive supports
(`ChainMat.chain_h47`). At the leaf's Frobenius values (`LeafFrob`) this gives the leaf's chain
values (`ChainValues`), hence the current leaf `CommonCoordinateInputsNF` and (4.7)
(`CommonCoordinateTarget`).

* `fracChain`, `fracChain_holds`: the limit data over `Frac Λ`, with its identities.
* `LeafFrob C Fam x ps f`: the Frobenius data `f` over `Λ` become the leaf's values at the order
  `ps` of the unused primes over `Frac Λ`.
* **`CommonCoordinateLimitST C D Fam x`**: the stage data of one chain of relaxations of the
  unused primes, with bounded (fixed) ranks along a nonprincipal ultrafilter, their identities at
  `U`-many stages, and the primitive and corrected expansions of the end coordinates of the limit.
* **`CommonCoordinateLimitST.toChainValues`**, **`commonCoordinateInputsNF_of_limit`**,
  **`commonCoordinateTarget_of_limit`**.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal)
open scoped PowerSeries.WithPiTopology

variable {m0 m1 m2 : ℕ}

/-- **The limit data over `F = Frac Λ`** (tex 4444–4448, 4157–4194). Kind: definition. -/
def fracChain (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) : ChainMat FracLam m0 m1 m2 :=
  (limitChain c U).map lamToF

/-- **The identities hold exactly for the limit data over `Frac Λ`** (tex 4444–4448).
Kind: PROVED. -/
theorem fracChain_holds (c : ℕ → ChainMat LamI m0 m1 m2) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (f : FrobSeq LamI) (n : ℕ)
    (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n) :
    (fracChain c U).Holds ⊥ (f.map lamToF) n :=
  (limit_holds c hU f n hs).map (limitChain c U) lamToF ⊥ fun x hx => by
    rw [Ideal.mem_bot] at hx ⊢
    rw [hx, map_zero]

section Leaf

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]

/-- **The leaf's Frobenius values at an order of the unused primes** (tex 4142–4194): over
`Frac Λ`, the data of step `i` are those of the prime `ps[i]`: `ρ_T(Fr_p)`, `p`, `p⁻¹`, `a_p`,
`z_p(x)`, `z_p(x)⁻¹`. Kind: definition. -/
def LeafFrob (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b) (ps : List ℕ)
    (f : FrobSeq LamI) : Prop :=
  ∀ i (hi : i < ps.length), (f.map lamToF).Fr i = (frobMat C ps[i]).map zTwoToF ∧
    (f.map lamToF).q i = (ps[i] : FracLam) ∧ (f.map lamToF).qi i = (ps[i] : FracLam)⁻¹ ∧
    (f.map lamToF).a i = (apE ℓ ps[i] : FracLam) ∧
    (f.map lamToF).z i = lamToF (zAt Fam x ps[i] : Lambda) ∧
    (f.map lamToF).zi i = lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ)

/-- **The leaf's Frobenius data over `Λ` have the leaf's values** (tex 4142–4194): for an order
`ps` of the unused primes, `leafFrobΛ` satisfies `LeafFrob`. Kind: PROVED. -/
theorem leafFrob_leafFrobΛ (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)
    (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2) {ps : List ℕ} (hps : ps.toFinset = unusedAt Fam x) :
    LeafFrob C Fam x ps (leafFrobΛ C Fam x ps) := fun i hi =>
  leafFrobΛ_map C Fam x ps i hi
    (odd_getElem Fam hprime (toFinset_subset_Q_of_unused Fam x hps) hi)

/-- **The common-coordinate data from the inner limit** (tex 4142–4194, 4385–4451): the graph
primes are good odd primes; an order `ps` of the unused primes; Frobenius data over `Λ` with the
leaf's values; a nonprincipal ultrafilter on the coefficient stages; the ranks `(m₀, m₁, m₂)` of
the model of `C_∅`, fixed on the ultrafilter (`shapes_fixed`); the matrix data of the chain at the
stages (lifts to `Λ`) with their identities modulo `(2^s, t^s)` at `U`-many stages; and the
primitive and corrected `t`-expansions of the end coordinates of the limit chain over `Frac Λ`.
Kind: definition (data). -/
structure CommonCoordinateLimitST (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) : Type where
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
  /-- the ultrafilter on the coefficient stages -/
  U : Ultrafilter ℕ
  /-- it is nonprincipal -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- the ranks of the model of `C_∅` in degrees `0` -/
  m0 : ℕ
  /-- the ranks of the model of `C_∅` in degree `1` (besides the class) -/
  m1 : ℕ
  /-- the ranks of the model of `C_∅` in degree `3` -/
  m2 : ℕ
  /-- the matrix data of the chain at the stages (lifts to `Λ`) -/
  c : ℕ → ChainMat LamI m0 m1 m2
  /-- the identities hold modulo the stage ideals at `U`-many stages -/
  hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f ps.length
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion ((fracChain c U).chainV (fracChain_holds c hU f ps.length hs) 0)
    (D.uPrim Fam x)
  /-- the corrected coordinate of the limit at `U_x` has `t`-expansion `ũ_x` (tex 4150–4151).
  Conclusion-shaped: since `chainSign = 1` and each step has `ε = q⁻⁴`,
  `η_x v_n = (∏_{q∈U_x} q⁻⁴) v₀`, so given `hprim` this field is equivalent to
  `ũ_x = (∏_{q∈U_x} q⁻⁴) u_{prim,x}`, the conclusion of Lemma `ex:arith-common-coordinate` with
  the unit pinned (stronger than the text's `ε_x ∈ Λ^×`, whose unit-disk factors, tex 4189–4193,
  are absorbed into the choice of the model and class of `C_∅`). The text's `ũ = η u_rel` is one
  common family (tex 4224–4225); that is not represented. -/
  htilde : IsTExpansion (etaF ℓ Fam x *
    (fracChain c U).chainV (fracChain_holds c hU f ps.length hs) ps.length) (D.uTilde Fam x)

/-- **The leaf's chain values from the inner limit** (tex 4142–4194, 4385–4451): the values are
the coordinates of the limit chain over `Frac Λ` in the iterated cone bases, `σ = 1` identically
(`chainSign_eq_one`; the orientations are compatible by construction), and (4.7) holds at every
step (`ChainMat.chain_h47`; the new block is invertible at the leaf's values,
`det B = p⁴ l_p(x) ≠ 0`). Kind: definition. -/
def CommonCoordinateLimitST.toChainValues {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
    {Fam : Family} {x : Addr Fam.b} (H : CommonCoordinateLimitST C D Fam x) :
    ChainValues C D Fam x where
  hprime := H.hprime
  hgood := H.hgood
  ps := H.ps
  hnd := H.hnd
  hps := H.hps
  v := (fracChain H.c H.U).chainV (fracChain_holds H.c H.hU H.f H.ps.length H.hs)
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
    have h := ChainMat.chain_h47 (fracChain H.c H.U)
      (fracChain_holds H.c H.hU H.f H.ps.length H.hs) i hi
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
  htilde := H.htilde

end Leaf

/-! ### The primitive coordinate of the limit on a rank-zero model -/

/-- **The primitive coordinate of the limit is the limit of the stage pairings** (tex 4444–4448,
4636–4640): when the model of `C_∅` has rank `(0, 1, 1, 0)` (`m₀ = m₁ = m₂ = 0`, the minimal
model), the primitive coordinate of the limit chain over `Frac Λ` is the image of the ultralimit of
the stage pairings `−z_P λ_P` (the coordinate on a rank-zero model is a polynomial,
`kmCoord_rankZero`). Kind: PROVED. -/
theorem limit_primCoord_rankZero (c : ℕ → ChainMat LamI 0 0 0) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (f : FrobSeq LamI) (n : ℕ)
    (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n) :
    (fracChain c U).chainV (fracChain_holds c hU f n hs) 0 =
      lamToF (ZInQ.Manuscript.RC.Limits.ulim U
        (fun s => -((c s).zP0 (Sum.inr (Sum.inl ())) * (c s).lP0 (Sum.inr (Sum.inl ()))))) := by
  rw [ChainMat.chainV_zero]
  unfold ChainMat.vPrim
  refine (kmCoord_rankZero ((fracChain c U).blockAt (fracChain_holds c hU f n hs) 0
    (Nat.zero_le n)) rfl rfl rfl _ _ _ _).trans ?_
  change (-1) * lamToF (ZInQ.Manuscript.RC.Limits.ulimHom U
      (fun s => (c s).zP0 (Sum.inr (Sum.inl ())))) *
    lamToF (ZInQ.Manuscript.RC.Limits.ulimHom U (fun s => (c s).lP0 (Sum.inr (Sum.inl ())))) = _
  rw [← ZInQ.Manuscript.RC.Limits.ulimHom_apply]
  have e : (fun s => -((c s).zP0 (Sum.inr (Sum.inl ())) * (c s).lP0 (Sum.inr (Sum.inl ())))) =
      -((fun s => (c s).zP0 (Sum.inr (Sum.inl ()))) *
        (fun s => (c s).lP0 (Sum.inr (Sum.inl ())))) :=
    rfl
  rw [e, map_neg, map_mul, map_neg, map_mul]
  ring

/-- **The primitive expansion from the limit of the stage pairings** (tex 4153, 4444–4448): on a
rank-zero model of `C_∅`, if the ultralimit `G ∈ Λ` of the stage pairings `−z_P λ_P` has
`t`-expansion `u_{prim,x}` (`G` is the text's `u_{prim,x}`, defined from the finite stages), the
primitive coordinate of the limit has the primitive expansion. Kind: PROVED. -/
theorem hprim_of_rankZero {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (c : ℕ → ChainMat LamI 0 0 0) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (f : FrobSeq LamI) (n : ℕ) (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n)
    (hG : lamIncl (ZInQ.Manuscript.RC.Limits.ulim U
      (fun s => -((c s).zP0 (Sum.inr (Sum.inl ())) * (c s).lP0 (Sum.inr (Sum.inl ())))))
        = D.uPrim Fam x) :
    IsTExpansion ((fracChain c U).chainV (fracChain_holds c hU f n hs) 0) (D.uPrim Fam x) := by
  rw [limit_primCoord_rankZero c hU f n hs]
  refine ⟨ZInQ.Manuscript.RC.Limits.ulim U
    (fun s => -((c s).zP0 (Sum.inr (Sum.inl ())) * (c s).lP0 (Sum.inr (Sum.inl ())))), 1,
    one_ne_zero, ?_, ?_⟩
  · rw [map_one, mul_one]
  · rw [map_one, mul_one, hG]


/-- **The common-coordinate inputs from the inner limit** (tex 4142–4194, 4385–4451): `E_ℓ`
elliptic, a coefficient datum, and at every address of every final family the stage data of one
chain of relaxations with their inner limit (`CommonCoordinateLimitST`). Kind: definition. -/
def CommonCoordinateInputsLimit {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateLimitST ℓ hE C D F x)

/-- **The current leaf from the inner limit of the stage chains** (tex 4142–4194, 4385–4451).
Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_limit {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsLimit D) : CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact commonCoordinateInputsNF_of_chainValues
    ⟨hE, C, fun Co Ce F hF x => (hT Co Ce F hF x).map fun t => t.toChainValues⟩

/-- **(4.7) from the inner limit of the stage chains** (tex 4142–4194, 4385–4451):
`RCSteps.common_coordinate`. Kind: PROVED. -/
theorem commonCoordinateTarget_of_limit {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsLimit D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_limit h)

end ZInQ.Manuscript.RC.Wiring
