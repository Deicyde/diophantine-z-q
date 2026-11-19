import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Model

/-!
# The inner limit of the matrix data of a chain of relaxations

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4385–4451): "Fix one
nonprincipal ultrafilter on coefficient stages. Bounded ranks can be fixed on a set in that
ultrafilter. Each finite tuple of matrix entries then has a compatible limit at every coefficient
precision, giving matrices over `Λ`. Every polynomial identity between the matrices survives"
(tex 4444–4448).

Only the matrix identities pass to the limit; the retained homotopy inverses and the maps to the
original cochains (tex 4403–4404, 4448–4450) are not carried, so the limit model is not identified
with the genuine Λ-adic complexes — that identification is the content of `hprim`/`htilde`.

The matrix data of a chain of relaxations at the finite coefficient stages `A_s = Λ/(2^s, t^s)`
are given by lifts to `Λ` (`c s : ChainMat Λ m₀ m₁ m₂`, the ranks fixed on a set of the
ultrafilter) whose identities hold modulo the stage ideals `(2^s, t^s)`. This file passes them to
the limit with lane RC6's ultralimit (`Limits/Ultralimit.lean`):

* `prodChain c`: the stage data as one chain over the product ring `ℕ → Λ`; `prodChain_eval`:
  its evaluation at the stage `s` is `c s`.
* `ultraIdeal U`: the sequences lying in the stage ideals for `U`-many stages; `diag`: the
  constant sequences.
* `Holds.of_eventually`, `holds_prod`: the identities at `U`-many stages are the identities of the
  product chain modulo `ultraIdeal U`.
* **`limitChain c U`**: the limit data over `Λ` (`ulimHom U` applied to the product chain, i.e.
  the entrywise ultralimits); **`limit_holds`**: the identities hold exactly over `Λ`, with the
  same Frobenius data.
* **`limit_spec_blk1`, `limit_spec_z`, `limit_spec_l`, `limit_spec_zP`, `limit_spec_lP`**: the
  specializations of the limit are the stage data, at every coefficient precision, for `U`-many
  stages ("a compatible limit at every coefficient precision", tex 4446).
* `shapes_fixed`: bounded ranks of the stage models are constant on a set of the ultrafilter
  (lane RC6's `bounded_rank_tuples_fixed`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter
open scoped PowerSeries.WithPiTopology
open ZInQ.Manuscript.RC.Limits (ulim ulimHom ulimHom_apply ulim_const ulim_eq_zero_of_mem
  stageIdeal stageIdeal_tendsToZero stageIdeal_isOpen eventually_sub_ulim_mem
  bounded_rank_tuples_fixed)

/-- The coefficient ring `Λ = ℤ₂[[t]]` of the inner limit (tex 2747). Kind: definition. -/
abbrev LamI : Type := ZInQ.Manuscript.RC.Limits.Lambda

variable {m0 m1 m2 : ℕ}

/-- **The stage data as one chain over the product ring** `ℕ → Λ` (tex 4444–4448): the entries
are the sequences of the stage entries. Kind: definition. -/
def prodChain (c : ℕ → ChainMat LamI m0 m1 m2) : ChainMat (ℕ → LamI) m0 m1 m2 where
  d0 := Matrix.of fun a b s => (c s).d0 a b
  d1 := Matrix.of fun a b s => (c s).d1 a b
  d2 := Matrix.of fun a b s => (c s).d2 a b
  Q i := Matrix.of fun a b s => (c s).Q i a b
  V i := Matrix.of fun a b s => (c s).V i a b
  B i := Matrix.of fun a b s => (c s).B i a b
  zP0 a s := (c s).zP0 a
  lP0 a s := (c s).lP0 a
  z i a s := (c s).z i a
  l i a s := (c s).l i a
  w i a s := (c s).w i a
  ν i a s := (c s).ν i a

/-- The evaluation at a stage (tex 4444–4448). Kind: definition. -/
abbrev evalAt (s : ℕ) : (ℕ → LamI) →+* LamI := Pi.evalRingHom (fun _ : ℕ => LamI) s

/-- **The product chain evaluated at a stage is the stage chain** (tex 4444–4448).
Kind: PROVED (definitional). -/
theorem prodChain_eval (c : ℕ → ChainMat LamI m0 m1 m2) (s : ℕ) :
    (prodChain c).map (evalAt s) = c s :=
  rfl

/-- The constant sequences (tex 4444–4448). Kind: definition. -/
abbrev diag : LamI →+* (ℕ → LamI) := RingHom.pi fun _ : ℕ => RingHom.id LamI

/-- The constant Frobenius data evaluated at a stage (tex 4444–4448). Kind: PROVED
(definitional). -/
theorem frob_diag_eval (f : FrobSeq LamI) (s : ℕ) : (f.map diag).map (evalAt s) = f :=
  rfl

/-- **The ideal of the sequences lying in the stage ideals for `U`-many stages**
(tex 4444–4448). Kind: definition. -/
def ultraIdeal (U : Ultrafilter ℕ) : Ideal (ℕ → LamI) where
  carrier := {x | ∀ᶠ s in (U : Filter ℕ), x s ∈ stageIdeal s}
  add_mem' {x y} hx hy := by
    filter_upwards [hx, hy] with s hxs hys
    exact Ideal.add_mem _ hxs hys
  zero_mem' := Eventually.of_forall fun s => Ideal.zero_mem _
  smul_mem' r x hx := by
    filter_upwards [hx] with s hxs
    exact Ideal.mul_mem_left _ (r s) hxs

/-- Membership in `ultraIdeal U` (tex 4444–4448). Kind: PROVED (definitional). -/
theorem mem_ultraIdeal {U : Ultrafilter ℕ} {x : ℕ → LamI} :
    x ∈ ultraIdeal U ↔ ∀ᶠ s in (U : Filter ℕ), x s ∈ stageIdeal s :=
  Iff.rfl

/-- **The ultralimit kills `ultraIdeal U`** along a nonprincipal ultrafilter (tex 4446–4448;
lane RC6's `ulim_eq_zero_of_mem`). Kind: PROVED. -/
theorem ulimHom_ultraIdeal {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {x : ℕ → LamI}
    (hx : x ∈ ultraIdeal U) : ulimHom U x = 0 :=
  ulim_eq_zero_of_mem stageIdeal_tendsToZero hU hx

/-- The limit of the constant Frobenius data is the Frobenius data (tex 4444–4448).
Kind: PROVED. -/
theorem frob_diag_ulim (f : FrobSeq LamI) (U : Ultrafilter ℕ) :
    (f.map diag).map (ulimHom U) = f := by
  obtain ⟨Fr, q, qi, a, z, zi⟩ := f
  simp only [FrobSeq.map, FrobSeq.mk.injEq]
  refine ⟨funext fun i => ?_, funext fun i => ulim_const (X := LamI) U _,
    funext fun i => ulim_const (X := LamI) U _, funext fun i => ulim_const (X := LamI) U _,
    funext fun i => ulim_const (X := LamI) U _, funext fun i => ulim_const (X := LamI) U _⟩
  funext a b
  exact ulim_const (X := LamI) U _

namespace ChainMat

variable {R : Type} [CommRing R]

/-- **Identities at many indices give the identities modulo the ideal of the eventual members**
(tex 4444–4448). Kind: PROVED. -/
theorem Holds.of_eventually (c : ChainMat R m0 m1 m2) {f : FrobSeq R} {n : ℕ}
    (U : Ultrafilter ℕ) {I : ℕ → Ideal R} {J : Ideal R}
    (hJ : ∀ x, (∀ᶠ s in (U : Filter ℕ), x ∈ I s) → x ∈ J)
    (h : ∀ᶠ s in (U : Filter ℕ), c.Holds (I s) f n) : c.Holds J f n :=
  ⟨fun a b => hJ _ (h.mono fun _ hs => hs.h10 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.h21 a b),
    fun i hi a b => hJ _ (h.mono fun _ hs => hs.hQVB i hi a b),
    fun i hi a b => hJ _ (h.mono fun _ hs => hs.hB i hi a b),
    fun a => hJ _ (h.mono fun _ hs => hs.hzP0 a),
    fun a => hJ _ (h.mono fun _ hs => hs.hlP0 a),
    fun i hi a => hJ _ (h.mono fun _ hs => hs.hz i hi a),
    fun i hi a => hJ _ (h.mono fun _ hs => hs.hl i hi a),
    fun i hi a => hJ _ (h.mono fun _ hs => hs.hnorm i hi a),
    fun i hi a => hJ _ (h.mono fun _ hs => hs.hnormN i hi a),
    fun i hi a => hJ _ (h.mono fun _ hs => hs.hfun i hi a)⟩

end ChainMat

/-- **The identities at `U`-many stages are the identities of the product chain modulo
`ultraIdeal U`** (tex 4444–4448). Kind: PROVED. -/
theorem holds_prod (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (f : FrobSeq LamI)
    (n : ℕ) (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n) :
    (prodChain c).Holds (ultraIdeal U) (f.map diag) n := by
  refine ChainMat.Holds.of_eventually (prodChain c) U (I := fun s =>
    (stageIdeal s).comap (evalAt s)) (fun x hx => hx) ?_
  filter_upwards [hs] with s h
  have h' : ((prodChain c).map (evalAt s)).Holds (stageIdeal s) ((f.map diag).map (evalAt s))
      n := h
  exact ((prodChain c).holds_map_iff (evalAt s) (stageIdeal s) (f.map diag) n).1 h'

/-- **The limit data over `Λ`** (tex 4444–4448: "giving matrices over `Λ`"): the entrywise
ultralimits of the stage data. Only the matrix identities pass to the limit; the retained homotopy
inverses and the maps to the original cochains (tex 4403–4404, 4448–4450) are not carried, so the
limit model is not identified with the genuine Λ-adic complexes — that identification is the
content of `hprim`/`htilde`. Kind: definition. -/
def limitChain (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) : ChainMat LamI m0 m1 m2 :=
  (prodChain c).map (ulimHom U)

/-- **The identities hold exactly for the limit data** (tex 4447–4448: "Every polynomial identity
between the matrices survives"): if they hold modulo the stage ideals at `U`-many stages, along a
nonprincipal ultrafilter. Kind: PROVED. -/
theorem limit_holds (c : ℕ → ChainMat LamI m0 m1 m2) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (f : FrobSeq LamI) (n : ℕ)
    (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s) f n) :
    (limitChain c U).Holds ⊥ f n := by
  have h := (holds_prod c U f n hs).map (prodChain c) (ulimHom U) ⊥ fun x hx => by
    rw [Ideal.mem_bot]
    exact ulimHom_ultraIdeal hU hx
  rwa [frob_diag_ulim] at h

/-! ### The specializations of the limit are the stage data -/

/-- The entries of the models of the product chain are the sequences of the stage entries
(tex 4444–4448). Kind: PROVED. -/
theorem prodChain_blk1 (c : ℕ → ChainMat LamI m0 m1 m2) (i : ℕ) (a b) (s : ℕ) :
    (prodChain c).blk1 i a b s = (c s).blk1 i a b := by
  rw [← prodChain_eval c s, ChainMat.blk1_map]
  rfl

/-- **The specialization of the limit models** (tex 4446: "a compatible limit at every
coefficient precision"): at every precision `k`, for `U`-many stages `s`, the stage model of
`C_{T_i}` is the limit model modulo `(2^k, t^k)`. Kind: PROVED. -/
theorem limit_spec_blk1 (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (k i : ℕ) (a b) :
    ∀ᶠ s in (U : Filter ℕ), (c s).blk1 i a b - (limitChain c U).blk1 i a b ∈ stageIdeal k := by
  have e : (limitChain c U).blk1 i a b = ulim U (fun s => (c s).blk1 i a b) := by
    change ((prodChain c).map (ulimHom U)).blk1 i a b = _
    rw [ChainMat.blk1_map]
    change ulimHom U ((prodChain c).blk1 i a b) = _
    rw [ulimHom_apply]
    exact congrArg (ulim U) (funext fun s => prodChain_blk1 c i a b s)
  rw [e]
  exact eventually_sub_ulim_mem (stageIdeal_isOpen k) U (fun s => (c s).blk1 i a b)

/-- **The specialization of the limit relaxed classes** (tex 4446). Kind: PROVED. -/
theorem limit_spec_z (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (k i : ℕ) (a) :
    ∀ᶠ s in (U : Filter ℕ), (c s).z i a - (limitChain c U).z i a ∈ stageIdeal k :=
  eventually_sub_ulim_mem (stageIdeal_isOpen k) U (fun s => (c s).z i a)

/-- **The specialization of the limit relaxed functionals** (tex 4446). Kind: PROVED. -/
theorem limit_spec_l (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (k i : ℕ) (a) :
    ∀ᶠ s in (U : Filter ℕ), (c s).l i a - (limitChain c U).l i a ∈ stageIdeal k :=
  eventually_sub_ulim_mem (stageIdeal_isOpen k) U (fun s => (c s).l i a)

/-- **The specialization of the limit primitive classes** (tex 4446). Kind: PROVED. -/
theorem limit_spec_zP (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (k i : ℕ) (a) :
    ∀ᶠ s in (U : Filter ℕ), (c s).zP i a - (limitChain c U).zP i a ∈ stageIdeal k := by
  have e : (limitChain c U).zP i a = ulim U (fun s => (c s).zP i a) := by
    change ((prodChain c).map (ulimHom U)).zP i a = _
    rw [ChainMat.zP_map]
    change ulimHom U ((prodChain c).zP i a) = _
    rw [ulimHom_apply]
    refine congrArg (ulim U) (funext fun s => ?_)
    have h := congrFun (ChainMat.zP_map (prodChain c) (evalAt s) i) a
    rw [prodChain_eval] at h
    exact h.symm
  rw [e]
  exact eventually_sub_ulim_mem (stageIdeal_isOpen k) U (fun s => (c s).zP i a)

/-- **The specialization of the limit primitive functionals** (tex 4446). Kind: PROVED. -/
theorem limit_spec_lP (c : ℕ → ChainMat LamI m0 m1 m2) (U : Ultrafilter ℕ) (k i : ℕ) (a) :
    ∀ᶠ s in (U : Filter ℕ), (c s).lP i a - (limitChain c U).lP i a ∈ stageIdeal k := by
  have e : (limitChain c U).lP i a = ulim U (fun s => (c s).lP i a) := by
    change ((prodChain c).map (ulimHom U)).lP i a = _
    rw [ChainMat.lP_map]
    change ulimHom U ((prodChain c).lP i a) = _
    rw [ulimHom_apply]
    refine congrArg (ulim U) (funext fun s => ?_)
    have h := congrFun (ChainMat.lP_map (prodChain c) (evalAt s) i) a
    rw [prodChain_eval] at h
    exact h.symm
  rw [e]
  exact eventually_sub_ulim_mem (stageIdeal_isOpen k) U (fun s => (c s).lP i a)

/-- **Bounded ranks are fixed on a set of the ultrafilter** (tex 4401–4402, 4444–4445; lane RC6's
`bounded_rank_tuples_fixed`): bounded ranks `(m₀, m₁, m₂)` of the stage models of `C_∅` are
constant on a set of `U`, so the stage data of the chain have fixed shapes there.
Kind: PROVED. -/
theorem shapes_fixed (U : Ultrafilter ℕ) {B : ℕ} (r : ℕ → Fin 3 → ℕ) (hr : ∀ s j, r s j ≤ B) :
    ∃ r₀ : Fin 3 → ℕ, (∀ j, r₀ j ≤ B) ∧ ∀ᶠ s in (U : Filter ℕ), r s = r₀ :=
  bounded_rank_tuples_fixed U r hr

end ZInQ.Manuscript.RC.Wiring
