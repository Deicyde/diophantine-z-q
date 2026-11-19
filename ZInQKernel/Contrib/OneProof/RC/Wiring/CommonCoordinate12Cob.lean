import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Chain

/-!
# The relaxation step with the functional relation up to a coboundary

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194):
"the retained pairing gives `λ_R ∘ i = e_q λ_P`".

The retained pairing gives the functional relation on cocycles: `λ_R(i w) = e λ_P(w)` for every
cocycle `w ∈ C_P²` (lane RC30's `PlaceRetentionG.pairedFunctional_natural`). On a model whose basis
vectors are cocycles (the minimal model) this is the exact relation of `KmStep` on the model
vectors. On the iterated cone model — the primitive model of every step after the first of a chain
of relaxations (`SupportTriangle.next`) — the basis vectors are not all cocycles; there the
relation holds up to a functional vanishing on cocycles, which over a field is `μ ∘ d`, a
coboundary, and the Knudsen–Mumford coordinate does not see it (`kmCoord_add_coboundary`).

* `exists_comp_of_vanish`: over a field, a functional vanishing on `ker d` is `μ ∘ d`.
* `kmStep_of_cob`: the torsion-level step with `λ ∘ inl = e λ_P + ν U` (`U = d²` of the cancelled
  complex, so `ν U` is a coboundary there) is a `KmStep`.
* `SupportTriangle.lamRv_inl_cob`: the cochain relation `λ_R ∘ i = c λ_P + μ ∘ d` gives the model
  relation up to the coboundary of `ν = μ ∘ i_D`.
* **`SupportTriangle.kmStep_of_supportTriangle_cob`**: the step with the functional relation up to
  a coboundary; **`SupportTriangle.kmStep_of_natural`**: the step with the functional relation on
  cocycles only, for any model of `C_P`.
* `kmStep_ofSelmer_retention_any`: lane RC30's retention data give the step of
  `SupportTriangle.ofSelmer` for ANY model of the primitive complex (not only the minimal one).
* `NextData`, `NextData.tri`: the data of the next step of a chain of relaxations;
  **`kmStep_next_of_natural`**: the next step of a chain is a `KmStep` when its relaxed functional
  satisfies the functional relation on cocycles against this step's relaxed functional (what the
  retained pairing of the next step gives), with the new block and the norm identity.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (changeMap)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun twoPlaceBlock det_twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor quotientDet quotientDet_eq)
open ZInQ.Manuscript.RC.SelmerComplex

/-! ### Linear algebra -/

/-- **A functional vanishing on the kernel factors through the map** (over a field;
tex 4170–4177): if `δ` vanishes on `ker d`, then `δ = μ ∘ d` for some `μ`. Kind: PROVED. -/
theorem exists_comp_of_vanish {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (d : V →ₗ[K] W) (δ : V →ₗ[K] K)
    (h : ∀ v, d v = 0 → δ v = 0) : ∃ μ : W →ₗ[K] K, δ = μ ∘ₗ d := by
  have hle : LinearMap.ker d ≤ LinearMap.ker δ := fun v hv => h v hv
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective
    ((LinearMap.ker d).liftQ d le_rfl) (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  refine ⟨((LinearMap.ker d).liftQ δ hle) ∘ₗ r, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : r (d v) = (LinearMap.ker d).mkQ v := by
    have := LinearMap.congr_fun hr ((LinearMap.ker d).mkQ v)
    simpa using this
  change δ v = (LinearMap.ker d).liftQ δ hle (r (d v))
  rw [hv, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-! ### The torsion-level step with a coboundary -/

section Model

variable {K : Type} [Field K]

/-- **The torsion-level step with the functional relation up to a coboundary** (tex 4157–4194,
4170–4177): if `λ ∘ inl = e λ_P + ν d²` with `ν d²` a coboundary of the cancelled complex, then
`λ − ν d²_C` is a closed functional of the pre-cancellation complex with the same coordinate whose
restriction is `e λ_P`, so the step is a `KmStep`. Kind: PROVED. -/
theorem kmStep_of_cob {Fr : Matrix (Fin 2) (Fin 2) K} {q a zq zqi uR uP : K}
    (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (hBe : ∃ e : C.N ≃ Fin 2 ⊕ Fin 2, C.B = (twoPlaceBlock Fr q zq zqi).submatrix e e)
    {z : C.D1 ⊕ C.N → K} {lam : C.D2 ⊕ C.N → K} (hz : C.toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.toFour.d1 = 0) {zP : C.D1 → K} {lamP : C.D2 → K}
    (hzP : (C.cancel hB).toFour.d1 *ᵥ zP = 0) (hlamP : lamP ᵥ* (C.cancel hB).toFour.d1 = 0)
    (ν : Fin C.m2 → K) (hzR : z ∘ Sum.inl = pointFactor a zq zqi • zP)
    (hlamR : ∀ j, lam (Sum.inl j) = pointFactor a zq zqi * lamP j + (ν ᵥ* C.U) j)
    (hR : uR = kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N))
    (hP : uP = kmCoord (C.cancel hB).toFour zP lamP hzP hlamP (σBlock C.m0 C.m1 C.m2)) :
    KmStep Fr q a zq zqi uR uP := by
  refine ⟨C, hB, hBe, z, lam + (-ν) ᵥ* C.toFour.d2, hz, closed_add_coboundary C.toFour hlam (-ν),
    zP, lamP, hzP, hlamP, hzR, ?_, ?_, hP⟩
  · funext j
    have h2 : ((-ν) ᵥ* C.toFour.d2) (Sum.inl j) = -((ν ᵥ* C.U) j) := by
      change ((-ν) ᵥ* fromCols C.U C.V) (Sum.inl j) = -((ν ᵥ* C.U) j)
      rw [vecMul_fromCols, Sum.elim_inl, neg_vecMul, Pi.neg_apply]
    change lam (Sum.inl j) + ((-ν) ᵥ* C.toFour.d2) (Sum.inl j) = pointFactor a zq zqi * lamP j
    rw [h2, hlamR j]
    ring
  · rw [hR]
    exact (kmCoord_add_coboundary C.toFour hz hlam (σFull C.m0 C.m1 C.m2 C.N) (-ν)).symm

end Model

/-! ### The support triangle with the functional relation up to a coboundary -/

namespace SupportTriangle

variable {F : Type} [Field F] (S : SupportTriangle F)

/-- **The model relation from the cochain relation up to a coboundary** (tex 4166–4177): if
`λ_R ∘ i = c λ_P + μ ∘ d` on `C_P²`, then on the model vectors
`λ_R^{mod} ∘ inl = c λ_P^{mod} + ν d²_D` with `ν = μ ∘ i_D` in degree three. Kind: PROVED. -/
theorem lamRv_inl_cob (c : F) (μ : S.CP.X 3 →ₗ[F] F)
    (h : S.lamR ∘ₗ S.E.i.f 2 2 rfl = c • S.lamP + μ ∘ₗ S.CP.d 2 3 rfl)
    (j : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2) :
    S.lamRv (Sum.inl j) = c * S.lamPv j +
      (funVec (ι := Fin S.D.m2) (μ ∘ₗ S.R.i.f 3 3 rfl) ᵥ* S.D.toFour.d2) j := by
  have h0 := congrFun (funVec_relRetract_inl S.E S.R S.RQ S.b1 S.b2 S.hQ' S.lamR) j
  rw [Function.comp_apply] at h0
  change funVec (ι := (Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2) ⊕ S.N)
    (S.lamR ∘ₗ S.retract.i.f 2 2 rfl) (Sum.inl j) = _
  rw [h0, h]
  set y : S.D.toGCx.X 2 := (Pi.single j (1 : F) : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2 → F) with hy
  change (c • S.lamP + μ ∘ₗ S.CP.d 2 3 rfl) (S.R.i.f 2 2 rfl y) =
    c * S.lamP (S.R.i.f 2 2 rfl y) + _
  rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    ← GRetract.i_d S.R 2 3 rfl y]
  congr 1
  have e1 := funVec_dotProduct (ι := Fin S.D.m2) (μ ∘ₗ S.R.i.f 3 3 rfl)
    (S.D.d2 *ᵥ (Pi.single j (1 : F) : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2 → F))
  rw [dotProduct_mulVec, dotProduct_single, mul_one] at e1
  exact e1

/-- **The relaxation step with the functional relation up to a coboundary** (tex 4157–4194,
5398–5424): with the new block the two-place block (`hBe`), `l_q ≠ 0`, the norm identity
(`hzR`) and `λ_R ∘ i = e_q λ_P + μ ∘ d` for some `μ` (`hlamR`), the step is a `KmStep` at the
coordinates of the models, for any block-complex model of `C_P`. Kind: PROVED. -/
theorem kmStep_of_supportTriangle_cob {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = pointFactor a zq zqi • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : ∃ μ : S.CP.X 3 →ₗ[F] F,
      S.lamR ∘ₗ S.E.i.f 2 2 rfl = pointFactor a zq zqi • S.lamP + μ ∘ₗ S.CP.d 2 3 rfl) :
    KmStep Fr q a zq zqi S.relCoord S.primCoord := by
  obtain ⟨e, he⟩ := hBe
  obtain ⟨b, hb⟩ := hzR
  obtain ⟨μ, hμ⟩ := hlamR
  have hB : IsUnit S.model.B.det := S.isUnit_relModel_det hq ha hd hl e he
  set c := pointFactor a zq zqi with hc
  have hz' := S.cycle_smul_zPext c
  have hzRv := S.zRv_eq c b hb
  have hcoordR : S.relCoord = kmCoord S.model.toFour (c • S.zPext) S.lamRv hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) := by
    unfold relCoord
    rw [kmCoord_congr S.model.toFour S.zRv_cycle
      (cycle_add_boundary S.model.toFour hz' (S.retract.p.f 0 0 rfl b)) S.lamRv_closed
      S.lamRv_closed hzRv rfl]
    exact kmCoord_add_boundary S.model.toFour hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) _
  have h4 : (S.model.cancel hB).toFour = S.D.toFour :=
    cancel_relModel_toFour S.E S.R S.RQ S.b1 S.b2 hB
  have hzP' : (S.model.cancel hB).toFour.d1 *ᵥ S.zPv = 0 := by
    rw [h4]
    exact S.zPv_cycle
  have hlamP' : S.lamPv ᵥ* (S.model.cancel hB).toFour.d1 = 0 := by
    rw [h4]
    exact S.lamPv_closed
  have hlam' : ∀ j, S.lamRv (Sum.inl j) = c * S.lamPv j +
      (funVec (ι := Fin S.D.m2) (μ ∘ₗ S.R.i.f 3 3 rfl) ᵥ* S.model.U) j :=
    fun j => S.lamRv_inl_cob c μ hμ j
  exact kmStep_of_cob S.model hB ⟨e, (relModel_B S.E S.R S.RQ S.b1 S.b2).trans he⟩ hz'
    S.lamRv_closed hzP' hlamP' _ rfl hlam' hcoordR (S.primCoord_eq_cancel hB hzP' hlamP')

/-- **The relaxation step with the functional relation on cocycles only** (tex 4157–4194,
4170–4177): if `λ_R(i w) = e_q λ_P(w)` for every cocycle `w ∈ C_P²` (what the retained pairing
gives, lane RC30's `pairedFunctional_natural`), then over a field the relation holds up to `μ ∘ d`
(`exists_comp_of_vanish`), and the step is a `KmStep`, for any model of `C_P`. Kind: PROVED. -/
theorem kmStep_of_natural {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = pointFactor a zq zqi • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hnat : ∀ w : S.CP.X 2, S.CP.d 2 3 rfl w = 0 →
      S.lamR (S.E.i.f 2 2 rfl w) = pointFactor a zq zqi * S.lamP w) :
    KmStep Fr q a zq zqi S.relCoord S.primCoord := by
  obtain ⟨μ, hμ⟩ := exists_comp_of_vanish (S.CP.d 2 3 rfl)
    (S.lamR ∘ₗ S.E.i.f 2 2 rfl - pointFactor a zq zqi • S.lamP) (fun w hw => by
      change S.lamR (S.E.i.f 2 2 rfl w) - pointFactor a zq zqi * S.lamP w = 0
      rw [hnat w hw, sub_self])
  refine S.kmStep_of_supportTriangle_cob hq ha hd hl hBe hzR ⟨μ, ?_⟩
  rw [← hμ]
  abel

end SupportTriangle

/-! ### Lane RC30's retention for any model -/

/-- **The step of the support triangle of Selmer complexes from lane RC30's retention data, for any
model of the primitive complex** (tex 4157–4194): lane RC30's `pairedFunctional_natural` gives
the functional relation on cocycles; `kmStep_of_natural` gives the step. Unlike
`kmStep_ofSelmer_retention`, the model `Dm` of `C_P` need not be minimal. Kind: PROVED. -/
theorem kmStep_ofSelmer_retention_any {F : Type} [Field F] (D : SelData F) {U' : GCx F}
    (EU : SplitInclusion U' D.U)
    {DPp : SelData F} {US : GCx F} {fS : GHom US DPp.U} {Lq Uq : GCx F} {ιq : GHom Uq Lq}
    (PR : PlaceRetentionG D DPp EU.i fS Lq Uq ιq)
    (tr : (coneCx PR.toRetainedPairing.QP.resE).X 3 →ₗ[F] F)
    (htr : ∀ x, tr ((coneCx PR.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0)
    (zPp : (selCx DPp).X 1) (hzPp : (selCx DPp).d 1 2 rfl zPp = 0) (b : (selCx DPp).X 0)
    (Dm : BlockComplex F) (R : GRetract (selCx (selRestrict D EU.i)) Dm.toGCx) {Q' : GCx F}
    (RW : GRetract EU.quotientCx Q') (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
    (zR : (selCx D).X 1) (hzR0 : (selCx D).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict D EU.i)).X 1)
    (hzP0 : (selCx (selRestrict D EU.i)).d 1 2 rfl zP = 0)
    {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS =
      pointFactor a zq zqi • zPp + (selCx DPp).d 0 1 rfl b)
    (hBe : ∃ e : N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix b1 b2 (Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ c : (selCx D).X 0,
      zR = pointFactor a zq zqi • (changeMap D EU.i).f 1 1 rfl zP + (selCx D).d 0 1 rfl c) :
    KmStep Fr q a zq zqi
      (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR0 zP hzP0
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).relCoord
      (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR0 zP hzP0
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).primCoord :=
  SupportTriangle.kmStep_of_natural _ hq ha hd hl hBe hzR
    (fun w hw => PR.pairedFunctional_natural tr htr zS zPp _ b hlift w hw)

/-! ### Chaining: the next step -/

/-- **The data of the next step of a chain of relaxations** (tex 4185–4193): a relaxed complex
`C_R'` containing this step's relaxed complex through a split inclusion, a retraction of the new
quotient onto a model with bases, and the next relaxed cycle and functional. Kind: definition
(data). -/
structure NextData {F : Type} [Field F] (S : SupportTriangle F) where
  /-- the next relaxed complex -/
  CR' : GCx F
  /-- the inclusion of this relaxed complex into the next one -/
  E' : SplitInclusion S.CR CR'
  /-- the model of the next quotient -/
  Q'' : GCx F
  /-- the retraction of the next quotient onto its model -/
  RQ' : GRetract E'.quotientCx Q''
  /-- the model of the next quotient lives in degrees one and two -/
  hQ'' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q''.X n)
  /-- the index set of the next new summands -/
  N' : Type
  /-- `N'` is finite -/
  [fN' : Fintype N']
  /-- `N'` has decidable equality -/
  [dN' : DecidableEq N']
  /-- a basis of the next quotient model in degree one -/
  b1' : Basis N' F (Q''.X 1)
  /-- a basis of the next quotient model in degree two -/
  b2' : Basis N' F (Q''.X 2)
  /-- the next relaxed cycle -/
  zR' : CR'.X 1
  /-- `d z_R' = 0` -/
  hzR' : CR'.d 1 2 rfl zR' = 0
  /-- the next relaxed functional -/
  lamR' : CR'.X 2 →ₗ[F] F
  /-- `λ_R' ∘ d = 0` -/
  hlamR' : lamR' ∘ₗ CR'.d 1 2 rfl = 0

attribute [instance] NextData.fN' NextData.dN'

/-- **The next step of a chain** (tex 4185–4193): `SupportTriangle.next` with the next data.
Kind: definition. -/
def NextData.tri {F : Type} [Field F] {S : SupportTriangle F} (nd : NextData S) :
    SupportTriangle F :=
  S.next nd.E' nd.RQ' nd.hQ'' nd.b1' nd.b2' nd.zR' nd.hzR' nd.lamR' nd.hlamR'

/-- **One coordinate per support along the chain** (tex 4185–4193): the primitive coordinate of the
next step is `±` the relaxed coordinate of this one (`next_primCoord`). Kind: PROVED. -/
theorem NextData.primCoord_tri {F : Type} [Field F] {S : SupportTriangle F} (nd : NextData S) :
    ∃ ε : ℤˣ, nd.tri.primCoord = (ε : F) * S.relCoord :=
  next_primCoord S nd.E' nd.RQ' nd.hQ'' nd.b1' nd.b2' nd.zR' nd.hzR' nd.lamR' nd.hlamR'

/-- **The next step of a chain is a `KmStep`** (tex 4157–4194, 4185–4193): with the new block of
the next step (`hBe`), the norm identity at the next step (`hzR`), and the functional relation on
cocycles of `C_{T ∪ p}` between the next relaxed functional and this step's relaxed functional
(`hnat`: the retained pairing of the next step, lane RC30, when its primitive functional is this
relaxed functional), the next step is a `KmStep` at its coordinates — although its primitive model
is the iterated cone model, whose basis vectors are not all cocycles. Kind: PROVED. -/
theorem kmStep_next_of_natural {F : Type} [Field F] {S : SupportTriangle F} (nd : NextData S)
    {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : nd.N' ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix nd.b1' nd.b2' (nd.Q''.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : nd.CR'.X 0,
      nd.zR' = pointFactor a zq zqi • nd.E'.i.f 1 1 rfl S.zR + nd.CR'.d 0 1 rfl b)
    (hnat : ∀ w : S.CR.X 2, S.CR.d 2 3 rfl w = 0 →
      nd.lamR' (nd.E'.i.f 2 2 rfl w) = pointFactor a zq zqi * S.lamR w) :
    KmStep Fr q a zq zqi nd.tri.relCoord nd.tri.primCoord :=
  SupportTriangle.kmStep_of_natural nd.tri hq ha hd hl hBe hzR hnat

end ZInQ.Manuscript.RC.Wiring
