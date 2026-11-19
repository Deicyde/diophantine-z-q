import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Genuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Local
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientPlace
import ZInQKernel.Contrib.CloudB3E2Norm.LocalComponents

/-!
# The genuine relaxation step at an unused split prime

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194), at
the two conjugate places `w`, `w̄` above an unused split prime `q` (tex 4176–4184), with the
unramified condition (tex 3470–3487).

This file assembles the genuine support triangle at the two places and its relaxation step.

* `genuineL2`, `genuineU2`, `genuineRes2`, `genuineRelaxed2`: the genuine local complexes,
  unramified conditions, restrictions and relaxed Selmer data at `w` and `w̄`.
* `prodQuotRetract`: a retraction of the direct sum of the two LOCAL quotients is a retraction
  of the quotient of the direct sum of the two split inclusions.
* `GenuineStepData`: genuine split inclusions `EU_w`, `EU_w̄` of the unramified conditions (they
  exist over a field: `exists_genuineSplit`), a retraction of the sum of the two local quotients
  onto `twoSingCx` (lane RC31's `exists_retract_twoPlaces_place` supplies one from the
  literature: `exists_genuineRQ`), a minimal model of the primitive complex and the cycles.
* `GenuineStepData.triangle`: the support triangle with `C_R` the genuine Selmer complex with the
  full conditions at `w`, `w̄` and `C_P` the one with the conditions `EU_w`, `EU_w̄`
  (`triangle_CP_eq`; the genuine unramified conditions when the `EU.i` are the genuine inflations:
  `triangle_i_eq`).
* **`genuineQuotEquiv`, `genuineQuotEquiv_d`**: the quotient of the full-at-`q` by the
  primitive-at-`q` Selmer complex is the direct sum of the two local full-by-unramified quotients
  at `w` and `w̄`, as complexes (tex 3489–3494, 4176–4184).
* `hzR_genuine2_of_strictLifts`: the norm identity `hzR` for strict lifts at the two-place data,
  from the global identity (`hG`, from the global transfer identity), by the generic local
  components lemmas of the norm identity.
* **`kmStep_genuine`**: with lane RC30's retention data for the genuine primitive-to-relaxed map
  (the functionals are its paired functionals), the paired strict lift `hlift` with `e = e_q`,
  the norm identity `hzR` and the units, the step is a `KmStep` at the coordinates of the models.
  The new block `hBe` is PROVED (`toMatrix_twoSing`); the functional relation is lane RC30's
  `hlamR_of_retention`, applied verbatim.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (changeMap)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)
open ZInQ.Manuscript.RC.Local (prodGCx singCx twoSingCx)

/-! ### A retraction of the sum of the local quotients -/

section ProdQuot

variable {A : Type} [CommRing A] {A₁ B₁ A₂ B₂ : GCx A} (E₁ : SplitInclusion A₁ B₁)
  (E₂ : SplitInclusion A₂ B₂)

/-- **A retraction of the sum of the two local quotients is a retraction of the quotient of the
sum of the two split inclusions** (tex 4176–4184): transport along `prodSplit_quotEquiv`.
Kind: definition. -/
def prodQuotRetract {Y : GCx A} (RQ : GRetract (prodGCx E₁.quotientCx E₂.quotientCx) Y) :
    GRetract (ZInQ.Manuscript.RC.Wiring.prodSplit E₁ E₂).quotientCx Y :=
  RQ.ofEquiv (fun n => (prodSplit_quotEquiv E₁ E₂ n).symm)
    (fun a b h x => (equiv_symm_d (prodSplit_quotEquiv E₁ E₂) (prodSplit_quotEquiv_d E₁ E₂)
      a b h x).symm)

end ProdQuot

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  (w₁ w₂ : Places K S) (X₁ : TopRep.{0} k (GUr K w₁.1)) (X₂ : TopRep.{0} k (GUr K w₂.1))

/-- **The genuine local complex at the two places** `C^•_cont(G_{K_w}, M) ⊕ C^•_cont(G_{K_w̄}, M)`
(tex 3455–3463, 4176–4184). Kind: definition. -/
abbrev genuineL2 : GCx k := prodGCx (genuineLq K S k M w₁) (genuineLq K S k M w₂)

/-- **The genuine unramified conditions at the two places** (tex 3471–3487).
Kind: definition. -/
abbrev genuineU2 : GCx k := prodGCx (genuineUq K S k w₁ X₁) (genuineUq K S k w₂ X₂)

/-- **The genuine restriction to the two places** (tex 3455–3463). Kind: definition. -/
abbrev genuineRes2 : GHom (genuineOld K S₀ S k M Δ).G (genuineL2 K S k M w₁ w₂) :=
  prodLift (genuineRes K S k M w₁) (genuineRes K S k M w₂)

/-- **The genuine relaxed Selmer data at the two places**: the full conditions at `w` and `w̄`
(tex 4157–4166). Kind: definition. -/
abbrev genuineRelaxed2 : SelData k :=
  relaxedAt (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)

/-! ### The global quotient is the sum of the two local quotients -/

section QuotEquiv

variable {K S₀ S k M Δ w₁ w₂ X₁ X₂}
variable (EU₁ : SplitInclusion (genuineUq K S k w₁ X₁) (genuineLq K S k M w₁))
  (EU₂ : SplitInclusion (genuineUq K S k w₂ X₂) (genuineLq K S k M w₂))

/-- **The quotient of the genuine relaxed by the genuine primitive Selmer complex is the direct
sum of the two local quotients at `w` and `w̄`** (tex 3489–3494: "replacing the unramified
condition by the full condition then gives the singular quotient"; tex 4176–4184: the two
places), degreewise: `C_R / C_P ≅ (L_w / U_w) ⊕ (L_w̄ / U_w̄)`. Kind: definition. -/
def genuineQuotEquiv (n : ℤ) :
    (selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
        (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
          (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))).quotientCx.X n ≃ₗ[k]
      (prodGCx EU₁.quotientCx EU₂.quotientCx).X n :=
  (atPlaceQEquiv (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
    (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂) n).symm.trans (prodSplit_quotEquiv EU₁ EU₂ n)

/-- **The identification commutes with the differentials**, so it is an isomorphism of
complexes (tex 3489–3494, 4176–4184). Kind: PROVED. -/
theorem genuineQuotEquiv_d (a b : ℤ) (h : a + 1 = b)
    (x : (selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))).quotientCx.X a) :
    (prodGCx EU₁.quotientCx EU₂.quotientCx).d a b h (genuineQuotEquiv EU₁ EU₂ a x) =
      genuineQuotEquiv EU₁ EU₂ b
        ((selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
          (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
            (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))).quotientCx.d a b h x) := by
  change (prodGCx EU₁.quotientCx EU₂.quotientCx).d a b h (prodSplit_quotEquiv EU₁ EU₂ a
      ((atPlaceQEquiv (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂) a).symm x)) =
    prodSplit_quotEquiv EU₁ EU₂ b
      ((atPlaceQEquiv (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂) b).symm
        ((selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
          (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
            (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))).quotientCx.d a b h x))
  have h2 := equiv_symm_d (X := (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).quotientCx)
    (X' := (selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))).quotientCx)
    (atPlaceQEquiv (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂))
    (atPlaceQEquiv_comm (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂)) a b h x
  exact (prodSplit_quotEquiv_d EU₁ EU₂ a b h _).trans
    (congrArg (prodSplit_quotEquiv EU₁ EU₂ b) h2.symm)

end QuotEquiv

/-! ### The genuine step -/

/-- **The genuine data of one relaxation step at an unused split prime** (tex 4157–4194,
4176–4184): split inclusions of the genuine unramified conditions at `w`, `w̄`, a retraction of
the sum of the two local quotients onto the two singular blocks `[M --zFr−q--> M]`,
`[M --z⁻¹Fr−q--> M]` (the tame local quotient of (4.4)), a minimal model of the primitive
complex, and the relaxed and primitive cycles. Kind: definition (data). -/
structure GenuineStepData (Fr : Matrix (Fin 2) (Fin 2) k) (q : ℕ) (z zi : k) where
  /-- the split inclusion of the unramified condition at `w` -/
  EU₁ : SplitInclusion (genuineUq K S k w₁ X₁) (genuineLq K S k M w₁)
  /-- the split inclusion of the unramified condition at `w̄` -/
  EU₂ : SplitInclusion (genuineUq K S k w₂ X₂) (genuineLq K S k M w₂)
  /-- the retraction of the sum of the two local quotients onto the two singular blocks -/
  RQ : GRetract (prodGCx EU₁.quotientCx EU₂.quotientCx) (twoSingCx Fr q z zi)
  /-- the minimal model of the primitive complex -/
  R : GRetract (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
    (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i))) (minBlock k).toGCx
  /-- the relaxed cycle -/
  zR : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).X 1
  /-- `d z_R = 0` -/
  hzR : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).d 1 2 rfl zR = 0
  /-- the primitive cycle -/
  zP : (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
    (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i))).X 1
  /-- `d z_P = 0` -/
  hzP : (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
    (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i))).d 1 2 rfl zP = 0

variable {K S₀ S k M Δ w₁ w₂ X₁ X₂} {Fr : Matrix (Fin 2) (Fin 2) k} {q : ℕ} {z zi : k}

/-- **The genuine support triangle at the two places** (tex 4157–4194): `C_R` the genuine Selmer
complex with the full conditions at `w`, `w̄`; `C_P` the one with the conditions `EU_w`, `EU_w̄`;
the inclusion the genuine primitive-to-relaxed map; the quotient retraction onto the two singular
blocks, through the global-to-local identification of the quotient; the bases of the two places.
Kind: definition. -/
def GenuineStepData.triangle (G : GenuineStepData K S₀ S k M Δ w₁ w₂ X₁ X₂ Fr q z zi)
    (lamR : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).X 2 →ₗ[k] k)
    (hlamR : lamR ∘ₗ (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).d 1 2 rfl = 0)
    (lamP : (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i))).X 2 →ₗ[k] k)
    (hlamP : lamP ∘ₗ (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i))).d 1 2 rfl = 0) :
    SupportTriangle k :=
  SupportTriangle.atPlace (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
    (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂) (minBlock k) G.R
    (prodQuotRetract G.EU₁ G.EU₂ G.RQ) (twoSing_subsingleton Fr q z zi)
    (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi) G.zR G.hzR G.zP G.hzP lamR hlamR lamP hlamP

/-- **Pinning, the inclusion**: the inclusion of the genuine triangle is the split inclusion of
the Selmer complexes from the split inclusion of the local conditions at the two places, so its
quotient is `genuineQuotEquiv` (tex 4157–4166, 3489–3494). Kind: PROVED (definitional). -/
theorem GenuineStepData.triangle_E (G : GenuineStepData K S₀ S k M Δ w₁ w₂ X₁ X₂ Fr q z zi)
    (lamR : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).X 2 →ₗ[k] k)
    (hlamR : lamR ∘ₗ (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).d 1 2 rfl = 0)
    (lamP : (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i))).X 2 →ₗ[k] k)
    (hlamP : lamP ∘ₗ (selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i))).d 1 2 rfl = 0) :
    (G.triangle lamR hlamR lamP hlamP).E =
      selSplit (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
        (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
          (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂)) :=
  rfl

/-- **Pinning**: the primitive complex of the genuine step is the genuine Selmer complex with the
conditions `EU_w`, `EU_w̄` at the two places (tex 4157–4166). Kind: PROVED. -/
theorem GenuineStepData.triangle_CP_eq (G : GenuineStepData K S₀ S k M Δ w₁ w₂ X₁ X₂ Fr q z zi) :
    selCx (selRestrict (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
        (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
          (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i)) =
      selCx (addPlace (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i) :=
  atPlace_CP_eq _ _ _

/-- **Pinning with the genuine inflations**: if `EU_w`, `EU_w̄` are split inclusions of the genuine
inflations, the condition at the two places is the genuine unramified condition
`ι_w ⊕ ι_w̄` (tex 3471–3487). Kind: PROVED. -/
theorem GenuineStepData.triangle_i_eq (G : GenuineStepData K S₀ S k M Δ w₁ w₂ X₁ X₂ Fr q z zi)
    [ContinuousSMul (GUr K w₁.1) X₁.V] [DiscreteTopology X₁.V] [Finite X₁.V]
    [ContinuousSMul (GUr K w₂.1) X₂.V] [DiscreteTopology X₂.V] [Finite X₂.V]
    (f₁ : X₁.V →ₗ[k] M)
    (hf₁ : ∀ (g : Gloc K w₁.1) (x : X₁.V), f₁ (resUr K w₁.1 g • x) = locMap K S w₁.1 g • f₁ x)
    (f₂ : X₂.V →ₗ[k] M)
    (hf₂ : ∀ (g : Gloc K w₂.1) (x : X₂.V), f₂ (resUr K w₂.1 g • x) = locMap K S w₂.1 g • f₂ x)
    (h₁ : G.EU₁.i = genuineιq K S k M w₁ X₁ f₁ hf₁)
    (h₂ : G.EU₂.i = genuineιq K S k M w₂ X₂ f₂ hf₂) :
    (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i =
      prodGHom (genuineιq K S k M w₁ X₁ f₁ hf₁) (genuineιq K S k M w₂ X₂ f₂ hf₂) := by
  change prodGHom G.EU₁.i G.EU₂.i = _
  rw [h₁, h₂]

/-- **The quotient retraction of the genuine step exists, from the literature** (tex 3470–3480,
4176–4184; lane RC31's `exists_retract_twoPlaces_place`, verbatim): at the two conjugate places of
odd residue cardinality `q`, for bijective inflations `f_w`, `f_w̄` and bases in which Frobenius
is `z Fr` and `z⁻¹ Fr`, given the literature statements `TameCochainQuasiIso` and
`IwasawaGenerators`, every pair of split inclusions of the genuine inflations has a retraction of
the sum of its local quotients onto `twoSingCx Fr q z zi`: the field `RQ` of
`GenuineStepData`. Kind: PROVED. -/
theorem exists_genuineRQ (hT : ZInQ.Manuscript.RC.Local.TameCochainQuasiIso)
    (hI : ZInQ.Manuscript.RC.Local.IwasawaGenerators) [Finite M]
    (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (q : ℕ) (hq : Odd q)
    (Fr : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    [ContinuousSMul (GUr K w₁.1) X₁.V] [DiscreteTopology X₁.V] [Finite X₁.V]
    [ContinuousSMul (GUr K w₂.1) X₂.V] [DiscreteTopology X₂.V] [Finite X₂.V]
    (f₁ : X₁.V →ₗ[k] M)
    (hf₁ : ∀ (g : Gloc K w₁.1) (x : X₁.V), f₁ (resUr K w₁.1 g • x) = locMap K S w₁.1 g • f₁ x)
    (hbij₁ : Function.Bijective f₁) (hq₁ : q = Nat.card (𝓞 K ⧸ w₁.1.asIdeal))
    (EU₁ : SplitInclusion (genuineUq K S k w₁ X₁) (genuineLq K S k M w₁))
    (hE₁ : EU₁.i = genuineιq K S k M w₁ X₁ f₁ hf₁)
    (b₁ : X₁.V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K w₁.1) X₁ v) =
      Matrix.toLin' (z • Fr) (b₁ v))
    (f₂ : X₂.V →ₗ[k] M)
    (hf₂ : ∀ (g : Gloc K w₂.1) (x : X₂.V), f₂ (resUr K w₂.1 g • x) = locMap K S w₂.1 g • f₂ x)
    (hbij₂ : Function.Bijective f₂) (hq₂ : q = Nat.card (𝓞 K ⧸ w₂.1.asIdeal))
    (EU₂ : SplitInclusion (genuineUq K S k w₂ X₂) (genuineLq K S k M w₂))
    (hE₂ : EU₂.i = genuineιq K S k M w₂ X₂ f₂ hf₂)
    (b₂ : X₂.V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K w₂.1) X₂ v) =
      Matrix.toLin' (zi • Fr) (b₂ v)) :
    Nonempty (GRetract (prodGCx EU₁.quotientCx EU₂.quotientCx) (twoSingCx Fr q z zi)) :=
  ZInQ.Manuscript.RC.Local.exists_retract_twoPlaces_place hT hI hexp q hq Fr z zi w₁ X₁ f₁ hf₁
    hbij₁ hq₁ EU₁ hE₁ b₁ hb₁ w₂ X₂ f₂ hf₂ hbij₂ hq₂ EU₂ hE₂ b₂ hb₂

/-- **The norm identity for strict lifts at the two-place data** (tex 4157–4170): for strict lifts
`z_R = (a_R, u_R, 0)`, `z_P = (a_P, u_P, 0)` (localizations exactly in the local conditions), with
the old conditions injective in degree one and liftable in degree zero, the global identity
`a_R = e a_P + d b_G` (from the global transfer identity) gives `z_R = e • i(z_P) + d b`: the
generic local components of the norm identity at the relaxed data of the two places.
Kind: PROVED. -/
theorem hzR_genuine2_of_strictLifts
    (EU₁ : SplitInclusion (genuineUq K S k w₁ X₁) (genuineLq K S k M w₁))
    (EU₂ : SplitInclusion (genuineUq K S k w₂ X₂) (genuineLq K S k M w₂))
    (aR aP : (globalCx k (GKS K S) M).X 1) (uR : (genuineRelaxed2 K S₀ S k M Δ w₁ w₂).U.X 1)
    (uP : (prodCx (genuineOld K S₀ S k M Δ).U (genuineU2 K S k w₁ w₂ X₁ X₂)).X 1) (e : k)
    (bG : (globalCx k (GKS K S) M).X 0)
    (hιold : Function.Injective ((genuineOld K S₀ S k M Δ).ι.f 1 1 rfl))
    (hsold : ∀ y : (genuineOld K S₀ S k M Δ).L.X 0,
      ∃ x : (genuineOld K S₀ S k M Δ).U.X 0, (genuineOld K S₀ S k M Δ).ι.f 0 0 rfl x = y)
    (hRloc : (genuineRelaxed2 K S₀ S k M Δ w₁ w₂).ι.f 1 1 rfl uR =
      (genuineRelaxed2 K S₀ S k M Δ w₁ w₂).res.f 1 1 rfl aR)
    (hPloc : (genuineRelaxed2 K S₀ S k M Δ w₁ w₂).ι.f 1 1 rfl
      ((primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i).f 1 1 rfl uP) =
      (genuineRelaxed2 K S₀ S k M Δ w₁ w₂).res.f 1 1 rfl aP)
    (hG : aR = e • aP + (globalCx k (GKS K S) M).d 0 1 rfl bG) :
    ∃ c : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).X 0,
      ZInQ.Contrib.CloudB3E2.NormCochain.strictLift (genuineRelaxed2 K S₀ S k M Δ w₁ w₂) aR uR =
        e • (changeMap (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
          (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
            (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i)).f 1 1 rfl
          (ZInQ.Contrib.CloudB3E2.NormCochain.strictLiftP (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
            (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
              (ZInQ.Manuscript.RC.Wiring.prodSplit EU₁ EU₂).i) aP uP) +
        (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).d 0 1 rfl c := by
  obtain ⟨bU, hbU⟩ := ZInQ.Contrib.CloudB3E2.NormCochain.addPlace_ι_surjective
    (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂) hsold
    ((genuineRelaxed2 K S₀ S k M Δ w₁ w₂).res.f 0 0 rfl bG)
  exact ⟨_, ZInQ.Contrib.CloudB3E2.NormCochain.hzR_of_strictLifts
    (genuineRelaxed2 K S₀ S k M Δ w₁ w₂) _ aR aP uR uP e bG bU
    (ZInQ.Contrib.CloudB3E2.NormCochain.addPlace_ι_injective (genuineOld K S₀ S k M Δ)
      (genuineRes2 K S₀ S k M Δ w₁ w₂) hιold) hRloc hPloc hG hbU⟩

/-- **The relaxation step at an unused split prime from genuine data** (tex 4157–4194): for the
genuine support triangle at `w`, `w̄`, with lane RC30's retention data for the genuine
primitive-to-relaxed map (the functionals `λ_R = β_R(z_S, ·)`, `λ_P = β_P(z_{P⊥}, ·)`), the paired
strict lift `hlift` with `e = e_q`, the norm identity `hzR` and the units, the step is a
`KmStep` at the coordinates of the models: the block hypothesis is PROVED (`toMatrix_twoSing`),
the functional relation is lane RC30's theorem. Kind: PROVED. -/
theorem kmStep_genuine (G : GenuineStepData K S₀ S k M Δ w₁ w₂ X₁ X₂ Fr q z zi)
    {DPp : SelData k} {US : GCx k} {fS : GHom US DPp.U} {Lq Uq : GCx k} {ιq : GHom Uq Lq}
    (PR : PlaceRetentionG (genuineRelaxed2 K S₀ S k M Δ w₁ w₂) DPp
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
        (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i) fS Lq Uq ιq)
    (tr : (coneCx PR.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx PR.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0)
    (zPp : (selCx DPp).X 1) (hzPp : (selCx DPp).d 1 2 rfl zPp = 0) (b : (selCx DPp).X 0)
    {qi a : k} (hq : (q : k) * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi z zi ≠ 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = pointFactor a z zi • zPp + (selCx DPp).d 0 1 rfl b)
    (hzR : ∃ c : (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).X 0,
      G.zR = pointFactor a z zi • (changeMap (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
        (primToRel (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
          (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂).i)).f 1 1 rfl G.zP +
        (selCx (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)).d 0 1 rfl c) :
    KmStep Fr (q : k) a z zi
      (G.triangle (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).relCoord
      (G.triangle (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).primCoord :=
  kmStep_ofSelmer_retention (genuineRelaxed2 K S₀ S k M Δ w₁ w₂)
    (newSplit (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂))
    PR tr htr zS hzS zPp hzPp b G.R
    (newQuotRetract (genuineOld K S₀ S k M Δ) (genuineRes2 K S₀ S k M Δ w₁ w₂)
      (ZInQ.Manuscript.RC.Wiring.prodSplit G.EU₁ G.EU₂) (prodQuotRetract G.EU₁ G.EU₂ G.RQ))
    (twoSing_subsingleton Fr q z zi) (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi) G.zR G.hzR G.zP
    G.hzP hq ha hd hl hlift
    ⟨Equiv.refl _, (toMatrix_twoSing Fr q z zi).trans (submatrix_id_id _).symm⟩ hzR

end ZInQ.Manuscript.RC.Wiring
