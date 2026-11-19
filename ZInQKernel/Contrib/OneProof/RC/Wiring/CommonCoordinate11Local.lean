import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10TwoSing
import ZInQKernel.Contrib.OneProof.RC.Wiring.RetentionGenuine
import ZInQKernel.Contrib.OneProof.RC.Local.TwoPlaceSplitBlock

/-!
# The local pieces of the support triangle: genuine splitting, two places, lane unification

Manuscript `diophantine_zq.tex`, the unramified condition at a new place (tex 3470–3487), the
support triangle of Lemma `ex:arith-common-coordinate` (tex 4157–4194) at the two conjugate places
above an unused split prime (tex 4176–4184), and the triangular model (tex 5398–5424):

> At augmentation `g = 1`, this is the direct sum of the unramified complex `[Φ − 1]` in degrees
> zero and one and the singular quotient `[Φ − q]` in degrees one and two. […]
> The two quotient determinants satisfy `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`.

**The genuine inflation is split over a field.** For an injective `G_{K_w}`-equivariant
`f : W → M`, every component of the genuine map `ι_q : [W --(Φ_w − 1)--> W] → C^•_cont(G_{K_w}, M)`
(`genuineιq`, the inflation `urToLocal_galois`) is injective:
* degree `0`: `x ↦` the constant cochain `f x` (`urLin₀_injective`);
* degree `1`: `x ↦ (g ↦ f (c_x (res g)))`; the restriction `G_{K_w} → Gal(K_w^ur/K_w)` is
  surjective (`resUr_surjective`) and `c_x(Frob) = x` (`urLin₁_injective`);
* the other degrees: the unramified complex vanishes there.
Hence `urToLocal_f_injective`, `genuineιq_f_injective` and **`exists_genuineSplit`**: over a field
the genuine `ι_q` extends to a `SplitInclusion` (from `exists_splitInclusion`).

**The two places `w`, `w̄`.** `prodGHom`, `GRetract.prodR`: chain maps and normalized retracts of
direct sums `prodGCx`, componentwise. `prodSplit`: the direct sum of two split inclusions, with
complements `Q₁ⁿ × Q₂ⁿ`; its quotient coordinate and quotient differential are componentwise
(`prodSplit_coordQ`, `prodSplit_dQ`), so its quotient complex is the direct sum of the two quotient
complexes (`prodSplit_quotEquiv`, `prodSplit_quotEquiv_d`). `prodSplitRetract`: retracts of the two
quotients onto `Y₁`, `Y₂` give a retract of the quotient of `prodSplit` onto `Y₁ ⊕ Y₂`
(`GRetract.ofEquiv`). For the singular blocks `[M --zFr−q--> M]`, `[M --z⁻¹Fr−q--> M]` the target
is `twoSingCx Fr q z z⁻¹` (`twoSingCx_eq_prodGCx`, definitional; `twoSingRetract`).

**Unification with lane RC31.** `triIncl_eq_triSplitInclusion` and `triQEquiv_eq_symm`
(definitional): this lane's split inclusion of a triangular extension is lane RC31's
`triSplitInclusion`, and its `triQEquiv` is the inverse of lane RC31's. `triQBasis_twoSing_one`,
`triQBasis_twoSing_two`: the bases transported from `twoSingB1`, `twoSingB2` are lane RC31's
`Basis.ofEquivFun (twoPieceCoord1 …)`, `Basis.ofEquivFun (twoPieceCoord2 …)`; hence
`relModel_twoSing_eq`: the full-condition model `relModel` with the two-place bases is lane RC31's
`fullPreOfSplit` of `triSplitInclusion`. Both forms of the block hypothesis `hBe` follow, each in
one line from the other lane: `twoPiece_hBe_of_toMatrix` (lane RC31's `twoPiece_hBe` over a field,
from `toMatrix_triIncl_dQ` and `toMatrix_twoSing`) and `relModel_twoSing_hBe` (from lane RC31's
`twoPiece_hBe` and `relModel_twoSing_eq`); `relModel_twoSing_B`: `B = twoPlaceBlock`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-! ### The genuine inflation is injective in every degree -/

section Generic

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **Degree zero of the inflation is injective** (tex 3470–3487): `x ↦` the constant
`0`-cochain `f x` is injective when `f` is. Kind: PROVED. -/
theorem urLin₀_injective {k : Type} [CommRing k] [TopologicalSpace k]
    {G : Type} [Group G] [TopologicalSpace G] {H : Type} [Group H] (X : TopRep.{0} k H)
    {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] (f : X.V →ₗ[k] M) (hinj : Function.Injective f) :
    Function.Injective (urLin₀ (G := G) X f) := fun _ _ hxy =>
  hinj (congrArg (fun c : contCochain k G M 0 => asFun k G M (n := 0) c.1 Fin.elim0) hxy)

/-- **Degree one of the inflation is injective** (tex 3470–3487): `x ↦ (g ↦ f (c_x (π g)))` is
injective when `f` is and `π` is surjective: evaluate at a preimage of the Frobenius, where
`c_x(Frob) = x` (`urCocycle_frob`). Kind: PROVED. -/
theorem urLin₁_injective {k : Type} [CommRing k] [TopologicalSpace k]
    {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
    [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
    {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] (f : X.V →ₗ[k] M) (hinj : Function.Injective f)
    (hπ : Function.Surjective π) : Function.Injective (urLin₁ e π X f) := by
  intro x y hxy
  obtain ⟨g, hg⟩ := hπ (frobElt e)
  have h := congrArg (fun c : contCochain k G M 1 => asFun k G M (n := 1) c.1 (fun _ => g)) hxy
  change f (urCocycle e X x (π g)) = f (urCocycle e X y (π g)) at h
  rw [hg, urCocycle_frob, urCocycle_frob] at h
  exact hinj h

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [hGkM : SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- **The inflation `urToLocal` is injective in every degree** (tex 3470–3487) when `f` is
injective and `π` is surjective: degrees `0` and `1` are `urLin₀`, `urLin₁` after the structural
isomorphisms of `HomologicalComplex.double`, and the unramified complex is zero in the other
degrees. Kind: PROVED. -/
theorem urToLocal_f_injective (hinj : Function.Injective f) (hπ : Function.Surjective π)
    (n : ℤ) : Function.Injective ((urToLocal e π X f hf).f n).hom := by
  by_cases h0 : n = 0
  · subst h0
    rw [urToLocal_f₀]
    exact (urLin₀_injective X f hinj).comp
      (HomologicalComplex.doubleXIso₀ _ rel01).toLinearEquiv.injective
  by_cases h1 : n = 1
  · subst h1
    rw [urToLocal_f₁]
    exact (urLin₁_injective e π X f hinj hπ).comp
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).toLinearEquiv.injective
  · have := ModuleCat.subsingleton_of_isZero (isZero_X (frob e X) n h0 h1)
    exact Function.injective_of_subsingleton _

end Generic

section Genuine

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The genuine map `ι_q` is injective in every degree** (tex 3470–3487, 4157–4194): for an
injective `G_{K_w}`-equivariant `f : W → M`, every component of the inflation
`[W --(Φ_w − 1)--> W] → C^•_cont(G_{K_w}, M)` is injective; the restriction
`G_{K_w} → Gal(K_w^ur/K_w)` is surjective (`resUr_surjective`). Kind: PROVED. -/
theorem genuineιq_f_injective (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hinj : Function.Injective f) (n : ℤ) :
    Function.Injective ((genuineιq K S k M w X f hf).f n n rfl) :=
  urToLocal_f_injective (eUr K w.1) (resUr K w.1) X (M := ResMod (locMap K S w.1) M)
    (hGkM := inferInstanceAs (SMulCommClass (Gloc K w.1) k (ResMod (locMap K S w.1) M)))
    f hf hinj (resUr_surjective K w.1) n

end Genuine

section GenuineField

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Manuscript.RC.Limits

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The genuine `ι_q` is a split inclusion over a field** (tex 3470–3487, 4157–4194,
5398–5424): over a field `k`, an injective `G_{K_w}`-equivariant `f : W → M` gives a
`SplitInclusion` of the unramified complex into `C^•_cont(G_{K_w}, M)` whose inclusion is the
genuine `ι_q` (`exists_splitInclusion` and `genuineιq_f_injective`). Kind: PROVED. -/
theorem exists_genuineSplit (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [Field k] [TopologicalSpace k]
    (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (GKS K S) M] (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hinj : Function.Injective f) :
    ∃ EUq : SplitInclusion (genuineUq K S k w X) (genuineLq K S k M w),
      EUq.i = genuineιq K S k M w X f hf :=
  exists_splitInclusion _ (genuineιq_f_injective K S k M w X f hf hinj)

end GenuineField

/-! ### Direct sums at the two places -/

section Products

open ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.Local (prodGCx)

variable {S : Type} [CommRing S]

/-- **The direct sum of two chain maps** (tex 4176–4184: the two places `w`, `w̄`):
`(x₁, x₂) ↦ (f₁ x₁, f₂ x₂)`. Kind: definition (PROVED chain property). -/
def prodGHom {X₁ Y₁ X₂ Y₂ : GCx S} (f₁ : GHom X₁ Y₁) (f₂ : GHom X₂ Y₂) :
    GHom (prodGCx X₁ X₂) (prodGCx Y₁ Y₂) where
  f a b h := (f₁.f a b h).prodMap (f₂.f a b h)
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    Prod.ext (f₁.comm i i₁ j j₁ hij h₁ h₂ hj x.1) (f₂.comm i i₁ j j₁ hij h₁ h₂ hj x.2)

/-- The direct sum of chain maps is componentwise (tex 4176–4184).
Kind: PROVED (definitional). -/
theorem prodGHom_f_apply {X₁ Y₁ X₂ Y₂ : GCx S} (f₁ : GHom X₁ Y₁) (f₂ : GHom X₂ Y₂) (n : ℤ)
    (x₁ : X₁.X n) (x₂ : X₂.X n) :
    (prodGHom f₁ f₂).f n n rfl ((x₁, x₂) : X₁.X n × X₂.X n) = (f₁.f n n rfl x₁, f₂.f n n rfl x₂) :=
  rfl

/-- **The direct sum of two normalized graded deformation retracts** (tex 4176–4184, 5398–5424):
retracts `R₁` of `X₁` onto `Y₁` and `R₂` of `X₂` onto `Y₂` give the retract of `X₁ ⊕ X₂` onto
`Y₁ ⊕ Y₂` whose inclusion, projection and homotopy are componentwise. Kind: definition (PROVED
identities). -/
def GRetract.prodR {X₁ Y₁ X₂ Y₂ : GCx S} (R₁ : GRetract X₁ Y₁) (R₂ : GRetract X₂ Y₂) :
    GRetract (prodGCx X₁ X₂) (prodGCx Y₁ Y₂) where
  i := prodGHom R₁.i R₂.i
  p := prodGHom R₁.p R₂.p
  h a b hab := (R₁.h a b hab).prodMap (R₂.h a b hab)
  p_i n y := Prod.ext (R₁.p_i n y.1) (R₂.p_i n y.2)
  homotopy n x := Prod.ext (R₁.homotopy n x.1) (R₂.homotopy n x.2)
  h_h a b c hab hbc x := Prod.ext (R₁.h_h a b c hab hbc x.1) (R₂.h_h a b c hab hbc x.2)
  h_i a b hab y := Prod.ext (R₁.h_i a b hab y.1) (R₂.h_i a b hab y.2)
  p_h a b hab x := Prod.ext (R₁.p_h a b hab x.1) (R₂.p_h a b hab x.2)

/-- Complements of submodules give complements of their products (tex 4176–4184).
Kind: PROVED. -/
theorem isCompl_submodule_prod {M₁ M₂ : Type*} [AddCommGroup M₁] [Module S M₁]
    [AddCommGroup M₂] [Module S M₂] {p₁ q₁ : Submodule S M₁} {p₂ q₂ : Submodule S M₂}
    (h₁ : IsCompl p₁ q₁) (h₂ : IsCompl p₂ q₂) : IsCompl (p₁.prod p₂) (q₁.prod q₂) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, h₁.inf_eq_bot, h₂.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, h₁.sup_eq_top, h₂.sup_eq_top, Submodule.prod_top]

variable {A₁ B₁ A₂ B₂ : GCx S} (E₁ : SplitInclusion A₁ B₁) (E₂ : SplitInclusion A₂ B₂)

/-- **The direct sum of two split inclusions** (tex 4176–4184, 5398–5424): the inclusion
`i₁ ⊕ i₂ : A₁ ⊕ A₂ → B₁ ⊕ B₂` with complements `Q₁ⁿ × Q₂ⁿ`. Kind: definition (PROVED
identities). -/
def prodSplit : SplitInclusion (prodGCx A₁ A₂) (prodGCx B₁ B₂) where
  i := prodGHom E₁.i E₂.i
  inj n := (E₁.inj n).prodMap (E₂.inj n)
  Qc n := (E₁.Qc n).prod (E₂.Qc n)
  compl n := by
    have h := isCompl_submodule_prod (E₁.compl n) (E₂.compl n)
    rwa [← LinearMap.range_prodMap] at h

/-- The quotient coordinate of a decomposition: if `x = i u + w` with `w ∈ Qⁿ`, then
`coordQ x = w` (tex 5398–5424). Kind: PROVED. -/
theorem coordQ_eq_of_add {CP CR : GCx S} (E : SplitInclusion CP CR) (n : ℤ) (x : CR.X n)
    (u : CP.X n) (w : E.Qc n) (h : E.i.f n n rfl u + (w : CR.X n) = x) : E.coordQ n x = w := by
  subst h
  rw [map_add, E.coordQ_i, E.coordQ_Q, zero_add]

/-- **The quotient coordinate of the direct sum is componentwise** (tex 4176–4184, 5398–5424).
Kind: PROVED. -/
theorem prodSplit_coordQ (n : ℤ) (x : (prodGCx B₁ B₂).X n) :
    (((prodSplit E₁ E₂).coordQ n x : (prodSplit E₁ E₂).Qc n) : (prodGCx B₁ B₂).X n) =
      ((E₁.coordQ n x.1 : B₁.X n), (E₂.coordQ n x.2 : B₂.X n)) :=
  congrArg Subtype.val (coordQ_eq_of_add (prodSplit E₁ E₂) n x
    ((E₁.coordP n x.1, E₂.coordP n x.2) : A₁.X n × A₂.X n)
    ⟨((E₁.coordQ n x.1 : B₁.X n), (E₂.coordQ n x.2 : B₂.X n)),
      Submodule.mem_prod.2 ⟨(E₁.coordQ n x.1).2, (E₂.coordQ n x.2).2⟩⟩
    (Prod.ext (E₁.decompose n x.1) (E₂.decompose n x.2)))

/-- **The quotient differential of the direct sum is componentwise** (tex 4176–4184,
5398–5424): `d_Q (q₁, q₂) = (d_{Q₁} q₁, d_{Q₂} q₂)`. Kind: PROVED. -/
theorem prodSplit_dQ (a b : ℤ) (h : a + 1 = b) (z : (prodSplit E₁ E₂).Qc a) :
    (((prodSplit E₁ E₂).dQ a b h z : (prodSplit E₁ E₂).Qc b) : (prodGCx B₁ B₂).X b) =
      ((E₁.dQ a b h ⟨z.1.1, (Submodule.mem_prod.1 z.2).1⟩ : B₁.X b),
        (E₂.dQ a b h ⟨z.1.2, (Submodule.mem_prod.1 z.2).2⟩ : B₂.X b)) :=
  prodSplit_coordQ E₁ E₂ b _

/-- **The quotient complex of the direct sum is the direct sum of the quotient complexes**,
degreewise (tex 4176–4184, 5398–5424): `Q₁ⁿ × Q₂ⁿ ≃ Q₁ⁿ ⊕ Q₂ⁿ`. Kind: definition. -/
def prodSplit_quotEquiv (n : ℤ) :
    (prodSplit E₁ E₂).quotientCx.X n ≃ₗ[S] (prodGCx E₁.quotientCx E₂.quotientCx).X n where
  toFun z := (⟨z.1.1, (Submodule.mem_prod.1 z.2).1⟩, ⟨z.1.2, (Submodule.mem_prod.1 z.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), Submodule.mem_prod.2 ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The degreewise equivalence commutes with the differentials** (tex 4176–4184, 5398–5424).
Kind: PROVED. -/
theorem prodSplit_quotEquiv_d (a b : ℤ) (h : a + 1 = b) (z : (prodSplit E₁ E₂).quotientCx.X a) :
    (prodGCx E₁.quotientCx E₂.quotientCx).d a b h (prodSplit_quotEquiv E₁ E₂ a z) =
      prodSplit_quotEquiv E₁ E₂ b ((prodSplit E₁ E₂).quotientCx.d a b h z) := by
  have e := prodSplit_dQ E₁ E₂ a b h z
  exact Prod.ext (Subtype.ext (congrArg Prod.fst e).symm) (Subtype.ext (congrArg Prod.snd e).symm)

/-- **A retract of the quotient of the direct sum from retracts of the two quotients**
(tex 4176–4184, 5398–5424): retracts `R_{Q₁}` of `Q₁` onto `Y₁` and `R_{Q₂}` of `Q₂` onto `Y₂`
give a retract of the quotient complex of `prodSplit E₁ E₂` onto `Y₁ ⊕ Y₂`, the direct sum
`GRetract.prodR` with its source transported along `prodSplit_quotEquiv` (`GRetract.ofEquiv`).
Kind: definition (PROVED identities). -/
def prodSplitRetract {Y₁ Y₂ : GCx S} (RQ₁ : GRetract E₁.quotientCx Y₁)
    (RQ₂ : GRetract E₂.quotientCx Y₂) :
    GRetract (prodSplit E₁ E₂).quotientCx (prodGCx Y₁ Y₂) :=
  (GRetract.prodR RQ₁ RQ₂).ofEquiv (fun n => (prodSplit_quotEquiv E₁ E₂ n).symm)
    (fun a b h x => (equiv_symm_d (prodSplit_quotEquiv E₁ E₂) (prodSplit_quotEquiv_d E₁ E₂)
      a b h x).symm)

section TwoSing

open ZInQ.Manuscript.RC.Local (singCx twoSingCx)

variable (Fr : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)

/-- **The two singular blocks are the direct sum of the singular blocks at `w` and `w̄`**
(tex 4176–4184, 3470–3487): `twoSingCx Fr q z z⁻¹ = [M --zFr−q--> M] ⊕ [M --z⁻¹Fr−q--> M]`.
Kind: PROVED (definitional). -/
theorem twoSingCx_eq_prodGCx :
    twoSingCx Fr q z zi =
      prodGCx (singCx (Matrix.toLin' (z • Fr)) q) (singCx (Matrix.toLin' (zi • Fr)) q) :=
  rfl

/-- **The retract of the quotient onto the two singular blocks from the two places**
(tex 4176–4184, 5398–5424): local retracts of the quotients at `w` and `w̄` onto
`[M --zFr−q--> M]` and `[M --z⁻¹Fr−q--> M]` give a retract of the quotient complex of
`prodSplit E₁ E₂` onto `twoSingCx Fr q z z⁻¹` (the shape of the input `R_Q` of
`SupportTriangle.ofTwoSing`, for the split inclusion `prodSplit E₁ E₂`). Kind: definition. -/
def twoSingRetract (RQ₁ : GRetract E₁.quotientCx (singCx (Matrix.toLin' (z • Fr)) q))
    (RQ₂ : GRetract E₂.quotientCx (singCx (Matrix.toLin' (zi • Fr)) q)) :
    GRetract (prodSplit E₁ E₂).quotientCx (twoSingCx Fr q z zi) :=
  prodSplitRetract E₁ E₂ RQ₁ RQ₂

end TwoSing

end Products

/-! ### Unification with lane RC31 -/

section Unify

open Module ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.Local (triSplitInclusion)

variable {S : Type} [CommRing S] (X Q : GCx S) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[S] X.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)

/-- **The two split inclusions of a triangular extension agree** (tex 5398–5424): `triIncl` of
this lane is lane RC31's `triSplitInclusion` (inclusion `x ↦ (x, 0)`, complement `0 ⊕ Q`).
Kind: PROVED (definitional). -/
theorem triIncl_eq_triSplitInclusion : triIncl X Q δ hδ = triSplitInclusion δ hδ :=
  rfl

/-- **`triQEquiv` of this lane is the inverse of lane RC31's** (tex 5398–5424): both are
`q ↦ (0, q)` and its inverse. Kind: PROVED (definitional). -/
theorem triQEquiv_eq_symm (n : ℤ) :
    triQEquiv X Q δ hδ n = (ZInQ.Manuscript.RC.Local.triQEquiv δ hδ n).symm :=
  rfl

/-- The transported basis `triQBasis` is the basis carried by the inverse of lane RC31's
`triQEquiv` (tex 5398–5424). Kind: PROVED (definitional). -/
theorem triQBasis_eq_map_symm {N : Type} (n : ℤ) (b : Basis N S (Q.X n)) :
    triQBasis X Q δ hδ n b = b.map (ZInQ.Manuscript.RC.Local.triQEquiv δ hδ n).symm :=
  rfl

end Unify

section UnifyTwo

open Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Local (twoSingCx twoPieceCoord1 twoPieceCoord2 triSplitInclusion)

variable {F : Type} [Field F] (Fr : Matrix (Fin 2) (Fin 2) F) (q : ℕ) (z zi : F)
  (D : BlockComplex F)
  (δ : ∀ a b : ℤ, a + 1 = b → (twoSingCx Fr q z zi).X a →ₗ[F] D.toGCx.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (x : (twoSingCx Fr q z zi).X a),
    D.toGCx.d b c hbc (δ a b hab x) + δ b c hbc ((twoSingCx Fr q z zi).d a b hab x) = 0)

/-- **The degree-one bases agree** (tex 4176–4184, 5398–5424): the basis of `0 ⊕ Q¹`
transported from the two-place basis `twoSingB1` is lane RC31's
`Basis.ofEquivFun (twoPieceCoord1 …)`. Kind: PROVED (definitional). -/
theorem triQBasis_twoSing_one :
    triQBasis D.toGCx (twoSingCx Fr q z zi) δ hδ 1 (twoSingB1 Fr q z zi) =
      Basis.ofEquivFun (twoPieceCoord1 Fr q z zi D δ hδ) :=
  rfl

/-- **The degree-two bases agree** (tex 4176–4184, 5398–5424): the basis of `0 ⊕ Q²`
transported from `twoSingB2` is lane RC31's `Basis.ofEquivFun (twoPieceCoord2 …)`.
Kind: PROVED (definitional). -/
theorem triQBasis_twoSing_two :
    triQBasis D.toGCx (twoSingCx Fr q z zi) δ hδ 2 (twoSingB2 Fr q z zi) =
      Basis.ofEquivFun (twoPieceCoord2 Fr q z zi D δ hδ) :=
  rfl

/-- **Lane RC31's `twoPiece_hBe` from this lane's matrices** (tex 4176–4184, 5398–5424), over
a field: the new block of lane RC31's `fullPreOfSplit` of the triangular split is the two-place
block, by `toMatrix_triIncl_dQ` (the quotient differential is `d_{Q'}`) and `toMatrix_twoSing`
(`d_{Q'}` is `twoPlaceBlock` in the two-place bases). Kind: PROVED. -/
theorem twoPiece_hBe_of_toMatrix :
    ∃ e : (fullPreOfSplit D (triSplitInclusion δ hδ)
        (Basis.ofEquivFun (twoPieceCoord1 Fr q z zi D δ hδ))
        (Basis.ofEquivFun (twoPieceCoord2 Fr q z zi D δ hδ))).N ≃ Fin 2 ⊕ Fin 2,
      (fullPreOfSplit D (triSplitInclusion δ hδ)
        (Basis.ofEquivFun (twoPieceCoord1 Fr q z zi D δ hδ))
        (Basis.ofEquivFun (twoPieceCoord2 Fr q z zi D δ hδ))).B =
        (twoPlaceBlock Fr (q : F) z zi).submatrix e e :=
  ⟨Equiv.refl _, (toMatrix_triIncl_dQ D.toGCx (twoSingCx Fr q z zi) δ hδ (twoSingB1 Fr q z zi)
    (twoSingB2 Fr q z zi)).trans
      ((toMatrix_twoSing Fr q z zi).trans (Matrix.submatrix_id_id _).symm)⟩

end UnifyTwo

section UnifyModel

open Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Local (twoSingCx twoPieceCoord1 twoPieceCoord2 triSplitInclusion
  twoPiece_hBe)

variable {F : Type} [Field F] {Fr : Matrix (Fin 2) (Fin 2) F} {q : ℕ} {z zi : F}
  {CP CR : GCx F} (E : SplitInclusion CP CR) {D : BlockComplex F} (R : GRetract CP D.toGCx)
  (RQ : GRetract E.quotientCx (twoSingCx Fr q z zi))

/-- **The full-condition model with the two-place bases is lane RC31's** (tex 4176–4184,
5398–5424): `relModel E R R_Q twoSingB1 twoSingB2` is lane RC31's `fullPreOfSplit` of
`triSplitInclusion` with the bases `Basis.ofEquivFun (twoPieceCoord1 …)`,
`Basis.ofEquivFun (twoPieceCoord2 …)` (`triIncl_eq_triSplitInclusion`, `triQBasis_twoSing_one`,
`triQBasis_twoSing_two`). Kind: PROVED (definitional). -/
theorem relModel_twoSing_eq :
    relModel E R RQ (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi) =
      fullPreOfSplit D
        (triSplitInclusion (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq))
        (Basis.ofEquivFun (twoPieceCoord1 Fr q z zi D (R.triδ₂ RQ E.offDiag)
          (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)))
        (Basis.ofEquivFun (twoPieceCoord2 Fr q z zi D (R.triδ₂ RQ E.offDiag)
          (R.triδ₂_sq RQ E.offDiag E.offDiag_sq))) :=
  rfl

/-- **The new block of the model with the two-place bases** (tex 4176–4184, 5398–5424):
`B = twoPlaceBlock Fr q z z⁻¹` (`relModel_B` and `toMatrix_twoSing`). Kind: PROVED. -/
theorem relModel_twoSing_B :
    (relModel E R RQ (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi)).B =
      twoPlaceBlock Fr (q : F) z zi :=
  (relModel_B E R RQ _ _).trans (toMatrix_twoSing Fr q z zi)

/-- **The block hypothesis `hBe` of the model from lane RC31's `twoPiece_hBe`** (tex 4176–4184,
5398–5424): one line from `relModel_twoSing_eq`. Kind: PROVED. -/
theorem relModel_twoSing_hBe :
    ∃ e : (relModel E R RQ (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi)).N ≃ Fin 2 ⊕ Fin 2,
      (relModel E R RQ (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi)).B =
        (twoPlaceBlock Fr (q : F) z zi).submatrix e e :=
  relModel_twoSing_eq E R RQ ▸ twoPiece_hBe Fr q z zi D (R.triδ₂ RQ E.offDiag)
    (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)

end UnifyModel

end ZInQ.Manuscript.RC.Wiring
