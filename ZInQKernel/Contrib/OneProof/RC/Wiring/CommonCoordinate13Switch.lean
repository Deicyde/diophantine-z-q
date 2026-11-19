import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Pres
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13SelCond
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Pi
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Chain
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate13Tame

/-!
# The genuine switches and the genuine chain of one presentation

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194), the actual
support comparisons (tex 3489–3498) and the two quotient blocks at an unused split prime
(tex 4176–4184).

For the one presentation of the support complexes (`suppCx T`, `CommonCoordinate13Pres.lean`):

* **`suppSwitch T p : SplitInclusion (suppCx T) (suppCx (insert p T))`**: the switch of the
  conditions at the two places above `p`, a split inclusion of genuine Selmer complexes
  (`selSplitOfCond` of the local switches `presSplit T p`); its inclusion is lane RC26's
  `changeIncl` (`suppSwitch_i`).
* **`suppQuotEquiv`, `suppQuotEquiv_d`**: for `p ∉ T`, the quotient `C_{T ∪ {p}} / C_T` is, as a
  complex, the direct sum of the two local quotients `C^•_cont(G_{K_w}, M) / [W → W]` at the two
  places `w = (p, false)`, `w̄ = (p, true)` above `p` (tex 3489–3498, 4176–4184).
* `suppSwitchRetract`: a retraction of the sum of the two local quotients is a retraction of the
  quotient of the switch; **`exists_suppSwitchRetract`**: one exists onto `twoSingCx Fr q z z⁻¹`
  from the two literature statements `MilneADT_I_2_8` and `IwasawaGenerators`
  (`exists_retract_twoPlaces_milne`), for genuine inflations and Frobenius bases at the two
  places.
* `genuineChainData`: the chain of switches of the presentation along an order of the unused
  primes, with the quotient retractions; its steps are the switches (`chainTri_E`), its later
  steps the next steps of the previous ones (`chainTri_link`), each a `KmStep` from the norm
  identity and the functional relation on cocycles (`chainTri_kmStep`), hence a `TriangleChain`
  (`ChainData.toTriangleChain`) with (4.7) along the chain.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Local (prodGCx twoSingCx IwasawaGenerators)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))
  [DecidableEq (Places K S₀)]

/-- **Composites of identifications of complexes commute with the differentials**
(tex 3489–3498). Kind: PROVED. -/
theorem equiv_trans_d {A : Type} [CommRing A] {X₁ X₂ X₃ : GCx A}
    (e₁ : ∀ n, X₁.X n ≃ₗ[A] X₂.X n) (e₂ : ∀ n, X₂.X n ≃ₗ[A] X₃.X n)
    (h₁ : ∀ a b (h : a + 1 = b) (x : X₁.X a), X₂.d a b h (e₁ a x) = e₁ b (X₁.d a b h x))
    (h₂ : ∀ a b (h : a + 1 = b) (x : X₂.X a), X₃.d a b h (e₂ a x) = e₂ b (X₂.d a b h x))
    (a b : ℤ) (h : a + 1 = b) (x : X₁.X a) :
    X₃.d a b h ((e₁ a).trans (e₂ a) x) = (e₁ b).trans (e₂ b) (X₁.d a b h x) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₂, h₁]

/-- **The switch `C_T ⊂ C_{T ∪ {p}}`** (tex 3489–3498, 4157–4166): the split inclusion of
genuine Selmer complexes from the switches of the local conditions at the two places above `p`.
Kind: definition. -/
def suppSwitch (T : Finset ι) (p : ι) :
    SplitInclusion (suppCx K S₀ S k M Δ place X EU T)
      (suppCx K S₀ S k M Δ place X EU (insert p T)) :=
  selSplitOfCond (presCond K S₀ S k M Δ place X EU T)
    (presCond K S₀ S k M Δ place X EU (insert p T)) (presSplit K S₀ S k M Δ place X EU T p)
    (presSplit_compat K S₀ S k M Δ place X EU T p)

omit [DecidableEq (Places K S₀)] in
/-- The inclusion of the switch is lane RC26's change of conditions (tex 3489–3498).
Kind: PROVED (definitional). -/
theorem suppSwitch_i (T : Finset ι) (p : ι) :
    (suppSwitch K S₀ S k M Δ place X EU T p).i = suppIncl K S₀ S k M Δ place X EU T p :=
  rfl

omit [NumberField K] [DecidableEq ι] [DecidableEq (Places K S₀)] in
/-- The two places above `p` are distinct (tex 4176–4184). Kind: PROVED. -/
theorem inr_ne_inr (p : ι) :
    (Sum.inr (p, false) : Places K S₀ ⊕ (ι × Bool)) ≠ Sum.inr (p, true) := by
  intro h
  simp at h

omit [DecidableEq (Places K S₀)] in
/-- The local quotients away from the two places above `p` vanish, in the form of the
extraction of two components (tex 3489–3498, 4176–4184). Kind: PROVED. -/
theorem suppQuot_sub (T : Finset ι) (p : ι) :
    ∀ (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ), v ≠ .inr (p, false) → v ≠ .inr (p, true) →
      Subsingleton ((presSplit K S₀ S k M Δ place X EU T p v).quotientCx.X n) :=
  fun v n h₁ h₂ => presSplit_quot_subsingleton K S₀ S k M Δ place X EU T p v h₁ h₂ n

/-- The identification of the two switched local quotients with the quotients of the genuine
unramified conditions (tex 3489–3498), degreewise, for `p ∉ T`. Kind: definition. -/
def suppQuotEquivTwo (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (prodGCx (presSplit K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
      (presSplit K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).X n ≃ₗ[k]
      (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).X n :=
  LinearEquiv.prodCongr
    (condSplitQuotEquiv K S k M place X EU (p, false) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) n)
    (condSplitQuotEquiv K S k M place X EU (p, true) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) n)

omit [DecidableEq (Places K S₀)] in
/-- The identification of the two switched local quotients commutes with the differentials
(tex 3489–3498). Kind: PROVED. -/
theorem suppQuotEquivTwo_d (T : Finset ι) (p : ι) (hp : p ∉ T) (a b : ℤ) (h : a + 1 = b)
    (x : (prodGCx (presSplit K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
      (presSplit K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).X a) :
    (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).d a b h
        (suppQuotEquivTwo K S₀ S k M Δ place X EU T p hp a x) =
      suppQuotEquivTwo K S₀ S k M Δ place X EU T p hp b
        ((prodGCx (presSplit K S₀ S k M Δ place X EU T p (.inr (p, false))).quotientCx
          (presSplit K S₀ S k M Δ place X EU T p (.inr (p, true))).quotientCx).d a b h x) :=
  Prod.ext
    (condSplitQuotEquiv_d K S k M place X EU (p, false) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) a b h x.1)
    (condSplitQuotEquiv_d K S k M place X EU (p, true) _ _ _ (decide_eq_false hp)
      (decide_eq_true (Finset.mem_insert_self p T)) a b h x.2)

/-- **The quotient of the switch is the sum of the two local quotients** (tex 3489–3498,
4176–4184), degreewise, for `p ∉ T`: `C_{T ∪ {p}} / C_T ≅ L_w / U_w ⊕ L_w̄ / U_w̄`.
Kind: definition. -/
def suppQuotEquiv (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (suppSwitch K S₀ S k M Δ place X EU T p).quotientCx.X n ≃ₗ[k]
      (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).X n :=
  ((selSplitOfCond_quotEquiv (presCond K S₀ S k M Δ place X EU T)
    (presCond K S₀ S k M Δ place X EU (insert p T)) (presSplit K S₀ S k M Δ place X EU T p)
    (presSplit_compat K S₀ S k M Δ place X EU T p) n).trans
    (piExtract (inr_ne_inr K S₀ p) (suppQuot_sub K S₀ S k M Δ place X EU T p) n)).trans
    (suppQuotEquivTwo K S₀ S k M Δ place X EU T p hp n)

/-- **The identification of the quotient of the switch commutes with the differentials**, so it
is an isomorphism of complexes (tex 3489–3498, 4176–4184). Kind: PROVED. -/
theorem suppQuotEquiv_d (T : Finset ι) (p : ι) (hp : p ∉ T) (a b : ℤ) (h : a + 1 = b)
    (x : (suppSwitch K S₀ S k M Δ place X EU T p).quotientCx.X a) :
    (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx).d a b h
        (suppQuotEquiv K S₀ S k M Δ place X EU T p hp a x) =
      suppQuotEquiv K S₀ S k M Δ place X EU T p hp b
        ((suppSwitch K S₀ S k M Δ place X EU T p).quotientCx.d a b h x) :=
  equiv_trans_d _ _
    (equiv_trans_d _ _
      (selSplitOfCond_quotEquiv_d (presCond K S₀ S k M Δ place X EU T)
        (presCond K S₀ S k M Δ place X EU (insert p T)) (presSplit K S₀ S k M Δ place X EU T p)
        (presSplit_compat K S₀ S k M Δ place X EU T p))
      (piExtract_d (inr_ne_inr K S₀ p) (suppQuot_sub K S₀ S k M Δ place X EU T p)))
    (suppQuotEquivTwo_d K S₀ S k M Δ place X EU T p hp) a b h x

/-- **A retraction of the sum of the two local quotients is a retraction of the quotient of the
switch** (tex 3489–3498, 4176–4184): transport along `suppQuotEquiv`. Kind: definition. -/
def suppSwitchRetract (T : Finset ι) (p : ι) (hp : p ∉ T) {Y : GCx k}
    (R : GRetract (prodGCx (EU (p, false)).quotientCx (EU (p, true)).quotientCx) Y) :
    GRetract (suppSwitch K S₀ S k M Δ place X EU T p).quotientCx Y :=
  R.ofEquiv (fun n => (suppQuotEquiv K S₀ S k M Δ place X EU T p hp n).symm)
    (fun a b h x => (equiv_symm_d (suppQuotEquiv K S₀ S k M Δ place X EU T p hp)
      (suppQuotEquiv_d K S₀ S k M Δ place X EU T p hp) a b h x).symm)

/-- **The quotient retraction of a switch exists, from the two literature statements**
(tex 3470–3481, 4176–4184): for `p ∉ T`, genuine bijective inflations `f_w`, `f_w̄` at the two
places above `p` (the chosen splits `EU` of the genuine inflations), residue cardinality `q`
(odd) at both, and bases in which Frobenius is `z Fr` at `w` and `z⁻¹ Fr` at `w̄`, the quotient
of the switch `C_T ⊂ C_{T ∪ {p}}` retracts onto `twoSingCx Fr q z z⁻¹`, given `MilneADT_I_2_8` and
`IwasawaGenerators`. Kind: PROVED (from the PRINTs). -/
theorem exists_suppSwitchRetract (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators) [Finite M]
    (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (T : Finset ι) (p : ι) (hp : p ∉ T) (q : ℕ)
    (hq : Odd q) (Fr : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    [∀ j, ContinuousSMul (GUr K (place j).1) (X j).V] [∀ j, DiscreteTopology (X j).V]
    [∀ j, Finite (X j).V] (f : ∀ j, (X j).V →ₗ[k] M)
    (hf : ∀ j (g : Gloc K (place j).1) (x : (X j).V),
      f j (resUr K (place j).1 g • x) = locMap K S (place j).1 g • f j x)
    (hbij : ∀ j, Function.Bijective (f j))
    (hqc : ∀ c : Bool, q = Nat.card (𝓞 K ⧸ (place (p, c)).1.asIdeal))
    (hE : ∀ j, (EU j).i = ofCCHom (urToLocal_galois K S (place j) (X j) (f j) (hf j)))
    (b₁ : (X (p, false)).V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K (place (p, false)).1) (X (p, false)) v) =
      Matrix.toLin' (z • Fr) (b₁ v))
    (b₂ : (X (p, true)).V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K (place (p, true)).1) (X (p, true)) v) =
      Matrix.toLin' (zi • Fr) (b₂ v)) :
    Nonempty (GRetract (suppSwitch K S₀ S k M Δ place X EU T p).quotientCx
      (twoSingCx Fr q z zi)) := by
  obtain ⟨R⟩ := exists_retract_twoPlaces_milne h28 hI hexp q hq Fr z zi (place (p, false))
    (X (p, false)) (f (p, false)) (hf (p, false)) (hbij (p, false)) (hqc false) (EU (p, false))
    (hE (p, false)) b₁ hb₁ (place (p, true)) (X (p, true)) (f (p, true)) (hf (p, true))
    (hbij (p, true)) (hqc true) (EU (p, true)) (hE (p, true)) b₂ hb₂
  exact ⟨suppSwitchRetract K S₀ S k M Δ place X EU T p hp R⟩

/-! ### The genuine chain -/

/-- **The data of a chain of switches of the presentation** (tex 4142–4194, 4185–4193):
`ChainData` for the support complexes `suppCx` and the switches `suppSwitch`. Kind: definition. -/
abbrev GenuineChainData (ps : ℕ → ι) : Type :=
  ChainData (suppCx K S₀ S k M Δ place X EU) (suppSwitch K S₀ S k M Δ place X EU) ps

/-- **The genuine chain from the two-place retractions** (tex 4142–4194, 4176–4184): the initial
state at `∅` (a model of `C_∅`, the primitive class and functional), the Frobenius data of the
primes `p_i`, the retractions of the sums of the two local quotients at the places above `p_i`
(from `exists_retract_twoPlaces_milne`), transported to the quotients of the switches, and the
relaxed classes and functionals. Kind: definition. -/
def genuineChainData (ps : ℕ → ι) (hfresh : ∀ i, ps i ∉ chainT ps i)
    (st0 : ChainState (suppCx K S₀ S k M Δ place X EU) ∅)
    (Fr : ℕ → Matrix (Fin 2) (Fin 2) k) (q : ℕ → ℕ) (z zi : ℕ → k)
    (R2 : ∀ i, GRetract (prodGCx (EU (ps i, false)).quotientCx (EU (ps i, true)).quotientCx)
      (twoSingCx (Fr i) (q i) (z i) (zi i)))
    (zR : ∀ i, (suppCx K S₀ S k M Δ place X EU (insert (ps i) (chainT ps i))).X 1)
    (hzR : ∀ i, (suppCx K S₀ S k M Δ place X EU (insert (ps i) (chainT ps i))).d 1 2 rfl
      (zR i) = 0)
    (lamR : ∀ i, (suppCx K S₀ S k M Δ place X EU (insert (ps i) (chainT ps i))).X 2 →ₗ[k] k)
    (hlamR : ∀ i, lamR i ∘ₗ
      (suppCx K S₀ S k M Δ place X EU (insert (ps i) (chainT ps i))).d 1 2 rfl = 0) :
    GenuineChainData K S₀ S k M Δ place X EU ps where
  st0 := st0
  Fr := Fr
  q := q
  z := z
  zi := zi
  RQ i := suppSwitchRetract K S₀ S k M Δ place X EU (chainT ps i) (ps i) (hfresh i) (R2 i)
  zR := zR
  hzR := hzR
  lamR := lamR
  hlamR := hlamR

omit [DecidableEq (Places K S₀)] in
/-- **The steps of the genuine chain are the switches of the presentation** (tex 4185–4193):
step `i` has primitive complex `C_{T_i}`, relaxed complex `C_{T_{i+1}}`, inclusion the switch
at `p_i`. Kind: PROVED (definitional). -/
theorem genuineChain_step (ps : ℕ → ι) (cd : GenuineChainData K S₀ S k M Δ place X EU ps)
    (i : ℕ) :
    (chainTri cd i).CP = suppCx K S₀ S k M Δ place X EU (chainT ps i) ∧
      (chainTri cd i).CR = suppCx K S₀ S k M Δ place X EU (insert (ps i) (chainT ps i)) ∧
      HEq (chainTri cd i).E (suppSwitch K S₀ S k M Δ place X EU (chainT ps i) (ps i)) :=
  ⟨rfl, rfl, HEq.rfl⟩

omit [DecidableEq (Places K S₀)] in
/-- **(4.7) along the genuine chain** (tex 4166–4194, 4222): with the arithmetic inputs of the
steps (`ChainHyps`: the units, the norm identity with its retained boundary, the functional
relation on cocycles), `(∏ l_i) v_n = (∏ σ_i e_i² q_i⁻⁴) v_0`, `v_0` the primitive coordinate
of `C_∅` and `v_n` the relaxed coordinate of `C_{T_n}` in the iterated cone model.
Kind: PROVED. -/
theorem genuineChain_prod_h47 (ps : ℕ → ι) (cd : GenuineChainData K S₀ S k M Δ place X EU ps)
    {n : ℕ} (H : ChainHyps cd n) :
    (∏ i ∈ Finset.range n, quotientFactor (cd.Fr i) (H.qi i) (cd.z i) (cd.zi i)) *
        (cd.toTriangleChain H).v n =
      (∏ i ∈ Finset.range n, pointFactor (H.a i) (cd.z i) (cd.zi i) ^ 2 * H.qi i ^ 4 *
        (((cd.toTriangleChain H).sign i : ℤ) : k)) * (cd.toTriangleChain H).v 0 :=
  cd.prod_h47 H

end ZInQ.Manuscript.RC.Wiring
