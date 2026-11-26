import ZInQKernel.Contrib.OneProof.AcrisImagePhi
import ZInQKernel.Contrib.OneProof.AcrisImageNormal
import ZInQKernel.Contrib.OneProof.AcrisImageSep

/-! # Fontaine's `A_cris` injects into `B_dR^+` with image `AcrisOf`

Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II: §2.3.3 (p. 78)
identifies `A_cris` with the `p`-adic separated completion of `W(R)[ξ^m/m! : m ≥ 1] ⊆ W(R)[1/p]`
(the tree's definition of `A_cris`);
§4.1.2 (p. 83) states that every element is a series `Σ a_n ξ^n/n!` with `a_n → 0`
`p`-adically and that the natural map `A_cris → B_dR^+` is injective. Brinon–Conrad's CMI
notes (preliminary version, June 24, 2009), p. 129, note that the map is `G_K`-equivariant, omit
the proof of injectivity, and print the same image. This file proves these statements for the
tree's objects (`fontaineCrystallineImage_proof`), and for the tree's abstract
`PanBergerSplit.Acris`, including equivariance for its Galois action (`acris_image`).

The map to `B_dR^+ = lim W(R)[1/p]/(ker θ)^m` is built level by level: the value of `x` at
level `m` is the image of a lift of `x` modulo `p^k`, up to the image of `p^k D`
(`IsVal`); it exists because `x` is the limit of a restricted series (`phi_surjective`) and is
unique because `D` is `p`-adically separated modulo `(ker θ)^m` (`mem_ith_pow_of_forall`).
-/

noncomputable section

namespace HDec.PkgI4.AcrisImage

open BergerBst FontaineSt BmaxOne PowerSeries Ideal
open PanBergerSplit (Ainf AinfP theta)
open FontaineComparison (finiteDividedPowers CrystallineCompletion FontaineCrystallineImage)

variable {p : ℕ} [Fact p.Prime] {w : Ainf p}

/-! ## §1. Values modulo `(ker θ)^m` -/

/-- `z ∈ W(R)[1/p]` represents the value of `x` modulo `(ker θ)^m`: for every `k`, it is a lift
of `x` modulo `p^k`, up to `p^k D + (ker θ)^m`. -/
def IsVal (m : ℕ) (x : CrystallineCompletion p w) (z : AinfP p) : Prop :=
  ∀ k, ∃ d : finiteDividedPowers p w,
    AdicCompletion.evalₐ (pIdeal w) k x = Ideal.Quotient.mk _ d ∧
      ∃ e ∈ finiteDividedPowers p w, z - (d : AinfP p) - (p : AinfP p) ^ k * e ∈ Ith p ^ m

/-- Two representatives in `D` agree modulo `(ker θ)^m` (`D` is `p`-adically separated
modulo `(ker θ)^m`). -/
theorem IsVal.sub_mem (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {m : ℕ} {x : CrystallineCompletion p w} {z z' : AinfP p}
    (hz : z ∈ finiteDividedPowers p w) (hz' : z' ∈ finiteDividedPowers p w)
    (h : IsVal m x z) (h' : IsVal m x z') : z - z' ∈ Ith p ^ m := by
  refine mem_ith_pow_of_forall hgen (Subring.sub_mem _ hz hz') m fun k => ?_
  obtain ⟨d, hd, e, he, hz1⟩ := h k
  obtain ⟨d', hd', e', he', hz2⟩ := h' k
  have hdd : d - d' ∈ pIdeal w ^ k := by
    rw [← Ideal.Quotient.eq, ← hd, ← hd']
  obtain ⟨e'', he'', hde⟩ := (mem_pIdeal_pow_iff w k (d - d')).mp hdd
  refine ⟨e'' + e - e', Subring.sub_mem _ (Subring.add_mem _ he'' he) he', ?_⟩
  have hc : ((d - d' : finiteDividedPowers p w) : AinfP p) = (d : AinfP p) - d' := rfl
  rw [hc] at hde
  have key : z - z' - (p : AinfP p) ^ k * (e'' + e - e') =
      (z - d - (p : AinfP p) ^ k * e) - (z' - d' - (p : AinfP p) ^ k * e') +
        ((d : AinfP p) - d' - (p : AinfP p) ^ k * e'') := by
    ring
  rw [key, hde, sub_self, add_zero]
  exact Ideal.sub_mem _ hz1 hz2

theorem isVal_phi (hw : theta p w = 0) {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (m : ℕ) :
    IsVal m (phi w hf) (psum w f m) := by
  intro k
  refine ⟨psumD w f (bnd hf k), evalₐ_phi w hf k _ le_rfl, ?_⟩
  obtain ⟨g, hg⟩ := exists_psum_eq_pow_mul w (k := k) (f := f)
    (Finset.Ico (bnd hf k) (max m (bnd hf k)))
    fun n hn => bnd_spec hf k n (Finset.mem_Ico.mp hn).1
  refine ⟨∑ n ∈ Finset.Ico (bnd hf k) (max m (bnd hf k)),
      algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n g) * gam w n,
    sum_gam_mem w _ _, ?_⟩
  rw [← hg, ← psum_sub_psum w f (le_max_right m (bnd hf k))]
  have hc : (psumD w f (bnd hf k) : AinfP p) = psum w f (bnd hf k) := rfl
  have key : psum w f m - (psumD w f (bnd hf k) : AinfP p) -
      (psum w f (max m (bnd hf k)) - psum w f (bnd hf k)) =
      -(psum w f (max m (bnd hf k)) - psum w f m) := by
    rw [hc]
    ring
  rw [key]
  exact neg_mem (psum_sub_psum_mem w hw f (le_max_left m _))

theorem isVal_add {m : ℕ} {x y : CrystallineCompletion p w} {z z' : AinfP p}
    (h : IsVal m x z) (h' : IsVal m y z') : IsVal m (x + y) (z + z') := by
  intro k
  obtain ⟨d, hd, e, he, hz1⟩ := h k
  obtain ⟨d', hd', e', he', hz2⟩ := h' k
  refine ⟨d + d', by rw [map_add, hd, hd', map_add], e + e', Subring.add_mem _ he he', ?_⟩
  have hc : ((d + d' : finiteDividedPowers p w) : AinfP p) = (d : AinfP p) + d' := rfl
  have key : z + z' - ((d + d' : finiteDividedPowers p w) : AinfP p) -
      (p : AinfP p) ^ k * (e + e') =
      (z - d - (p : AinfP p) ^ k * e) + (z' - d' - (p : AinfP p) ^ k * e') := by
    rw [hc]
    ring
  rw [key]
  exact Ideal.add_mem _ hz1 hz2

theorem isVal_mul {m : ℕ} {x y : CrystallineCompletion p w} {z z' : AinfP p}
    (h : IsVal m x z) (h' : IsVal m y z') (hz' : z' ∈ finiteDividedPowers p w) :
    IsVal m (x * y) (z * z') := by
  intro k
  obtain ⟨d, hd, e, he, hz1⟩ := h k
  obtain ⟨d', hd', e', he', hz2⟩ := h' k
  refine ⟨d * d', by rw [map_mul, hd, hd', map_mul], e * z' + d * e',
    Subring.add_mem _ (Subring.mul_mem _ he hz') (Subring.mul_mem _ d.2 he'), ?_⟩
  have hc : ((d * d' : finiteDividedPowers p w) : AinfP p) = (d : AinfP p) * d' := rfl
  have key : z * z' - ((d * d' : finiteDividedPowers p w) : AinfP p) -
      (p : AinfP p) ^ k * (e * z' + d * e') =
      (z - d - (p : AinfP p) ^ k * e) * z' + (d : AinfP p) * (z' - d' - (p : AinfP p) ^ k * e') := by
    rw [hc]
    ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz1) (Ideal.mul_mem_left _ _ hz2)

theorem isVal_one (m : ℕ) : IsVal m (1 : CrystallineCompletion p w) 1 := by
  intro k
  refine ⟨1, by rw [map_one, map_one], 0, Subring.zero_mem _, ?_⟩
  have key : (1 : AinfP p) - ((1 : finiteDividedPowers p w) : AinfP p) -
      (p : AinfP p) ^ k * 0 = 0 := by
    rw [OneMemClass.coe_one]
    ring
  rw [key]
  exact Ideal.zero_mem _

theorem isVal_zero (m : ℕ) : IsVal m (0 : CrystallineCompletion p w) 0 := by
  intro k
  refine ⟨0, by rw [map_zero, map_zero], 0, Subring.zero_mem _, ?_⟩
  have key : (0 : AinfP p) - ((0 : finiteDividedPowers p w) : AinfP p) -
      (p : AinfP p) ^ k * 0 = 0 := by
    rw [ZeroMemClass.coe_zero]
    ring
  rw [key]
  exact Ideal.zero_mem _

/-! ## §2. The ring map `A_cris → B_dR^+` -/

theorem theta_of_gen (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    theta p w = 0 := by
  change w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [hgen]
  exact mem_span_singleton_self w

variable (w)

/-- A restricted series representing `x` (`phi_surjective`). -/
def rep (x : CrystallineCompletion p w) : (Ainf p)⟦X⟧ :=
  Classical.choose (phi_surjective w x)

theorem rep_mem (x : CrystallineCompletion p w) : rep w x ∈ restricted p :=
  (Classical.choose_spec (phi_surjective w x)).fst

theorem phi_rep (x : CrystallineCompletion p w) : phi w (rep_mem w x) = x :=
  (Classical.choose_spec (phi_surjective w x)).snd

/-- The value of `x` in `W(R)[1/p]/(ker θ)^m`. -/
def valm (m : ℕ) (x : CrystallineCompletion p w) : AinfP p ⧸ Ith p ^ m :=
  Ideal.Quotient.mk _ (psum w (rep w x) m)

variable {w}

theorem isVal_rep (hw : theta p w = 0) (m : ℕ) (x : CrystallineCompletion p w) :
    IsVal m x (psum w (rep w x) m) := by
  have h := isVal_phi hw (rep_mem w x) m
  rwa [phi_rep] at h

theorem valm_eq_of_isVal (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {m : ℕ} {x : CrystallineCompletion p w} {z : AinfP p} (hz : z ∈ finiteDividedPowers p w)
    (h : IsVal m x z) : valm w m x = Ideal.Quotient.mk _ z :=
  Ideal.Quotient.eq.mpr ((isVal_rep (theta_of_gen hgen) m x).sub_mem hgen (psum_mem w _ m) hz h)

/-- The value at level `m`, as a ring map. -/
def valRingHom (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (m : ℕ) :
    CrystallineCompletion p w →+* AinfP p ⧸ Ith p ^ m where
  toFun := valm w m
  map_one' := by
    rw [valm_eq_of_isVal hgen (Subring.one_mem _) (isVal_one m), map_one]
  map_mul' x y := by
    rw [valm_eq_of_isVal hgen (Subring.mul_mem _ (psum_mem w _ m) (psum_mem w _ m))
      (isVal_mul (isVal_rep (theta_of_gen hgen) m x) (isVal_rep (theta_of_gen hgen) m y)
        (psum_mem w _ m)), map_mul]
    rfl
  map_zero' := by
    rw [valm_eq_of_isVal hgen (Subring.zero_mem _) (isVal_zero m), map_zero]
  map_add' x y := by
    rw [valm_eq_of_isVal hgen (Subring.add_mem _ (psum_mem w _ m) (psum_mem w _ m))
      (isVal_add (isVal_rep (theta_of_gen hgen) m x) (isVal_rep (theta_of_gen hgen) m y)),
      map_add]
    rfl

theorem valRingHom_apply (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) (x : CrystallineCompletion p w) : valRingHom hgen m x = valm w m x := rfl

theorem valRingHom_compat (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ith p) hle).comp (valRingHom hgen n) = valRingHom hgen m := by
  ext x
  rw [RingHom.comp_apply, valRingHom_apply, valRingHom_apply, valm, valm]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact psum_sub_psum_mem w (theta_of_gen hgen) _ hle

/-- **The natural map `A_cris → B_dR^+`.** -/
def toBdRPlus (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    CrystallineCompletion p w →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  AdicCompletion.liftRingHom (Ith p) (valRingHom hgen) (valRingHom_compat hgen)

theorem evB_toBdRPlus (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) (x : CrystallineCompletion p w) :
    evB p m (toBdRPlus hgen x) = valm w m x :=
  AdicCompletion.evalₐ_liftRingHom (Ith p) (valRingHom hgen) (valRingHom_compat hgen) m x

/-- On the element given by a restricted series, the map is the series evaluated in `B_dR^+`. -/
theorem toBdRPlus_phi (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    toBdRPlus hgen (phi w hf) =
      evalB p (algebraMap_mem_ith p (theta_of_gen hgen)) (dpSeries p f) := by
  refine ext_evB p fun m => ?_
  rw [evB_toBdRPlus, evB_evalB_dpSeries w (theta_of_gen hgen)]
  exact valm_eq_of_isVal hgen (psum_mem w f m) (isVal_phi (theta_of_gen hgen) hf m)

/-- On `D` itself, the map is the inclusion `D ⊆ W(R)[1/p] → B_dR^+`. -/
theorem toBdRPlus_algebraMap (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (x : finiteDividedPowers p w) :
    toBdRPlus hgen (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
      (show BDeRhamPlus 𝓞_ℂ_[p] p from
        algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (x : AinfP p)) := by
  refine ext_evB p fun m => ?_
  rw [evB_toBdRPlus]
  have hv : IsVal m (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x)
      (x : AinfP p) := by
    intro k
    refine ⟨x, ?_, 0, Subring.zero_mem _, ?_⟩
    · rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of]
    · rw [sub_self, mul_zero, sub_zero]
      exact Ideal.zero_mem _
  rw [valm_eq_of_isVal hgen x.2 hv]
  change _ = AdicCompletion.evalₐ (Ith p) m
    (algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (x : AinfP p))
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]

/-! ## §3. Image and injectivity -/

theorem range_toBdRPlus (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    Set.range (toBdRPlus hgen) = AcrisOf p w (theta_of_gen hgen) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [← phi_rep w x, toBdRPlus_phi]
    exact ⟨rep w x, rep_mem w x, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨phi w hf, toBdRPlus_phi hgen hf⟩

theorem toBdRPlus_eq_zero
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {x : CrystallineCompletion p w} (hx : toBdRPlus hgen x = 0) : x = 0 := by
  obtain ⟨g, hg, hgn, hfg⟩ := exists_normalized hgen (rep_mem w x)
  have hphi : phi w (rep_mem w x) = phi w hg := phi_eq_of_forall w _ _ hfg
  have h0 : ∀ m, psum w g m ∈ Ith p ^ m := by
    intro m
    have h1 := congrArg (evB p m) hx
    rw [← phi_rep w x, hphi, toBdRPlus_phi, evB_evalB_dpSeries w (theta_of_gen hgen),
      RingHom.map_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hg0 : g = 0 := eq_zero_of_normalized hgen hgn h0
  subst hg0
  rw [← phi_rep w x, hphi]
  exact phi_zero w

theorem toBdRPlus_injective
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    Function.Injective (toBdRPlus hgen) := by
  intro x y hxy
  have h : toBdRPlus hgen (x - y) = 0 := by
    rw [RingHom.map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (toBdRPlus_eq_zero hgen h)

/-- **Fontaine II, §§2.3.3 and 4.1.2 for the tree's objects.** The natural map from the
`p`-adic completion of `W(R)[w^n/n!]` to `B_dR^+` is injective, restricts to the inclusion on
`W(R)[w^n/n!]`, and has image `AcrisOf`. -/
theorem fontaineCrystallineImage_proof : FontaineCrystallineImage := by
  intro ℓ _ w hw hgen
  refine ⟨toBdRPlus hgen, toBdRPlus_injective hgen, toBdRPlus_algebraMap hgen, ?_⟩
  exact range_toBdRPlus hgen

/-! ## §4. Galois equivariance -/

/-- A ring endomorphism of `D` acting as `σ` on `W(R)[1/p]` transports values. -/
theorem isVal_adicMap (σ : GQp p) (g : finiteDividedPowers p w →+* finiteDividedPowers p w)
    (hg : ∀ s, (g s : AinfP p) = PanBergerSplit.locAct p σ s) {m : ℕ}
    {x : CrystallineCompletion p w} {z : AinfP p} (h : IsVal m x z) :
    IsVal m (DR.adicMap (pIdeal w) (pIdeal w) g (DR.span_p_le_comap p g) x)
      (PanBergerSplit.locAct p σ z) := by
  intro k
  obtain ⟨d, hd, e, he, hz⟩ := h k
  refine ⟨g d, ?_, PanBergerSplit.locAct p σ e, ?_, ?_⟩
  · rw [DR.adicMap_evalₐ]
    unfold DR.adicMapAux
    rw [RingHom.comp_apply]
    erw [hd]
    rw [Ideal.quotientMap_mk]
  · rw [← hg ⟨e, he⟩]
    exact (g ⟨e, he⟩).2
  · have key : PanBergerSplit.locAct p σ z - (g d : AinfP p) -
        (p : AinfP p) ^ k * PanBergerSplit.locAct p σ e =
        PanBergerSplit.locAct p σ (z - d - (p : AinfP p) ^ k * e) := by
      rw [hg d, map_sub, map_sub, map_mul, map_pow, map_natCast]
    rw [key]
    exact DR.pow_le_comap (Ith p) (Ith p) (PanBergerSplit.locAct p σ)
      (fun _ hy => BergerBst.locAct_mem p σ hy) m hz

/-- **Equivariance**: the map `A_cris → B_dR^+` intertwines the action of `σ` on the completion
(induced by an endomorphism of `D` acting as `σ`) with `σ` on `B_dR^+`. -/
theorem toBdRPlus_adicMap (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : GQp p) (g : finiteDividedPowers p w →+* finiteDividedPowers p w)
    (hg : ∀ s, (g s : AinfP p) = PanBergerSplit.locAct p σ s) (x : CrystallineCompletion p w) :
    toBdRPlus hgen (DR.adicMap (pIdeal w) (pIdeal w) g (DR.span_p_le_comap p g) x) =
      DR.bdrPlusMap p (oAct p σ) (toBdRPlus hgen x) := by
  refine ext_evB p fun m => ?_
  rw [evB_toBdRPlus]
  have hz : PanBergerSplit.locAct p σ (psum w (rep w x) m) ∈ finiteDividedPowers p w := by
    rw [← hg ⟨_, psum_mem w _ m⟩]
    exact (g ⟨_, psum_mem w _ m⟩).2
  rw [valm_eq_of_isVal hgen hz (isVal_adicMap σ g hg (isVal_rep (theta_of_gen hgen) m x))]
  have h2 := DR.adicMap_evalₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) (Ith p)
    (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ)) m (toBdRPlus hgen x)
  refine Eq.trans ?_ h2.symm
  have h3 : AdicCompletion.evalₐ (Ith p) m (toBdRPlus hgen x) = valm w m x :=
    evB_toBdRPlus hgen m x
  change _ = Ideal.quotientMap (Ith p ^ m) (DR.locMap p (oAct p σ))
    (DR.pow_le_comap _ _ _ (DR.ker_le_comap_locMap p (oAct p σ)) m)
    (AdicCompletion.evalₐ (Ith p) m (toBdRPlus hgen x))
  rw [h3, valm, Ideal.quotientMap_mk]
  rfl

/-! ## §5. The tree's abstract `A_cris` -/

/-- The tree's `A_cris^0` (generated by the divided powers of every element of `ker θ`) is
`W(R)[ξ^n/n!]`. -/
theorem acris0_eq : PanBergerSplit.Acris0 p = finiteDividedPowers p (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) := by
  apply le_antisymm
  · rw [PanBergerSplit.Acris0, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | ⟨n, x, hx, rfl⟩)
    · exact algebraMap_mem_fdp _ a
    · have hk : x ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hx
      rw [_root_.ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, mem_span_singleton'] at hk
      obtain ⟨c, rfl⟩ := hk
      have : PanBergerSplit.dpow p n (c * _root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) =
          algebraMap (Ainf p) (AinfP p) (c ^ n) * gam (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) n := by
        rw [PanBergerSplit.dpow, gam, map_mul, map_pow]
        ring
      rw [this]
      exact Subring.mul_mem _ (algebraMap_mem_fdp _ _) (gam_mem _ n)
  · rw [finiteDividedPowers, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | ⟨n, rfl⟩)
    · exact PanBergerSplit.algebraMap_mem p a
    · have h := PanBergerSplit.dpow_mem p (n + 1) (theta_xi p)
      rw [PanBergerSplit.dpow, mul_comm] at h
      exact h

/-- **Fontaine II, §§2.3.3 and 4.1.2 for the tree's abstract `PanBergerSplit.Acris`**: an
injective ring map to `B_dR^+`, the inclusion on `A_cris^0`, with image `AcrisOf` at `ξ`, and
`G_{ℚ_p}`-equivariant for the tree's action `PanBergerSplit.acrisAct` and `σ` on `B_dR^+`. -/
theorem acris_image :
    ∃ j : PanBergerSplit.Acris p →+* BDeRhamPlus 𝓞_ℂ_[p] p, Function.Injective j ∧
      (∀ x : PanBergerSplit.Acris0 p,
        j (algebraMap (PanBergerSplit.Acris0 p) (PanBergerSplit.Acris p) x) =
          (show BDeRhamPlus 𝓞_ℂ_[p] p from
            algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (x : AinfP p))) ∧
      Set.range j = AcrisOf p (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) ∧
      ∀ (σ : GQp p) (x : PanBergerSplit.Acris p),
        j (PanBergerSplit.acrisAct p σ x) = DR.bdrPlusMap p (oAct p σ) (j x) := by
  have key : ∀ (S : Subring (AinfP p)),
      S = finiteDividedPowers p (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) →
      ∀ (act : GQp p → S →+* S),
      (∀ σ s, (act σ s : AinfP p) = PanBergerSplit.locAct p σ s) →
      ∃ j : AdicCompletion (Ideal.span ({(p : S)} : Set S)) S →+* BDeRhamPlus 𝓞_ℂ_[p] p,
        Function.Injective j ∧
        (∀ x : S, j (algebraMap S (AdicCompletion (Ideal.span ({(p : S)} : Set S)) S) x) =
          (show BDeRhamPlus 𝓞_ℂ_[p] p from
            algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (x : AinfP p))) ∧
        Set.range j = AcrisOf p (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) ∧
        ∀ (σ : GQp p) (x : AdicCompletion (Ideal.span ({(p : S)} : Set S)) S),
          j (DR.adicMap _ _ (act σ) (DR.span_p_le_comap p (act σ)) x) =
            DR.bdrPlusMap p (oAct p σ) (j x) := by
    rintro S rfl act hact
    have hgen := _root_.ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p
    exact ⟨toBdRPlus hgen, toBdRPlus_injective hgen, toBdRPlus_algebraMap hgen,
      range_toBdRPlus hgen, fun σ x => toBdRPlus_adicMap hgen σ (act σ) (hact σ) x⟩
  exact key _ acris0_eq (PanBergerSplit.acris0Act p) fun _ _ => rfl

end HDec.PkgI4.AcrisImage
