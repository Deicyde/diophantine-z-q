import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import ZInQKernel.Contrib.OneProof.NeronDVR

/-!
# nos-converse: the converse of Néron–Ogg–Shafarevich reduced along Serre–Tate's proof

Serre–Tate's proof of (c) ⇒ (a) (Ann. of Math. 88 (1968), §2; UNVERIFIED locator), mapped onto the open fields:

1. a Néron model `𝒩` of `A` over `O` (field `neronSchemeExtensionExists`, only at number fields; over a general
   DVR this is BLR §1.4 Thm 3, `ReductSplit.NeronSchemeModelExistsDVR`, which is not a field);
2. inertia-fixed `m`-torsion is rational over the inertia field `E` (GLUE `InertiaFixedRational`);
3. Raynaud's criterion over the strictly henselian `w ∩ E` (field `raynaudSemistableSH`), Néron models commute with
   strict henselization (field `neronBaseChangeStrictHenselization`), semistability descends
   (`ReductGlue.isSemistable_bcDVR_iff`, proved): `𝒩` is semistable;
4. counting `m`-torsion on the semi-abelian special fibre: the torus part is trivial (GLUE `TorusRankZero`);
5. abelian identity component of the special fibre ⇒ good reduction (LEAF `AbelianReductionGood`).
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction InertiaTrivialOn torsion galAct Pts)
open ReductSplit ReductGlue

namespace NOSConverse

/-! ## §1 Statements -/

/-- **The direction (c) ⇒ (a) of the chain's `r7a`, verbatim** (over `K̄ = AlgebraicClosure K`, as in
`PkgI2.NeronOggShafarevich`). -/
def NOSConverseBar : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite → HasGoodReduction A O

/-- **`NOSConverseBar` at number fields** (the only place the chain uses the converse: LPrefix l. 856,
`PkgI2.goodReduction_of_QM_rational3_of_alg`, `[NumberField K]`). -/
def NOSConverseNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite → HasGoodReduction A O

/-- The identity component of a group scheme `G` over a field `k` is an abelian variety: an open connected
subgroup scheme `U ⊆ G` (necessarily `G⁰`) that is proper over `k` (for `G` smooth, `U` is smooth, so it is a
proper smooth connected group scheme, i.e. an abelian variety). -/
def HasAbelianIdentityComponent {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧ IsProper U.hom

/-- **GLUE `InertiaFixedRational`** (Galois theory of the inertia field; step 2). `K` a field, `O` a DVR,
`w` a valuation ring of `K̄` over `O`, `E = GapSHPair.inertiaField w` (the fixed field of inertia, whose valuation
ring `w ∩ E` is the strict henselization of `O`, `GapSHPair.isSHSep_inertia`). A `K̄`-point of `A[m]`, `m`
invertible in `O`, fixed by every inertia element of `w` is rational over `E`. Proof route (STANDARD): `A[m]` is
étale over `K` (`[m]` étale, fork PR #19), so the point is defined over the finite Galois field `K(A[m])`; it is
fixed by the inertia group of `w ∩ K(A[m])` because the restriction `I_w → I_{w ∩ K(A[m])}` is onto, hence its
coordinates lie in `E` (definition of `E`). -/
def InertiaFixedRational : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), IsUnit (m : O) →
    ∀ x ∈ torsion A (AlgebraicClosure K) m,
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ → galAct A σ x = x) →
      ∃ y : (ObjBridge.ofGrp A).Pt (GapSHPair.inertiaField (K := K) w),
        ZInQ.Contrib.AbVarBC.extPt (ObjBridge.ofGrp A) (GapSHPair.inertiaField (K := K) w).val y = x

/-- **GLUE `TorusRankZero`** (Serre–Tate §2, the torsion count; step 4). `𝒩` a Néron model of `A` over the DVR
`O` whose geometric special fibre has semi-abelian identity component `0 → 𝔾_m^r → 𝒩⁰_{k̄} → B → 0`. If inertia
acts trivially on `A(K̄)[m]` for infinitely many `m` invertible in `O`, then `r = 0`: the identity component is
an abelian variety. Proof route (STANDARD): over `O^sh` the points of `A[m]` are rational
(`InertiaFixedRational`), `A(K^sh)[m] = 𝒩(O^sh)[m] ↪ 𝒩_s(k̄)[m]` (Néron property and `[m]` étale on the smooth
group scheme `𝒩`, BLR 7.3 Lemma 2), `#𝒩_s(k̄)[m] ≤ #Φ · m^r · m^{2a}` (`mumfordTorsionAlgClosed` for `B`,
roots of unity for the torus, `Φ` the finite component group), `a + r = g` (equidimensionality of the smooth
group scheme `𝒩⁰`), so `m^{2g} ≤ #Φ · m^{2g-r}` for infinitely many `m`, `r = 0`, and `𝒩⁰_{k̄} ≅ B`. -/
def TorusRankZero : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
      𝒩.IsNeronModel → 𝒩.IsSemistable →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite →
      HasAbelianIdentityComponent (geomSpecialFibre 𝒩)

/-- **LEAF `AbelianReductionGood`** (step 5; printed form pending reading, locators UNVERIFIED). `O` a DVR with
fraction field `K`, `A/K` an abelian variety with Néron model `𝒩`. If the identity component of the geometric
special fibre of `𝒩` is an abelian variety, then `A` has good reduction (an abelian scheme over `O` with generic
fibre `A`; it is `𝒩` itself). Sources (UNVERIFIED, from memory): Serre–Tate 1968 §1 (good reduction iff the
identity component of the special fibre of the Néron model is an abelian variety) and §2 (end of the proof of
Thm 1); Bosch–Lütkebohmert–Raynaud, *Néron models*, §7.4; the properness criterion for smooth group schemes over a
DVR with proper connected special fibre (EGA IV₃ 15.7.10, SGA 3 VI_B). -/
def AbelianReductionGood : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
    𝒩.IsNeronModel → HasAbelianIdentityComponent (geomSpecialFibre 𝒩) → HasGoodReduction A O

/-! ## §2 The reduction -/

section Core

variable {K : Type} [Field K]

/-- `m` invertible in `O` stays invertible in an extension `O'` over `O`. -/
theorem isUnit_natCast_comap {K' : Type} [Field K'] [Algebra K K'] {O : ValuationSubring K}
    {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O) {m : ℕ} (hm : IsUnit (m : O)) :
    IsUnit (m : O') := by
  have := hm.map (comapHom hO)
  rwa [map_natCast] at this

set_option synthInstance.maxHeartbeats 200000 in
/-- **Step 2 + transport**: inertia-fixed `m`-torsion makes the `m`-torsion of `A_E` rational over `E`. -/
theorem torsion_rational_inertiaField (hE : AvSplit.T4.MulEtaleAbelianScheme) (hA : InertiaFixedRational)
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ) (hmu : IsUnit (m : O))
    (hmt : InertiaTrivialOn A w m) :
    ∀ x : ((ObjBridge.ofGrp A).baseChange (GapSHPair.inertiaField (K := K) w)).Pt
        (AlgebraicClosure (GapSHPair.inertiaField (K := K) w)), x ^ m = 1 →
      ∃ y : ((ObjBridge.ofGrp A).baseChange (GapSHPair.inertiaField (K := K) w)).Pt
          (GapSHPair.inertiaField (K := K) w),
        ZInQ.Contrib.AbVarBC.extPt _ (Algebra.ofId _ (AlgebraicClosure _)) y = x := by
  intro x hx
  let E := GapSHPair.inertiaField (K := K) w
  let A' := ObjBridge.ofGrp A
  have hmK : (m : K) ≠ 0 := ReductSplit.natCast_ne_zero_of_isUnit O hmu
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) E
  haveI : Module.IsTorsionFree E (AlgebraicClosure E) := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  let κE : AlgebraicClosure K →ₐ[E] AlgebraicClosure E := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := κE.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A' κ m hmK x hx
  obtain ⟨y, hy⟩ := hA K O w hw A m hmu p hp (fun σ hσ => hmt σ hσ p hp)
  refine ⟨(ZInQ.Contrib.AbVarBC.bcPt A' E).symm y, ?_⟩
  rw [← hpx, ← hy]
  apply (ZInQ.Contrib.AbVarBC.bcPt A' (AlgebraicClosure E)).injective
  have hκ : (Algebra.ofId E (AlgebraicClosure E)).restrictScalars K = κ.comp E.val := by
    ext a
    exact (κE.commutes a).symm
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, hκ]

/-- **The core of the reduction**: a Néron model over `O`, and the pieces, give good reduction. -/
theorem goodReduction_of_neron (hSH : GapSHPair.NeronBaseChangeStrictHenselization)
    (hR : RaynaudSemistableSH) (hE : AvSplit.T4.MulEtaleAbelianScheme) (hA : InertiaFixedRational)
    (hB : TorusRankZero) (hC : AbelianReductionGood)
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒩 : GroupModelO (ObjBridge.ofGrp A) O) (h𝒩 : 𝒩.IsNeronModel)
    (hinf : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite) :
    HasGoodReduction A O := by
  obtain ⟨m, ⟨-, hmu, hmt⟩, hm3⟩ := hinf.exists_gt 2
  set E := GapSHPair.inertiaField (K := K) w
  set P := GapSHPair.wE (K := K) w
  have hP : P.comap (algebraMap K E) = O := GapSHPair.hE_eq w hw
  have hS := GapSHPair.isSHSep_inertia w hw
  haveI : IsDiscreteValuationRing P := hS.1.1
  have halg : (letI := (resMap hP).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField P)) := by
    letI := (resMap hP).toAlgebra
    have := hS.2.2.2
    exact Algebra.IsSeparable.isAlgebraic _ _
  have hss : 𝒩.IsSemistable := by
    rw [isSemistable_bcDVR_iff hP halg]
    exact hR E P hS.1 ((ObjBridge.ofGrp A).baseChange E) m (by omega) (isUnit_natCast_comap hP hmu)
      (torsion_rational_inertiaField hE hA O w hw A m hmu hmt) _ (hSH K O E P hP hS _ 𝒩 h𝒩)
  exact hC K O A 𝒩 h𝒩 (hB K O w hw A 𝒩 h𝒩 hss hinf)

end Core

/-- **`NOSConverseNF` from the open fields and the three named pieces.** Fields: `neronSchemeExtensionExists`
(textbook), `neronBaseChangeStrictHenselization`, `raynaudSemistableSH` (research); proved rows:
`ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof`. -/
theorem nosConverseNF_of_pieces (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hA : InertiaFixedRational) (hB : TorusRankZero) (hC : AbelianReductionGood) : NOSConverseNF := by
  intro K _ _ O _ w hw A _ hinf
  obtain ⟨𝒩, h𝒩⟩ := GapNeron.exists_neron_groupModelNF (GapNeron.neronSchemeModelExistsNF hN1) O
    (ObjBridge.ofGrp A)
  exact goodReduction_of_neron hSH hR ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof hA hB hC O w hw A 𝒩 h𝒩 hinf

/-- **`NOSConverseBar` over every field**, with BLR §1.4 Thm 3 over an arbitrary DVR (not a field) in place of
`neronSchemeExtensionExists`. -/
theorem nosConverseBar_of_pieces (hN : NeronSchemeModelExistsDVR)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hA : InertiaFixedRational) (hB : TorusRankZero) (hC : AbelianReductionGood) : NOSConverseBar := by
  intro K _ O _ w hw A _ hinf
  obtain ⟨𝒩, h𝒩⟩ := exists_neron_groupModel hN O (ObjBridge.ofGrp A)
  exact goodReduction_of_neron hSH hR ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof hA hB hC O w hw A 𝒩 h𝒩 hinf

/-! ## §3 Relations with `r7a`, the old leaf and the consumer -/

/-- **`r7a` from `NOSConverseBar`** ((a) ⇒ (b) and (b) ⇒ (c) proved by nos-proof). -/
theorem neronOggShafarevich_of_bar (h : NOSConverseBar) : PkgI2.NeronOggShafarevich.{0} := by
  intro K _ O _ w hw A _
  have hbc : (∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite := by
    intro hb
    refine (NOSProof.infinite_natCast_isUnit O).mono ?_
    rintro m ⟨hm, hu⟩
    exact ⟨hm, hu, hb m hm hu⟩
  have hab : HasGoodReduction A O → ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m :=
    fun hA m hm hu => NOSProof.inertiaTrivialOn_of_goodReduction O w hw A hA m hm hu
  exact ⟨⟨hab, fun hb => h K O w hw A (hbc hb)⟩, ⟨fun hA => hbc (hab hA), h K O w hw A⟩⟩

/-- `NOSConverseBar` is the converse direction of `r7a`. -/
theorem bar_of_neronOggShafarevich (h : PkgI2.NeronOggShafarevich.{0}) : NOSConverseBar :=
  fun K _ O _ w hw A _ hinf => (h K O w hw A).2.mpr hinf

/-- nos-proof's leaf gives `NOSConverseBar` (via `r7a`). -/
theorem bar_of_sep (h : NOSProof.NOSConverseSep) : NOSConverseBar :=
  bar_of_neronOggShafarevich (NOSProof.neronOggShafarevich_of_converse h)

/-- The number-field form is a specialization. -/
theorem nf_of_bar (h : NOSConverseBar) : NOSConverseNF :=
  fun K _ _ O _ w hw A _ hinf => h K O w hw A hinf

/-- **The live consumer reads only `NOSConverseNF`**: `PkgI2.goodReduction_of_QM_rational3_of_alg` (LPrefix
l. 814) with `hNOS : NeronOggShafarevich` replaced by `NOSConverseNF` (proof otherwise verbatim). -/
theorem goodReduction_of_QM_rational3_of_algNF {K : Type} [Field K] [NumberField K] (hNOS : NOSConverseNF)
    (hRay : HDec.PkgI2.RaynaudCriterionNF.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (hAlg : HDec.PkgI2.QuatUnipotentTrivial.{0})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have h3' : IsUnit ((3 : ℕ) : O) := by exact_mod_cast h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    apply h3.ne_zero
    apply Subtype.val_injective
    have h' : (3 : K) = 0 := by exact_mod_cast h
    have e3 : ((3 : O) : K) = 3 := rfl
    rw [e3, h']
    rfl
  have key : ∀ k : ℕ, 1 ≤ k → InertiaTrivialOn A w (3 ^ k) := by
    intro k hk σ hσ x hx
    obtain ⟨e, he⟩ := hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K)
    exact hAlg (Pts A (AlgebraicClosure K)) k hk (HDec.PkgI2.endPts A I) (HDec.PkgI2.endPts A J)
      (HDec.PkgI2.galHomPts A σ) hI hJ hIJ (fun x => by
        simp only [HDec.PkgI2.galHomPts, HDec.PkgI2.endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct,
          Category.assoc])
      (fun x => by
        simp only [HDec.PkgI2.galHomPts, HDec.PkgI2.endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct,
          Category.assoc])
      ⟨e, he⟩ (fun y hy => hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
        (2 * k) y hy) x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a), at a number field
  refine hNOS K O w hw A ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

/-- Sanity: the copy agrees with the original on `r7a`. -/
example {K : Type} [Field K] [NumberField K] (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : HDec.PkgI2.RaynaudCriterionNF.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞)) (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O :=
  goodReduction_of_QM_rational3_of_algNF (nf_of_bar (bar_of_neronOggShafarevich hNOS)) hRay hTors
    HDec.PkgI2.quatUnipotentTrivial O w hw A hdim I J hI hJ hIJ h3 hrat

/-! ## §4 `InertiaFixedRational`, proved: `Aut(K̄/E)` is contained in the inertia group -/

section InertiaGroup

open GapSHPair
open scoped IntermediateField Pointwise

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (w : ValuationSubring Ω)

/-- An element of a finite Galois `M` fixed by the finite inertia group `inertM w M` lies in the inertia field. -/
theorem mem_inertiaField_of_fixed {M : IntermediateField K Ω} (hM : IsFG M) (z : M)
    (hz : ∀ τ ∈ @inertM K _ Ω _ _ w M hM.1, τ z = z) : (z : Ω) ∈ inertiaField (K := K) w := by
  haveI := hM.1
  haveI := hM.2
  refine ⟨M, hM, z.2, fun τ hτ => ?_⟩
  have hmem : τ.restrictNormal M ∈ inertM w M := by
    rw [mem_inertM]
    intro y hy
    have h := AlgEquiv.restrictNormal_commutes τ M y
    change ((τ.restrictNormal M y : M) : Ω) = τ (y : Ω) at h
    rw [h]
    exact hτ y y.2 hy
  have h1 := hz _ hmem
  have h2 := AlgEquiv.restrictNormal_commutes τ M z
  change ((τ.restrictNormal M z : M) : Ω) = τ (z : Ω) at h2
  rw [h1] at h2
  exact h2.symm

/-- For `σ` fixing the inertia field and `y ∈ w` separable over `K`: `σ y - y ∈ 𝔪_w`. -/
theorem sub_mem_nonunits_of_sep {σ : Ω ≃ₐ[K] Ω} (hσ : ∀ x ∈ inertiaField (K := K) w, σ x = x)
    {y : Ω} (hsep : IsSeparable K y) (hy : y ∈ w) : σ y - y ∈ w.nonunits := by
  haveI : FiniteDimensional K K⟮y⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) y)
  haveI : Algebra.IsSeparable K K⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K Ω).2 hsep
  obtain ⟨M, hM, hle⟩ := isFG_of (K := K) (Ω := Ω) K⟮y⟯
  haveI := hM.1
  haveI := hM.2
  have hyM : y ∈ M := hle (IntermediateField.mem_adjoin_simple_self K y)
  have hτ : σ.restrictNormal M ∈ inertM w M := by
    rw [← IntermediateField.fixingSubgroup_fixedField (inertM w M),
      IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hzE := mem_inertiaField_of_fixed w hM z
      (fun τ' hτ' => (IntermediateField.mem_fixedField_iff _ _).1 hz τ' hτ')
    apply Subtype.ext
    have h := AlgEquiv.restrictNormal_commutes σ M z
    change ((σ.restrictNormal M z : M) : Ω) = σ (z : Ω) at h
    rw [h]
    exact hσ _ hzE
  have h := (mem_inertM w).1 hτ ⟨y, hyM⟩ hy
  have h2 := AlgEquiv.restrictNormal_commutes σ M ⟨y, hyM⟩
  change ((σ.restrictNormal M ⟨y, hyM⟩ : M) : Ω) = σ y at h2
  rwa [h2] at h

/-- For `σ` fixing the inertia field: `σ y - y ∈ 𝔪_w` for every `y ∈ w` (the inseparable part by `p`-th powers). -/
theorem sub_mem_nonunits {σ : Ω ≃ₐ[K] Ω} (hσ : ∀ x ∈ inertiaField (K := K) w, σ x = x)
    {y : Ω} (hy : y ∈ w) : σ y - y ∈ w.nonunits := by
  set p := ringExpChar K
  haveI : ExpChar Ω p := expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  haveI : ExpChar (separableClosure K Ω) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  obtain ⟨n, z, hz⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K Ω) p).mp inferInstance y
  have hsep : IsSeparable K (y ^ p ^ n) := by
    rw [← hz]; exact mem_separableClosure_iff.mp z.2
  have h := sub_mem_nonunits_of_sep w hσ hsep (pow_mem hy _)
  rw [map_pow, ← sub_pow_expChar_pow] at h
  rw [ValuationSubring.mem_nonunits_iff] at h ⊢
  rw [map_pow] at h
  by_contra hc
  exact absurd h (not_lt.mpr (one_le_pow_of_one_le' (not_lt.mp hc) _))

/-- **`Aut(K̄/E)` lies in the inertia group of `w`**: an automorphism fixing the inertia field pointwise is
inertia at `w`. -/
theorem isInertia_of_fixes {σ : Ω ≃ₐ[K] Ω} (hσ : ∀ x ∈ inertiaField (K := K) w, σ x = x) :
    PkgI2.IsInertia w σ := by
  have hσ' : ∀ x ∈ inertiaField (K := K) w, σ.symm x = x := fun x hx => by
    conv_lhs => rw [← hσ x hx]
    exact σ.symm_apply_apply x
  have hmap : ∀ {τ : Ω ≃ₐ[K] Ω}, (∀ x ∈ inertiaField (K := K) w, τ x = x) → ∀ y ∈ w, τ y ∈ w := by
    intro τ hτ y hy
    have : τ y = y + (τ y - y) := by ring
    rw [this]
    exact add_mem hy (ValuationSubring.nonunits_le (sub_mem_nonunits w hτ hy))
  have hd : σ ∈ w.decompositionSubgroup K := by
    show σ • w = w
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set,
      AlgEquiv.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmap hσ z hz
    · intro hy
      exact ⟨σ.symm y, hmap hσ' y hy, σ.apply_symm_apply y⟩
  refine ⟨hd, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  refine RingEquiv.ext fun r => ?_
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w b = IsLocalRing.residue w b
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, GapSHPair.mem_max_iff]
  exact sub_mem_nonunits w hσ b.2

end InertiaGroup

/-- **GLUE `InertiaFixedRational`, PROVED** (from `isInertia_of_fixes` and reduct-b's Galois descent of
torsion to an intermediate field, `ReductB.fixedTorsionRational_inter`, with `[m]` étale, fork PR #19). -/
theorem inertiaFixedRational_proof : InertiaFixedRational := by
  intro K _ O _ w hw A _ m hmu x hx hfix
  have hmK : (m : K) ≠ 0 := ReductSplit.natCast_ne_zero_of_isUnit O hmu
  exact ReductB.fixedTorsionRational_inter ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
    (GapSHPair.inertiaField (K := K) w) (ObjBridge.ofGrp A) m hmK x hx
    (fun σ hσ => hfix σ (isInertia_of_fixes w hσ))


/-- **`NOSConverseNF` from the open fields, the glue `TorusRankZero` and the leaf `AbelianReductionGood`**
(`InertiaFixedRational` is proved). -/
theorem nosConverseNF_of_two (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hB : TorusRankZero) (hC : AbelianReductionGood) : NOSConverseNF :=
  nosConverseNF_of_pieces hN1 hSH hR inertiaFixedRational_proof hB hC

/-- **`r7a` from BLR §1.4 Thm 3 over every DVR, the open fields, `TorusRankZero` and `AbelianReductionGood`.** -/
theorem neronOggShafarevich_of_two (hN : NeronSchemeModelExistsDVR)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hB : TorusRankZero) (hC : AbelianReductionGood) : PkgI2.NeronOggShafarevich.{0} :=
  neronOggShafarevich_of_bar (nosConverseBar_of_pieces hN hSH hR inertiaFixedRational_proof hB hC)

/-! ## §5 `TorusRankZero` decomposed (Serre–Tate's count) -/

section TorusDecomp

open ZInQ.HeightSplit

/-- The clauses of `HasSemiAbelianIdentityComponent G` for given `U, inc, B, π` and torus rank `r`. -/
def SemiAbelianRank {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (inc : U ⟶ G) (B : PkgI3.AbVar k) (π : U ⟶ B.X)
    (r : ℕ) : Prop :=
  IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧ IsMonHom π ∧ Flat π.left ∧
    Surjective π.left ∧
    ∃ (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
        u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
        (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

theorem hasSemiAbelian_iff {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    HasSemiAbelianIdentityComponent G ↔
      ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G) (B : PkgI3.AbVar k)
        (π : U ⟶ B.X) (r : ℕ), SemiAbelianRank G U inc B π r := by
  constructor
  · rintro ⟨U, hU, inc, h1, h2, h3, B, π, h4, h5, h6, r, e, h7, h8, h9⟩
    exact ⟨U, hU, inc, B, π, r, h1, h2, h3, h4, h5, h6, e, h7, h8, h9⟩
  · rintro ⟨U, hU, inc, B, π, r, h1, h2, h3, h4, h5, h6, e, h7, h8, h9⟩
    exact ⟨U, hU, inc, h1, h2, h3, B, π, h4, h5, h6, r, e, h7, h8, h9⟩

/-- The `m`-torsion `k`-points of a group scheme `X` over `k`. -/
def ptsTors {k : Type} [Field k] (X : Over (Spec (CommRingCat.of k))) [GrpObj X] (m : ℕ) :
    Set (algPt k k ⟶ X) :=
  {y | y ^ m = 1}

/-- **GLUE `TorsionInjectsSpecialFibre`** (Serre–Tate §2, first half of the count; BLR §7.3 Lemma 2 for `[m]` étale
on a smooth commutative group scheme, UNVERIFIED locator). The inertia-fixed `m`-torsion of `A(K̄)`, `m`
invertible in `O`, injects into the `m`-torsion `k̄`-points of the geometric special fibre of a Néron model:
it is rational over `K^sh` (`InertiaFixedRational`), `A(K^sh) = 𝒩(O^sh)` (Néron property, `𝒩 ⊗ O^sh` Néron by
`neronBaseChangeStrictHenselization`), and reduction `𝒩(O^sh)[m] → 𝒩(κ(O^sh))[m] ⊆ 𝒩(k̄)[m]` is injective
because `𝒩[m]` is étale and separated over `O^sh` (as in av-split's `UnramifiedSectionsEq`). -/
def TorsionInjectsSpecialFibre : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
      𝒩.IsNeronModel → ∀ m : ℕ, IsUnit (m : O) →
      ∃ f : {x // x ∈ torsion A (AlgebraicClosure K) m ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ → galAct A σ x = x} →
        ptsTors (geomSpecialFibre 𝒩) m, Function.Injective f

/-- **GLUE `ComponentIndexBound`** (finiteness of the component group). For a Néron model `𝒩` of an abelian
variety and an open subgroup scheme `U` of its geometric special fibre `G`, there is `c` with
`#G(k̄)[m] ≤ c · #U(k̄)[m]` for every `m`: `G` is of finite type, so `U(k̄)` has finite index `c` in `G(k̄)` (its
cosets are disjoint opens), and `G` is commutative (the generic fibre `A` is commutative and schematically dense
in the flat separated `𝒩`), so each coset meets `G(k̄)[m]` in a translate of a subset of `U(k̄)[m]`. -/
def ComponentIndexBound : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
      𝒩.IsNeronModel →
      ∀ (U : Over (Spec (CommRingCat.of (ResBarO O)))) [GrpObj U] (inc : U ⟶ geomSpecialFibre 𝒩),
        IsOpenImmersion inc.left → IsMonHom inc →
        ∃ c : ℕ, ∀ m : ℕ, (ptsTors (geomSpecialFibre 𝒩) m).encard ≤ c * (ptsTors U m).encard

/-- **GLUE `DimensionRelation`** (dimension of the special fibre). For a Néron model `𝒩` of an abelian variety `A`
whose geometric special fibre has semi-abelian identity component `0 → 𝔾_m^r → U → B → 0`:
`dim B + r = dim A`, both finite. (`dim U = dim A` since `𝒩` is smooth with fibres of constant dimension along the
identity section, field `groupSchemeEquidim` and infra-smooth-dim; `dim U = dim B + r` for the flat surjection
`U → B` with fibres `𝔾_m^r`.) -/
def DimensionRelation : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
      𝒩.IsNeronModel →
      ∀ (U : Over (Spec (CommRingCat.of (ResBarO O)))) [GrpObj U] (inc : U ⟶ geomSpecialFibre 𝒩)
        (B : PkgI3.AbVar (ResBarO O)) (π : U ⟶ B.X) (r : ℕ),
        SemiAbelianRank (geomSpecialFibre 𝒩) U inc B π r →
        ∃ g a : ℕ, topologicalKrullDim A.X.left = g ∧ topologicalKrullDim B.X.left = a ∧ a + r = g

/-- **GLUE `NeronSpecialFibreComm`**: the `k̄`-points of the geometric special fibre of a Néron model of an abelian
variety form a commutative group. (Provable from the Néron property: `μ` and `μ ∘ swap : 𝒩 ×_O 𝒩 → 𝒩` agree on
the generic fibre since `A` is commutative, and `𝒩 ×_O 𝒩` is smooth, so they are equal; then base change.) -/
def NeronSpecialFibreComm : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (𝒩 : GroupModelO (ObjBridge.ofGrp A) O),
      𝒩.IsNeronModel → ∀ x y : algPt (ResBarO O) (ResBarO O) ⟶ geomSpecialFibre 𝒩, x * y = y * x


/-- **A Néron model of a commutative group variety is commutative**: `fst * snd` and `snd * fst` on `𝒩 ×_O 𝒩`
(smooth) have the same generic fibre (`gen` is a homomorphism into the commutative `A`), so they agree by the
Néron mapping property. -/
theorem isCommMonObj_neron {K : Type} [Field K] {O : ValuationSubring K} {A' : PkgI3.AbVar K}
    [IsCommMonObj A'.X] (𝒩 : GroupModelO A' O) (h𝒩 : 𝒩.IsNeronModel) : IsCommMonObj 𝒩.G := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj 𝒩.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒩.gen.hom := 𝒩.gen_hom
  haveI hY : Smooth (𝒩.G ⊗ 𝒩.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  have key : (fst 𝒩.G 𝒩.G * snd 𝒩.G 𝒩.G : 𝒩.G ⊗ 𝒩.G ⟶ 𝒩.G) = snd _ _ * fst _ _ := by
    apply (@h𝒩 (𝒩.G ⊗ 𝒩.G) hY).1
    change F.map (fst 𝒩.G 𝒩.G * snd 𝒩.G 𝒩.G) ≫ 𝒩.gen.hom = F.map (snd 𝒩.G 𝒩.G * fst 𝒩.G 𝒩.G) ≫ 𝒩.gen.hom
    rw [Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  refine ⟨⟨fun f g => ?_⟩⟩
  have h1 : f * g = lift f g ≫ (fst 𝒩.G 𝒩.G * snd 𝒩.G 𝒩.G) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  have h2 : g * f = lift f g ≫ (snd 𝒩.G 𝒩.G * fst 𝒩.G 𝒩.G) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [h1, h2, key]

/-- **GLUE `NeronSpecialFibreComm`, PROVED**: base change along `Spec κ̄ → Spec O` is braided, so the geometric
special fibre of the commutative `𝒩` is commutative. -/
theorem neronSpecialFibreComm_proof : NeronSpecialFibreComm := by
  intro K _ O _ A _ 𝒩 h𝒩 x y
  haveI : IsCommMonObj (ObjBridge.ofGrp A).X := ObjBridge.isCommMonObj A
  haveI := isCommMonObj_neron 𝒩 h𝒩
  haveI : IsCommMonObj (geomSpecialFibre 𝒩) :=
    Functor.isCommMonObj_obj (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))))
  exact mul_comm x y

/-- **`SemiAbelianTorsionBound`** (to be proved from `mumfordTorsionAlgClosed`): over an algebraically closed `k`,
`#U(k)[m] ≤ m^r · m^{2a}` for a semi-abelian `U` with torus rank `r` and abelian quotient of dimension `a`. -/
def SemiAbelianTorsionBound : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (inc : U ⟶ G) (B : PkgI3.AbVar k) (π : U ⟶ B.X)
    (r a m : ℕ), SemiAbelianRank G U inc B π r → topologicalKrullDim B.X.left = a → 0 < m →
      (m : k) ≠ 0 → (∀ x y : algPt k k ⟶ U, x * y = y * x) →
      (ptsTors U m).encard ≤ ((m ^ r * m ^ (2 * a) : ℕ) : ℕ∞)

/-- **`RankZeroAbelian`** (to be proved: Mathlib's `Flat.isIso_of_surjective_of_mono`): a semi-abelian identity
component of torus rank `0` is an abelian variety. -/
def RankZeroAbelian : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], LocallyOfFinitePresentation G.hom →
    ∀ (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (inc : U ⟶ G) (B : PkgI3.AbVar k) (π : U ⟶ B.X),
      SemiAbelianRank G U inc B π 0 → HasAbelianIdentityComponent G


/-- With torus rank `0`, two morphisms `Spec R → U` with the same composite to `B` are equal. -/
theorem eq_of_comp_eq_rank_zero {k : Type} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    {U : Over (Spec (CommRingCat.of k))} [GrpObj U] {inc : U ⟶ G} {B : PkgI3.AbVar k} {π : U ⟶ B.X}
    (hU : SemiAbelianRank G U inc B π 0) (R : CommRingCat.{0}) (h1 h2 : Spec R ⟶ U.left)
    (h : h1 ≫ π.left = h2 ≫ π.left) : h1 = h2 := by
  obtain ⟨-, -, -, hπ, -, -, e, -, hker, -⟩ := hU
  let s : Spec R ⟶ Spec (CommRingCat.of k) := h1 ≫ U.hom
  let φ : CommRingCat.of k ⟶ R := Spec.preimage s
  letI : Algebra k R := φ.hom.toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k R)) = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hw2 : h2 ≫ U.hom = s := by
    change h2 ≫ U.hom = h1 ≫ U.hom
    rw [← Over.w π, ← Category.assoc, ← h, Category.assoc]
  let u1 : algPt k R ⟶ U := Over.homMk h1 (by simpa [algPt] using hs.symm)
  let u2 : algPt k R ⟶ U := Over.homMk h2 (by simp only [algPt, Over.mk_hom]; rw [hw2, hs])
  have hu : u1 ≫ π = u2 ≫ π := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    exact h
  let F : (algPt k R ⟶ U) →* (algPt k R ⟶ B.X) :=
    { toFun := fun x => x ≫ π
      map_one' := MonObj.one_comp π
      map_mul' := fun x y => MonObj.mul_comp x y π }
  have h0 : (u1 * u2⁻¹) ≫ π = 1 := by
    change F (u1 * u2⁻¹) = 1
    rw [map_mul, map_inv]
    change (u1 ≫ π) * (u2 ≫ π)⁻¹ = 1
    rw [hu, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (hker R (u1 * u2⁻¹)).mp h0
  have ht1 : t = 1 := funext fun i => Fin.elim0 i
  rw [ht1, map_one] at ht
  have h12 : u1 = u2 := (mul_inv_eq_one.mp ht.symm)
  exact congrArg Over.Hom.left h12

/-- **`RankZeroAbelian`, PROVED**: with torus rank `0`, `π : U → B` is a flat surjective monomorphism locally of
finite presentation, hence an isomorphism (Mathlib `IsOpenImmersion.of_flat_of_mono`), so `U` is proper. -/
theorem rankZeroAbelian_proof : RankZeroAbelian := by
  intro k _ G _ hG U _ inc B π hU
  have hU' := hU
  obtain ⟨hinc, hmon, hconn, hπ, hflat, hsurj, -⟩ := hU'
  haveI : Mono π.left := ⟨fun {Z} g1 g2 h => by
    refine Scheme.hom_ext_of_forall g1 g2 fun z => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    change Z.Opens at V
    change IsAffineOpen V at hV
    refine ⟨V, hzV, ?_⟩
    rw [← cancel_epi hV.isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact eq_of_comp_eq_rank_zero hU Γ(Z, V) _ _ (by rw [Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, h])⟩
  haveI : LocallyOfFiniteType U.hom := by
    rw [← Over.w inc]; infer_instance
  haveI : LocallyOfFiniteType (π.left ≫ B.X.hom) := by
    rw [Over.w π]; infer_instance
  haveI : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left B.X.hom
  haveI : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  haveI : LocallyOfFinitePresentation π.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : IsOpenImmersion π.left := IsOpenImmersion.of_flat_of_mono π.left
  haveI : IsIso π.left := (isIso_iff_isOpenImmersion_and_surjective π.left).mpr ⟨inferInstance, hsurj⟩
  haveI : IsProper B.X.hom := B.proper
  refine ⟨U, inferInstance, inc, hinc, hmon, hconn, ?_⟩
  rw [← Over.w π]
  infer_instance


/-- **`SemiAbelianTorsionBound`, PROVED** from the field `mumfordTorsionAlgClosed`: `U(k)[m]` injects into
`B(k)[m] × μ_m(k)^r` (a chosen preimage in each fibre, the torus coordinates of the difference). -/
theorem semiAbelianTorsionBound_of (hM : AvSplit.MumfordTorsionAlgClosed) : SemiAbelianTorsionBound := by
  classical
  intro k _ _ G _ U _ inc B π r a m hU ha hm0 hmk hcomm
  obtain ⟨-, -, -, hπ, -, -, e, he, hker, -⟩ := hU
  haveI : NeZero m := ⟨hm0.ne'⟩
  let F : (algPt k k ⟶ U) →* (algPt k k ⟶ B.X) :=
    { toFun := fun x => x ≫ π
      map_one' := MonObj.one_comp π
      map_mul' := fun x y => MonObj.mul_comp x y π }
  obtain ⟨eB, -⟩ := hM k (ObjBridge.toGrp B) a m ha hm0 hmk
  have hB : (ptsTors B.X m).encard = ((m ^ (2 * a) : ℕ) : ℕ∞) := by
    change (torsion (ObjBridge.toGrp B) k m).encard = _
    rw [Set.encard, ENat.card_congr eB, ENat.card_eq_coe_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  let T : Set (Fin r → kˣ) := {t | ∀ i, t i ^ m = 1}
  have hT : T.encard ≤ ((m ^ r : ℕ) : ℕ∞) := by
    have eT : T ≃ (Fin r → rootsOfUnity m k) :=
      { toFun := fun t i => ⟨t.1 i, (mem_rootsOfUnity m _).2 (t.2 i)⟩
        invFun := fun t => ⟨fun i => (t i : kˣ), fun i => (mem_rootsOfUnity m _).1 (t i).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    haveI : Fintype (rootsOfUnity m k) := Fintype.ofFinite _
    rw [Set.encard, ENat.card_congr eT, ENat.card_eq_coe_fintype_card, Fintype.card_fun,
      Fintype.card_fin]
    have h1 := card_rootsOfUnity k m
    rw [Nat.card_eq_fintype_card] at h1
    exact_mod_cast Nat.pow_le_pow_left h1 r
  have hFm : ∀ u ∈ ptsTors U m, F u ∈ ptsTors B.X m := fun u hu => by
    change F u ^ m = 1
    rw [← map_pow, show u ^ m = 1 from hu, map_one]
  let sec : (algPt k k ⟶ B.X) → (algPt k k ⟶ U) := fun b =>
    if h : ∃ u ∈ ptsTors U m, F u = b then h.choose else 1
  have hsec : ∀ u ∈ ptsTors U m, sec (F u) ∈ ptsTors U m ∧ F (sec (F u)) = F u := by
    intro u hu
    have h : ∃ u' ∈ ptsTors U m, F u' = F u := ⟨u, hu, rfl⟩
    simp only [sec, dif_pos h]
    exact h.choose_spec
  have hkerT : ∀ u ∈ ptsTors U m, ∃ t ∈ T, e k t = u * (sec (F u))⁻¹ := by
    intro u hu
    obtain ⟨hs, hFs⟩ := hsec u hu
    have h0 : F (u * (sec (F u))⁻¹) ≫ 𝟙 _ = 1 := by
      rw [Category.comp_id, map_mul, map_inv, hFs, mul_inv_cancel]
    rw [Category.comp_id] at h0
    obtain ⟨t, ht⟩ := (hker k _).mp h0
    refine ⟨t, fun i => ?_, ht⟩
    have hpow : (u * (sec (F u))⁻¹) ^ m = 1 := by
      rw [(show Commute u (sec (F u))⁻¹ from hcomm _ _).mul_pow, inv_pow,
        show u ^ m = 1 from hu, show sec (F u) ^ m = 1 from hs, inv_one, _root_.one_mul]
    have h2 : e k (t ^ m) = e k 1 := by rw [map_pow, ht, hpow, map_one]
    have htm : t ^ m = 1 := he k h2
    have := congrFun htm i
    simpa using this
  choose! τ hτT hτ using hkerT
  have hinj : Set.InjOn (fun u => (F u, τ u)) (ptsTors U m) := by
    intro u hu u' hu' huu
    simp only [Prod.mk.injEq] at huu
    obtain ⟨h1, h2⟩ := huu
    have h3 := (hτ u hu).symm.trans ((congrArg (e k) h2).trans (hτ u' hu'))
    rw [h1] at h3
    exact mul_right_cancel h3
  have hmaps : Set.MapsTo (fun u => (F u, τ u)) (ptsTors U m) (ptsTors B.X m ×ˢ T) :=
    fun u hu => ⟨hFm u hu, hτT u hu⟩
  calc (ptsTors U m).encard ≤ (ptsTors B.X m ×ˢ T).encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = (ptsTors B.X m).encard * T.encard := Set.encard_prod
    _ ≤ ((m ^ (2 * a) : ℕ) : ℕ∞) * ((m ^ r : ℕ) : ℕ∞) := by rw [hB]; gcongr
    _ = ((m ^ r * m ^ (2 * a) : ℕ) : ℕ∞) := by push_cast; ring

/-- `m` invertible in `O` is nonzero in `κ̄(O)`. -/
theorem natCast_ne_zero_resBar {K : Type} [Field K] (O : ValuationSubring K) {m : ℕ}
    (hm : IsUnit (m : O)) : (m : ResBarO O) ≠ 0 := by
  have h1 : IsUnit (m : IsLocalRing.ResidueField O) := by
    have := hm.map (IsLocalRing.residue O)
    rwa [map_natCast] at this
  have h2 := h1.map (algebraMap (IsLocalRing.ResidueField O) (ResBarO O))
  rw [map_natCast] at h2
  exact h2.ne_zero

/-- **`TorusRankZero` from Serre–Tate's count**: the glue `TorsionInjectsSpecialFibre`, `ComponentIndexBound`,
`DimensionRelation`, the field `mumfordTorsionAlgClosed`, and `SemiAbelianTorsionBound`, `RankZeroAbelian`. -/
theorem torusRankZero_of_count (hInj : TorsionInjectsSpecialFibre) (hComp : ComponentIndexBound)
    (hDim : DimensionRelation) (hComm : NeronSpecialFibreComm) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hSemi : SemiAbelianTorsionBound) (hB7 : RankZeroAbelian) : TorusRankZero := by
  intro K _ O _ w hw A _ 𝒩 h𝒩 hss hinf
  obtain ⟨U, _, inc, B, π, r, hU⟩ := (hasSemiAbelian_iff _).mp hss
  have hcommU : ∀ x y : algPt (ResBarO O) (ResBarO O) ⟶ U, x * y = y * x := by
    haveI : IsOpenImmersion inc.left := hU.1
    haveI : IsMonHom inc := hU.2.1
    intro x y
    apply Over.OverMorphism.ext
    rw [← cancel_mono inc.left, ← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.mul_comp,
      hComm K O A 𝒩 h𝒩]
  obtain ⟨g, a, hg, ha, hgar⟩ := hDim K O A 𝒩 h𝒩 U inc B π r hU
  obtain ⟨c, hc⟩ := hComp K O A 𝒩 h𝒩 U inc hU.1 hU.2.1
  have hbound : ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m → m ^ r ≤ c := by
    intro m hm0 hmu hmt
    haveI : NeZero m := ⟨hm0.ne'⟩
    have hmK : (m : K) ≠ 0 := ReductSplit.natCast_ne_zero_of_isUnit O hmu
    obtain ⟨e, -⟩ := AvSplit.torsionStructure_of_mumford hM K A g m hg hm0 hmK
    have hA : (torsion A (AlgebraicClosure K) m).encard = ((m ^ (2 * g) : ℕ) : ℕ∞) := by
      rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_fintype_card, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
    obtain ⟨f, hf⟩ := hInj K O w hw A 𝒩 h𝒩 m hmu
    have h1 : (torsion A (AlgebraicClosure K) m).encard ≤ (ptsTors (geomSpecialFibre 𝒩) m).encard := by
      have e2 : torsion A (AlgebraicClosure K) m ≃
          {x // x ∈ torsion A (AlgebraicClosure K) m ∧
            ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ → galAct A σ x = x} :=
        { toFun := fun x => ⟨x.1, x.2, fun σ hσ => hmt σ hσ x.1 x.2⟩
          invFun := fun x => ⟨x.1, x.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Set.encard, Set.encard, ENat.card_congr e2]
      exact ENat.card_le_card_of_injective hf
    have h2 := hSemi (ResBarO O) _ U inc B π r a m hU ha hm0 (natCast_ne_zero_resBar O hmu) hcommU
    have h3 : ((m ^ (2 * g) : ℕ) : ℕ∞) ≤ ((c * (m ^ r * m ^ (2 * a)) : ℕ) : ℕ∞) := by
      rw [← hA]
      calc (torsion A (AlgebraicClosure K) m).encard ≤ (ptsTors (geomSpecialFibre 𝒩) m).encard := h1
        _ ≤ c * (ptsTors U m).encard := hc m
        _ ≤ c * ((m ^ r * m ^ (2 * a) : ℕ) : ℕ∞) := by gcongr
        _ = ((c * (m ^ r * m ^ (2 * a)) : ℕ) : ℕ∞) := by push_cast; ring
    have h4 : m ^ (2 * g) ≤ c * (m ^ r * m ^ (2 * a)) := by exact_mod_cast h3
    have hpos : 0 < m ^ r * m ^ (2 * a) := by positivity
    have h5 : m ^ r * (m ^ r * m ^ (2 * a)) ≤ c * (m ^ r * m ^ (2 * a)) := by
      calc m ^ r * (m ^ r * m ^ (2 * a)) = m ^ (2 * g) := by
            rw [← hgar, ← pow_add, ← pow_add]; ring_nf
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_right h5 hpos
  have hr : r = 0 := by
    by_contra hr0
    apply hinf
    refine (Set.finite_Iic c).subset ?_
    rintro m ⟨hm0, hmu, hmt⟩
    exact (Nat.le_self_pow hr0 m).trans (hbound m hm0 hmu hmt)
  subst hr
  have hlfp : LocallyOfFinitePresentation (geomSpecialFibre 𝒩).hom := by
    change LocallyOfFinitePresentation (pullback.snd 𝒩.G.hom _)
    infer_instance
  exact hB7 _ _ hlfp U inc B π hU

/-- **`TorusRankZero` from the count with the proved pieces**: glue `TorsionInjectsSpecialFibre`,
`ComponentIndexBound`, `DimensionRelation` and the field `mumfordTorsionAlgClosed`. -/
theorem torusRankZero_of_glue (hInj : TorsionInjectsSpecialFibre) (hComp : ComponentIndexBound)
    (hDim : DimensionRelation) (hM : AvSplit.MumfordTorsionAlgClosed) : TorusRankZero :=
  torusRankZero_of_count hInj hComp hDim neronSpecialFibreComm_proof hM (semiAbelianTorsionBound_of hM)
    rankZeroAbelian_proof

end TorusDecomp

/-! ## §6 The finest form -/

/-- **`NOSConverseNF` from the open fields and four open pieces**: fields `neronSchemeExtensionExists`,
`neronBaseChangeStrictHenselization`, `raynaudSemistableSH`, `mumfordTorsionAlgClosed`; GLUE
`TorsionInjectsSpecialFibre`, `ComponentIndexBound`, `DimensionRelation`; LEAF `AbelianReductionGood`. -/
theorem nosConverseNF_of_glue (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hInj : TorsionInjectsSpecialFibre)
    (hComp : ComponentIndexBound) (hDim : DimensionRelation) (hC : AbelianReductionGood) : NOSConverseNF :=
  nosConverseNF_of_two hN1 hSH hR (torusRankZero_of_glue hInj hComp hDim hM) hC

/-- **`r7a` from BLR §1.4 Thm 3 over every DVR, the open fields and the four open pieces.** -/
theorem neronOggShafarevich_of_glue (hN : NeronSchemeModelExistsDVR)
    (hSH : GapSHPair.NeronBaseChangeStrictHenselization) (hR : RaynaudSemistableSH)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hInj : TorsionInjectsSpecialFibre)
    (hComp : ComponentIndexBound) (hDim : DimensionRelation) (hC : AbelianReductionGood) :
    PkgI2.NeronOggShafarevich.{0} :=
  neronOggShafarevich_of_two hN hSH hR (torusRankZero_of_glue hInj hComp hDim hM) hC

end NOSConverse

#print axioms NOSConverse.nosConverseNF_of_pieces
#print axioms NOSConverse.nosConverseBar_of_pieces
#print axioms NOSConverse.neronOggShafarevich_of_bar
#print axioms NOSConverse.goodReduction_of_QM_rational3_of_algNF
#print axioms NOSConverse.inertiaFixedRational_proof
#print axioms NOSConverse.nosConverseNF_of_two
#print axioms NOSConverse.neronOggShafarevich_of_two
#print axioms NOSConverse.torusRankZero_of_count
#print axioms NOSConverse.rankZeroAbelian_proof
#print axioms NOSConverse.semiAbelianTorsionBound_of
#print axioms NOSConverse.neronSpecialFibreComm_proof
#print axioms NOSConverse.torusRankZero_of_glue
#print axioms NOSConverse.nosConverseNF_of_glue
#print axioms NOSConverse.neronOggShafarevich_of_glue
