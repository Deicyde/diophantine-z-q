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

end NOSConverse

#print axioms NOSConverse.nosConverseNF_of_pieces
#print axioms NOSConverse.nosConverseBar_of_pieces
#print axioms NOSConverse.neronOggShafarevich_of_bar
#print axioms NOSConverse.goodReduction_of_QM_rational3_of_algNF
