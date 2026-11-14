import TailL
import ZInQKernel.Contrib.AVB2.SerreLemma
import ZInQKernel.Contrib.AVB1.AlgClosed
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.NeronC.NeronGroup

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_e20_avb2
-- (leaf-fold5) mk_e20.py: scratch/av-b2/olean/AVB2Main.lean, `namespace AVB2` ... `end AVB2`, verbatim
noncomputable section

namespace AVB2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## 1. T9 -/

/-- **T9 is glue** given the two `OpenAddedLeaves3` fields `t09SymmIsogenyExists` and
`isogenyQuasiInverse` (proof: weil-pairing's `oldT9_of_symmIsogeny`). -/
theorem t9_of_leaves3 (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) : LeafPush.T09_WeilPairing.{0} :=
  WeilPairing.oldT9_of_symmIsogeny h9 hQ

/-! ## 2. `DivisiblePoints` -/

/-- **Leaf (positive-characteristic half of "`[n]` is an isogeny").** Over a field `k` of positive
characteristic, multiplication by `n ≠ 0` on an abelian variety is finite and surjective.
Published: Mumford, *Abelian varieties*, §4, Application 2 (`n_X` is an isogeny of degree
`n^{2g}`, over an algebraically closed field) and §6; Milne, *Abelian varieties* (Cornell–Silverman
1986), Thm 8.2, over any field (locators UNVERIFIED). The degree is dropped, so a consequence of the
published statement. The characteristic-0 half is g9-abvarbc's proved `MulIsogeny`. -/
def MulIsogenyPosChar : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 → ringChar k ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

/-- `[n]` is an isogeny in every characteristic. -/
theorem mulIsogenyAll (hP : MulIsogenyPosChar) (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ)
    (hn : n ≠ 0) : PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom) := by
  by_cases h : ringChar k = 0
  · haveI : CharP k 0 := ringChar.eq_iff.1 h
    haveI : CharZero k := CharP.charP_to_charZero k
    exact HSyn.mulIsogeny_proved k A n hn
  · exact hP k A n hn h

/-- **Lifting `K̄`-points through a finite surjective `K`-endomorphism** (the fibre is a nonempty
finite `K̄`-scheme; its closed points are `K̄`-points). -/
theorem exists_lift_pt {K : Type} [Field K] (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    (hf : PkgI3.AbVar.IsIsogenyMor f) (z : A.Pt (AlgebraicClosure K)) :
    ∃ w : A.Pt (AlgebraicClosure K), w ≫ f = z := by
  obtain ⟨hfin, hsurj⟩ := hf
  let zl : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ A.X.left := z.left
  let s : pullback f.left zl ⟶ Spec (CommRingCat.of (AlgebraicClosure K)) := pullback.snd f.left zl
  haveI : IsFinite s := by dsimp [s]; infer_instance
  haveI : Surjective s := by dsimp [s]; infer_instance
  haveI : CompactSpace ((pullback f.left zl : Scheme) : Type) := QuasiCompact.compactSpace_of_compactSpace s
  haveI : Nonempty ((pullback f.left zl : Scheme) : Type) := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))) := inferInstance
    exact ⟨(s.surjective y).choose⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := ((pullback f.left zl : Scheme) : Type))
    isClosed_univ Set.univ_nonempty
  let pt := pointOfClosedPoint s x hx
  have hpt : pt ≫ s = 𝟙 _ := pointOfClosedPoint_comp s x hx
  have hz : zl ≫ A.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := Over.w z
  have hw : f.left ≫ A.X.hom = A.X.hom := Over.w f
  refine ⟨Over.homMk (pt ≫ pullback.fst f.left zl) ?_, ?_⟩
  · change (pt ≫ pullback.fst f.left zl) ≫ A.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    rw [Category.assoc, ← hw, pullback.condition_assoc, hz, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]
  · apply Over.OverMorphism.ext
    change (pt ≫ pullback.fst f.left zl) ≫ f.left = zl
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]

/-- **`DivisiblePoints` from `MulIsogenyPosChar`** (characteristic 0: g9-abvarbc's `MulIsogeny`). -/
theorem divisiblePoints_of_posChar (hP : MulIsogenyPosChar) : WeilPairing.DivisiblePoints := by
  intro K _ A n hn z
  have hiso := mulIsogenyAll hP K A (n : ℤ) (by exact_mod_cast hn.ne')
  obtain ⟨w, hw⟩ := exists_lift_pt A _ hiso (Additive.toMul z)
  refine ⟨Additive.ofMul w, ?_⟩
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_ofMul, ← ZInQ.Contrib.AbVarBC.comp_natCast_hom A w n, hw]

/-! ## 3. `SerreRigidity3` -/

/-- `Spec σ : Spec ℂ → Spec K` as a morphism of `K`-schemes. -/
def sC {K : Type} [Field K] (σ : K →+* ℂ) :
    ZInQ.LeafPush2.cptObj σ ⟶ PkgI3.AbVar.ptObj (K := K) K :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ)) (by
    simp only [ZInQ.LeafPush2.cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- Precomposition with `Spec σ` is injective on `K`-points. -/
theorem sC_cancel {K : Type} [Field K] (σ : K →+* ℂ) {Y : Over (Spec (CommRingCat.of K))}
    {a b : PkgI3.AbVar.ptObj (K := K) K ⟶ Y} (h : sC σ ≫ a = sC σ ≫ b) : a = b := by
  haveI := ZInQ.Contrib.AbVarBC.epi_spec_map_field σ
  apply Over.OverMorphism.ext
  have h2 := congrArg CommaMorphism.left h
  simp only [Over.comp_left] at h2
  exact (cancel_epi (Spec.map (CommRingCat.ofHom σ))).1 h2

/-- **Torsion of `A(ℂ)_σ` comes from `A(K)`** for `K` algebraically closed of characteristic `0`
(`[N]` is finite by `MulIsogeny`; points of a finite `K`-scheme, g9-abvarbc's
`exists_lift_of_isFinite`). -/
theorem cpt_torsion_descends {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (A : PkgI3.AbVar K) (σ : K →+* ℂ) (N : ℕ) (hN : 0 < N) (x : ZInQ.LeafPush2.CPts A σ)
    (hx : x ^ N = 1) : ∃ y : A.Pt K, sC σ ≫ y = x := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hfinN : IsFinite ((((N : ℕ) : ℤ) : PkgI3.AbVar.End A).hom.left) :=
    (HSyn.mulIsogeny_proved K A (N : ℤ) (by exact_mod_cast hN.ne')).1
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have h1 : x ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by
    rw [ZInQ.Contrib.AbVarBC.comp_natCast_hom, hx]
  have hq0 : x.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K ℂ)) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  haveI : IsFinite fN := hfinN
  let z : Spec (CommRingCat.of ℂ) ⟶ pullback fN e :=
    pullback.lift x.left (Spec.map (CommRingCat.ofHom (algebraMap K ℂ))) hq0
  obtain ⟨p0, hp0, hp0g⟩ := ZInQ.Contrib.AbVarBC.exists_lift_of_isFinite (Algebra.ofId K ℂ)
    (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  refine ⟨Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl), ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((Algebra.ofId K ℂ : K →ₐ[K] ℂ) : K →+* ℂ)) ≫
    p0 ≫ pullback.fst fN e = x.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

/-- **Morphisms of abelian varieties over an algebraically closed `K` agreeing on `K`-points are
equal** (hom-unify's `hom_ext_of_cpts` with `K` for `ℂ`). -/
theorem hom_ext_of_pts {K : Type} [Field K] [IsAlgClosed K] {A B : PkgI3.AbVar K}
    (f f' : A.X ⟶ B.X) (h : ∀ p : A.Pt K, p ≫ f = p ≫ f') : f = f' := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  apply Over.OverMorphism.ext
  have hw : f.left ≫ B.X.hom = f'.left ≫ B.X.hom := by rw [Over.w f, Over.w f']
  have : LocallyOfFiniteType (f.left ≫ B.X.hom) := by rw [Over.w f]; infer_instance
  refine ext_of_apply_eq B.X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => ?_) hw
  let p0 := pointOfClosedPoint A.X.hom x hx
  let p : A.Pt K := Over.homMk p0 (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Spec.map_id]
    exact pointOfClosedPoint_comp A.X.hom x hx)
  have hp : p0 ≫ f.left = p0 ≫ f'.left := congrArg CommaMorphism.left (h p)
  have key : (p0 ≫ f.left) (A.X.hom x) = (p0 ≫ f'.left) (A.X.hom x) := by rw [hp]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at key
  exact key


/-! ## 3′. T11(b): uniqueness proved, existence left as the leaf -/

/-- **Base change along a field extension is injective on morphisms** between abelian varieties
over an algebraically closed `k` (compare on `k`-points; `Spec L → Spec k` is an epimorphism). -/
theorem baseChange_map_injective {k : Type} [Field k] [IsAlgClosed k] (L : Type) [Field L]
    [Algebra k L] {A B : PkgI3.AbVar k} {φ φ' : A.X ⟶ B.X}
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ') : φ = φ' := by
  apply hom_ext_of_pts φ φ'
  intro p
  haveI := ZInQ.Contrib.AbVarBC.epi_spec_map_field (algebraMap k L)
  have hp1 : p.left ≫ A.X.hom = 𝟙 _ := by
    have := Over.w p
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Spec.map_id] at this
    exact this
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let q : Spec (CommRingCat.of L) ⟶ pullback A.X.hom s :=
    pullback.lift (s ≫ p.left) (𝟙 _)
      ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) hp1).trans
        ((Category.comp_id s).trans (Category.id_comp s).symm)))
  have key : ∀ g : A.X ⟶ B.X,
      ((Over.pullback s).map g).left ≫ pullback.fst B.X.hom s = pullback.fst A.X.hom s ≫ g.left := by
    intro g
    simp
  have h2 : s ≫ (p ≫ φ).left = s ≫ (p ≫ φ').left := by
    have e1 : s ≫ (p ≫ φ).left = q ≫ ((Over.pullback s).map φ).left ≫ pullback.fst B.X.hom s := by
      rw [key, ← Category.assoc, pullback.lift_fst, Over.comp_left]
      exact (Category.assoc _ _ _).symm
    have e2 : s ≫ (p ≫ φ').left = q ≫ ((Over.pullback s).map φ').left ≫ pullback.fst B.X.hom s := by
      rw [key, ← Category.assoc, pullback.lift_fst, Over.comp_left]
      exact (Category.assoc _ _ _).symm
    rw [e1, e2, h]
  exact Over.OverMorphism.ext ((cancel_epi s).1 h2)

/-- **Leaf (T11(b), existence half).** For abelian varieties over an algebraically closed field `k`
of characteristic `0` and an extension `L/k`, every homomorphism `A_L → B_L` is the base change of a
homomorphism `A → B`. Published: Conrad, *Chow's `K/k`-image and `K/k`-trace, and the Lang–Néron
theorem*, Enseign. Math. 52 (2006), §3 (rigidity of `Hom` for primary extensions, locator UNVERIFIED);
Milne, *Abelian varieties* (Cornell–Silverman 1986), §20 (UNVERIFIED). `LeafPush2.T11b_Rigidity`
without its uniqueness clause, which `baseChange_map_injective` proves. -/
def T11bExists : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
    (A B : PkgI3.AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
    ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ

/-- **`T11b_Rigidity` from its existence half** (uniqueness: `baseChange_map_injective`). -/
theorem t11b_of_exists (h : T11bExists) : ZInQ.LeafPush2.T11b_Rigidity := by
  intro k _ _ _ L _ _ A B ψ hψ
  obtain ⟨φ, hφ, hφψ⟩ := h k L A B ψ hψ
  exact ⟨φ, ⟨hφ, hφψ⟩, fun φ' hφ' => baseChange_map_injective L (hφ'.2.trans hφψ.symm)⟩

/-- **`SerreRigidity3` from T35 and `HomLatticeCorr`** (with the proved `MulIsogeny`). Embed
`ℚ̄ ↪ ℂ`; `A(ℂ) = ℂ^g/Λ` (T35); `φ` acts by a `ℂ`-linear `M` (HomLatticeCorr, clause 1); `M`
preserves `Λ`, `M^m − 1` maps `ℂ^g` into `Λ`, and `M ≡ 1 (mod 3Λ)` because `3`-torsion of `A(ℂ)`
comes from `A(ℚ̄)`, where `φ` fixes it; Serre's lemma (`lattice_serre`) gives `M = 1`, so `φ`
fixes `A(ℂ)`, hence `A(ℚ̄)`, hence `φ = 1`. -/
theorem serreRigidity3_of_T35 (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HomUnify.HomLatticeCorr) : HeckeRest.SerreRigidity3 := by
  intro A φ hφ hfix
  obtain ⟨m, hm, hφm⟩ := hφ
  let σ : AlgebraicClosure ℚ →+* ℂ :=
    ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hdisc, hΛ, hΦ⟩ := hU (AlgebraicClosure ℚ) A σ g hg
  obtain ⟨M, hM⟩ := hC.1 (AlgebraicClosure ℚ) A A σ g g Λ Λ Φ Φ hg hg hΦ hΦ φ
  obtain ⟨hadd, hker, hsurj, -, -⟩ := hΦ
  have hdiff : ∀ a b, Φ a = Φ b → a - b ∈ Λ := by
    intro a b hab
    rw [← hker]
    have h := hadd (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_eq_right.1 h.symm
  have hMΛ : ∀ z ∈ Λ, M z ∈ Λ := by
    intro z hz
    rw [← hker, hM z, (hker z).2 hz, MonObj.one_comp]
  have hpowM : ∀ (k : ℕ) (z : Fin g → ℂ), Φ ((M ^ k) z) = Φ z ≫ (φ ^ k).hom := by
    intro k
    induction k with
    | zero =>
      intro z
      rw [pow_zero, pow_zero, Module.End.one_apply]
      exact (Category.comp_id _).symm
    | succ k ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, ih, hM z, pow_succ]
      exact Category.assoc _ _ _
  have hfin : ∀ z, (M ^ m) z - z ∈ Λ := by
    intro z
    refine hdiff _ _ ?_
    rw [hpowM, hφm]
    exact Category.comp_id _
  have h3 : ∀ z ∈ Λ, (3⁻¹ : ℂ) • (M z - z) ∈ Λ := by
    intro z hz
    set u : Fin g → ℂ := (3⁻¹ : ℂ) • z with hu
    have huz : u + u + u = z := by
      rw [hu, ← add_smul, ← add_smul]
      norm_num
    have hu3 : Φ u ^ 3 = 1 := by
      rw [pow_succ, pow_succ, pow_one, ← hadd, ← hadd, huz]
      exact (hker z).2 hz
    obtain ⟨y, hy⟩ := cpt_torsion_descends A σ 3 (by norm_num) (Φ u) hu3
    have hy3 : y ^ 3 = 1 := by
      apply sC_cancel σ
      rw [MonObj.comp_pow, hy, hu3, MonObj.comp_one]
    have hfu : Φ u ≫ φ.hom = Φ u := by
      rw [← hy, Category.assoc, hfix y hy3]
    have := hdiff (M u) u (by rw [hM u, hfu])
    rwa [hu, map_smul, ← smul_sub] at this
  haveI := hdisc
  have hM1 : M = 1 := ZInQ.Contrib.AVB2.lattice_serre Λ hΛ M hMΛ h3 hm hfin
  have hC1 : ∀ x : ZInQ.LeafPush2.CPts A σ, x ≫ φ.hom = x := by
    intro x
    obtain ⟨z, rfl⟩ := hsurj x
    rw [← hM z, hM1, Module.End.one_apply]
  have hK1 : ∀ y : A.Pt (AlgebraicClosure ℚ), y ≫ φ.hom = y ≫ 𝟙 _ := by
    intro y
    apply sC_cancel σ
    rw [← Category.assoc, hC1, Category.comp_id]
  have hφ1 : φ.hom = 𝟙 _ := hom_ext_of_pts φ.hom (𝟙 _) hK1
  exact PkgI3.AbVar.Hom.ext' hφ1

end AVB2

end

end G0A2_e20_avb2

section G0A2_e30_kernel
/-! ## leaf-fold5: the chain's textbook fields from the kernel's av-b1, curves-g and neron-c theorems

Each theorem below has as its type the chain's own Prop (the field of `OpenTextbookLeaves4`) and is proved by
applying a kernel theorem (`ZInQKernel/Contrib/AVB1`, `CurvesG`, `NeronC`, imported), whose hypotheses are the
kernel's own leaf Props over the kernel's objects (`ZInQKernel/HDecomp/Objects.lean`). The chain's `PkgI3.AbVar`
is a copy of the kernel's; `HSyn.toAbVarK4` and `HSyn.ofAbVarK4` (leaf-fold4) pass between the two with the
same scheme, and Lean accepts the remaining identifications (`Hom`, `T`, `V`, `dim`, `baseChange`, ...) by
unfolding, as it did for leaf-fold4's T26. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### av-b1: T6, T7 from their algebraically closed forms; T8 from Poincaré's complement form -/

/-- **T6 from `HomFreeFiniteAlgClosed`** (Mumford §19 Thm 3 over an algebraically closed field; the kernel's
`ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed`). -/
theorem t6_of_algClosed5 (h : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : PkgI3.HomFreeFinite :=
  fun k _ A B => _root_.ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed h k (toAbVarK4 A) (toAbVarK4 B)

/-- **T7 from `CharPolyIndepOfEllAlgClosed`** (Mumford §19 Thm 4 over an algebraically closed field; the
kernel's `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed`). -/
theorem t7_of_algClosed5 (h : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) :
    PkgI3.CharPolyIndepOfEll :=
  fun k _ A φ => _root_.ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed h k (toAbVarK4 A) φ

/-- **T8 from `PoincareComplement` and `SimpleImageIsogeny`** (the kernel's
`ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`; the complement `Z` is the kernel's abelian
variety, read back with `ofAbVarK4`). -/
theorem t8_of_simpleImage5 (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement)
    (hSI : _root_.ZInQ.Contrib.AVB1.SimpleImageIsogeny) : PkgI3.PoincareReducibility := by
  intro k _ _ A J hA f hf
  obtain ⟨Z, g, hg⟩ := _root_.ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage hP hSI k
    (toAbVarK4 A) (toAbVarK4 J) hA f hf
  exact ⟨ofAbVarK4 Z, g, hg⟩

/-! ### curves-g: T38 with its rational-point clause proved; T34 from its two published halves -/

/-- **T38 from three textbook facts** (the kernel's `ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split`:
the rational-point clause is proved by the valuative criterion; (A) normal models of function fields, (B) normal
curves over `ℚ` are smooth, (C) geometric connectedness from the constant field). `X1Belyi.CurveOfFunctionFieldQ`
is over Mathlib definitions and the class `IsCurve`, of which the chain has a copy (rebuilt field by field). -/
theorem t38_of_split5 (hA : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ)
    (hB : _root_.ZInQ.Contrib.CurvesG.NormalCurveSmoothQ)
    (hC : _root_.ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ) : X1Belyi.CurveOfFunctionFieldQ := by
  intro F _ _ _ hF
  obtain ⟨X, hX, hP, hI, he⟩ := _root_.ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split hA hB hC F hF
  exact ⟨X, ⟨hX.proper, hX.smooth, hX.geomConnected⟩, hP, hI, he⟩

/-- The chain's Jacobian property gives the kernel's, for the kernel's copy of the abelian variety. -/
theorem isJacobianK_of5 {X : Over (Spec (CommRingCat.of ℚ))}
    {P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X} {J : PkgI3.AbVar ℚ} {aj : X ⟶ J.X}
    (h : LeafModCurves.IsJacobian X P₀ J aj) :
    _root_.LeafModCurves.IsJacobian X P₀ (toAbVarK4 J) aj :=
  ⟨h.base, fun A f hf => h.univ (ofAbVarK4 A) f hf⟩

/-- **T34 from its two halves** (the kernel's `ZInQ.Contrib.CurvesG.dimJ1Genus_of_split`: `dim Jac X = genus`
for curves over `ℚ`, and the genus of `K_N` is the genus of `Γ₁(N)`). -/
theorem t34_of_split5 (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (h2 : _root_.ZInQ.Contrib.CurvesG.GenusX1Field) : LeafModCurves.DimJ1Genus := by
  rintro N J hN ⟨X, P₀, aj, hX, hJ⟩
  exact _root_.ZInQ.Contrib.CurvesG.dimJ1Genus_of_split h1 h2 N (toAbVarK4 J) hN
    ⟨X, P₀, aj, ⟨⟨hX.1.proper, hX.1.smooth, hX.1.geomConnected⟩, hX.2⟩, isJacobianK_of5 hJ⟩

/-! ### neron-c: T3 from its surjective half; T41 from the scheme-level Néron extension property -/

/-- **T3 from `NeronMappingAbelianSchemeSurj`** (BLR §1.2 Prop. 8, surjective half; the injective half is
the kernel's proved `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective`). The two `IsAbelianScheme`
classes are copies; only the instances are transported. -/
theorem t3_of_surj5 (h : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}) :
    PkgI2.NeronMappingAbelianScheme.{0} := by
  intro K _ O _ 𝒜 ℬ h𝒜 hℬ
  haveI : _root_.PkgI2.IsAbelianScheme 𝒜 := ⟨h𝒜.proper, h𝒜.smooth, h𝒜.geomConnected⟩
  haveI : _root_.PkgI2.IsAbelianScheme ℬ := ⟨hℬ.proper, hℬ.smooth, hℬ.geomConnected⟩
  exact _root_.ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj h K O 𝒜 ℬ

/-- **T41 from `NeronSchemeExtensionExists`** (BLR §1.4 Thm 3 at the level of schemes; the group law and the
uniqueness of extensions are the kernel's proved `ZInQ.Contrib.NeronC.neronModelExists_of_extension`). The
chain's `NeronModelExists` is over its copy `ZInQ.DefFaltings.AbVar` (h5-neron); the kernel's abelian variety
`⟨A.X⟩` has the same scheme, and the kernel's Néron model is read as the chain's `GroupModel` of `A` (same fields). -/
theorem t41_of_extension5 (h : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    ZInQ.H5Neron.NeronModelExists := by
  intro K _ A L _ _ _
  obtain ⟨𝒩, h𝒩⟩ := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension h K ⟨A.X⟩ L
  exact ⟨⟨𝒩.G, 𝒩.gen, 𝒩.gen_hom⟩, h𝒩⟩

end HSyn

end

end G0A2_e30_kernel

section G0A2_e40_kernelfields
/-! ## leaf-fold5 (c): fields restated over the kernel's own Props

The chain's Props below are verbatim copies (inside `namespace HDec`) of kernel declarations
(`ZInQKernel/HDecomp/Objects.lean`, `ZInQKernel/HDecomp/LeafPush2/`, `ZInQKernel/HDecomp/ModCurves/`). They are
not definitionally equal to the kernel's, because the structures and classes they quantify over (`PkgI3.AbVar`,
`PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme`, `LeafModCurves.IsCurve`, `IsJacobian`) are copies too. Each
theorem derives the chain's Prop from the kernel's, so that leaf-fold5's bundles can take the kernel's Prop as the
field: the instances are rebuilt field by field and abelian varieties are passed with `toAbVarK4`/`ofAbVarK4`
(same scheme). -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Group B / C: the PkgI2 leaves (over Mathlib's `Grp` and the class `IsAbelianVariety`) -/

/-- T5 (`TorsionStructure`, Mumford §4) from the kernel's statement. -/
theorem torsionStructure_ofK5 (h : _root_.PkgI2.TorsionStructure.{0}) : PkgI2.TorsionStructure.{0} := by
  intro K _ A hA g n hg hn hnK
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K A g n hg hn hnK

/-- T4 (`ReductionTorsionBijective`) from the kernel's statement. -/
theorem reductionTorsionBijective_ofK5 (h : _root_.PkgI2.ReductionTorsionBijective.{0}) :
    PkgI2.ReductionTorsionBijective.{0} := by
  intro K _ O _ w hw A hA 𝒜 h𝒜 e m hm hmO
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  haveI : _root_.PkgI2.IsAbelianScheme 𝒜 := ⟨h𝒜.proper, h𝒜.smooth, h𝒜.geomConnected⟩
  exact h K O w hw A 𝒜 e m hm hmO

/-- R6 (`RaynaudCriterion`, SGA 7 IX 4.7) from the kernel's statement. -/
theorem raynaudCriterion_ofK5 (h : _root_.PkgI2.RaynaudCriterion.{0}) : PkgI2.RaynaudCriterion.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K O w hw A

/-- The kernel's `HasGoodReduction` is the chain's (the class `IsAbelianScheme` inside it is a copy). -/
theorem hasGoodReduction_iffK5 {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) :
    _root_.PkgI2.HasGoodReduction A O ↔ PkgI2.HasGoodReduction A O :=
  ⟨fun ⟨𝒜, h, e⟩ => ⟨𝒜, ⟨h.proper, h.smooth, h.geomConnected⟩, e⟩,
   fun ⟨𝒜, h, e⟩ => ⟨𝒜, ⟨h.proper, h.smooth, h.geomConnected⟩, e⟩⟩

/-- R7(a) (`NeronOggShafarevich`, Serre–Tate 1968 Thm 1) from the kernel's statement. -/
theorem neronOggShafarevich_ofK5 (h : _root_.PkgI2.NeronOggShafarevich.{0}) :
    PkgI2.NeronOggShafarevich.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  have h' := h K O w hw A
  rw [hasGoodReduction_iffK5] at h'
  exact h'

/-- R7(b) (`SerreTatePotentialGood`) from the kernel's statement. -/
theorem serreTatePotentialGood_ofK5 (h : _root_.PkgI2.SerreTatePotentialGood.{0}) :
    PkgI2.SerreTatePotentialGood.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  have h' := h K O w hw A
  simp only [hasGoodReduction_iffK5] at h'
  exact h'

/-- R8 (`GrothendieckMonodromy`, SGA 7 IX) from the kernel's statement. -/
theorem grothendieckMonodromy_ofK5 (h : _root_.PkgI2.GrothendieckMonodromy.{0}) :
    PkgI2.GrothendieckMonodromy.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K O w hw A

/-! ### Group B / D: the PkgI3 leaves (over `PkgI3.AbVar`) -/

set_option maxHeartbeats 8000000 in
/-- R9(a) (`FaltingsSemisimple`, Faltings 1983 Satz 3) from the kernel's statement. -/
theorem faltingsSemisimple_ofK5 (h : _root_.PkgI3.FaltingsSemisimple) : PkgI3.FaltingsSemisimple :=
  fun K _ _ A ℓ _ => h K (toAbVarK4 A) ℓ

/-- R9(b) (`FaltingsTate`, Faltings 1983 Satz 4, Kor. 1) from the kernel's statement. -/
theorem faltingsTate_ofK5 (h : _root_.PkgI3.FaltingsTate) : PkgI3.FaltingsTate :=
  fun K _ _ A B ℓ _ => h K (toAbVarK4 A) (toAbVarK4 B) ℓ

/-- T27 (`QMDichotomyYu`, Yu 2013 Thm 1.1) from the kernel's statement. -/
theorem qmDichotomyYu_ofK5 (h : _root_.PkgI3.QMDichotomyYu) : PkgI3.QMDichotomyYu :=
  fun k _ _ _ A hA a b hab hdiv hemb => h k (toAbVarK4 A) hA a b hab hdiv hemb

/-- T35 (`UniformizationExists`, `A(ℂ) ≅ ℂ^g/Λ`) from the kernel's statement. -/
theorem uniformizationExists_ofK5 (h : _root_.ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.LeafPush2.UniformizationExists :=
  fun K _ A σ g hg => h K (toAbVarK4 A) σ g hg

/-! ### Group G: Jacobians -/

/-- T33 (`JacobianExists ℚ`, Weil; Milne 1986 Thm 1.1, Prop. 6.1) from the kernel's statement. -/
theorem jacobianExists_ofK5 (h : _root_.LeafModCurves.JacobianExists ℚ) : LeafModCurves.JacobianExists ℚ := by
  intro X hX P₀
  obtain ⟨J, aj, hJ⟩ := h X ⟨hX.proper, hX.smooth, hX.geomConnected⟩ P₀
  exact ⟨ofAbVarK4 J, aj, ⟨hJ.base, fun A f hf => hJ.univ (toAbVarK4 A) f hf⟩⟩

end HSyn

end

#print axioms HSyn.torsionStructure_ofK5
#print axioms HSyn.reductionTorsionBijective_ofK5
#print axioms HSyn.raynaudCriterion_ofK5
#print axioms HSyn.hasGoodReduction_iffK5
#print axioms HSyn.neronOggShafarevich_ofK5
#print axioms HSyn.serreTatePotentialGood_ofK5
#print axioms HSyn.grothendieckMonodromy_ofK5
#print axioms HSyn.faltingsSemisimple_ofK5
#print axioms HSyn.faltingsTate_ofK5
#print axioms HSyn.qmDichotomyYu_ofK5
#print axioms HSyn.uniformizationExists_ofK5
#print axioms HSyn.jacobianExists_ofK5

end G0A2_e40_kernelfields

end HDec
