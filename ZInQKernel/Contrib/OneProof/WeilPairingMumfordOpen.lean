import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyOpen

/-!
# `weilPairingMumford` from L1, L2 and the torsion leaf (phisurj)

`PhiSurj.weilPairingMumford_of_open : T09Pic.PicRepresentableAbVar → T09Pic.PicZeroAbVar →
AvSplit.MumfordTorsionAlgClosed → T09Pic.WeilPairingMumford`.

The proof is pic-dict's assembly `PicDict.weilPairingMumford_of_printed` with every Mumford display now a theorem.
* §6 Cor. 4 and §8 (iv): `MumfordSquareMulN.lean`.
* §20 (formula, bilinearity) and §23: weil-proof.
* `PhiAmpleIsogeny`: `PhiAmpleIsogenyOpen.lean`.
* §20 nondegeneracy, two parts:
  * right kernel: descent, `AVDesc.formula_nondeg_right`, through pic-dict's bridge (`weilNondegRight_of_open`);
  * left kernel: by counting (`left_kernel_of_open`). `y ↦ e(·, y)` embeds `Pic⁰[n]` into `Hom(A[n], μ_n)`, and
    `#Pic⁰[n] = n^{2 dim B} = n^{2 dim A} ≥ #Hom(A[n], μ_n)` (torsion leaf, with `dim A = dim B` from the finite
    surjective `λ_L`). So the embedding is onto, and characters `(ℤ/n)^{2g} → μ_n` separate points.

The use of §8 Thm 1 (`MumfordPhiSurjectiveAC`) in pic-dict's assembly was only for this left kernel, so it is no
longer needed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace PhiSurj

open PicDict T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

/-- A locally quasi-finite closed morphism does not raise dimension. -/
theorem dim_le_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  let F : IrreducibleCloseds X → IrreducibleCloseds Y := fun Z =>
    ⟨f.base '' Z, Z.isIrreducible.image _ f.base.hom.continuous.continuousOn, hc _ Z.isClosed⟩
  have hF : StrictMono F := by
    intro Z W hZW
    have hsub : (Z : Set X) ⊆ W := hZW.le
    refine lt_of_le_of_ne (Set.image_mono hsub) ?_
    intro heq
    have heq' : f.base '' (Z : Set X) = f.base '' W :=
      congrArg (fun T : IrreducibleCloseds Y => (T : Set Y)) heq
    obtain ⟨z₀, hz₀⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
    obtain ⟨w₀, hw₀⟩ := QuasiSober.sober W.isIrreducible W.isClosed
    have hz₀W : z₀ ∈ (W : Set X) := hsub hz₀.mem
    have hw₀z₀ : w₀ ⤳ z₀ := hw₀.specializes hz₀W
    have hne : w₀ ≠ z₀ := by
      intro h
      subst h
      apply (ne_of_lt hZW)
      apply SetLike.coe_injective
      exact (isGenericPoint_def.mp hz₀).symm.trans (isGenericPoint_def.mp hw₀)
    have h1 := ZInQ.Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf f hw₀z₀ hne
    obtain ⟨z, hz, hfz⟩ : f.base w₀ ∈ f.base '' (Z : Set X) := by rw [heq']; exact ⟨w₀, hw₀.mem, rfl⟩
    have h2 : z₀ ⤳ z := hz₀.specializes hz
    have h3 : f.base z₀ ⤳ f.base w₀ := hfz ▸ h2.map f.base.hom.continuous
    have h4 : f.base w₀ ⤳ f.base z₀ := hw₀z₀.map f.base.hom.continuous
    exact h1 (h4.antisymm h3).eq
  exact Order.krullDim_le_of_strictMono F hF

/-- `dim A ≤ dim Pic⁰`: `λ_L` (very ample `L`) is finite. -/
theorem dim_ge_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) (hT : AvSplit.MumfordTorsionAlgClosed)
    {K : Type} [Field K] {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) : topologicalKrullDim A.X.left ≤ topologicalKrullDim B.X.left := by
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨hfin, -⟩ := phiAmpleIsogeny_of_open h1 h2 hT K A P rep B j hj L (veryAmpleIsAmple K A L hL)
    lam.hom hlam
  have : IsProper (lam.hom.left ≫ B.X.hom) := by rw [Over.w lam.hom]; infer_instance
  have : IsProper lam.hom.left := IsProper.of_comp lam.hom.left B.X.hom
  exact dim_le_of_lqf lam.hom.left lam.hom.left.isClosedMap

/-- An injective hom `ZMod n → μ_n(K̄)` (a primitive root). -/
theorem exists_zmod_mu_injective {K : Type} [Field K] {n : ℕ} [NeZero n] (hnK : (n : K) ≠ 0) :
    ∃ ψ : ZMod n →+ Mu K n, Function.Injective ψ := by
  have : NeZero (n : K) := ⟨hnK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) n
  let u : (AlgebraicClosure K)ˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)
  have hle : Subgroup.zpowers u ≤ rootsOfUnity n (AlgebraicClosure K) :=
    (Subgroup.zpowers_le).2 ((mem_rootsOfUnity _ _).2 hu.pow_eq_one)
  exact ⟨(Subgroup.inclusion hle).toAdditive.comp hu.zmodEquivZPowers.toAddMonoidHom,
    (Subgroup.inclusion_injective hle).comp hu.zmodEquivZPowers.injective⟩

/-- Characters `(ℤ/n)^m → μ_n` separate points. -/
theorem exists_char_ne_zero {G : Type*} [AddCommGroup G] {M : Type*} [AddCommGroup M] {n m : ℕ}
    (E : G ≃+ (Fin m → ZMod n)) (ψ : ZMod n →+ M) (hψ : Function.Injective ψ) (x : G) (hx : x ≠ 0) :
    ∃ χ : G →+ M, χ x ≠ 0 := by
  have hEx : E x ≠ 0 := fun h => hx (E.injective (h.trans (map_zero E).symm))
  obtain ⟨i, hi⟩ : ∃ i, E x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hEx (funext h)
  refine ⟨ψ.comp ((Pi.evalAddMonoidHom (fun _ => ZMod n) i).comp E.toAddMonoidHom), fun h => hi ?_⟩
  apply hψ
  rw [map_zero]
  exact h

/-- **The left kernel of a pairing `A[n] × Pic⁰[n] → μ_n` with trivial right kernel is trivial**, by counting:
`#Pic⁰[n] = n^{2 dim B} = n^{2 dim A} ≥ #Hom(A[n], μ_n)`, so `y ↦ e(·, y)` is onto, and characters separate points. -/
theorem left_kernel_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) (hT : AvSplit.MumfordTorsionAlgClosed)
    {K : Type} [Field K] {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) (e : Pairing A B n)
    (hR : ∀ y : tors B n, (∀ x, e x y = 0) → y = 0) :
    ∀ x : tors A n, (∀ y, e x y = 0) → x = 0 := by
  intro x hx
  by_contra hx0
  have : NeZero n := ⟨by omega⟩
  obtain ⟨a, ha⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨b, hb⟩ := PkgI3.AbVar.dim_finite B
  have ha' : topologicalKrullDim A.X.left = a := ha
  have hb' : topologicalKrullDim B.X.left = b := hb
  have hba := dim_le_of_open h1 h2 hT rep hj a b ha' hb'
  have hab : a ≤ b := by
    have := dim_ge_of_open h1 h2 hT rep hj
    rw [ha', hb'] at this
    exact_mod_cast this
  have hab' : a = b := le_antisymm hab hba
  obtain ⟨EA⟩ := exists_torsAddEquiv hT A a n ha' hn hnK
  obtain ⟨EB⟩ := exists_torsAddEquiv hT B b n hb' hn hnK
  let Φ : tors B n →+ (tors A n →+ Mu K n) := e.flip
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact hR y (fun x => DFunLike.congr_fun hy x)
  have hfinH : Finite (tors A n →+ Mu K n) := by
    have : Finite (tors A n) := Finite.of_equiv _ EA.symm.toEquiv
    exact DFunLike.finite _
  have hcard : Nat.card (tors A n →+ Mu K n) ≤ Nat.card (tors B n) := by
    calc Nat.card (tors A n →+ Mu K n) ≤ Nat.card (Mu K n) ^ (2 * a) := AVDesc.card_hom_le EA
      _ ≤ n ^ (2 * a) := Nat.pow_le_pow_left (card_mu_le n) _
      _ = Nat.card (tors B n) := by
          rw [Nat.card_congr EB.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
            Fintype.card_fin, hab']
  have hsurj : Function.Surjective Φ := (hΦ.bijective_of_nat_card_le hcard).2
  obtain ⟨ψ, hψ⟩ := exists_zmod_mu_injective (n := n) hnK
  obtain ⟨χ, hχ⟩ := exists_char_ne_zero EA ψ hψ x hx0
  obtain ⟨y, hy⟩ := hsurj χ
  apply hχ
  rw [← hy]
  exact hx y

/-- The right half of Mumford §20 nondegeneracy at `A_K̄`, in pic-dict's coordinates. -/
theorem weilNondegRight_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) :
    ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
      ∀ c : (AK A).Pic, IsDualTors n c → (∀ (x : tors A n) (ψ : Triv A n c), weilFormula x c ψ = 1) →
        c = 1 := by
  intro K _ A n hn hnK c hc hx
  have hc' := (isDT_iff n c).2 hc
  obtain ⟨ψ'⟩ := AVDesc.nonempty_triv_ac (X := AKbar A) (n := n) (c := c)
    (by rw [mumfordMulNPicZeroAC_of_open h1 h2 _ (AKbar A) c hc'.1 n, hc'.2])
  refine AVDesc.formula_nondeg_right (AKbar A) n (natCast_ne_zero_bar hnK) c ψ' (fun σ hσ => ?_)
  obtain ⟨y, rfl⟩ := pts_surjective σ
  obtain ⟨ψ, rfl⟩ := triv_surj ψ'
  have hy : Additive.ofMul y ∈ tors A n := by
    rw [mem_tors]
    apply Additive.toMul.injective
    apply pts_injective
    rw [toMul_nsmul, toMul_ofMul, pts_pow, hσ, toMul_zero]
    exact (map_one (ptsHom A)).symm
  exact (formula_congr_pt rfl _ _ _ _).trans ((formula_bridge ⟨_, hy⟩ c ψ).trans (hx ⟨_, hy⟩ ψ))

theorem weilPairingMumford_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (hT : AvSplit.MumfordTorsionAlgClosed) : WeilPairingMumford := by
  have hsq : MumfordSquare := mumfordSquare_of_ac (mumfordSquareAC_of_open h1 h2)
  have h8iv : MumfordMulNPicZero := mumfordMulNPicZero_of_ac (mumfordMulNPicZeroAC_of_open h1 h2)
  have hamp : AmpleBaseChangeAlgClosure := ampleBaseChangeAlgClosure
  have h20a : MumfordWeilPairing := mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof
  have h23 : MumfordWeilAlt := mumfordWeilAlt_of_ac WeilProof.Theta.mumfordWeilAltAC_proof
  have h3 : PhiAmpleIsogeny := phiAmpleIsogeny_of_open h1 h2 hT
  have h20bR := weilNondegRight_of_open h1 h2
  classical
  have h20d := mumfordWeilDual_of_pairing h20a
  have h20c := mumfordWeilCompat_of_pairing h20a
  intro K _ A P rep B j hj
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  have hLa := veryAmpleIsAmple K A L hL
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨hfin, hsurj⟩ := h3 K A P rep B j hj L hLa lam.hom hlam
  -- `B(K̄) ⊆ Pic⁰(A_K̄)`
  have hsub : ∀ y, IsTranslInv (picClass rep j y) := fun y => by
    obtain ⟨x, rfl⟩ := exists_lift_pt lam.hom hsurj y
    rw [picClass_phiL rep L lam.hom hlam x]
    exact phiPt_translInv (hsq K A) _ x
  have hone : picClass rep j 1 = 1 := map_one (picHom rep hj)
  have htors : ∀ (n : ℕ) (y : tors B n),
      IsDualTors n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) := fun n y => by
    refine ⟨hsub _, ?_⟩
    rw [← picHom_apply rep hj, ← map_pow, ← toMul_nsmul, nsmul_tors y]
    exact hone
  have htriv : ∀ (n : ℕ) (y : tors B n),
      Nonempty (Triv A n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))) :=
    fun n y => nonempty_triv (by rw [h8iv K A _ (hsub _) n, (htors n y).2])
  have hspec : ∀ (n : ℕ) (x : tors A n) (y : tors B n),
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) =
        weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) (htriv n y).some := by
    intro n x y
    unfold weilScalar
    rw [dite_eq_left (transl_left_comp_mulN_left x)]
    exact dite_eq_left (htriv n y)
  have hval : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧ constK A (u : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) := by
    intro n hn hnK x y
    rw [hspec]
    exact (h20a K A n hn hnK x x _ _ (htors n y) (htors n y)).2.1 _
  choose u hu1 hu2 using hval
  -- the values are pinned by `weilScalar`
  have hpin : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n)
      (v : (AlgebraicClosure K)ˣ), constK A (v : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) → u n hn hnK x y = v := by
    intro n hn hnK x y v hv
    exact Units.ext (constK_injective A ((hu2 n hn hnK x y).trans hv.symm))
  have hux : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x x' : tors A n) (y : tors B n),
      u n hn hnK (x + x') y = u n hn hnK x y * u n hn hnK x' y := by
    intro n hn hnK x x' y
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    exact ((h20a K A n hn hnK x x' _ _ (htors n y) (htors n y)).2.2.1 _).symm
  have huy : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y y' : tors B n),
      u n hn hnK x (y + y') = u n hn hnK x y * u n hn hnK x y' := by
    intro n hn hnK x y y'
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    have hc : picClass rep j (Additive.toMul ((y + y' : tors B n) : HDec.WeilPairing.P B)) =
        picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)) *
          picClass rep j (Additive.toMul (y' : HDec.WeilPairing.P B)) :=
      picClass_mul rep hj _ _
    rw [← weilFormula_congr x hc]
    exact ((h20a K A n hn hnK x x _ _ (htors n y) (htors n y')).2.2.2 _ _ _).symm
  let e : ∀ n : ℕ, Pairing A B n := fun n =>
    if h : 0 < n ∧ (n : K) ≠ 0 then
      mkPairing (u n h.1 h.2) (hu1 n h.1 h.2) (hux n h.1 h.2) (huy n h.1 h.2)
    else 0
  have he : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      (e n x y).val = u n hn hnK x y := by
    intro n hn hnK x y
    simp only [e, dif_pos (And.intro hn hnK), mkPairing_val]
  have he0 : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      e n x y = 0 ↔ weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))
        (htriv n y).some = 1 := by
    intro n hn hnK x y
    constructor
    · intro h
      have h1 := he n hn hnK x y
      rw [h, Mu.val_zero] at h1
      rw [← hspec, ← hu2 n hn hnK x y, ← h1]
      simp
    · intro h
      apply Mu.val_injective
      rw [he n hn hnK x y, Mu.val_zero]
      apply hpin
      rw [hspec, h]
      simp
  -- independence of the trivialization
  have hind : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (c : (AK A).Pic),
      IsDualTors n c → ∀ ψ ψ' : Triv A n c, weilFormula x c ψ = weilFormula x c ψ' :=
    fun n hn hnK x c hc ψ ψ' => (h20a K A n hn hnK x x c c hc hc).1 ψ ψ'
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- perfect
    intro n hn hnK
    have hR : ∀ y : tors B n, (∀ x, e n x y = 0) → y = 0 := fun y hy => by
      have hc := h20bR K A n hn hnK _ (htors n y) (fun x ψ => by
        rw [hind n hn hnK x _ (htors n y) ψ (htriv n y).some]
        exact (he0 n hn hnK x y).1 (hy x))
      exact Subtype.ext (Additive.toMul.injective (picClass_injective rep hj (hc.trans hone.symm)))
    refine ⟨fun x hx => ?_, hR⟩
    exact left_kernel_of_open h1 h2 hT rep hj hn hnK (e n) hR x hx
  · -- Galois
    intro n hn hnK σ x y
    apply Mu.val_injective
    apply Units.ext
    rw [he n hn hnK, galMu_val, he n hn hnK]
    apply constK_injective A
    rw [hu2, hspec]
    have hg : picClass rep j (Additive.toMul ((galTors B n σ y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_gal rep j σ _
    obtain ⟨ψ', hψ'⟩ := weilFormulaGaloisEx K A n σ x _ _ hg (htriv n y).some _
      ((hspec n x y).symm.trans (hu2 n hn hnK x y).symm)
    rw [hind n hn hnK _ _ (htors n (galTors B n σ y)) _ ψ']
    exact hψ'
  · -- compatibility
    intro m n hm hn hmnK x y
    have hnK : (n : K) ≠ 0 := by
      intro h; apply hmnK; rw [Nat.cast_mul, h, mul_zero]
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    rw [he (m * n) hmn hmnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    exact (h20c K A m n hm hn hmnK x _ (htors n y) _ _).symm
  · -- adjoint
    intro f fv hfv n hn hnK x y
    apply Mu.val_injective
    rw [he n hn hnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    have hd : picClass rep j (Additive.toMul ((torsMap fv n y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (famMap f.hom (ptK K))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_dual rep j f.hom fv.hom hfv _
    rw [← weilFormula_congr x hd]
    exact (h20d K A n hn hnK f x _ (htors n y) _ _).symm
  · -- `e_n(x, λ_L x) = 1`
    intro L' hL' lam' hlam' n hn hnK x
    rw [he0 n hn hnK]
    have hp : picClass rep j (Additive.toMul ((torsMap lam' n x : tors B n) : HDec.WeilPairing.P B)) =
        phiPt (bcPic A L') (Additive.toMul (x : HDec.WeilPairing.P A)) :=
      picClass_phiL rep L' lam'.hom hlam' _
    rw [← weilFormula_congr x hp]
    exact h23 K A n hn hnK _ x _
  · -- the pin
    intro n hn hnK x y
    rw [he n hn hnK]
    exact hu2 n hn hnK x y

end PhiSurj

