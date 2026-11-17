import ZInQKernel.Contrib.OneProof.MumfordKLFinite
import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.AbVarBC.Dim

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace PhiSurj

/-- **Dimension count.** A locally quasi-finite closed morphism `f : X → Y` of schemes, with `Y`
irreducible and `dim Y ≤ dim X = a < ∞`, is surjective: otherwise images of irreducible closed subsets of
`X` (strictly increasing, since fibres are discrete) followed by `Y` give a chain of length `a + 1` in `Y`. -/
theorem surjective_of_dim_le {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (hc : IsClosedMap f.base) [IrreducibleSpace Y] [Nonempty X] (a : ℕ)
    (hX : topologicalKrullDim X = a) (hY : topologicalKrullDim Y ≤ a) :
    Function.Surjective f.base := by
  by_contra hns
  have hrange : Set.range f.base ≠ Set.univ := fun h => hns (Set.range_eq_univ.mp h)
  let F : IrreducibleCloseds X → IrreducibleCloseds Y := fun Z =>
    ⟨f.base '' Z, Z.isIrreducible.image _ f.base.hom.continuous.continuousOn, hc _ Z.isClosed⟩
  have hF : StrictMono F := by
    intro Z W hZW
    have hsub : (Z : Set X) ⊆ W := hZW.le
    refine lt_of_le_of_ne (Set.image_mono hsub) ?_
    intro heq
    have heq' : f.base '' (Z : Set X) = f.base '' W := congrArg (fun T : IrreducibleCloseds Y => (T : Set Y)) heq
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
  let top : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  let G : WithTop (IrreducibleCloseds X) → IrreducibleCloseds Y := fun t => t.elim top F
  have hG : StrictMono G := by
    intro s t hst
    cases t with
    | top =>
      cases s with
      | top => exact absurd hst (lt_irrefl _)
      | coe Z =>
        change F Z < top
        refine lt_of_le_of_ne (fun _ _ => trivial) ?_
        intro h
        apply hrange
        apply Set.eq_univ_of_univ_subset
        intro y _
        have : y ∈ (F Z : Set Y) := by rw [h]; trivial
        obtain ⟨x, -, rfl⟩ := this
        exact ⟨x, rfl⟩
    | coe W =>
      cases s with
      | top => exact absurd hst (not_lt_of_ge le_top)
      | coe Z => exact hF (WithTop.coe_lt_coe.mp hst)
  have hle := Order.krullDim_le_of_strictMono G hG
  have : Nonempty (IrreducibleCloseds X) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  rw [Order.krullDim_WithTop] at hle
  change topologicalKrullDim X + 1 ≤ topologicalKrullDim Y at hle
  rw [hX] at hle
  have := hle.trans hY
  have h' : ((a + 1 : ℕ) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) := by exact_mod_cast this
  have h'' : a + 1 ≤ a := by exact_mod_cast h'
  omega


noncomputable section Torsion

open T09Pic PkgI3 PkgI3.AbVar PicDict HDec.WeilPairing

variable {K : Type} [Field K]

/-- `Spec K̄` over itself, as the unit object. -/
def unitIso : PkgI2.specOver (AlgebraicClosure K) (AlgebraicClosure K) ≅
    𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure K)))) :=
  Over.isoMk (Iso.refl _) (by simp [PkgI2.specOver])

/-- An abelian variety as a group object. -/
abbrev grpOf {k : Type} [Field k] (A : AbVar k) : Grp (Over (Spec (CommRingCat.of k))) := ⟨A.X⟩

theorem isAV {k : Type} [Field k] (A : AbVar k) : PkgI2.IsAbelianVariety (grpOf A) :=
  ⟨inferInstanceAs (IsProper A.X.hom), inferInstanceAs (Smooth A.X.hom),
    inferInstanceAs (GeometricallyIntegral A.X.hom)⟩

/-- `A(K̄) ≃ A_K̄(K̄)` in the `PkgI2` form. -/
def ptEquiv (A : AbVar K) :
    A.Pt (AlgebraicClosure K) ≃ PkgI2.Pts (grpOf (AKbar A)) (AlgebraicClosure K) :=
  Equiv.ofBijective (fun x => unitIso.hom ≫ pts x)
    ⟨fun x y h => pts_injective ((cancel_epi _).mp h), fun z => by
      obtain ⟨w, hw⟩ := pts_surjective (unitIso.inv ≫ z)
      exact ⟨w, by simp only [hw, Iso.hom_inv_id_assoc]⟩⟩

lemma ptEquiv_mul (A : AbVar K) (x y : A.Pt (AlgebraicClosure K)) :
    ptEquiv A (x * y) = ptEquiv A x * ptEquiv A y := by
  change unitIso.hom ≫ pts (x * y) = (unitIso.hom ≫ pts x) * (unitIso.hom ≫ pts y)
  rw [pts_mul, MonObj.comp_mul]

lemma ptEquiv_pow (A : AbVar K) (x : A.Pt (AlgebraicClosure K)) (n : ℕ) :
    ptEquiv A (x ^ n) = ptEquiv A x ^ n := by
  change unitIso.hom ≫ pts (x ^ n) = (unitIso.hom ≫ pts x) ^ n
  rw [map_pow (ptsHom A) x n |>.symm.trans rfl |> fun h => (show pts (x ^ n) = pts x ^ n from map_pow (ptsHom A) x n)]
  rw [MonObj.comp_pow]

lemma ptEquiv_one (A : AbVar K) : ptEquiv A 1 = 1 := by
  simpa using ptEquiv_pow A 1 0

/-- `A[n] ≃ A_K̄(K̄)[n]`. -/
def torsEquiv (A : AbVar K) (n : ℕ) :
    tors A n ≃ PkgI2.torsion (grpOf (AKbar A)) (AlgebraicClosure K) n :=
  Equiv.subtypeEquiv (Additive.toMul.trans (ptEquiv A)) (by
    intro x
    change n • x = 0 ↔ ptEquiv A (Additive.toMul x) ^ n = 1
    rw [← ptEquiv_pow, ← ptEquiv_one A, (ptEquiv A).injective.eq_iff]
    constructor
    · intro h; have := congrArg Additive.toMul h; simpa using this
    · intro h; apply Additive.toMul.injective; simpa using h)

lemma torsEquiv_add (A : AbVar K) (n : ℕ) (x y : tors A n)
    (h : (torsEquiv A n x).1 * (torsEquiv A n y).1 ∈ PkgI2.torsion (grpOf (AKbar A)) (AlgebraicClosure K) n) :
    torsEquiv A n (x + y) = ⟨_, h⟩ :=
  Subtype.ext (ptEquiv_mul A _ _)

/-- **`A[n] ≅ (ℤ/n)^{2g}`** for `A` over any field, from Mumford's theorem over `K̄` (the textbook leaf
`AvSplit.MumfordTorsionAlgClosed`) applied to `A_K̄`. -/
theorem exists_torsAddEquiv (hT : AvSplit.MumfordTorsionAlgClosed) (A : AbVar K) (g n : ℕ)
    (hg : topologicalKrullDim A.X.left = g) (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    Nonempty (tors A n ≃+ (Fin (2 * g) → ZMod n)) := by
  have hg' : topologicalKrullDim (grpOf (AKbar A)).X.left = g :=
    (ZInQ.Contrib.AbVarBC.dim_baseChange_scheme (AlgebraicClosure K) A.X.left A.X.hom).trans hg
  have hnK' : (n : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact (map_ne_zero _).mpr hnK
  have := isAV (AKbar A)
  obtain ⟨e, he⟩ := hT (AlgebraicClosure K) (grpOf (AKbar A)) g n hg' hn hnK'
  refine ⟨AddEquiv.mk' ((torsEquiv A n).trans e) ?_⟩
  intro x y
  simp only [Equiv.trans_apply]
  have hmem : (torsEquiv A n x).1 * (torsEquiv A n y).1 ∈
      PkgI2.torsion (grpOf (AKbar A)) (AlgebraicClosure K) n := by
    have h := (torsEquiv A n (x + y)).2
    have e1 : (torsEquiv A n (x + y)).1 = (torsEquiv A n x).1 * (torsEquiv A n y).1 :=
      ptEquiv_mul A _ _
    rwa [e1] at h
  rw [torsEquiv_add A n x y hmem, he]

lemma card_mu_le (n : ℕ) [NeZero n] : Nat.card (Mu K n) ≤ n := by
  rw [Nat.card_congr (Additive.toMul : Mu K n ≃ _)]
  exact card_rootsOfUnity _ _

/-- **Counting through a perfect pairing**: if `A[n] ≅ (ℤ/n)^m` and `e : A[n] × B[n] → μ_n` has trivial right
kernel, then `#B[n] ≤ n^m`. -/
theorem card_le_of_perfect {A B : AbVar K} {n : ℕ} [NeZero n] (e : Pairing A B n) (he : IsPerfect e)
    {m : ℕ} (E : tors A n ≃+ (Fin m → ZMod n)) : Nat.card (tors B n) ≤ n ^ m := by
  classical
  let basis : Fin m → tors A n := fun i => E.symm (Pi.single i 1)
  have hspan : ∀ x : tors A n, x = ∑ i, (E x i).val • basis i := by
    intro x
    apply E.injective
    rw [map_sum]
    simp only [map_nsmul, basis, AddEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    · intro i _ hij
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  let Φ : tors B n → (Fin m → Mu K n) := fun y i => e (basis i) y
  have hinj : Function.Injective Φ := by
    intro y y' h
    have hz : ∀ x, e x (y - y') = 0 := by
      intro x
      rw [hspan x, map_sum, AddMonoidHom.finsetSum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_nsmul, AddMonoidHom.nsmul_apply, map_sub]
      have := congrFun h i
      change e (basis i) y = e (basis i) y' at this
      rw [this, sub_self, smul_zero]
    exact sub_eq_zero.mp (he.2 _ hz)
  calc Nat.card (tors B n) ≤ Nat.card (Fin m → Mu K n) := Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card (Mu K n) ^ m := by simp [Nat.card_fun]
    _ ≤ n ^ m := Nat.pow_le_pow_left (card_mu_le n) m

end Torsion

section Main

open T09Pic PkgI3 PkgI3.AbVar PicDict HDec.WeilPairing

variable {K : Type} [Field K]

lemma exists_prime_ne_zero : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : K) ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨3, by norm_num, ?_⟩
    have : ((3 : ℕ) : K) = 2 + 1 := by push_cast; ring
    rw [this, h2, zero_add]
    exact one_ne_zero
  · exact ⟨2, le_rfl, by exact_mod_cast h2⟩

/-- **`dim Pic⁰ ≤ dim A`**: from the perfect pairing `A[ℓ] × Pic⁰[ℓ] → μ_ℓ` of `WeilPairingMumford` and the
torsion counts `#X[ℓ] = ℓ^{2 dim X}`. -/
theorem dim_le_of_weil (h4 : WeilPairingMumford) (hT : AvSplit.MumfordTorsionAlgClosed) {A : AbVar K}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    {B : AbVar K} {j : B.X ⟶ P} (hj : IsPicZero rep B j) (a b : ℕ)
    (ha : topologicalKrullDim A.X.left = a) (hb : topologicalKrullDim B.X.left = b) : b ≤ a := by
  obtain ⟨ℓ, hℓ2, hℓK⟩ := exists_prime_ne_zero (K := K)
  have hℓ0 : 0 < ℓ := by omega
  have : NeZero ℓ := ⟨by omega⟩
  obtain ⟨e, hperf, -⟩ := h4 K A P rep B j hj
  obtain ⟨EA⟩ := exists_torsAddEquiv hT A a ℓ ha hℓ0 hℓK
  obtain ⟨EB⟩ := exists_torsAddEquiv hT B b ℓ hb hℓ0 hℓK
  have h1 := card_le_of_perfect (e ℓ) (hperf ℓ hℓ0 hℓK) EA
  have h2 : Nat.card (tors B ℓ) = ℓ ^ (2 * b) := by
    rw [Nat.card_congr EB.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [h2] at h1
  have := (Nat.pow_le_pow_iff_right (by omega : 1 < ℓ)).mp h1
  omega

/-- **Main result.** `λ_L` is an isogeny for every ample `L` (`T09Pic.PhiAmpleIsogeny`), from the bundle's
`WeilPairingMumford` and the textbook leaf `AvSplit.MumfordTorsionAlgClosed`: finiteness is phi-ample's
`finite_ker_pts`; surjectivity is the dimension count `surjective_of_dim_le` with `dim B ≤ dim A`. -/
theorem phiAmpleIsogeny_of_weil (h4 : WeilPairingMumford) (hT : AvSplit.MumfordTorsionAlgClosed) :
    PhiAmpleIsogeny := by
  intro K _ A P rep B j hj L hL lam hlam
  obtain ⟨lam', hlam'⟩ := exists_hom_comp_eq_phiL rep hj L
  have hjm : Mono j := by
    have : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have he : lam = lam'.hom := by rw [← cancel_mono j, hlam, hlam']
  subst he
  have hfin := finiteOfFiniteKerPts K A B lam' (PhiAmple.finite_ker_pts rep hj hL hlam)
  refine ⟨hfin, ⟨?_⟩⟩
  have := hfin
  have : IsProper (lam'.hom.left ≫ B.X.hom) := by rw [Over.w lam'.hom]; infer_instance
  have : IsProper lam'.hom.left := IsProper.of_comp lam'.hom.left B.X.hom
  have : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := B.X.hom)
  have : Nonempty A.X.left := ⟨η[A.X].left (IsLocalRing.closedPoint K)⟩
  obtain ⟨a, ha⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨b, hb⟩ := PkgI3.AbVar.dim_finite B
  have hba := dim_le_of_weil h4 hT rep hj a b ha hb
  refine surjective_of_dim_le lam'.hom.left lam'.hom.left.isClosedMap a ha ?_
  have hb' : topologicalKrullDim B.X.left = b := hb
  rw [hb']
  exact_mod_cast hba

end Main

end PhiSurj

#print axioms PhiSurj.phiAmpleIsogeny_of_weil
