import ZInQKernel.Contrib.OneProof.CMjReroute.Assemble
import ZInQKernel.Contrib.OneProof.CMjReroute.MatrixUnitRestrict

/-!
# Descent of the CM order to the model over `L` and to the matrix-unit curve

Let `A/L` be a model of the QM surface `P.A` of a CM fibre point (an isomorphism `θ : A_ℚ̄ ≅ P.A`,
every geometric endomorphism defined over `L`), and let `E` be the matrix-unit curve of `A`, with the
injective restriction `ρ : Z(End A) → End E` and `End(E_{L̄}) ≅ R ⊆ k`. The order `R' = q⁻¹(𝒪)` of the
CM point acts centrally on `P'.A`; through the ring isomorphisms `End(P'.A) ≅ End(P.A)` (rigidity),
`End(P.A) ≅ End(A_ℚ̄)` (conjugation by `θ`) and `End(A) ≅ End(A_ℚ̄)` (the model), it acts centrally on
`A`, hence on `E`, and its image `R₀ ⊆ R` is an order of `k` isomorphic to `R'`. So
`card Pic(R₀) = card Pic(R') ≤ 324`, `R₀ ≤ R`, and `R₀` is an imaginary quadratic order: exactly what the
consumer `faltingsHeight_le_bcm_of_sub` needs in place of `CMjDegree`.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT
open NumberField

/-- A ring isomorphism carries the centre into the centre. -/
theorem mem_center_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) {x : R}
    (hx : x ∈ Subring.center R) : e x ∈ Subring.center S := by
  rw [Subring.mem_center_iff] at hx ⊢
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, hx g']

/-- **The model**: `End(A) ≅ End(P.A)` for a model `A/L` of `P.A` over which every geometric
endomorphism is defined. -/
theorem model_equiv {L : Type} [Field L] [Algebra L Qbar] (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (θ : PkgI3.AbVar.Hom (A.baseChange Qbar) P.A) (θ' : PkgI3.AbVar.Hom P.A (A.baseChange Qbar))
    (h1 : θ.hom ≫ θ'.hom = 𝟙 _) (h2 : θ'.hom ≫ θ.hom = 𝟙 _)
    (hsurj : Function.Surjective (HDec.G0ModField.KernelField.endBC A Qbar)) :
    Nonempty (PkgI3.AbVar.End A ≃+* PkgI3.AbVar.End P.A) := by
  let e : P.A.X ≅ (A.baseChange Qbar).X := ⟨θ'.hom, θ.hom, h2, h1⟩
  have k1 : IsMonHom e.hom := inferInstanceAs (IsMonHom θ'.hom)
  have k2 : IsMonHom e.inv := inferInstanceAs (IsMonHom θ.hom)
  let eBC : PkgI3.AbVar.End A ≃+* PkgI3.AbVar.End (A.baseChange Qbar) :=
    RingEquiv.ofBijective (HDec.G0ModField.KernelField.endBC A Qbar)
      ⟨HDec.G0ModField.KernelField.endBC_injective A Qbar, hsurj⟩
  let eC : PkgI3.AbVar.End (A.baseChange Qbar) ≃+* PkgI3.AbVar.End P.A :=
    RingEquiv.ofBijective (conjEnd e k1 k2) ⟨conjEnd_injective e k1 k2, conjEnd_surjective e k1 k2⟩
  exact ⟨eBC.trans eC⟩

/-- A ring isomorphism between subrings of number fields keeps an integral non-integer non-rational. -/
theorem not_rat_of_ringEquiv {K k : Type} [Field K] [Field k] [CharZero k] {R : Subring K}
    {R₀ : Subring k} (hR₀ : R₀ ≤ (integralClosure ℤ k).toSubring) (e : R ≃+* R₀) {t : R}
    (ht : ∀ n : ℤ, t ≠ n) : ((e t : R₀) : k) ∉ Set.range (algebraMap ℚ k) := by
  rintro ⟨r, hr⟩
  have hint : IsIntegral ℤ (algebraMap ℚ k r) := by rw [hr]; exact hR₀ (e t).2
  have hint' : IsIntegral ℤ r :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
      (algebraMap ℚ k).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  apply ht n
  apply e.injective
  apply Subtype.ext
  rw [← hr, ← hn, map_intCast]
  simp

/-- **The descent.** For the data of a CM fibre point (as in `exists_cmOrder_card_pic_le_324`), a
model `A/L` of `P.A` with all geometric endomorphisms defined, and the matrix-unit curve `E` of `A`
with its CM order `R ⊆ k`: some order `R₀ ≤ R` of `k` has `card Pic(R₀) ≤ 324`. -/
theorem exists_suborder_card_pic_le_324
    (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDel : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hY3j : _root_.Y3P1j.Y3ToP1j)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) (r : ℚ) (y : fieldPt Qbar ⟶ Y)
    (hy : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar r))
    (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) {φ : PkgI3.AbVar.End P.A} (hφ : φ ∈ com P.q)
    (hne : ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End P.A))
    {L : Type} [Field L] [Algebra L Qbar] (A : PkgI3.AbVar L)
    (θ : PkgI3.AbVar.Hom (A.baseChange Qbar) P.A) (θ' : PkgI3.AbVar.Hom P.A (A.baseChange Qbar))
    (hθ1 : θ.hom ≫ θ'.hom = 𝟙 _) (hθ2 : θ'.hom ≫ θ.hom = 𝟙 _)
    (hsurj : Function.Surjective (HDec.G0ModField.KernelField.endBC A Qbar))
    {E : PkgI3.AbVar L} (ρ : Subring.center (PkgI3.AbVar.End A) →+* PkgI3.AbVar.End E)
    (hρ : Function.Injective ρ) {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) (eR : PkgI3.AbVar.End (E.baseChange (AlgebraicClosure L)) ≃+* R) :
    ∃ R₀ : Subring k, R₀ ≤ R ∧ IsImagQuadOrder k R₀ ∧ Nat.card (CommRing.Pic R₀) ≤ 324 := by
  obtain ⟨K, _, _, _, q, P', hK, hpic, ⟨T, -⟩, eD, hcen⟩ :=
    exists_cmOrder_card_pic_le_324 hModel hDel hY3j hR1 hR2 r y hy P hP hφ hne
  obtain ⟨eA⟩ := model_equiv A P θ θ' hθ1 hθ2 hsurj
  -- `R' = q⁻¹(𝒪) → End(A)`, injective with central image
  let χ : ordR q →+* PkgI3.AbVar.End A :=
    eA.symm.toRingHom.comp (T.symm.toRingHom.comp ((com P'.q).subtype.comp eD.toRingHom))
  have hχ : Function.Injective χ :=
    eA.symm.injective.comp (T.symm.injective.comp (Subtype.val_injective.comp eD.injective))
  have hχc : ∀ t, χ t ∈ Subring.center (PkgI3.AbVar.End A) := fun t =>
    mem_center_of_ringEquiv eA.symm (mem_center_of_ringEquiv T.symm (hcen t))
  have hZ : χ.range ≤ Subring.center (PkgI3.AbVar.End A) := by
    rintro _ ⟨t, rfl⟩
    exact hχc t
  obtain ⟨R₀, hle, ⟨eZ⟩⟩ := exists_le_of_center A ρ hρ R eR χ.range hZ
  let eR' : ordR q ≃+* χ.range := RingEquiv.ofBijective χ.rangeRestrict
    ⟨fun a b h => hχ (by simpa using congrArg Subtype.val h), χ.rangeRestrict_surjective⟩
  let e0 : ordR q ≃+* R₀ := eR'.trans eZ
  have hR₀int : R₀ ≤ (integralClosure ℤ k).toSubring := hle.trans hR.2.2.1
  -- a non-rational element of `R₀`
  obtain ⟨w, hw⟩ := exists_not_rat hK
  obtain ⟨D, hD, hDw⟩ := exists_natCast_mul_mem q w
  have ht : ∀ n : ℤ, (⟨(D : K) * w, hDw⟩ : ordR q) ≠ n := by
    intro n hn
    have h := congrArg Subtype.val hn
    simp only [SubringClass.coe_intCast] at h
    apply hw ((n : ℚ) / D)
    have hD' : (D : K) ≠ 0 := by exact_mod_cast hD.ne'
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hD', mul_comm, h]
  have hnq := not_rat_of_ringEquiv hR₀int e0 ht
  refine ⟨R₀, hle, ⟨hR.1, hR.2.1, hR₀int,
    FibreSplit.conductor_ne_zero_of_mem hR.2.1 R₀ hR₀int (e0 _).2 hnq⟩, ?_⟩
  rw [← Nat.card_congr (GR512Bridge.picCongr e0).toEquiv]
  exact hpic

end HDec.CMBranch.CMjReroute
