import ZInQKernel.OneProof.H.TailB

/-! # gr14-narrow, chain-side helper: the forward row `R19Fwd` and reverse isogenies from a quasi-inverse

Task gr14-narrow (docs/research/gr14-narrow.md). This module imports only `ZInQKernel.OneProof.H.TailB` (hence
`LPrefix`, `TailA`), so that the fold can import it from `TailD` without bringing any new module (or instance)
into the chain earlier than before.

* `GapGR.R19Fwd`: the first conjunct of the kernel row `ZInQ.DefFaltings.R19_GaudronRemond` (the forward isogeny
  `A → B` of degree `≤ κ(A)`); `GapGR.r19Fwd_of_r19 : R19_GaudronRemond → R19Fwd`.
* `GapGR.transfer_core_fwd`: `HDec.HSyn.G0Split.transfer_core` (LPrefix) with `R19Fwd` in place of
  `R19_GaudronRemond`; the proof is the original one, whose only use of R19 is its first conjunct.
* `GapGR.isIsogeny_of_comp_eq_mul`: if `f` is an isogeny and `f ≫ g = [d]_A`, `g ≫ f = [d]_B` with `d ≥ 1`
  (characteristic `0`), then `g` is an isogeny (the end of `HDec.G0FibreSimple.end0Division_of_homFree`, TailA).
* `GapGR.isogenyReverseExists_of_weil`: the chain's interface `HDec.HSyn.G0RevIsog.IsogenyReverseExists` from the
  `K̄`-point quasi-inverse leaf `HDec.WeilPairing.IsogenyQuasiInverse` (the field `isogenyQuasiInverse` of
  `OpenAddedLeaves4`, itself derived from `milneIsogenyQuasiInverse` by `isogenyQuasiInverse_lf7`, TailX) and
  `MulIsogeny` (proved: `mulIsogeny_proved`, TailE). Morphisms of abelian varieties are determined by their
  `K̄`-points (`GapGR.hom_ext_of_points`, a verbatim copy of `AVGlue.hom_ext_of_points`, TailP L589).
-/

set_option linter.all false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GapGR

/-! ## §1 The forward row -/

/-- **The forward half of R19** (kernel objects: def-faltings' `stableFaltingsHeight`): the first conjunct of
`ZInQ.DefFaltings.R19_GaudronRemond` (HDecomp/Faltings/Leaves.lean L59), verbatim. -/
def R19Fwd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : ZInQ.DefFaltings.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → ZInQ.DefFaltings.stableFaltingsHeight A = x →
    (∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ) →
    ∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ ∧
      (ZInQ.DefFaltings.isogDeg φ : ℝ) ≤ ZInQ.DefFaltings.grKappa g (Module.finrank ℚ K) x

/-- **The kernel row R19 implies its forward half (proved).** -/
theorem r19Fwd_of_r19 (h : ZInQ.DefFaltings.R19_GaudronRemond) : R19Fwd :=
  fun K _ _ A B g x hg hx hiso => (h K A B g x hg hx hiso).1

open HDec.HSyn.G0Split ZInQ.DefFaltings in
/-- **E3-E4 numerics from the forward half of R19 (proved).** `HDec.HSyn.G0Split.transfer_core` (LPrefix L12153)
with `r19 : R19Fwd`; the proof is copied from there, with `obtain ⟨⟨ψ, hψ, hdeg⟩, -⟩` replaced by
`obtain ⟨ψ, hψ, hdeg⟩`. -/
theorem transfer_core_fwd (r19 : R19Fwd) (r20 : R20Lower) (r21 : R21_Bost)
    {L : Type} [Field L] [NumberField L] (J P A Z : ZInQ.DefFaltings.AbVar L) (g gZ : ℕ)
    (hJd : J.dim = (g : WithBot ℕ∞)) (hZd : Z.dim = (gZ : WithBot ℕ∞)) (hgZ : gZ ≤ g)
    (hg2 : 2 ≤ g) (φ : J.X ⟶ P.X) (hφ : IsIsogeny φ) (x y a z : ℝ)
    (hx : stableFaltingsHeight J = x) (hy : stableFaltingsHeight P = y)
    (hz : stableFaltingsHeight Z = z) (hadd : a + z ≤ y) {Q M N : ℝ} (hN1 : 1 ≤ N)
    (hN : N ≤ Q * M ^ 2) (hJav : x ≤ 13000000 * N ^ 12) (hgN : (g : ℝ) ≤ N ^ 2)
    (hd : (Module.finrank ℚ L : ℝ) ≤ Q * M) :
    GlueAssembly.NonCMOutput Q M a := by
  obtain ⟨ψ, hψ, hdeg⟩ := r19 L J P g x hJd hx ⟨φ, hφ⟩
  have hvar := r20 L J P ψ hψ x y hx hy
  have hB := r21 L Z gZ hZd
  rw [hz] at hB
  have hB' : -(3 / 2) * (gZ : ℝ) ≤ z := EReal.coe_le_coe_iff.mp hB
  set d := Module.finrank ℚ L with hdd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hg1 : 1 ≤ g := by omega
  have hκ := log_grKappa g d x hg1 hd1
  have hκ1 := one_le_grKappa g d x hg1 hd1
  have hlogdeg : Real.log (isogDeg ψ) ≤ Real.log (grKappa g d x) := by
    rcases Nat.eq_zero_or_pos (isogDeg ψ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hκ1
    · exact Real.log_le_log (by exact_mod_cast hpos) hdeg
  refine ⟨N, g, d, x, Real.log (isogDeg ψ), z, hN1, hN, hJav, by exact_mod_cast hg2, hgN,
    by exact_mod_cast hd1, hd, ?_, ?_, ?_⟩
  · rw [hκ] at hlogdeg; exact hlogdeg
  · have := hvar
    linarith
  · have hgZr : (gZ : ℝ) ≤ g := by exact_mod_cast hgZ
    linarith

/-! ## §2 A quasi-inverse of an isogeny is an isogeny -/

/-- `[n]_A` as a power of the identity in the group `Hom(A, A)` (copy of `AVGlue.natCast_hom`, TailP L629). -/
theorem natCast_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℕ) :
    (((n : ℤ) : PkgI3.AbVar.End A)).hom = (𝟙 A.X) ^ n := by
  rw [Int.cast_natCast]
  induction n with
  | zero => rw [Nat.cast_zero, PkgI3.AbVar.Hom.hom_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, PkgI3.AbVar.Hom.hom_add, ih, pow_succ]
    rfl

/-- **A quasi-inverse of an isogeny is an isogeny (proved; characteristic `0`).** If `f : A → B` is finite and
surjective and `g : B → A` satisfies `f ≫ g = [d]_A`, `g ≫ f = [d]_B` with `d ≥ 1`, then `g` is finite and
surjective: `[d]_B = g ≫ f` is finite (`MulIsogeny`) and `f` is separated (`A` is proper over `K`), so `g` is finite
(`IsFinite.of_comp`); `[d]_A = f ≫ g` is surjective, so `g` is surjective (`Surjective.of_comp`). This is the end of
`HDec.G0FibreSimple.end0Division_of_homFree` (TailA L1290-1327) with the roles of `f` and `g` exchanged. -/
theorem isIsogenyMor_of_comp_eq_mul (hMul : HDec.G0FibreSimple.MulIsogeny) {K : Type} [Field K] [CharZero K]
    {A B : PkgI3.AbVar K} (f : A.X ⟶ B.X) (g : B.X ⟶ A.X) (d : ℕ) (hd : 0 < d)
    (hfg : f ≫ g = (𝟙 A.X) ^ d) (hgf : g ≫ f = (𝟙 B.X) ^ d) : PkgI3.AbVar.IsIsogenyMor g := by
  have hd0 : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨-, hsurjA⟩ := hMul K A (d : ℤ) hd0
  obtain ⟨hfinB, -⟩ := hMul K B (d : ℤ) hd0
  rw [natCast_hom, ← hfg, Over.comp_left] at hsurjA
  rw [natCast_hom, ← hgf, Over.comp_left] at hfinB
  have hsep : IsSeparated (f.left ≫ B.X.hom) := by rw [Over.w f]; infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp (f := f.left) (g := B.X.hom)
  exact ⟨IsFinite.of_comp g.left f.left, Surjective.of_comp f.left g.left⟩

/-! ## §3 Morphisms of abelian varieties are determined by their `K̄`-points -/

/-- **Homomorphisms of abelian varieties are determined by their `K̄`-points** (glue, proved). Verbatim copy of
`AVGlue.hom_ext_of_points` (TailP L589-L627; TailP is not imported by the chain before TailX), with one added
line (the instance `IsReduced A.X.left`, found in TailP through `import Mathlib`). -/
theorem hom_ext_of_points {K : Type} [Field K] {A B : PkgI3.AbVar K} (u v : A.X ⟶ B.X)
    (H : ∀ z : A.Pt (AlgebraicClosure K), z ≫ u = z ≫ v) : u = v := by
  ext1
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  -- (gr14-narrow) TailP gets this instance from `import Mathlib`; here it is supplied by hand.
  haveI : IsReduced A.X.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom
  refine ext_of_fromSpecResidueField_eq u.left v.left B.X.hom (closedPoints A.X.left)
    (by rw [dense_iff_closure_eq]; exact closure_closedPoints) ?_ (by rw [Over.w u, Over.w v])
  intro x hx
  have hx' : IsClosed {x} := hx
  have hfin : IsFinite (A.X.left.fromSpecResidueField x ≫ A.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx'
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  set ι0 : CommRingCat.of K ⟶ A.X.left.residueField x :=
    Spec.preimage (A.X.left.fromSpecResidueField x ≫ A.X.hom) with hι0
  have hint : ι0.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hι0, Spec.map_preimage]; infer_instance
  letI : Algebra K (A.X.left.residueField x) := ι0.hom.toAlgebra
  haveI : Algebra.IsIntegral K (A.X.left.residueField x) := ⟨hint⟩
  let φ : A.X.left.residueField x →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hφι : ι0 ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    ext c; exact φ.commutes c
  let z : A.Pt (AlgebraicClosure K) :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x) (by
      change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x) ≫
        A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
      rw [Category.assoc, ← Spec.map_preimage (A.X.left.fromSpecResidueField x ≫ A.X.hom),
        ← hι0, ← Spec.map_comp]
      exact congrArg Spec.map hφι)
  have h2 := congrArg Over.Hom.left (H z)
  simp only [Over.comp_left, z, Over.homMk_left] at h2
  have h3 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x ≫ u.left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x ≫ v.left := by
    have h4 := h2
    erw [Category.assoc, Category.assoc] at h4
    exact h4
  haveI : Epi (Spec.map (CommRingCat.ofHom φ.toRingHom)) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi _).1 h3

/-- The two clauses of `HDec.WeilPairing.IsQuasiInverse` as identities of morphisms (as
`AVGlue.comp_eq_pow_of_isQuasiInverse`, TailP L639, for both clauses and the chain's `HDec.WeilPairing`). -/
theorem comp_eq_pow_of_isQuasiInverse {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : PkgI3.AbVar.Hom A B) (g : PkgI3.AbVar.Hom B A) (d : ℕ)
    (hq : HDec.WeilPairing.IsQuasiInverse f g d) :
    f.hom ≫ g.hom = (𝟙 A.X) ^ d ∧ g.hom ≫ f.hom = (𝟙 B.X) ^ d := by
  constructor
  · apply hom_ext_of_points
    intro z
    have := congrArg Additive.toMul (hq.2 (Additive.ofMul z))
    rw [toMul_nsmul, toMul_ofMul] at this
    rw [MonObj.comp_pow, Category.comp_id]
    exact this
  · apply hom_ext_of_points
    intro z
    have := congrArg Additive.toMul (hq.1 (Additive.ofMul z))
    rw [toMul_nsmul, toMul_ofMul] at this
    rw [MonObj.comp_pow, Category.comp_id]
    exact this

/-! ## §4 Reverse isogenies -/

/-- **Reverse isogenies from the `K̄`-point quasi-inverse leaf (proved).** Over a number field, an isogeny
`φ : A → B` has an isogeny `B → A`: the quasi-inverse `g` of `φ` (`HDec.WeilPairing.IsogenyQuasiInverse`) satisfies
`φ ≫ g = [d]`, `g ≫ φ = [d]` as morphisms (`comp_eq_pow_of_isQuasiInverse`), so `g` is finite and surjective
(`isIsogenyMor_of_comp_eq_mul`), and a homomorphism (`PkgI3.AbVar.Hom`). -/
theorem isogenyReverseExists_of_weil (hMul : HDec.G0FibreSimple.MulIsogeny)
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) : HDec.HSyn.G0RevIsog.IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨hmon, hfin, hsurj⟩ := hφ
  let A' := HDec.LeafAdopt.abVarEquiv K A
  let B' := HDec.LeafAdopt.abVarEquiv K B
  let f : PkgI3.AbVar.Hom A' B' := @PkgI3.AbVar.Hom.mk' K _ A' B' φ hmon
  obtain ⟨d, hd, g, hq⟩ := hQ K A' B' f ⟨hfin, hsurj⟩
  obtain ⟨hfg, hgf⟩ := comp_eq_pow_of_isQuasiInverse f g d hq
  have hg := isIsogenyMor_of_comp_eq_mul hMul f.hom g.hom d hd hfg hgf
  exact ⟨g.hom, inferInstanceAs (IsMonHom g.hom), hg.1, hg.2⟩

/-- **`ReverseIsogeny` (G17 after Poincaré) from the `K̄`-point quasi-inverse leaf (proved).** The replacement
for `HDec.HSyn.G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite` in `gluePieces_of_open4` (TailK L308). -/
theorem reverseIsogeny_of_weil (hMul : HDec.G0FibreSimple.MulIsogeny)
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) : HDec.HSyn.G0Split.ReverseIsogeny :=
  HDec.HSyn.G0RevIsog.reverseIsogeny_of_exists (isogenyReverseExists_of_weil hMul hQ)

end GapGR
