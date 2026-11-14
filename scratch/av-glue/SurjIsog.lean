import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# av-glue, part A: `SimpleSurjIsogeny` from three leaves

Check with `lake env lean scratch/av-glue/SurjIsog.lean` (needs the oleans of
`ZInQKernel.Contrib.AVB1.Poincare`: `lake build ZInQKernel.Contrib.AVB1.Poincare`).

§1 copies verbatim (namespace `AVGlue`) the glue Prop `SimpleSurjIsogeny` of
`ZInQKernel/Contrib/AVB1/Poincare.lean` and checks `Iff.rfl` against the original.
§2 states the leaves. §3 proves `SimpleSurjIsogeny` from
`PoincareComplement` (existing LEAF), `IsogenyQuasiInverse` (existing LEAF, scheme level) and
`KernelAbSubvariety` (new LEAF).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AVGlue

/-! ## §1. Verbatim copy -/

/-- **A nonzero surjective homomorphism out of a simple abelian variety is an isogeny**
(textbook; GLUE-level composite). Over a field of characteristic `0`, if `End⁰(A)` is a division
algebra (`EndDivision A`) and `h : A → B` is a nonzero surjective homomorphism, then `h` is finite
(and surjective). Sources (UNVERIFIED locators): `(ker h)⁰_red` is an abelian subvariety of `A`
(characteristic `0`); it is not `A` since `h ≠ 0`; it is `0` because a proper nonzero abelian
subvariety would give, by Poincaré (Mumford §19 Thm 1, Cor. 1; Milne 1986 Prop. 12.1) and an
isogeny quasi-inverse, a nonzero endomorphism of `A` that is not surjective; a surjective
homomorphism with finite kernel is finite (Milne 1986, Prop. 7.1; Mumford §6, Application 1). -/
def SimpleSurjIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k), _root_.PkgI3.EndDivision A →
    ∀ h : _root_.PkgI3.AbVar.Hom A B, h ≠ 0 → Surjective h.hom.left →
      _root_.PkgI3.AbVar.IsIsogenyMor h.hom

theorem simpleSurjIsogeny_iff : SimpleSurjIsogeny ↔ ZInQ.Contrib.AVB1.SimpleSurjIsogeny := Iff.rfl

/-! ## §2. Leaves -/

/-- (verbatim from `ZInQKernel/HDecomp/Faltings/Leaves.lean`, `ZInQ.DefFaltings.IsIsogeny`)
An isogeny: a homomorphism of group schemes, finite and surjective. -/
def IsIsogeny {K : Type} [Field K] {A B : _root_.PkgI3.AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left

/-- **LEAF (Mumford; Milne).** Verbatim text of `HSyn.G0RevIsog.IsogenyQuasiInverse`
(`scratch/av-b2/olean/TailA.lean` l. 1660; g0-revisog), with `ZInQ.DefFaltings.AbVar` (a
structure with the same five fields as `PkgI3.AbVar` in that assembly; in the kernel
`ZInQ.DefFaltings` opens `PkgI3 (AbVar)`) written `PkgI3.AbVar`.
An isogeny `φ : A → B` of abelian varieties over a field `K` (a homomorphism of group schemes
that is finite and surjective) has a quasi-inverse: an isogeny `ψ : B → A` and an integer `n ≥ 1`
(the degree of `φ`) with `ψ ∘ φ = [n]_A` and `φ ∘ ψ = [n]_B`. Here `[n]_A` is `(𝟙 A)ⁿ` in
Mathlib's group of morphisms into the group object `A`. Sources (numbers UNVERIFIED): Mumford,
*Abelian Varieties*, §7 Remark after Thm 4 / §8; Milne, *Abelian Varieties* (Cornell-Silverman
1986) §8 and Milne's notes *Abelian Varieties* (2008) I, Prop. 7.1, Remark 7.2 (any field). -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : _root_.PkgI3.AbVar K) (φ : A.X ⟶ B.X),
    IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n

/-- **LEAF (new; `(ker h)⁰_red` is an abelian subvariety).** Over a field of characteristic `0`,
if a homomorphism `h : A → B` of abelian varieties is not locally quasi-finite (equivalently, its
kernel is positive-dimensional), there is an abelian subvariety `C ⊆ A` of positive dimension
killed by `h`: an abelian variety `C` with a homomorphism `j : C → A` that is a closed immersion,
`0 < dim C`, and `h ∘ j = 0`. Take `C = (ker h)⁰_red`. Sources (UNVERIFIED locators): the reduced
identity component of a closed subgroup scheme of an abelian variety is an abelian subvariety
(Milne, *Abelian varieties*, Cornell-Silverman 1986, §8 / notes (2008) I §8; Mumford §8; reduced
⇒ smooth: Mumford §11 Thm 1 (Cartier), char `0`); the fibres of `h` over `k̄`-points are
translates of `ker h`, so `h` is quasi-finite iff `ker h` is finite (Mumford §4, Milne 1986 §7).
A consequence of these published statements, never stronger: `C` is existential. -/
def KernelAbSubvariety : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B), ¬ LocallyQuasiFinite h.hom.left →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

/-! ## §3. Products of abelian varieties (copied from `scratch/g0-product/Product.lean`) -/

/-- (verbatim from `scratch/g0-product/Product.lean`) Geometric integrality is stable under
composition `X → Y → S` when the first map is geometrically integral, flat and universally open
and the second is geometrically integral and locally of finite type. -/
theorem geometricallyIntegral_comp {X Y S : Scheme} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [GeometricallyIntegral h] [LocallyOfFiniteType h] :
    GeometricallyIntegral (g ≫ h) := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  have : IsIntegral (pullback h y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := h)) K y
  have : IsLocallyNoetherian (pullback h y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
  have hI : IsIntegral (pullback g (pullback.fst h y)) := inferInstance
  let e : Z ≅ pullback g (pullback.fst h y) :=
    hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y g).symm
  have : Nonempty Z := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- The product `C ×_k Z` (Mathlib's cartesian monoidal product in `Over (Spec k)`, product
group structure) as a `PkgI3.AbVar` (same proof as g0-product's `prodAbVar`). -/
noncomputable abbrev prodAbVar {K : Type} [Field K] (A Z : _root_.PkgI3.AbVar K) :
    _root_.PkgI3.AbVar K :=
  haveI : IsProper (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : Smooth (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (A.X ⊗ Z.X).hom := by
    rw [Over.tensorObj_hom]; exact geometricallyIntegral_comp _ _
  { X := A.X ⊗ Z.X }

/-! ## §4. Glue -/

section Glue

variable {k : Type} [Field k]

/-- The underlying scheme of an abelian variety is integral. -/
instance isIntegral_left (A : _root_.PkgI3.AbVar k) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) : IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

/-- If `j : C → A` is a closed immersion whose composite with a homomorphism `h` is `0` and `j`
is surjective, then `h = 0` (`A` is reduced). -/
theorem hom_eq_one_of_surjective {C A B : _root_.PkgI3.AbVar k} (j : C.X ⟶ A.X) (h : A.X ⟶ B.X)
    [IsClosedImmersion j.left] [Surjective j.left] (hjh : j ≫ h = 1) : h = 1 := by
  have : IsIso j.left := isIso_of_isClosedImmersion_of_surjective j.left
  have : IsIso ((Over.forget _).map j) := (inferInstance : IsIso j.left)
  have : IsIso j := isIso_of_reflects_iso j (Over.forget _)
  calc h = inv j ≫ (j ≫ h) := by simp
    _ = 1 := by rw [hjh, MonObj.comp_one]

/-- If `j : C → A` is an embedding whose composite with a finite map `m : A → A'` is constant
(`= 1`), then `C` is discrete, so `dim C ≤ 0`. -/
theorem dim_le_zero_of_comp_one {C A : _root_.PkgI3.AbVar k} (j : C.X ⟶ A.X)
    [IsClosedImmersion j.left] (m : A.X ⟶ A.X) [IsFinite m.left] (hjm : j ≫ m = 1) :
    C.dim ≤ 0 := by
  set e : A.X.left := (η[A.X]).left (Nonempty.some (inferInstance : Nonempty
    (Spec (CommRingCat.of k)))) with he
  have hsub : Set.range j.left ⊆ m.left ⁻¹' {e} := by
    rintro _ ⟨x, rfl⟩
    have h1 : (j ≫ m).left = (toUnit C.X ≫ η[A.X]).left := by rw [hjm, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 : (j.left ≫ m.left) x = ((toUnit C.X).left ≫ (η[A.X]).left) x := by rw [h1]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [h2, he]
    congr 1
    have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
      (inferInstance : Subsingleton (Spec (CommRingCat.of k)))
    exact Subsingleton.elim _ _
  have hdisc : _root_.IsDiscrete (m.left ⁻¹' {e}) := m.left.isDiscrete_preimage_singleton e
  have : DiscreteTopology (m.left ⁻¹' {e}) := hdisc.to_subtype
  have hemb : Topology.IsEmbedding (Set.codRestrict j.left _ fun x => hsub ⟨x, rfl⟩) :=
    j.left.isClosedEmbedding.isEmbedding.codRestrict _ _
  have : DiscreteTopology C.X.left := hemb.discreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology C.X.left

end Glue

/-- **`SimpleSurjIsogeny` from three leaves.** -/
theorem simpleSurjIsogeny_of_leaves (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny := by
  intro k _ _ A B hA h hh hsurj
  have hprop : IsProper h.hom.left := isProper_hom h.hom
  suffices hlqf : LocallyQuasiFinite h.hom.left from
    ⟨IsFinite.of_isProper_of_locallyQuasiFinite h.hom.left, hsurj⟩
  by_contra hnot
  obtain ⟨C, j, hjci, hCdim, hjh⟩ := hK k A B h hnot
  obtain ⟨Z, g, hφ⟩ := hP k A C j hjci
  set φ : (C.X ⊗ Z.X) ⟶ A.X := fst C.X Z.X ≫ j.hom * snd C.X Z.X ≫ g.hom with hφ_def
  have hφmon : IsMonHom φ := by
    change IsMonHom (lift (fst C.X Z.X ≫ j.hom) (snd C.X Z.X ≫ g.hom) ≫ μ[A.X])
    infer_instance
  obtain ⟨ψ, n, hn, ⟨hψmon, hψfin, hψsurj⟩, hφψ, hψφ⟩ := hQ k (prodAbVar C Z) A φ ⟨hφmon, hφ.1, hφ.2⟩
  -- the endomorphism `e = j ∘ pr₁ ∘ ψ`
  set e : A.X ⟶ A.X := ψ ≫ fst C.X Z.X ≫ j.hom with he_def
  haveI := hψmon
  haveI : IsMonHom e := by
    change IsMonHom (ψ ≫ fst C.X Z.X ≫ j.hom)
    infer_instance
  set E : _root_.PkgI3.AbVar.End A := _root_.PkgI3.AbVar.Hom.mk' e with hE_def
  haveI : IsClosedImmersion j.hom.left := hjci
  by_cases hE : E = 0
  · -- `e = 0` forces `j ∘ [n] = 0` with `[n] = φ ∘ ψ` finite, so `C` is discrete
    have he0 : e = 1 := by
      have := congrArg _root_.PkgI3.AbVar.Hom.hom hE
      simpa [hE_def] using this
    have hjn : j.hom ≫ ((𝟙 A.X) ^ n) = 1 := by
      have h1 : φ ≫ e = 1 := by rw [he0, MonObj.comp_one]
      have h2 : φ ≫ e = ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom := by
        rw [he_def, ← Category.assoc, hφψ]
      have h3 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ φ = j.hom := by
        rw [hφ_def, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd,
          Category.id_comp, MonObj.one_comp, _root_.mul_one]
      have h4 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom
          = 1 := by rw [← h2, h1, MonObj.comp_one]
      haveI : IsMonHom (fst C.X Z.X ≫ j.hom) := inferInstance
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp,
        ← Category.assoc, lift_fst, Category.id_comp] at h4
      rw [MonObj.comp_pow, Category.comp_id]
      exact h4
    have hfin : IsFinite ((𝟙 A.X) ^ n).left := by
      haveI := hψfin
      haveI : IsFinite φ.left := hφ.1
      rw [← hψφ, Over.comp_left]; infer_instance
    have := dim_le_zero_of_comp_one j.hom ((𝟙 A.X) ^ n) hjn
    exact absurd hCdim (not_lt.mpr this)
  · -- `e ≠ 0` is an isogeny, so `j` is surjective, so `h = 0`
    obtain ⟨-, hesurj⟩ := hA E hE
    have hjsurj : Surjective j.hom.left := by
      have h1 : Surjective (ψ.left ≫ (fst C.X Z.X ≫ j.hom).left) := by
        simpa [hE_def, he_def] using hesurj
      have h2 : Surjective (fst C.X Z.X ≫ j.hom).left := Surjective.of_comp ψ.left _
      rw [Over.comp_left] at h2
      exact Surjective.of_comp (fst C.X Z.X).left _
    apply hh
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [_root_.PkgI3.AbVar.Hom.hom_zero]
    exact hom_eq_one_of_surjective j.hom h.hom hjh

end AVGlue


/-! ## §5. Variant: the quasi-inverse on `K̄`-points (the assembly's existing leaf) -/

namespace AVGlue.WeilPairing

open _root_.PkgI3 _root_.PkgI3.AbVar

variable {K : Type} [Field K]

/-- (verbatim from weil-pairing, `scratch/av-b2/olean/TailB.lean` l. 5484) The group `A(K̄)`,
written additively. -/
abbrev P (A : AbVar K) : Type := Additive (A.Pt (AlgebraicClosure K))

/-- (verbatim, l. 5570) A homomorphism `f : A → B` acting on `K̄`-points. -/
noncomputable def homP {A B : AbVar K} (f : Hom A B) : P A →+ P B := MonoidHom.toAdditive (ptMap f)

/-- (verbatim, l. 5771) `ψ : Â → A` is a quasi-inverse of `λ` of exponent `d`: `λ ψ = [d]` on
`Â(K̄)` and `ψ λ = [d]` on `A(K̄)`. -/
def IsQuasiInverse {A B : AbVar K} (f : Hom A B) (g : Hom B A) (d : ℕ) : Prop :=
  (∀ z : P B, homP f (homP g z) = d • z) ∧ ∀ x : P A, homP g (homP f x) = d • x

/-- (verbatim, l. 5864; the canonical assembly's LEAF field `isogenyQuasiInverse`, H-54)
**Quasi-inverse of an isogeny.** For an isogeny `f : A → B` (finite and surjective) there are
`d ≥ 1` and `g : B → A` with `f g = [d]`, `g f = [d]` (take `d = deg f`, which kills `ker f`;
Mumford §7, Remark after Thm 4, and §8 Thm 1 (UNVERIFIED numbering); Milne 1986, Prop. 7.1 /
Rem. 8.4 (UNVERIFIED)). Stated on `K̄`-points, a consequence. -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A, IsQuasiInverse f g d

end AVGlue.WeilPairing

namespace AVGlue

section PointsExt

variable {K : Type} [Field K]

/-- **Homomorphisms of abelian varieties are determined by their `K̄`-points** (glue, proved):
two `K`-morphisms `u v : A → B` agreeing on `A(K̄)` are equal. Closed points of `A` are dense
(Jacobson), each closed point has a residue field finite over `K`, which embeds into `K̄`, and
`Spec K̄ → Spec κ(x)` is an epimorphism; Mathlib's `ext_of_fromSpecResidueField_eq`. -/
theorem hom_ext_of_points {A B : _root_.PkgI3.AbVar K} (u v : A.X ⟶ B.X)
    (H : ∀ z : A.Pt (AlgebraicClosure K), z ≫ u = z ≫ v) : u = v := by
  ext1
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
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

/-- `[n]` as the integer `n ∈ End A`. -/
theorem natCast_hom (A : _root_.PkgI3.AbVar K) (n : ℕ) :
    (((n : ℤ) : _root_.PkgI3.AbVar.End A)).hom = (𝟙 A.X) ^ n := by
  rw [Int.cast_natCast]
  induction n with
  | zero => rw [Nat.cast_zero, _root_.PkgI3.AbVar.Hom.hom_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, _root_.PkgI3.AbVar.Hom.hom_add, ih, pow_succ]
    rfl

/-- The second clause of `IsQuasiInverse` as an identity of morphisms. -/
theorem comp_eq_pow_of_isQuasiInverse {A B : _root_.PkgI3.AbVar K}
    (f : _root_.PkgI3.AbVar.Hom A B) (g : _root_.PkgI3.AbVar.Hom B A) (d : ℕ)
    (hq : WeilPairing.IsQuasiInverse f g d) : f.hom ≫ g.hom = (𝟙 A.X) ^ d := by
  apply hom_ext_of_points
  intro z
  have := congrArg Additive.toMul (hq.2 (Additive.ofMul z))
  rw [toMul_nsmul, toMul_ofMul] at this
  rw [MonObj.comp_pow, Category.comp_id]
  exact this

end PointsExt

/-- **`SimpleSurjIsogeny` from `PoincareComplement`, the assembly's `K̄`-point quasi-inverse leaf
and `KernelAbSubvariety`** (with the kernel's proved `MulIsogeny`, g9-abvarbc). -/
theorem simpleSurjIsogeny_of_leaves' (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny := by
  intro k _ _ A B hA h hh hsurj
  have hprop : IsProper h.hom.left := isProper_hom h.hom
  suffices hlqf : LocallyQuasiFinite h.hom.left from
    ⟨IsFinite.of_isProper_of_locallyQuasiFinite h.hom.left, hsurj⟩
  by_contra hnot
  obtain ⟨C, j, hjci, hCdim, hjh⟩ := hK k A B h hnot
  obtain ⟨Z, g, hφ⟩ := hP k A C j hjci
  set φ : (C.X ⊗ Z.X) ⟶ A.X := fst C.X Z.X ≫ j.hom * snd C.X Z.X ≫ g.hom with hφ_def
  haveI hφmon : IsMonHom φ := by
    change IsMonHom (lift (fst C.X Z.X ≫ j.hom) (snd C.X Z.X ≫ g.hom) ≫ μ[A.X])
    infer_instance
  obtain ⟨n, hn, ψH, hq⟩ := hQ k (prodAbVar C Z) A
    (_root_.PkgI3.AbVar.Hom.mk' (A := prodAbVar C Z) φ) hφ
  set ψ : A.X ⟶ (C.X ⊗ Z.X) := ψH.hom with hψ_def
  have hφψ : φ ≫ ψ = (𝟙 (C.X ⊗ Z.X)) ^ n := comp_eq_pow_of_isQuasiInverse _ ψH n hq
  set e : A.X ⟶ A.X := ψ ≫ fst C.X Z.X ≫ j.hom with he_def
  haveI : IsMonHom e := by
    change IsMonHom (ψH.hom ≫ fst C.X Z.X ≫ j.hom)
    infer_instance
  set E : _root_.PkgI3.AbVar.End A := _root_.PkgI3.AbVar.Hom.mk' e with hE_def
  haveI : IsClosedImmersion j.hom.left := hjci
  by_cases hE : E = 0
  · have he0 : e = 1 := by
      have := congrArg _root_.PkgI3.AbVar.Hom.hom hE
      simpa [hE_def] using this
    have hjn : j.hom ≫ ((𝟙 A.X) ^ n) = 1 := by
      have h1 : φ ≫ e = 1 := by rw [he0, MonObj.comp_one]
      have h2 : φ ≫ e = ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom := by
        rw [he_def, ← Category.assoc, hφψ]
      have h4 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫
          fst C.X Z.X ≫ j.hom = 1 := by rw [← h2, h1, MonObj.comp_one]
      haveI : IsMonHom (fst C.X Z.X ≫ j.hom) := inferInstance
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp,
        ← Category.assoc, lift_fst, Category.id_comp] at h4
      rw [MonObj.comp_pow, Category.comp_id]
      exact h4
    have hfin : IsFinite ((𝟙 A.X) ^ n).left := by
      rw [← natCast_hom]
      exact (ZInQ.Contrib.AbVarBC.mulIsogeny k A n (by exact_mod_cast hn.ne')).1
    have := dim_le_zero_of_comp_one j.hom ((𝟙 A.X) ^ n) hjn
    exact absurd hCdim (not_lt.mpr this)
  · obtain ⟨-, hesurj⟩ := hA E hE
    have hjsurj : Surjective j.hom.left := by
      have h1 : Surjective (ψ.left ≫ (fst C.X Z.X ≫ j.hom).left) := by
        simpa [hE_def, he_def] using hesurj
      have h2 : Surjective (fst C.X Z.X ≫ j.hom).left := Surjective.of_comp ψ.left _
      rw [Over.comp_left] at h2
      exact Surjective.of_comp (fst C.X Z.X).left _
    apply hh
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [_root_.PkgI3.AbVar.Hom.hom_zero]
    exact hom_eq_one_of_surjective j.hom h.hom hjh

end AVGlue

#print axioms AVGlue.simpleSurjIsogeny_of_leaves
#print axioms AVGlue.simpleSurjIsogeny_of_leaves'
