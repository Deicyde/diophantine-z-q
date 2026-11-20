import ZInQKernel.Contrib.OneProof.PicDictionary

/-!
# `PhiAmpleIsogeny` from Mumford §6 Application 1 in its printed form and §8 Thm 1 (pic-fix)
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicFix

open T09Pic PkgI3 PkgI3.AbVar PicDict

/-- **LEAF (printed form).** Mumford, *Abelian varieties*, §6, Application 1, direction (iv) ⇒ (ii): for `X` an
abelian variety over an algebraically closed field `k`, `D` an effective divisor and `L = 𝒪_X(D)` ample,
`K(L) = {x ∈ X(k) : t_x^*L ≅ L}` is finite. Stated for `L` with a nonzero global section `s` (on the integral
scheme `X`, `D = Z(s)` is an effective Cartier divisor and `L ≅ 𝒪_X(D)`; vendored
`Scheme.Modules.Hom.isInvertible_zeroLocus`, `Hom.nonempty_iso_dual_toModules_tensorObj`). UNVERIFIED numbering. -/
def MumfordKLFiniteSectionAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    (∃ s : 𝟙_ X.X.left.Modules ⟶ AC.modX c₀, s ≠ 0) →
    {x : AC.Kpt X | AC.phi c₀ x = 1}.Finite

section Glue

variable {X : Scheme.{0}}

/-- `[M^{⊗ n}] = [M]^n`. -/
theorem mk_tensorPow (M : X.Modules) [M.IsInvertible] (n : ℕ) :
    Scheme.Pic.mk (M.tensorPow n) = Scheme.Pic.mk M ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ', ← ih]
    exact Scheme.Pic.mk_tensorObj M (M.tensorPow n)

/-- Composing a section with an isomorphism does not change its zero scheme. -/
theorem zeroLocus_comp_iso {M N : X.Modules} [M.IsInvertible] [N.IsInvertible]
    (s : 𝟙_ X.Modules ⟶ M) (e : M ≅ N) :
    Scheme.Modules.Hom.zeroLocus (s ≫ e.hom) = Scheme.Modules.Hom.zeroLocus s :=
  (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso s (s ≫ e.hom)
    (Arrow.isoMk (Iso.refl _) e (by simp))).symm

/-- `Z(s^{⊗ m})` and `Z(s)` have the same support for `m > 0`. -/
theorem support_tensorPowSection {M : X.Modules} [M.IsInvertible] (s : 𝟙_ X.Modules ⟶ M) {m : ℕ}
    (hm : 0 < m) :
    (Scheme.Modules.Hom.zeroLocus (Scheme.Modules.tensorPowSection s m)).support =
      (Scheme.Modules.Hom.zeroLocus s).support := by
  ext x
  obtain ⟨U, hxU, -, e, he⟩ := Scheme.Modules.exists_isFreeGenerator M (TopologicalSpace.Opens.mem_top x)
  obtain ⟨f, hf⟩ := he.exists_smul_eq (s.app U.1 (Scheme.Modules.unitSectionsEquiv U.1 1))
  obtain ⟨E, hE, hE'⟩ := Scheme.Modules.exists_tensorPowSectionOne_eq_pow_smul s he hf.symm m
  have h1 := Scheme.Modules.Hom.ideal_zeroLocus s U (Scheme.Modules.isFreeGenerator_one U.1) he hf.symm
  have h2 := Scheme.Modules.Hom.ideal_zeroLocus (Scheme.Modules.tensorPowSection s m) U
    (Scheme.Modules.isFreeGenerator_one U.1) hE hE'
  change x ∈ (Scheme.Modules.Hom.zeroLocus _).support ↔ x ∈ (Scheme.Modules.Hom.zeroLocus _).support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, Scheme.IdealSheafData.mem_support_iff_of_mem hxU,
    h1, h2, Scheme.zeroLocus_span, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton,
    Scheme.zeroLocus_singleton]
  have hp : X.basicOpen (f ^ m) = X.basicOpen f := Scheme.basicOpen_pow X f hm
  rw [hp]

/-- **`L` ample ⇒ `L^n` ample** (`n > 0`; Stacks 01PT, UNVERIFIED), for the EGA/Stacks notion `IsAmple`. -/
theorem isAmple_pow (c : X.Pic) (hc : IsAmple X c) {n : ℕ} (hn : 0 < n) : IsAmple X (c ^ n) := by
  refine ⟨hc.1, fun x => ?_⟩
  obtain ⟨m, hm, s, hx, haff⟩ := hc.2 x
  let M := (fromSkeleton X.Modules).obj c.val
  have hk : Scheme.Pic.mk ((M.tensorPow m).tensorPow n) =
      Scheme.Pic.mk (((fromSkeleton X.Modules).obj (c ^ n).val).tensorPow m) := by
    rw [mk_tensorPow, mk_tensorPow, mk_tensorPow, Scheme.Pic.mk_fromSkeleton, Scheme.Pic.mk_fromSkeleton,
      ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).1 hk
  have hz : (Scheme.Modules.Hom.zeroLocus (Scheme.Modules.tensorPowSection s n ≫ e.hom)).support =
      (Scheme.Modules.Hom.zeroLocus s).support := by
    rw [zeroLocus_comp_iso, support_tensorPowSection _ hn]
  refine ⟨m, hm, Scheme.Modules.tensorPowSection s n ≫ e.hom, ?_, ?_⟩
  · rw [hz]; exact hx
  · rw [hz]; exact haff

/-- An ample class on a nonempty scheme has a power with a nonzero global section. -/
theorem exists_pow_section [Nonempty X] (c : X.Pic) (hc : IsAmple X c) :
    ∃ m, 0 < m ∧ ∃ s : 𝟙_ X.Modules ⟶ (fromSkeleton X.Modules).obj (c ^ m).val, s ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨m, hm, s, hx, -⟩ := hc.2 x
  let M := (fromSkeleton X.Modules).obj c.val
  have hk : Scheme.Pic.mk (M.tensorPow m) = Scheme.Pic.mk ((fromSkeleton X.Modules).obj (c ^ m).val) := by
    rw [mk_tensorPow, Scheme.Pic.mk_fromSkeleton, Scheme.Pic.mk_fromSkeleton]
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).1 hk
  refine ⟨m, hm, s ≫ e.hom, fun h0 => ?_⟩
  have h := (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).2 h0
  rw [zeroLocus_comp_iso] at h
  apply hx
  rw [h]
  trivial

end Glue

/-- `φ_{L^n}(x) = φ_L(x)^n`. -/
theorem phi_pow {k : Type} [Field k] {X : AbVar k} (c : X.X.left.Pic) (x : AC.Kpt X) (n : ℕ) :
    AC.phi (c ^ n) x = AC.phi c x ^ n := by
  simp only [AC.phi]
  rw [← Scheme.Pic.mapHom_apply, map_pow, Scheme.Pic.mapHom_apply, mul_pow, inv_pow]

/-- **`K(L)` finite for every ample `L`** from the printed form: `L^m` is ample with a nonzero section, and
`K(L) ⊆ K(L^m)`. -/
theorem mumfordKLFiniteAC_of_section (h : MumfordKLFiniteSectionAC) : MumfordKLFiniteAC := by
  intro k _ _ X c₀ hc₀
  have : Nonempty X.X.left :=
    ⟨η[X.X].left (show PrimeSpectrum k from Nonempty.some (inferInstance : Nonempty (PrimeSpectrum k)))⟩
  obtain ⟨m, hm, s, hs⟩ := exists_pow_section c₀ hc₀
  refine (h k X (c₀ ^ m) (isAmple_pow c₀ hc₀ hm) ⟨s, hs⟩).subset fun x hx => ?_
  change AC.phi (c₀ ^ m) x = 1
  rw [phi_pow, show AC.phi c₀ x = 1 from hx, one_pow]

/-- **Main result (`PhiAmpleIsogeny`)** from two of Mumford's statements over an algebraically closed field, each
in its printed form: §6 Application 1 (`K(L)` finite for `L = 𝒪(D)` ample, `D` effective) and §8 Thm 1. -/
theorem phiAmpleIsogeny_of_printed (hKL : MumfordKLFiniteSectionAC) (h8 : MumfordPhiSurjectiveAC) :
    PhiAmpleIsogeny :=
  phiAmpleIsogeny_final (mumfordKLFiniteAC_of_section hKL) h8

end PicFix

