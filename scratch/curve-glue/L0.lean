import ZInQKernel.HDecomp.QM.Pairs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# curve-glue, part 4: the leaf (L) `GlobalFunctionsConst` from finiteness of global sections

Task curve-glue (2026-11-13). `res`, `cst` and `GlobalFunctionsConst` are copied verbatim from
`scratch/curve-glue/C2K.lean`. The leaf (L) is reduced to the finiteness theorem for proper
morphisms (L0, `FiniteGlobalSections`, no smoothness, no algebraic closedness) plus two
Lean-proved lemmas: a connected finite algebra over an algebraically closed field is `K` plus
nilpotents (`exists_nilpotent_sub_of_finite`), and a section of `𝒪_X` over a preconnected open
that is idempotent is `0` or `1` (`idempotent_trivial_of_isPreconnected`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace

section Copied

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Restriction of sections along `O' ≤ O`, as a ring hom. -/
abbrev res {O O' : X.Opens} (h : O' ≤ O) : Γ(X, O) →+* Γ(X, O') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (s : Γ(X, O)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The constant section `a ∈ K` on `O`, through the structure morphism `f : X → Spec K`. -/
def cst (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) : Γ(X, O) :=
  res le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

end Copied

/-- **(L) "Liouville": regular functions on a connected component of a proper smooth curve over
an algebraically closed field are constant** (up to nilpotents, which is weaker than the printed
statement). `X → Spec K` proper and smooth of relative dimension 1, `K` algebraically closed,
`W ⊆ X` open, closed and (pre)connected, `s ∈ Γ(W, 𝒪_X)`: then `s − c` is nilpotent for some
constant `c ∈ K` (the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(W)`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED, recalled without network): `W` is a
proper connected `K`-scheme (an open and closed subscheme of a proper one), so `Γ(W, 𝒪_W)` is a
finite-dimensional `K`-algebra (finiteness of coherent cohomology for proper morphisms, EGA III
3.2.1; Hartshorne III.5.2 in the projective case) without nontrivial idempotents (`W`
connected), hence local Artinian with residue field `K` (`K` algebraically closed): every element
is a constant plus a nilpotent. With `W` reduced (smooth ⇒ reduced) this is the printed form
"`Γ(W, 𝒪_W) = K` for `W` proper, connected and reduced over `K = K̄`" (Stacks, Varieties, lemma
on `Γ` of a proper reduced connected scheme; Hartshorne Ex. II.4.5(d) for integral `W`; I.3.4
for projective varieties). Smoothness and dimension 1 are not needed; they are kept so that the
leaf is applied exactly where C2K is. Not in Mathlib v4.35 (no finiteness theorem for proper
morphisms). -/
def GlobalFunctionsConst : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ W : X.Opens, IsClopen (W : Set X) → _root_.IsPreconnected (W : Set X) →
      ∀ s : Γ(X, W), ∃ c : K, IsNilpotent (s - cst f W c)

/-! ## The leaf (L0) and the reduction -/

section L0

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- `cst f O` as a ring hom `K → Γ(X, O)` (the `K`-algebra structure of `Γ(X, O)`). -/
def cstHom (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) : K →+* Γ(X, O) :=
  (res le_top).comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem cstHom_apply (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) :
    cstHom f O a = cst f O a := rfl

end L0

/-- **(L0) Finiteness of global sections for proper schemes over a field.** If `X → Spec K` is
proper and `W ⊆ X` is open and closed, then `Γ(W, 𝒪_X)` is a finite `K`-module (for the
`K`-algebra structure through `X → Spec K`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED): the finiteness theorem for proper
morphisms, `f_* 𝓕` coherent for `𝓕` coherent and `f` proper (EGA III₁ 3.2.1; Stacks, *Cohomology
of Schemes*, "coherent sheaves on proper schemes"; Hartshorne II.5.20 / III.8.8 in the projective
case), applied to `𝓕 = 𝒪_W` (`W` is open and closed, hence a closed subscheme, so `W → Spec K` is
proper). Not in Mathlib v4.35. -/
def FiniteGlobalSections : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    ∀ W : X.Opens, IsClopen (W : Set X) → (cstHom f W).Finite

/-- **Algebra (Lean-proved): a connected finite algebra over an algebraically closed field is
`K` plus nilpotents.** In an Artinian ring with only the trivial idempotents every element is a
unit or nilpotent (Fitting: `s^n = s^{n+1} y` makes `s^n y^n` idempotent); and `s - c` is not a
unit for an eigenvalue `c` of multiplication by `s`. -/
theorem exists_nilpotent_sub_of_finite {K A : Type} [Field K] [IsAlgClosed K] [CommRing A]
    (φ : K →+* A) (hφ : φ.Finite) (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : A) : ∃ c : K, IsNilpotent (s - φ c) := by
  let _ := φ.toAlgebra
  have : Module.Finite K A := hφ
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  -- unit or nilpotent
  have key : ∀ x : A, IsUnit x ∨ IsNilpotent x := by
    intro x
    obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
    simp only [smul_eq_mul, mul_one] at hy
    replace hy : x ^ (n + 1) * y = x ^ n := hy
    have hpow : ∀ k : ℕ, x ^ n = x ^ (n + k) * y ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ih]
        calc x ^ (n + k) * y ^ k = (x ^ k * x ^ n) * y ^ k := by ring
          _ = (x ^ k * (x ^ (n + 1) * y)) * y ^ k := by rw [hy]
          _ = x ^ (n + (k + 1)) * y ^ (k + 1) := by ring
    have he : IsIdempotentElem (x ^ n * y ^ n) := by
      unfold IsIdempotentElem
      calc x ^ n * y ^ n * (x ^ n * y ^ n) = (x ^ (n + n) * y ^ n) * y ^ n := by ring
        _ = x ^ n * y ^ n := by rw [← hpow n]
    rcases hidem _ he with h0 | h1
    · right
      refine ⟨n, ?_⟩
      rw [hpow n]
      calc x ^ (n + n) * y ^ n = x ^ n * (x ^ n * y ^ n) := by ring
        _ = 0 := by rw [h0, mul_zero]
    · left
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have : x * y = 1 := by simpa using hy
        exact isUnit_iff_exists_inv.mpr ⟨y, this⟩
      · refine isUnit_iff_exists_inv.mpr ⟨x ^ (n - 1) * y ^ n, ?_⟩
        calc x * (x ^ (n - 1) * y ^ n) = x ^ (n - 1 + 1) * y ^ n := by ring
          _ = 1 := by rw [Nat.sub_add_cancel hn, h1]
  by_cases hA : Nontrivial A
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.mulLeft K s)
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hsv : s * v = φ c * v := by
      have := hv.apply_eq_smul
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using this
    refine ⟨c, (key (s - φ c)).resolve_left fun hu => hv0 ?_⟩
    have : (s - φ c) * v = 0 := by rw [sub_mul, hsv, sub_self]
    exact (hu.mul_right_eq_zero).mp this
  · rw [not_nontrivial_iff_subsingleton] at hA
    exact ⟨0, ⟨1, Subsingleton.elim _ _⟩⟩

/-- **Topology/sheaves (Lean-proved): idempotent sections over a preconnected open are trivial.**
At each point the germ of an idempotent is `0` or `1` (local ring), so `W` is the disjoint union
of the open sets `D(e)` and `D(1 - e)`. -/
theorem idempotent_trivial_of_isPreconnected {X : Scheme.{0}} {W : X.Opens}
    (hW : _root_.IsPreconnected (W : Set X)) (e : Γ(X, W)) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hcover : (W : Set X) ⊆ (X.basicOpen e : Set X) ∪ (X.basicOpen (1 - e) : Set X) := by
    intro x hx
    have hg : IsIdempotentElem (X.presheaf.germ W x hx e) := by
      unfold IsIdempotentElem; rw [← map_mul, he.eq]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ W x hx e) with hu | hu
    · exact Or.inl ((X.mem_basicOpen e x hx).2 hu)
    · right
      refine (X.mem_basicOpen (1 - e) x hx).2 ?_
      rwa [map_sub, map_one]
  have hdisj : Disjoint (X.basicOpen e : Set X) (X.basicOpen (1 - e) : Set X) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    have hxW : x ∈ W := X.basicOpen_le e h1
    have u1 := (X.mem_basicOpen e x hxW).1 h1
    have u2 := (X.mem_basicOpen (1 - e) x hxW).1 h2
    have h0 : X.presheaf.germ W x hxW e * X.presheaf.germ W x hxW (1 - e) = 0 := by
      rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero]
    exact not_isUnit_zero (h0 ▸ u1.mul u2)
  have hunit : ∀ a : Γ(X, W), (W : Set X) ⊆ (X.basicOpen a : Set X) → IsUnit a := by
    intro a ha
    refine X.toRingedSpace.isUnit_of_isUnit_germ W a fun x hx => ?_
    exact (X.mem_basicOpen a x hx).1 (ha hx)
  rcases hW.subset_or_subset (X.basicOpen e).isOpen (X.basicOpen (1 - e)).isOpen hdisj hcover
    with h | h
  · right
    obtain ⟨u, hu⟩ := hunit e h
    have : (u : Γ(X, W)) * u = u * 1 := by rw [mul_one, hu]; exact he.eq
    rw [← hu]; exact u.isUnit.mul_left_cancel this
  · left
    obtain ⟨u, hu⟩ := hunit (1 - e) h
    have he' : IsIdempotentElem (1 - e) := he.one_sub
    have : (u : Γ(X, W)) * u = u * 1 := by rw [mul_one, hu]; exact he'.eq
    have h1 : 1 - e = 1 := by rw [← hu]; exact u.isUnit.mul_left_cancel this
    rw [sub_eq_self] at h1; exact h1

/-- **(L) from (L0).** -/
theorem globalFunctionsConst_of (h : FiniteGlobalSections) : GlobalFunctionsConst := by
  intro K _ _ X f hP _ W hWc hWp s
  obtain ⟨c, hc⟩ := exists_nilpotent_sub_of_finite (cstHom f W) (h K X f hP W hWc)
    (fun e he => idempotent_trivial_of_isPreconnected hWp e he) s
  exact ⟨c, hc⟩

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.globalFunctionsConst_of
