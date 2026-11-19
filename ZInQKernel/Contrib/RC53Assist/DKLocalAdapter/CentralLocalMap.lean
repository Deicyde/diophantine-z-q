import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalDuality

/-!
# The central local duality map as a finite product of literal per-place comparisons

The local duality map of the central Selmer pairing data,
`Cone(−ι : ∏_v U_v → ∏_v C(G_v, T))[−1] → Hom(∏_v U_v, ℤ₂)[−3]`,
`(u, x) ↦ (y ↦ tr(0, x ∪ ι y + h(u, y)))`, is identified, in every degree and for the same fixed
global trace `tr`, with the finite product over the places of the support of the per-place
literal comparisons

`ordinaryCone(ι_v) → Hom(U_v, ℤ₂)[−2]`, `(x, u) ↦ (y ↦ ℓ_v(x ∪ ι_v y))`,

built with the pure-local restriction `ℓ_v` of the same global trace.

The identification consists of:

* the regrouping `Cone(−∏ι_v)[−1] ≅ ∏_v Cone(−ι_v)[−1]`;
* the swap `Cone(−ι_v)[−1] ≅ ordinaryCone(ι_v)[−1]`, `(u, x) ↦ (x, u)`, which intertwines the
  differentials exactly once the map is negated;
* the identification `Hom(U_v, ℤ₂)[−2][−1] = Hom(U_v, ℤ₂)[−3]`, where the shift sign and the
  dual sign combine to the sign of the target;
* the dual of the finite product, `∏_v Hom(U_v, ℤ₂) ≅ Hom(∏_v U_v, ℤ₂)`, by summation;
* the decomposition of the global trace of a pure-local class as the sum of its pure-local
  traces, and the vanishing of the truncated isotropy term, because the conditions are
  concentrated in degrees `0` and `1`.

Consequently the central local duality map is a quasi-isomorphism exactly when every per-place
comparison is one. No local duality, isotropy or quasi-isomorphism conclusion is assumed here.

References: `diophantine_zq.tex`, lines 3413–3463; Nekovář, *Selmer complexes*, 1.1.3, 6.2–6.3.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory HomologicalComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (truncSub truncSub_of_eq truncGe2)

section IndexTransport

universe u
variable {R : Type u} [CommRing R]

/-- Transport between two equal degrees of one complex. -/
def castX (A : GCx R) {a b : ℤ} (h : a = b) : A.X a →ₗ[R] A.X b := by
  subst h
  exact LinearMap.id

theorem castX_rfl (A : GCx R) (a : ℤ) (x : A.X a) : castX A (rfl : a = a) x = x := rfl

theorem castX_castX (A : GCx R) {a b c : ℤ} (h : a = b) (h' : b = c) (x : A.X a) :
    castX A h' (castX A h x) = castX A (h.trans h') x := by
  subst h h'
  rfl

theorem castX_self (A : GCx R) {a : ℤ} (h : a = a) (x : A.X a) : castX A h x = x := rfl

theorem castX_bijective (A : GCx R) {a b : ℤ} (h : a = b) : Function.Bijective (castX A h) := by
  subst h
  exact Function.bijective_id

/-- Differentials commute with index transport. -/
theorem d_castX (A : GCx R) {a b a' b' : ℤ} (ha : a = a') (hb : b = b') (h : a + 1 = b)
    (h' : a' + 1 = b') (x : A.X a) :
    A.d a' b' h' (castX A ha x) = castX A hb (A.d a b h x) := by
  subst ha hb
  rfl

/-- A relation-indexed component is the diagonal component followed by index transport. -/
theorem GHom.f_eq_castX {A B : GCx R} (f : GHom A B) {a b : ℤ} (h : a = b) (x : A.X a) :
    f.f a b h x = castX B h (f.f a a rfl x) := by
  subst h
  rfl

/-- A relation-indexed component on a transported source. -/
theorem GHom.f_castX {A B : GCx R} (f : GHom A B) {a b c : ℤ} (h : a = b) (h' : b = c)
    (x : A.X a) : f.f b c h' (castX A h x) = f.f a c (h.trans h') x := by
  subst h h'
  rfl

end IndexTransport

section Generic

universe u
variable {R : Type u} [CommRing R]

/-- The negative of a cochain map. -/
def negGHom {U L : GCx R} (ι : GHom U L) : GHom U L where
  f i j h := -(ι.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    simp only [LinearMap.neg_apply, map_neg, ι.comm i i₁ j j₁ hij h₁ h₂ hj x]

/-- The shift `A[−1] → B[−1]` of a cochain map, `x ↦ f x`. -/
def shiftDownGHom {A B : GCx R} (g : GHom A B) : GHom (shiftDown A) (shiftDown B) where
  f i j h := by
    subst h
    exact g.f (i - 1) (i - 1) rfl
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change g.f (i₁ - 1) (i₁ - 1) rfl (-(A.d (i - 1) (i₁ - 1) (by omega) x)) =
      -(B.d (i - 1) (i₁ - 1) (by omega) (g.f (i - 1) (i - 1) rfl x))
    rw [map_neg, g.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x]

theorem shiftDownGHom_f {A B : GCx R} (g : GHom A B) {i j : ℤ} (h : i = j) (x : A.X (i - 1)) :
    (shiftDownGHom g).f i j h x = g.f (i - 1) (j - 1) (by omega) x := by
  subst h
  rfl

/-- **Quasi-isomorphy and acyclicity of the shifted cone are equivalent.** -/
theorem quasiIso_toCC_iff_coneAcyclic {A B : GCx R} (f : GHom A B) :
    QuasiIso (GHom.toCC f) ↔ GAcyclic (coneCx f) :=
  ⟨coneCx_acyclic_of_quasiIso f, quasiIso_of_cone_exact f⟩

/-- **Quasi-isomorphy is invariant under degreewise bijective cochain maps on both sides.**
If `f = β ∘ g ∘ α` degreewise, with `α` and `β` bijective in every degree, then `f` is a
quasi-isomorphism exactly when `g` is. -/
theorem quasiIso_toCC_iff_of_factor {A B A' B' : GCx R} (f : GHom A B) (g : GHom A' B')
    (α : GHom A A') (β : GHom B' B)
    (hα : ∀ n, Function.Bijective (α.f n n rfl)) (hβ : ∀ n, Function.Bijective (β.f n n rfl))
    (hfac : ∀ n x, f.f n n rfl x = β.f n n rfl (g.f n n rfl (α.f n n rfl x))) :
    QuasiIso (GHom.toCC f) ↔ QuasiIso (GHom.toCC g) := by
  have e : GHom.toCC f = GHom.toCC α ≫ GHom.toCC g ≫ GHom.toCC β := by
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun n x => hfac n x
  have : IsIso (GHom.toCC α) := by
    have : ∀ n, IsIso ((GHom.toCC α).f n) := fun n =>
      (ConcreteCategory.isIso_iff_bijective _).2 (hα n)
    exact HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (GHom.toCC β) := by
    have : ∀ n, IsIso ((GHom.toCC β).f n) := fun n =>
      (ConcreteCategory.isIso_iff_bijective _).2 (hβ n)
    exact HomologicalComplex.Hom.isIso_of_components _
  rw [e, quasiIso_iff_comp_left, quasiIso_iff_comp_right]

/-- The shifted cone of a shifted map is the shifted cone of the map placed one degree
higher: with the second component negated, its differential is `(−d₁, d₂)` of the original. -/
theorem coneCx_shiftDownGHom_d {A B : GCx R} (g : GHom A B) (i j : ℤ) (h : i + 1 = j)
    (z : (coneCx g).X (i - 1)) :
    (coneCx (shiftDownGHom g)).d i j h ((z.1, -z.2) : (coneCx g).X (i - 1)) =
      ((-((coneCx g).d (i - 1) (j - 1) (by omega) z).1,
        ((coneCx g).d (i - 1) (j - 1) (by omega) z).2) : (coneCx g).X (j - 1)) := by
  apply Prod.ext
  · rfl
  · change (shiftDownGHom g).f i (j - 1) (by omega) z.1 -
        (shiftDown B).d (i - 1) (j - 1) (by omega) (-z.2) =
      g.f (i - 1) (j - 1 - 1) (by omega) z.1 - B.d (i - 1 - 1) (j - 1 - 1) (by omega) z.2
    rw [shiftDownGHom_f]
    change g.f (i - 1) (j - 1 - 1) _ z.1 - (-(B.d (i - 1 - 1) (j - 1 - 1) _ (-z.2))) =
      g.f (i - 1) (j - 1 - 1) _ z.1 - B.d (i - 1 - 1) (j - 1 - 1) _ z.2
    rw [map_neg, neg_neg]

/-- An acyclic shifted cone stays acyclic after shifting the map. -/
theorem coneAcyclic_shiftDownGHom {A B : GCx R} (g : GHom A B) (hg : GAcyclic (coneCx g)) :
    GAcyclic (coneCx (shiftDownGHom g)) := by
  intro i j k hij hjk w hw
  let z : (coneCx g).X (j - 1) := (w.1, -w.2)
  have hwz : w = ((z.1, -z.2) : (coneCx g).X (j - 1)) := by
    change w = (w.1, -(-w.2))
    rw [neg_neg]
    rfl
  have hw' : (coneCx (shiftDownGHom g)).d j k hjk ((z.1, -z.2) : (coneCx g).X (j - 1)) = 0 := by
    rw [← hwz]
    exact hw
  have hz : (coneCx g).d (j - 1) (k - 1) (by omega) z = 0 := by
    have e := (coneCx_shiftDownGHom_d g j k hjk z).symm.trans hw'
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    apply Prod.ext
    · exact neg_eq_zero.mp e1
    · exact e2
  obtain ⟨y, hy⟩ := hg (i - 1) (j - 1) (k - 1) (by omega) (by omega) z hz
  let y' : (coneCx g).X (i - 1) := -y
  refine ⟨((y'.1, -y'.2) : (coneCx g).X (i - 1)), ?_⟩
  refine (coneCx_shiftDownGHom_d g i j hij y').trans ?_
  have hy' : (coneCx g).d (i - 1) (j - 1) (by omega) y' = -z := by
    change (coneCx g).d (i - 1) (j - 1) _ (-y) = -z
    rw [map_neg, hy]
  rw [hy', hwz]
  exact Prod.ext (neg_neg _) rfl

/-- The converse: acyclicity of the shifted map's cone gives acyclicity of the original. -/
theorem coneAcyclic_of_shiftDownGHom {A B : GCx R} (g : GHom A B)
    (hg : GAcyclic (coneCx (shiftDownGHom g))) : GAcyclic (coneCx g) := by
  intro i j k hij hjk z hz
  let z' : (coneCx g).X (j + 1 - 1) := castX (coneCx g) (by omega : j = j + 1 - 1) z
  have hz₁ : (coneCx g).d (j + 1 - 1) (k + 1 - 1) (by omega) z' = 0 := by
    change (coneCx g).d (j + 1 - 1) (k + 1 - 1) _ (castX (coneCx g) _ z) = 0
    rw [d_castX (coneCx g) (by omega : j = j + 1 - 1) (by omega : k = k + 1 - 1) hjk, hz,
      map_zero]
  have hw : (coneCx (shiftDownGHom g)).d (j + 1) (k + 1) (by omega)
      ((z'.1, -z'.2) : (coneCx g).X (j + 1 - 1)) = 0 := by
    refine (coneCx_shiftDownGHom_d g (j + 1) (k + 1) (by omega) z').trans ?_
    rw [hz₁]
    exact Prod.ext neg_zero rfl
  obtain ⟨y, hy⟩ := hg (i + 1) (j + 1) (k + 1) (by omega) (by omega) _ hw
  let t : (coneCx g).X (i + 1 - 1) := (y.1, -y.2)
  have hyt : y = ((t.1, -t.2) : (coneCx g).X (i + 1 - 1)) := by
    change y = (y.1, -(-y.2))
    rw [neg_neg]
    rfl
  rw [hyt] at hy
  have e := (coneCx_shiftDownGHom_d g (i + 1) (j + 1) (by omega) t).symm.trans hy
  have hdt : (coneCx g).d (i + 1 - 1) (j + 1 - 1) (by omega) (-t) = z' := by
    rw [map_neg]
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    change -(((coneCx g).d (i + 1 - 1) (j + 1 - 1) (by omega) t).1) = z'.1 at e1
    change ((coneCx g).d (i + 1 - 1) (j + 1 - 1) (by omega) t).2 = -z'.2 at e2
    apply Prod.ext
    · change -(((coneCx g).d (i + 1 - 1) (j + 1 - 1) (by omega) t).1) = z'.1
      exact e1
    · change -(((coneCx g).d (i + 1 - 1) (j + 1 - 1) (by omega) t).2) = z'.2
      rw [e2, neg_neg]
  refine ⟨castX (coneCx g) (by omega : i + 1 - 1 = i) (-t), ?_⟩
  rw [d_castX (coneCx g) (by omega : i + 1 - 1 = i) (by omega : j + 1 - 1 = j) (by omega) hij,
    hdt]
  change castX (coneCx g) _ (castX (coneCx g) _ z) = z
  rw [castX_castX]
  rfl

/-- Quasi-isomorphy of a map and of its shift are equivalent. -/
theorem quasiIso_toCC_shiftDownGHom_iff {A B : GCx R} (g : GHom A B) :
    QuasiIso (GHom.toCC (shiftDownGHom g)) ↔ QuasiIso (GHom.toCC g) := by
  rw [quasiIso_toCC_iff_coneAcyclic, quasiIso_toCC_iff_coneAcyclic]
  exact ⟨coneAcyclic_of_shiftDownGHom g, coneAcyclic_shiftDownGHom g⟩

end Generic

section SwapShift

variable {R : Type} [CommRing R] {U L : GCx R}

/-- **The swap isomorphism** `Cone(−ι : U → L)[−1] ≅ (L ⊕ U[1])[−1]`: in degree `n`,
`U^n × L^(n−1) → L^(n−1) × U^((n−1)+1)`, `(u, x) ↦ (x, u)`. With the negated map on the left,
it intertwines the differentials exactly, with no additional sign. -/
def coneSwap (ι : GHom U L) : GHom (coneCx (negGHom ι)) (shiftDown (ordinaryCone ι)) where
  f i j h :=
    ((castX L (by omega : i - 1 = j - 1)).comp (LinearMap.snd R (U.X i) (L.X (i - 1)))).prod
      ((castX U (by omega : i = j - 1 + 1)).comp (LinearMap.fst R (U.X i) (L.X (i - 1))))
  comm i i₁ j j₁ hij h₁ h₂ hj z := by
    subst hij hj
    apply Prod.ext
    · change castX L (by omega : i₁ - 1 = i₁ - 1)
          (-(ι.f i (i₁ - 1) (by omega) z.1) - L.d (i - 1) (i₁ - 1) (by omega) z.2) =
        -(L.d (i - 1) (i₁ - 1) (by omega) (castX L (by omega : i - 1 = i - 1) z.2) +
          ι.f (i - 1 + 1) (i₁ - 1) (by omega) (castX U (by omega : i = i - 1 + 1) z.1))
      rw [castX_self, castX_self, GHom.f_castX]
      abel
    · change castX U (by omega : i₁ = i₁ - 1 + 1) (U.d i i₁ h₁ z.1) =
        -(-(U.d (i - 1 + 1) (i₁ - 1 + 1) (by omega) (castX U (by omega : i = i - 1 + 1) z.1)))
      rw [neg_neg, d_castX U (by omega : i = i - 1 + 1) (by omega : i₁ = i₁ - 1 + 1) h₁]

theorem coneSwap_bijective (ι : GHom U L) (n : ℤ) :
    Function.Bijective ((coneSwap ι).f n n rfl) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z => ((castX U (by omega : n - 1 + 1 = n) z.2, z.1) : U.X n × L.X (n - 1)), ?_, ?_⟩
  · intro z
    change ((castX U (by omega : n - 1 + 1 = n) (castX U (by omega : n = n - 1 + 1) z.1),
      castX L (by omega : n - 1 = n - 1) z.2) : U.X n × L.X (n - 1)) = z
    rw [castX_castX]
    rfl
  · intro z
    change ((castX L (by omega : n - 1 = n - 1) z.1,
      castX U (by omega : n = n - 1 + 1) (castX U (by omega : n - 1 + 1 = n) z.2)) :
        L.X (n - 1) × U.X (n - 1 + 1)) = z
    rw [castX_castX]
    rfl

/-- **The dual shift identification** `Hom(U, R)[−2][−1] = Hom(U, R)[−3]`: in degree `n`,
`Hom(U^(2−(n−1)), R) → Hom(U^(3−n), R)` by index transport. The shift sign of `[−1]` and the
dual sign `−(−1)^n` combine to the sign of `Hom(U, R)[−3]`. -/
def dualShift (U : GCx R) : GHom (shiftDown (dualCx U 2)) (dualCx U 3) where
  f i j h := (castX U (by omega : 3 - j = 2 - (i - 1))).dualMap
  comm i i₁ j j₁ hij h₁ h₂ hj φ := by
    subst hij hj
    refine dualCx_ext fun x => ?_
    change (-(-(sgn (i - 1)) • asDual (show (dualCx U 2).X (i - 1) from φ)
        (U.d (2 - (i₁ - 1)) (2 - (i - 1)) (by omega)
          (castX U (by omega : 3 - i₁ = 2 - (i₁ - 1)) x)))) =
      (-(sgn i)) • asDual (show (dualCx U 2).X (i - 1) from φ)
        (castX U (by omega : 3 - i = 2 - (i - 1)) (U.d (3 - i₁) (3 - i) (by omega) x))
    rw [d_castX U (by omega : 3 - i₁ = 2 - (i₁ - 1)) (by omega : 3 - i = 2 - (i - 1))
      (by omega), sgn_pred, neg_neg, neg_smul]

theorem dualShift_bijective (U : GCx R) (n : ℤ) :
    Function.Bijective ((dualShift U).f n n rfl) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨(castX U (by omega : 2 - (n - 1) = 3 - n)).dualMap, ?_, ?_⟩
  · intro φ
    refine LinearMap.ext fun x => ?_
    change (show Module.Dual R (U.X (2 - (n - 1))) from φ) (castX U _ (castX U _ x)) =
      (show Module.Dual R (U.X (2 - (n - 1))) from φ) x
    rw [castX_castX]
    rfl
  · intro φ
    refine LinearMap.ext fun x => ?_
    change (show Module.Dual R (U.X (3 - n)) from φ) (castX U _ (castX U _ x)) =
      (show Module.Dual R (U.X (3 - n)) from φ) x
    rw [castX_castX]
    rfl

/-- The traced comparison from the ordinary cone, transported to the original shifted-cone
indexing `Cone(−ι)[−1] → Hom(U, R)[−3]`. -/
def coneDualTransport (ι : GHom U L) (C : GHom (ordinaryCone ι) (dualCx U 2)) :
    GHom (coneCx (negGHom ι)) (dualCx U 3) :=
  ghomComp (coneSwap ι) (ghomComp (shiftDownGHom C) (dualShift U))

/-- **Shift/sign transport.** The transported map is a quasi-isomorphism exactly when the
ordinary-cone comparison is. -/
theorem quasiIso_coneDualTransport_iff (ι : GHom U L) (C : GHom (ordinaryCone ι) (dualCx U 2)) :
    QuasiIso (GHom.toCC (coneDualTransport ι C)) ↔ QuasiIso (GHom.toCC C) := by
  rw [← quasiIso_toCC_shiftDownGHom_iff C]
  exact quasiIso_toCC_iff_of_factor _ _ (coneSwap ι) (dualShift U) (coneSwap_bijective ι)
    (dualShift_bijective U) fun _ _ => rfl

/-- The transported map evaluates the ordinary-cone comparison on the swapped input. -/
theorem coneDualTransport_apply (ι : GHom U L) (C : GHom (ordinaryCone ι) (dualCx U 2)) (n : ℤ)
    (u : U.X n) (x : L.X (n - 1)) (y : U.X (3 - n)) :
    asDual ((coneDualTransport ι C).f n n rfl ((u, x) : U.X n × L.X (n - 1))) y =
      asDual (C.f (n - 1) (n - 1) rfl
          ((x, castX U (by omega : n = n - 1 + 1) u) : L.X (n - 1) × U.X (n - 1 + 1)))
        (castX U (by omega : 3 - n = 2 - (n - 1)) y) :=
  rfl

end SwapShift

section FiniteProducts

universe u
variable {R : Type u} [CommRing R] {V : Type u}

/-- The shifted cone of a product of maps is acyclic when every factor's is. -/
theorem coneAcyclic_piMap {A B : V → GCx R} (g : ∀ v, GHom (A v) (B v))
    (h : ∀ v, GAcyclic (coneCx (g v))) : GAcyclic (coneCx (piMap g)) := by
  intro i j k hij hjk z hz
  have hv : ∀ v, ∃ y : (coneCx (g v)).X i,
      (coneCx (g v)).d i j hij y = ((z.1 v, z.2 v) : (A v).X j × (B v).X (j - 1)) := by
    intro v
    refine h v i j k hij hjk _ ?_
    have e1 := congrFun (congrArg Prod.fst hz) v
    have e2 := congrFun (congrArg Prod.snd hz) v
    exact Prod.ext e1 e2
  choose y hy using hv
  refine ⟨((fun v => (y v).1, fun v => (y v).2) : (∀ v, (A v).X i) × (∀ v, (B v).X (i - 1))), ?_⟩
  apply Prod.ext
  · funext v
    exact congrArg Prod.fst (hy v)
  · funext v
    exact congrArg Prod.snd (hy v)

/-- A product of quasi-isomorphisms is a quasi-isomorphism. -/
theorem quasiIso_toCC_piMap {A B : V → GCx R} (g : ∀ v, GHom (A v) (B v))
    (h : ∀ v, QuasiIso (GHom.toCC (g v))) : QuasiIso (GHom.toCC (piMap g)) :=
  (quasiIso_toCC_iff_coneAcyclic _).2
    (coneAcyclic_piMap g fun v => (quasiIso_toCC_iff_coneAcyclic _).1 (h v))

/-- Conversely, each factor of a product quasi-isomorphism is a quasi-isomorphism. -/
theorem quasiIso_toCC_of_piMap [DecidableEq V] {A B : V → GCx R} (g : ∀ v, GHom (A v) (B v))
    (h : QuasiIso (GHom.toCC (piMap g))) (v : V) : QuasiIso (GHom.toCC (g v)) := by
  rw [quasiIso_toCC_iff_coneAcyclic] at h ⊢
  intro i j k hij hjk z hz
  let Z1 : ∀ w, (A w).X j := Pi.single v z.1
  let Z2 : ∀ w, (B w).X (j - 1) := Pi.single v z.2
  have hZ : (coneCx (piMap g)).d j k hjk
      ((Z1, Z2) : (∀ w, (A w).X j) × (∀ w, (B w).X (j - 1))) = 0 := by
    have e1 := congrArg Prod.fst hz
    have e2 := congrArg Prod.snd hz
    apply Prod.ext
    · funext w
      change (A w).d j k hjk (Z1 w) = 0
      by_cases hw : w = v
      · subst hw
        change (A w).d j k hjk ((Pi.single w z.1 : ∀ w, (A w).X j) w) = 0
        rw [Pi.single_eq_same]
        exact e1
      · change (A w).d j k hjk ((Pi.single v z.1 : ∀ w, (A w).X j) w) = 0
        rw [Pi.single_eq_of_ne hw, map_zero]
    · funext w
      change (g w).f j (k - 1) (by omega) (Z1 w) - (B w).d (j - 1) (k - 1) (by omega) (Z2 w) = 0
      by_cases hw : w = v
      · subst hw
        change (g w).f j (k - 1) (by omega) ((Pi.single w z.1 : ∀ w, (A w).X j) w) -
          (B w).d (j - 1) (k - 1) (by omega) ((Pi.single w z.2 : ∀ w, (B w).X (j - 1)) w) = 0
        rw [Pi.single_eq_same, Pi.single_eq_same]
        exact e2
      · change (g w).f j (k - 1) (by omega) ((Pi.single v z.1 : ∀ w, (A w).X j) w) -
          (B w).d (j - 1) (k - 1) (by omega) ((Pi.single v z.2 : ∀ w, (B w).X (j - 1)) w) = 0
        rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, map_zero, map_zero, sub_zero]
  obtain ⟨Y, hY⟩ := h i j k hij hjk _ hZ
  refine ⟨((Y.1 v, Y.2 v) : (A v).X i × (B v).X (i - 1)), ?_⟩
  have e1 := congrFun (congrArg Prod.fst hY) v
  have e2 := congrFun (congrArg Prod.snd hY) v
  apply Prod.ext
  · refine e1.trans ?_
    change (Pi.single v z.1 : ∀ w, (A w).X j) v = z.1
    rw [Pi.single_eq_same]
  · refine e2.trans ?_
    change (Pi.single v z.2 : ∀ w, (B w).X (j - 1)) v = z.2
    rw [Pi.single_eq_same]

/-- **Regrouping the cone of a product.** `Cone(−∏ι_v)[−1] ≅ ∏ Cone(−ι_v)[−1]`, `(u, x) ↦
(u_v, x_v)_v`. -/
def coneRegroup {U L : V → GCx R} (ιs : ∀ v, GHom (U v) (L v)) :
    GHom (coneCx (negGHom (piMap ιs))) (piCx fun v => coneCx (negGHom (ιs v))) where
  f i j h := by
    subst h
    exact LinearMap.pi fun v =>
      ((LinearMap.proj v).comp (LinearMap.fst R (∀ w, (U w).X i) (∀ w, (L w).X (i - 1)))).prod
        ((LinearMap.proj v).comp (LinearMap.snd R (∀ w, (U w).X i) (∀ w, (L w).X (i - 1))))
  comm i i₁ j j₁ hij h₁ h₂ hj z := by
    subst hij hj
    rfl

theorem coneRegroup_bijective {U L : V → GCx R} (ιs : ∀ v, GHom (U v) (L v)) (n : ℤ) :
    Function.Bijective ((coneRegroup ιs).f n n rfl) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z => ((fun v => (z v).1, fun v => (z v).2) : (∀ w, (U w).X n) × (∀ w, (L w).X (n - 1))),
      fun _ => rfl, fun _ => rfl⟩

/-- The underlying map of the dual of a finite product, `(φ_v) ↦ (y ↦ ∑_v φ_v(y_v))`. -/
def dualPiSumMap [Fintype V] (U : V → GCx R) (a : ℤ) :
    (∀ v, Module.Dual R ((U v).X a)) →ₗ[R] Module.Dual R (∀ v, (U v).X a) :=
  ∑ v, ((LinearMap.proj v : (∀ w, (U w).X a) →ₗ[R] (U v).X a).dualMap).comp
    (LinearMap.proj v : (∀ w, Module.Dual R ((U w).X a)) →ₗ[R] Module.Dual R ((U v).X a))

theorem dualPiSumMap_apply [Fintype V] (U : V → GCx R) (a : ℤ)
    (φ : ∀ v, Module.Dual R ((U v).X a)) (y : ∀ v, (U v).X a) :
    dualPiSumMap U a φ y = ∑ v, φ v (y v) := by
  simp only [dualPiSumMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.dualMap_apply,
    LinearMap.proj_apply]

/-- **The dual of a finite product.** `∏ Hom(U_v, R)[−m] → Hom(∏ U_v, R)[−m]`,
`(φ_v) ↦ (y ↦ ∑_v φ_v(y_v))`. -/
def dualPiSum [Fintype V] (U : V → GCx R) (m : ℤ) :
    GHom (piCx fun v => dualCx (U v) m) (dualCx (piCx U) m) where
  f i j h := by
    subst h
    exact dualPiSumMap U (m - i)
  comm i i₁ j j₁ hij h₁ h₂ hj φ := by
    subst hij hj
    refine dualCx_ext fun y => ?_
    change dualPiSumMap U (m - i₁) (fun v => (dualCx (U v) m).d i i₁ h₁ (φ v)) y =
      (-(sgn i)) • dualPiSumMap U (m - i) φ ((piCx U).d (m - i₁) (m - i) (by omega) y)
    refine (dualPiSumMap_apply U (m - i₁) (fun v => (dualCx (U v) m).d i i₁ h₁ (φ v)) y).trans
      (Eq.trans ?_ (congrArg (fun t : R => (-(sgn i)) • t)
        (dualPiSumMap_apply U (m - i) φ ((piCx U).d (m - i₁) (m - i) (by omega) y))).symm)
    rw [Finset.smul_sum]
    rfl

theorem dualPiSum_apply [Fintype V] (U : V → GCx R) (m n : ℤ)
    (φ : ∀ v, Module.Dual R ((U v).X (m - n))) (y : ∀ v, (U v).X (m - n)) :
    asDual ((dualPiSum U m).f n n rfl φ) y = ∑ v, φ v (y v) :=
  dualPiSumMap_apply U (m - n) φ y

theorem dualPiSum_bijective [Fintype V] (U : V → GCx R) (m n : ℤ) :
    Function.Bijective ((dualPiSum U m).f n n rfl) := by
  classical
  change Function.Bijective (dualPiSumMap U (m - n))
  refine Function.bijective_iff_has_inverse.2
    ⟨fun ψ v => ψ.comp (LinearMap.single R (fun w => (U w).X (m - n)) v), ?_, ?_⟩
  · intro φ
    funext v
    refine LinearMap.ext fun x => ?_
    change dualPiSumMap U (m - n) φ (Pi.single v x) = φ v x
    rw [dualPiSumMap_apply, Finset.sum_eq_single v]
    · rw [Pi.single_eq_same]
    · intro w _ hw
      rw [Pi.single_eq_of_ne hw, map_zero]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  · intro ψ
    refine LinearMap.ext fun y => ?_
    rw [dualPiSumMap_apply]
    change ∑ v, ψ (Pi.single v (y v)) = ψ y
    rw [← map_sum, Finset.univ_sum_single]

end FiniteProducts

section TruncatedProducts

universe u
variable {R : Type u} [CommRing R] {V : Type u}

/-- In the truncation of a product, the pure-local image of a degree-two coboundary is zero. -/
theorem truncMk_single_boundary [DecidableEq V] (T : V → GCx R) (v : V) (y : (T v).X 1) :
    (truncSub (piCx T) (3 - 1)).mkQ (Pi.single v ((T v).d 1 2 rfl y) : ∀ w, (T w).X 2) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    truncSub_of_eq (piCx T) (by norm_num : (3 : ℤ) - 1 = 2)]
  refine ⟨(Pi.single v y : ∀ w, (T w).X 1), ?_⟩
  funext w
  by_cases hw : w = v
  · subst hw
    change (T w).d 1 2 rfl ((Pi.single w y : ∀ w, (T w).X 1) w) =
      (Pi.single w ((T w).d 1 2 rfl y) : ∀ w, (T w).X 2) w
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · change (T w).d 1 2 rfl ((Pi.single v y : ∀ w, (T w).X 1) w) =
      (Pi.single v ((T v).d 1 2 rfl y) : ∀ w, (T w).X 2) w
    rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, map_zero]

/-- A linear functional on a finite product is the sum of its pure-local restrictions. -/
theorem linear_eq_sum_single [Fintype V] [DecidableEq V] {M : V → Type u}
    [∀ w, AddCommGroup (M w)] [∀ w, Module R (M w)] (G : (∀ w, M w) →ₗ[R] R) (c : ∀ w, M w) :
    G c = ∑ w, G (Pi.single w (c w)) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [map_sum]

end TruncatedProducts

section Central

open NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
variable (D : GenuineKummerData K E₀ hZ) (I : CentralIntegralTruncIsotropy D)
  (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])

/-- The pure-local trace vanishes on coboundaries. -/
theorem centralLocalIntegralTrace_boundary (v : Places K D.S)
    (y : (centralLocalCyclotomicCx D v).X 1) :
    centralLocalIntegralTrace D I tr v ((centralLocalCyclotomicCx D v).d 1 2 rfl y) = 0 := by
  rw [centralLocalIntegralTrace_apply]
  have h := truncMk_single_boundary (fun w : Places K D.S => centralLocalCyclotomicCx D w) v y
  change tr ((0, (truncSub (piCx fun w : Places K D.S => centralLocalCyclotomicCx D w)
    (3 - 1)).mkQ (Pi.single v ((centralLocalCyclotomicCx D v).d 1 2 rfl y) :
      ∀ w, (centralLocalCyclotomicCx D w).X 2)) :
        (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3) = 0
  rw [h]
  exact map_zero tr

/-- The truncated isotropy of the same pairing data makes the degree-`(1, 1)` cup of the Kummer
condition a coboundary, so its pure-local trace vanishes. -/
theorem centralLocalIntegralTrace_cup (v : Places K D.S)
    (u w : (integralCondition (S := D.S) (centralCurve D) v.1).X 1) :
    centralLocalIntegralTrace D I tr v
      ((natPair (restrictedIntegralCup (S := D.S) (centralCurve D) v.1)).P 1 1 2 rfl
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl u)
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl w)) = 0 := by
  have hU := integralKummerCondition_support (S := D.S) (centralCurve D) v.1
  have hdu : (integralCondition (S := D.S) (centralCurve D) v.1).d 1 2 rfl u = 0 :=
    @Subsingleton.elim _ (hU 2 (by omega)) _ _
  have hdw : (integralCondition (S := D.S) (centralCurve D) v.1).d 1 2 rfl w = 0 :=
    @Subsingleton.elim _ (hU 2 (by omega)) _ _
  have hiso := I.isotropy₂ v 1 2 1 2 rfl rfl rfl u w
  change I.h v 2 1 2 _ ((integralCondition (S := D.S) (centralCurve D) v.1).d 1 2 rfl u) w +
      sgn 1 • I.h v 1 2 2 _ u ((integralCondition (S := D.S) (centralCurve D) v.1).d 1 2 rfl w) -
      (natPair (restrictedIntegralCup (S := D.S) (centralCurve D) v.1)).P 1 1 2 rfl
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl u)
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl w) ∈
      LinearMap.range ((centralLocalCyclotomicCx D v).d 1 2 rfl) at hiso
  rw [hdu, hdw, map_zero, LinearMap.zero_apply, map_zero, smul_zero, zero_add, zero_sub] at hiso
  obtain ⟨y, hy⟩ := hiso
  have e : (centralLocalCyclotomicCx D v).d 1 2 rfl (-y) =
      (natPair (restrictedIntegralCup (S := D.S) (centralCurve D) v.1)).P 1 1 2 rfl
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl u)
        ((integralConditionMap (S := D.S) (centralCurve D) v.1).f 1 1 rfl w) := by
    rw [map_neg, hy, neg_neg]
  rw [← e]
  exact centralLocalIntegralTrace_boundary D I tr v (-y)

/-- **The per-place literal comparison with the pure-local trace.** At a place `v` of the
central support, the canonical cone comparison of the literal integral Kummer condition,
`ordinaryCone(ι_v) → Hom(U_v, ℤ₂)[−2]`, built with the pure-local restriction `ℓ_v` of the
given global trace. -/
def centralLocalTraceComparison (v : Places K D.S) :
    GHom (ordinaryCone (integralConditionMap (S := D.S) (centralCurve D) v.1))
      (dualCx (integralCondition (S := D.S) (centralCurve D) v.1) 2) :=
  selfDualConeComparison (integralConditionMap (S := D.S) (centralCurve D) v.1)
    (natPair (restrictedIntegralCup (S := D.S) (centralCurve D) v.1))
    (centralLocalIntegralTrace D I tr v) (centralLocalIntegralTrace_boundary D I tr v)
    (integralKummerCondition_support (S := D.S) (centralCurve D) v.1)
    (centralLocalIntegralTrace_cup D I tr v)

/-- The per-place comparison evaluates the literal local cup and the pure-local trace. -/
theorem centralLocalTraceComparison_apply (v : Places K D.S) (n : ℤ)
    (x : (ordinaryCone (integralConditionMap (S := D.S) (centralCurve D) v.1)).X n)
    (u : (integralCondition (S := D.S) (centralCurve D) v.1).X (2 - n)) :
    asDual ((centralLocalTraceComparison D I tr v).f n n rfl x) u =
      centralLocalIntegralTrace D I tr v
        ((natPair (restrictedIntegralCup (S := D.S) (centralCurve D) v.1)).P n (2 - n) 2
          (by omega) x.1
          ((integralConditionMap (S := D.S) (centralCurve D) v.1).f (2 - n) (2 - n) rfl u)) :=
  rfl

end Central

section CentralFactorization

open NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
variable (D : GenuineKummerData K E₀ hZ) (I : CentralIntegralTruncIsotropy D)
  (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
  (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)

/-- The per-place comparison transported to the original local-map indexing. -/
abbrev centralLocalTraceTransport (v : Places K D.S) :
    GHom (coneCx (negGHom (integralConditionMap (S := D.S) (centralCurve D) v.1)))
      (dualCx (integralCondition (S := D.S) (centralCurve D) v.1) 3) :=
  coneDualTransport (integralConditionMap (S := D.S) (centralCurve D) v.1)
    (centralLocalTraceComparison D I tr v)

/-- The original local duality map evaluates the local cup of the condition with the pure local
component and the truncated isotropy term; the latter vanishes because the conditions are
concentrated in degrees `0` and `1`. -/
theorem centralLocalDualityMap_apply (n : ℤ)
    (u : (compactCentralSelData D).U.X n) (x : (compactCentralSelData D).L.X (n - 1))
    (y : (compactCentralSelData D).U.X (3 - n)) :
    asDual ((localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr).f n n rfl
        ((u, x) : (locCx (compactCentralSelData D)).X n)) y =
      tr ((0, (truncSub (centralIntegralPairDataTrunc D I).EL (3 - 1)).mkQ
        (fun w => (natPair (restrictedIntegralCup (S := D.S) (centralCurve D) w.1)).P (n - 1)
          (3 - n) (3 - 1) (by omega) (x w)
          ((integralConditionMap (S := D.S) (centralCurve D) w.1).f (3 - n) (3 - n) rfl (y w)))) :
        (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3) := by
  classical
  let Q := (centralIntegralPairDataTrunc D I).toSelPairData
  have e : asDual ((localDualityMap Q tr htr).f n n rfl
        ((u, x) : (locCx (compactCentralSelData D)).X n)) y =
      tr ((0, Q.cupL.P (n - 1) (3 - n) (3 - 1) (by omega) x
          ((compactCentralSelData D).ι.f (3 - n) (3 - n) rfl y) +
        Q.hU n (3 - n) (3 - 1) (by omega) u y) : (coneCx Q.resE).X 3) := by
    change tr (selCupFun Q n (3 - n) 3 _ (0, u, x) (0, y, 0)) = _
    simp only [selCupFun, map_zero, smul_zero, add_zero]
  refine e.trans ?_
  have hzero : Q.hU n (3 - n) (3 - 1) (by omega) u y = 0 := by
    have hfun : (fun w : Places K D.S => I.h w n (3 - n) (3 - 1) (by omega) (u w) (y w)) = 0 := by
      funext w
      have hU := integralKummerCondition_support (S := D.S) (centralCurve D) w.1
      by_cases hn : n = 0 ∨ n = 1
      · have hy : y w = 0 := @Subsingleton.elim _ (hU (3 - n) (by omega)) _ _
        rw [hy, map_zero]
        rfl
      · have hu : u w = 0 := @Subsingleton.elim _ (hU n hn) _ _
        rw [hu, map_zero, LinearMap.zero_apply]
        rfl
    change (truncSub (centralIntegralPairDataTrunc D I).EL (3 - 1)).mkQ
      (fun w : Places K D.S => I.h w n (3 - n) (3 - 1) (by omega) (u w) (y w)) = 0
    rw [hfun, map_zero]
  rw [hzero, add_zero]
  rfl

/-- **Finite-product trace decomposition.** The global trace of a pure-local class is the sum
over the finite places of the pure-local traces of its components. -/
theorem trace_pureLocal_eq_sum [Fintype (Places K D.S)]
    (c : ∀ w : Places K D.S, (centralLocalCyclotomicCx D w).X 2) :
    tr ((0, (truncSub (centralIntegralPairDataTrunc D I).EL (3 - 1)).mkQ c) :
        (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3) =
      ∑ w, centralLocalIntegralTrace D I tr w (c w) := by
  let G : (∀ w : Places K D.S, (centralLocalCyclotomicCx D w).X 2) →ₗ[ℤ_[2]] ℤ_[2] :=
    tr.comp ((LinearMap.inr ℤ_[2] ((centralIntegralPairDataTrunc D I).E.X 3)
      ((truncGe2 (centralIntegralPairDataTrunc D I).EL).X (3 - 1))).comp
      (truncSub (centralIntegralPairDataTrunc D I).EL (3 - 1)).mkQ)
  exact linear_eq_sum_single G c

/-- **Exact correspondence with the original central local duality map.** In every degree the
original map is the finite sum, over the places of the central support, of the per-place
comparisons with the pure-local traces `ℓ_v`, after the regrouping `Cone(−∏ι_v) ≅ ∏ Cone(−ι_v)`,
the swap/shift identification, and the dual of the finite product. -/
theorem centralLocalDualityMap_factor [Fintype (Places K D.S)] (n : ℤ)
    (c : (locCx (compactCentralSelData D)).X n) :
    (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr).f n n rfl c =
      (dualPiSum (fun v : Places K D.S => integralCondition (S := D.S) (centralCurve D) v.1) 3).f
        n n rfl ((piMap (centralLocalTraceTransport D I tr)).f n n rfl
          ((coneRegroup fun v : Places K D.S =>
            integralConditionMap (S := D.S) (centralCurve D) v.1).f n n rfl c)) := by
  refine dualCx_ext fun y => ?_
  obtain ⟨u, x⟩ := c
  refine (centralLocalDualityMap_apply D I tr htr n u x y).trans ?_
  refine (trace_pureLocal_eq_sum D I tr _).trans ?_
  refine Eq.trans ?_ (dualPiSum_apply
    (fun v : Places K D.S => integralCondition (S := D.S) (centralCurve D) v.1) 3 n _ y).symm
  refine Finset.sum_congr rfl fun w _ => ?_
  refine Eq.trans ?_ (coneDualTransport_apply
    (integralConditionMap (S := D.S) (centralCurve D) w.1)
    (centralLocalTraceComparison D I tr w) n (u w) (x w) (y w)).symm
  refine Eq.trans ?_ (centralLocalTraceComparison_apply D I tr w (n - 1) _ _).symm
  exact congrArg (centralLocalIntegralTrace D I tr w)
    ((natPair (restrictedIntegralCup (S := D.S) (centralCurve D) w.1)).congr
      (X := (natCx (restrictedPointComplex (S := D.S) (centralCurve D) w.1)).X (n - 1))
      (Y := (integralCondition (S := D.S) (centralCurve D) w.1).X (3 - n))
      (i := n - 1) (j := 3 - n) (k := 2)
      (fun m hm => castX _ hm)
      (fun m hm => ((integralConditionMap (S := D.S) (centralCurve D) w.1).f m m rfl).comp
        (castX _ hm))
      (n - 1) (n - 1) (3 - n) (2 - (n - 1)) rfl rfl rfl (by omega) (by omega) (by omega)
      (x w) (y w))

/-- **The central local duality map is a quasi-isomorphism exactly when every per-place literal
comparison with the pure-local trace is one.** No local duality or isotropy conclusion is
assumed: this is the exact shift/sign and finite-product binding of the same fixed map. -/
theorem centralLocalDuality_quasiIso_iff :
    QuasiIso (GHom.toCC
        (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr)) ↔
      ∀ v : Places K D.S, QuasiIso (GHom.toCC (centralLocalTraceComparison D I tr v)) := by
  classical
  let : Fintype (Places K D.S) := D.hSfin.fintype
  rw [quasiIso_toCC_iff_of_factor _ (piMap (centralLocalTraceTransport D I tr))
    (coneRegroup fun v : Places K D.S => integralConditionMap (S := D.S) (centralCurve D) v.1)
    (dualPiSum (fun v : Places K D.S => integralCondition (S := D.S) (centralCurve D) v.1) 3)
    (coneRegroup_bijective _) (dualPiSum_bijective _ 3)
    (centralLocalDualityMap_factor D I tr htr)]
  constructor
  · intro h v
    exact (quasiIso_coneDualTransport_iff _ _).1 (quasiIso_toCC_of_piMap _ h v)
  · intro h
    exact quasiIso_toCC_piMap _ fun v => (quasiIso_coneDualTransport_iff _ _).2 (h v)

/-- **The local orthogonality input from the per-place family.** -/
theorem centralLocalOrthogonality_of_traceComparisons (P : PerfectCoefficientPairing ℤ_[2])
    (hfam : ∀ v : Places K D.S,
      QuasiIso (GHom.toCC (centralLocalTraceComparison D I tr v))) :
    LocalOrthogonalityInput (centralIntegralPairDataTrunc D I).toSelPairData tr htr P :=
  (centralLocalDuality_quasiIso_iff D I tr htr).2 hfam

/-- The same binding for the constructed central pairing: the isotropy witness is the one built
from the cited local input, not a premise. -/
theorem centralLocalDuality_quasiIso_iff_of_print (hM : DerivedKummer.MilneLocalDualityPrint)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z,
      tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0) :
    QuasiIso (GHom.toCC
        (localDualityMap (centralIntegralPairing_of_print D hM).toSelPairData tr htr)) ↔
      ∀ v : Places K D.S, QuasiIso (GHom.toCC
        (centralLocalTraceComparison D (centralIntegralTruncIsotropy_of_print D hM) tr v)) :=
  centralLocalDuality_quasiIso_iff D (centralIntegralTruncIsotropy_of_print D hM) tr htr

end CentralFactorization

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
