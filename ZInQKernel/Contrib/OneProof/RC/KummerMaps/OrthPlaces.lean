import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncPrints
import ZInQKernel.Contrib.OneProof.RC.CoefModules.LocalConditions

/-!
# Lane RC29 (item 2): orthogonal complements, place by place

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830: "With the
conjugate places, actual orthogonal local conditions and their isotropy homotopies, finite Selmer
duality gives `C_U(M_i) ≃ RHom(C_{U⊥}(M_i^*(1)), R_i)[−3]`"), Lemma `ex:arith-local-kummer`
(tex 3413–3463) and tex 3829–3835 ("the actual orthogonal local diagrams with their isotropy
homotopies"); Nekovář, *Selmer complexes* (Astérisque 310, 2006), 6.2.2 (the local products
`u⁻`), 6.2.7 (orthogonal complements, defined place by place: `Δ(X₁) ⊥⊥ Δ(X₂)` means
`Δ_v(X₁) ⊥⊥ Δ_v(X₂)` for all `v ∈ S_f`) and 6.3.4.

Lane RC26 defines `OrthogonalComplements` (and its `τ≥2` form `OrthogonalComplementsT`) as the
quasi-isomorphy of ONE global map, the local duality map
`Cone(⊕_v U_v → ⊕_v C(G_v, M))[−1] → Hom_R(⊕_v U'_v, R)[−3]`,
`(u, x) ↦ (y ↦ tr(0, x ∪ i' y + h(u, y)))`, and proves the case (zero condition, full condition)
by splitting this map into one map per place (`Orthogonality.lean`). This file generalizes that
splitting argument to arbitrary local conditions with arbitrary per-place isotropy homotopies, so
that orthogonality becomes Nekovář's per-place statement:

* `orthNeg`: `−f` for a chain map; the per-place cone is `coneCx (orthNeg i_v) =
  Cone(U_v → C(G_v, M))[−1]` (the same cone as `locCx` of lane RC26 / the other group).
* `orthLocalMap iU iU' P J trv htrv`: for a local condition `iU : U → L`, a dual condition
  `iU' : U' → L'`, a local cup product `P : L × L' → E`, a per-place `τ≥2` isotropy homotopy `J`
  (the other group's `LocalTruncIsotropy`, the per-place form of `TruncIsotropyData`) and a local
  trace `trv : E² → R` killing coboundaries, **the per-place local duality map**
  `Cone(U → L)[−1] → Hom_R(U', R)[−3]`, `(u, x) ↦ (y ↦ trv(x ∪ iU' y + h(u, y)))` (Nekovář's
  `u⁻_{π,h_v}` of 6.2.2). It is a chain map (PROVED from the Leibniz rule, the degree-two
  isotropy identity and `trv ∘ d = 0`); `orthLocalMap_apply` gives its values.
* `orthCone_acyclic`: **the splitting lemma** — a global chain map whose values are the sums of
  per-place chain maps has acyclic cone as soon as every per-place cone is acyclic (finitely many
  places).
* **(a) of lane RC29 item 2**: `orth_localDualityMapT_quasiIso` (generic topological groups,
  `τ≥2` isotropy data) and `orth_localDualityMap_quasiIso` (untruncated isotropy data): for
  finitely many places and a global trace whose local part is `∑_v tr_v`, the global local
  duality map is a quasi-isomorphism as soon as every per-place local duality map is one. Galois
  forms: `orthogonalComplementsT_of_places`, `orthogonalComplements_of_places`, and for local
  conditions given place by place in lane RC28's format: `orthogonalComplementsT_ofCondAt`.
* Non-vacuity: `orthLocalMap_full_zero_quasiIso` (the per-place hypothesis holds for the full
  condition against the zero condition, any isotropy data, any trace), and the recovery of lane
  RC26's `orthogonal_relaxed_strictT` shape (`orthogonalComplementsT_relaxed_strict_of_places`).

Kinds: all declarations are definitions or PROVED. No hypothesis of this file is a PRINT or an
ELLIOT step; the per-place inputs are supplied in `OrthUnramified.lean` and `OrthActual.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

universe u

/-! ### The per-place local duality map -/

section Abstract

variable {k : Type u} [CommRing k]

/-- **The negative `−f` of a chain map** (the cone `Cone(U → L)[−1]` of a local condition is
`coneCx (orthNeg i)`, differential `d(u, x) = (du, −i u − dx)`, as for lane RC26's `locCx`). -/
def orthNeg {A B : GCx k} (f : GHom A B) : GHom A B where
  f i j h := -(f.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    simp only [LinearMap.neg_apply, map_neg, f.comm i i₁ j j₁ hij h₁ h₂ hj x]

theorem orthNeg_f_apply {A B : GCx k} (f : GHom A B) (i j : ℤ) (h : i = j) (x : A.X i) :
    (orthNeg f).f i j h x = -(f.f i j h x) :=
  rfl

variable {U U' L L' E : GCx k} (iU : GHom U L) (iU' : GHom U' L') (P : GPair L L' E)
  (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[k] k)

/-- The components of the per-place local duality map,
`(u, x) ↦ (y ↦ trv(h(u, y)) + trv(x ∪ iU' y))`. -/
def orthLocalFun (i j : ℤ) (h : i = j) :
    (coneCx (orthNeg iU)).X i →ₗ[k] (dualCx U' 3).X j :=
  LinearMap.coprod ((J.h i (3 - j) 2 (by omega)).compr₂ trv)
    (((P.P (i - 1) (3 - j) 2 (by omega)).compl₂ (iU'.f (3 - j) (3 - j) rfl)).compr₂ trv)

variable (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)

include htrv in
/-- The per-place local duality map commutes with the differentials (Leibniz rule of `P`,
degree-two isotropy identity of `J` modulo coboundaries, `trv ∘ d = 0`). -/
theorem orthLocalFun_comm (i i₁ : ℤ) (h₁ : i + 1 = i₁) (u : U.X i) (x : L.X (i - 1)) :
    orthLocalFun iU iU' P J trv i₁ i₁ rfl
        ((coneCx (orthNeg iU)).d i i₁ h₁ ((u, x) : coneT (orthNeg iU) i)) =
      (dualCx U' 3).d i i₁ h₁ (orthLocalFun iU iU' P J trv i i rfl ((u, x) : coneT (orthNeg iU) i)) := by
  refine dualCx_ext fun y => ?_
  change trv (J.h i₁ (3 - i₁) 2 (by omega) (U.d i i₁ h₁ u) y) +
      trv (P.P (i₁ - 1) (3 - i₁) 2 (by omega)
        (-(iU.f i (i₁ - 1) (by omega) u) - L.d (i - 1) (i₁ - 1) (by omega) x)
        (iU'.f (3 - i₁) (3 - i₁) rfl y)) =
    (-(sgn i)) • (trv (J.h i (3 - i) 2 (by omega) u (U'.d (3 - i₁) (3 - i) (by omega) y)) +
      trv (P.P (i - 1) (3 - i) 2 (by omega) x
        (iU'.f (3 - i) (3 - i) rfl (U'.d (3 - i₁) (3 - i) (by omega) y))))
  -- the Leibniz rule, traced
  have hL := P.leib (i - 1) (i₁ - 1) (3 - i₁) (3 - i) 1 2 (by omega) (by omega) (by omega) rfl x
    (iU'.f (3 - i₁) (3 - i₁) rfl y)
  have h0 := htrv (P.P (i - 1) (3 - i₁) 1 (by omega) x (iU'.f (3 - i₁) (3 - i₁) rfl y))
  rw [hL, map_add, map_zsmul] at h0
  have hc := iU'.comm (3 - i₁) (3 - i) (3 - i₁) (3 - i) rfl (by omega) (by omega) rfl y
  rw [← hc, sgn_pred] at h0
  -- the isotropy identity in degree two, traced
  obtain ⟨w, hw⟩ := J.isotropy₂ i i₁ (3 - i₁) (3 - i) (by omega) h₁ (by omega) u y
  have h1 := htrv w
  rw [hw, map_sub, map_add, map_zsmul] at h1
  -- index congruence for `iU`
  have hk := P.congr (k := 2) (fun n hn => iU.f i n hn) (fun m hm => iU'.f (3 - i₁) m hm)
    (i₁ - 1) i (3 - i₁) (3 - i₁) (by omega) rfl rfl rfl (by omega) (by omega) u y
  rw [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hk, map_sub, map_neg]
  simp only [zsmul_eq_mul, Int.cast_neg] at h0 h1 ⊢
  linear_combination h1 - h0

/-- **The per-place local duality map** (Nekovář, *Selmer complexes*, 6.2.2, `u⁻_{π,h_v}`):
for a local condition `iU : U → L`, a dual local condition `iU' : U' → L'`, a local cup product
`P : L × L' → E`, a `τ≥2` isotropy homotopy `J` (degree-two identity modulo `d(E¹)`) and a local
trace `trv : E² → R` killing coboundaries,
`Cone(U → L)[−1] → Hom_R(U', R)[−3]`, `(u, x) ↦ (y ↦ trv(x ∪ iU' y + h(u, y)))`. A chain map. -/
def orthLocalMap : GHom (coneCx (orthNeg iU)) (dualCx U' 3) where
  f := orthLocalFun iU iU' P J trv
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨u, x⟩ := c
    exact orthLocalFun_comm iU iU' P J trv htrv i i₁ h₁ u x

/-- **Values of the per-place local duality map**:
`(u, x) ↦ (y ↦ trv(x ∪ iU' y + h(u, y)))`. -/
theorem orthLocalMap_apply (i j : ℤ) (h : i = j) (u : U.X i) (x : L.X (i - 1)) (y : U'.X (3 - j)) :
    asDual ((orthLocalMap iU iU' P J trv htrv).f i j h ((u, x) : coneT (orthNeg iU) i)) y =
      trv (P.P (i - 1) (3 - j) 2 (by omega) x (iU'.f (3 - j) (3 - j) rfl y) +
        J.h i (3 - j) 2 (by omega) u y) := by
  change trv (J.h i (3 - j) 2 _ u y) +
    trv (P.P (i - 1) (3 - j) 2 _ x (iU'.f (3 - j) (3 - j) rfl y)) = _
  rw [map_add, add_comm]

end Abstract

/-! ### The splitting lemma -/

section Splitting

variable {k : Type u} [CommRing k]

/-- **The splitting lemma** (generalizing lane RC26's `coneCx_localDualityMap_acyclic`): let
`g : ⊕_v U_v → ⊕_v L_v` be a chain map acting place by place through `g_v`, and
`F : Cone(g)[−1] → Hom(⊕_v U'_v, R)[−3]` a chain map whose values are the sums of the values of
per-place chain maps `F_v : Cone(g_v)[−1] → Hom(U'_v, R)[−3]`. For finitely many places, if
every `Cone(F_v)[−1]` is acyclic, so is `Cone(F)[−1]`. (A cycle of the global cone splits into
cycles of the local cones; their primitives assemble into a primitive.) PROVED. -/
theorem orthCone_acyclic {V : Type u} [Fintype V] {UA LA UB : V → GCx k}
    (g : GHom (piCx UA) (piCx LA)) (gv : ∀ v, GHom (UA v) (LA v))
    (hg : ∀ (i j : ℤ) (h : i = j) (u : (piCx UA).X i) (v : V),
      (g.f i j h u : ∀ w, (LA w).X j) v = (gv v).f i j h ((u : ∀ w, (UA w).X i) v))
    (F : GHom (coneCx g) (dualCx (piCx UB) 3))
    (Fv : ∀ v, GHom (coneCx (gv v)) (dualCx (UB v) 3))
    (hF : ∀ (i j : ℤ) (h : i = j) (u : (piCx UA).X i) (x : (piCx LA).X (i - 1))
      (y : (piCx UB).X (3 - j)),
      asDual (F.f i j h ((u, x) : coneT g i)) y =
        ∑ v, asDual ((Fv v).f i j h (((u : ∀ w, (UA w).X i) v,
          (x : ∀ w, (LA w).X (i - 1)) v) : coneT (gv v) i)) ((y : ∀ w, (UB w).X (3 - j)) v))
    (hv : ∀ v, GAcyclic (coneCx (Fv v))) : GAcyclic (coneCx F) := by
  classical
  intro I J L hIJ hJL c hc
  obtain ⟨⟨u, x⟩, φ⟩ := c
  -- the cycle conditions, read place by place
  have hu : ∀ v, (UA v).d J L hJL ((u : ∀ w, (UA w).X J) v) = 0 := fun v =>
    congrArg (fun w : coneT F L => (w.1.1 : ∀ v, (UA v).X L) v) hc
  have hx : ∀ v, (gv v).f J (L - 1) (by omega) ((u : ∀ w, (UA w).X J) v) -
      (LA v).d (J - 1) (L - 1) (by omega) ((x : ∀ w, (LA w).X (J - 1)) v) = 0 := by
    intro v
    have h1 := congrArg (fun w : coneT F L => (w.1.2 : ∀ v, (LA v).X (L - 1)) v) hc
    change (g.f J (L - 1) _ u : ∀ w, (LA w).X (L - 1)) v -
      (LA v).d (J - 1) (L - 1) _ ((x : ∀ w, (LA w).X (J - 1)) v) = 0 at h1
    exact (congrArg (· - (LA v).d (J - 1) (L - 1) (by omega) ((x : ∀ w, (LA w).X (J - 1)) v))
      (hg J (L - 1) (by omega) u v)).symm.trans h1
  have hφ : ∀ y : (piCx UB).X (3 - (L - 1)),
      asDual (F.f J (L - 1) (by omega) ((u, x) : coneT g J)) y -
        (-(sgn (J - 1))) • asDual φ ((piCx UB).d (3 - (L - 1)) (3 - (J - 1)) (by omega) y) = 0 :=
    fun y => congrArg (fun w : coneT F L => asDual w.2 y) hc
  -- the per-place cycles
  let φv : ∀ v, Module.Dual k ((UB v).X (3 - (J - 1))) := fun v =>
    (asDual φ).comp (LinearMap.single k (fun w => ((UB w).X (3 - (J - 1)) : Type u)) v)
  have hsingle : ∀ (v : V) (a b : ℤ) (hab : a + 1 = b) (y : (UB v).X a),
      (piCx UB).d a b hab (Pi.single (M := fun w => ((UB w).X a : Type u)) v y) =
        Pi.single (M := fun w => ((UB w).X b : Type u)) v ((UB v).d a b hab y) := by
    intro v a b hab y
    refine funext fun w => ?_
    change (UB w).d a b hab (Pi.single (M := fun w => ((UB w).X a : Type u)) v y w) = _
    by_cases hw : w = v
    · subst hw
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, map_zero]
  have hcyc : ∀ v, (coneCx (Fv v)).d J L hJL
      (((((u : ∀ w, (UA w).X J) v, (x : ∀ w, (LA w).X (J - 1)) v) : coneT (gv v) J), φv v) :
        coneT (Fv v) J) = 0 := by
    intro v
    refine Prod.ext (Prod.ext (hu v) (hx v)) (dualCx_ext fun y => ?_)
    let ys : (piCx UB).X (3 - (L - 1)) :=
      (Pi.single (M := fun w => ((UB w).X (3 - (L - 1)) : Type u)) v y :
        ∀ w, (UB w).X (3 - (L - 1)))
    have h4 := hF J (L - 1) (by omega) u x ys
    have h5 : ∑ w, asDual ((Fv w).f J (L - 1) (by omega) (((u : ∀ w, (UA w).X J) w,
        (x : ∀ w, (LA w).X (J - 1)) w) : coneT (gv w) J)) ((ys : ∀ w, (UB w).X (3 - (L - 1))) w) =
        asDual ((Fv v).f J (L - 1) (by omega) (((u : ∀ w, (UA w).X J) v,
          (x : ∀ w, (LA w).X (J - 1)) v) : coneT (gv v) J)) y := by
      refine (Finset.sum_eq_single v (fun w _ hw => ?_)
        (fun h => absurd (Finset.mem_univ v) h)).trans ?_
      · change asDual _ (Pi.single (M := fun w => ((UB w).X (3 - (L - 1)) : Type u)) v y w) = 0
        rw [Pi.single_eq_of_ne hw, map_zero]
      · change asDual _ (Pi.single (M := fun w => ((UB w).X (3 - (L - 1)) : Type u)) v y v) = _
        rw [Pi.single_eq_same]
    have h6 := hsingle v (3 - (L - 1)) (3 - (J - 1)) (by omega) y
    change asDual ((Fv v).f J (L - 1) _ (((u : ∀ w, (UA w).X J) v,
        (x : ∀ w, (LA w).X (J - 1)) v) : coneT (gv v) J)) y -
      (-(sgn (J - 1))) • asDual φ (Pi.single (M := fun w => ((UB w).X (3 - (J - 1)) : Type u)) v
        ((UB v).d (3 - (L - 1)) (3 - (J - 1)) _ y)) = 0
    refine Eq.trans (congrArg₂ (· - ·) (h4.trans h5).symm
      (congrArg (fun t : (piCx UB).X (3 - (J - 1)) => (-(sgn (J - 1))) • asDual φ t) h6.symm)) ?_
    exact hφ ys
  -- solve at every place
  choose e he using fun v => hv v I J L hIJ hJL _ (hcyc v)
  -- assemble the primitive
  let u' : (piCx UA).X I := (fun v => (e v).1.1 : ∀ v, (UA v).X I)
  let x' : (piCx LA).X (I - 1) := (fun v => (e v).1.2 : ∀ v, (LA v).X (I - 1))
  let ψ : Module.Dual k ((piCx UB).X (3 - (I - 1))) :=
    ∑ v, (asDual (e v).2).comp (LinearMap.proj (R := k)
      (φ := fun w => ((UB w).X (3 - (I - 1)) : Type u)) v)
  refine ⟨((((u', x') : coneT g I), ψ) : coneT F I), ?_⟩
  have he1 : ∀ v, (UA v).d I J hIJ ((u' : ∀ w, (UA w).X I) v) = (u : ∀ w, (UA w).X J) v :=
    fun v => congrArg (fun w : coneT (Fv v) J => w.1.1) (he v)
  have he2 : ∀ v, (gv v).f I (J - 1) (by omega) ((u' : ∀ w, (UA w).X I) v) -
      (LA v).d (I - 1) (J - 1) (by omega) ((x' : ∀ w, (LA w).X (I - 1)) v) =
      (x : ∀ w, (LA w).X (J - 1)) v :=
    fun v => congrArg (fun w : coneT (Fv v) J => w.1.2) (he v)
  have he3 : ∀ (v : V) (y : (UB v).X (3 - (J - 1))),
      asDual ((Fv v).f I (J - 1) (by omega) (((u' : ∀ w, (UA w).X I) v,
        (x' : ∀ w, (LA w).X (I - 1)) v) : coneT (gv v) I)) y -
        (-(sgn (I - 1))) • asDual (e v).2 ((UB v).d (3 - (J - 1)) (3 - (I - 1)) (by omega) y) =
      φv v y := fun v y => congrArg (fun w : coneT (Fv v) J => asDual w.2 y) (he v)
  refine Prod.ext (Prod.ext (funext fun v => he1 v) (funext fun v => ?_)) (dualCx_ext fun y => ?_)
  · change (g.f I (J - 1) _ u' : ∀ w, (LA w).X (J - 1)) v -
      (LA v).d (I - 1) (J - 1) _ ((x' : ∀ w, (LA w).X (I - 1)) v) = (x : ∀ w, (LA w).X (J - 1)) v
    exact (congrArg (· - (LA v).d (I - 1) (J - 1) (by omega) ((x' : ∀ w, (LA w).X (I - 1)) v))
      (hg I (J - 1) (by omega) u' v)).trans (he2 v)
  · change asDual (F.f I (J - 1) _ ((u', x') : coneT g I)) y -
      (-(sgn (I - 1))) • ψ ((piCx UB).d (3 - (J - 1)) (3 - (I - 1)) _ y) = asDual φ y
    have hψ : ψ ((piCx UB).d (3 - (J - 1)) (3 - (I - 1)) (by omega) y) =
        ∑ v, asDual (e v).2 ((UB v).d (3 - (J - 1)) (3 - (I - 1)) (by omega)
          ((y : ∀ w, (UB w).X (3 - (J - 1))) v)) := by
      change (∑ v, (asDual (e v).2).comp (LinearMap.proj (R := k)
        (φ := fun w => ((UB w).X (3 - (I - 1)) : Type u)) v)) _ = _
      exact LinearMap.sum_apply Finset.univ (fun v => (asDual (e v).2).comp (LinearMap.proj (R := k)
        (φ := fun w => ((UB w).X (3 - (I - 1)) : Type u)) v)) _
    have hy : asDual φ y = ∑ v, φv v ((y : ∀ w, (UB w).X (3 - (J - 1))) v) := by
      have e0 : (y : ∀ w, ((UB w).X (3 - (J - 1)) : Type u)) =
          ∑ w, Pi.single (M := fun w => ((UB w).X (3 - (J - 1)) : Type u)) w
            ((y : ∀ w, (UB w).X (3 - (J - 1))) w) :=
        (Finset.univ_sum_single (fun w => ((y : ∀ w, (UB w).X (3 - (J - 1))) w :
          (UB w).X (3 - (J - 1))))).symm
      calc asDual φ y = asDual φ (∑ w, Pi.single
            (M := fun w => ((UB w).X (3 - (J - 1)) : Type u)) w
              ((y : ∀ w, (UB w).X (3 - (J - 1))) w)) := congrArg _ e0
        _ = _ := map_sum (asDual φ) _ _
    calc _ = (∑ v, asDual ((Fv v).f I (J - 1) (by omega) (((u' : ∀ w, (UA w).X I) v,
            (x' : ∀ w, (LA w).X (I - 1)) v) : coneT (gv v) I))
              ((y : ∀ w, (UB w).X (3 - (J - 1))) v)) -
          (-(sgn (I - 1))) • ∑ v, asDual (e v).2 ((UB v).d (3 - (J - 1)) (3 - (I - 1)) (by omega)
            ((y : ∀ w, (UB w).X (3 - (J - 1))) v)) :=
          congrArg₂ (· - ·) (hF I (J - 1) (by omega) u' x' y)
            (congrArg (fun t : k => (-(sgn (I - 1))) • t) hψ)
      _ = ∑ v, (asDual ((Fv v).f I (J - 1) (by omega) (((u' : ∀ w, (UA w).X I) v,
            (x' : ∀ w, (LA w).X (I - 1)) v) : coneT (gv v) I))
              ((y : ∀ w, (UB w).X (3 - (J - 1))) v) -
          (-(sgn (I - 1))) • asDual (e v).2 ((UB v).d (3 - (J - 1)) (3 - (I - 1)) (by omega)
            ((y : ∀ w, (UB w).X (3 - (J - 1))) v))) := by
          rw [Finset.smul_sum, Finset.sum_sub_distrib]
      _ = ∑ v, φv v ((y : ∀ w, (UB w).X (3 - (J - 1))) v) :=
          Finset.sum_congr rfl fun v _ => he3 v _
      _ = asDual φ y := hy.symm

end Splitting

/-! ### (a) The generic per-place reduction -/

section Generic

variable (k : Type u) [CommRing k] (GS : Type u) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {V : Type u} (Gv : V → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup B] [Module k B] [DistribMulAction GS B] [SMulCommClass GS k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul GS B]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : A →ₗ[k] B →ₗ[k] T) (hβ : ∀ (g : GS) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × B => β x.1 x.2)

/-- **The per-place local duality map of genuine local conditions** with `τ≥2` isotropy data
(Nekovář 6.2.2): at the place `v`, `Cone(U_v → C(G_v, A))[−1] → Hom_k(U'_v, k)[−3]`,
`(u, x) ↦ (y ↦ tr_v(x ∪ i'_v y + h_v(u, y)))`. -/
abbrev orthPlaceMap (ΔA : LocalConditions k GS Gv loc A) (ΔB : LocalConditions k GS Gv loc B)
    (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB)
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d 1 2 rfl z) = 0) (v : V) :
    GHom (coneCx (orthNeg (ΔA.i v))) (dualCx (ΔB.U v) 3) :=
  orthLocalMap (ΔA.i v) (ΔB.i v) (localPair k GS Gv loc β hβ hβc v) (I.toLocal v) (trv v)
    (htrv v)

/-- The local condition map `−i_S` of the genuine Selmer data acts place by place. -/
theorem orth_negι_apply (ΔA : LocalConditions k GS Gv loc A) (i j : ℤ) (h : i = j)
    (u : (piCx ΔA.U).X i) (v : V) :
    ((negι (selData k GS Gv loc A ΔA)).f i j h u : ∀ w, (localCx k GS Gv loc A w).X j) v =
      (orthNeg (ΔA.i v)).f i j h ((u : ∀ w, (ΔA.U w).X i) v) :=
  rfl

/-- **Values of the global local duality map of `τ≥2` data, place by place**: if the global
trace restricts on the local part to `∑_v tr_v`, the global local duality map
`(u, x) ↦ (y ↦ tr(0, x ∪ i' y + h(u, y)))` is the sum of the per-place local duality maps.
PROVED. -/
theorem orth_localDualityMapT_apply (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB)
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d 1 2 rfl z) = 0) [Fintype V]
    (tr : (coneCx (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), (truncSub (localSumCx k GS Gv loc T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (i j : ℤ) (h : i = j) (u : (piCx ΔA.U).X i) (x : (localSumCx k GS Gv loc A).X (i - 1))
    (y : (piCx ΔB.U).X (3 - j)) :
    asDual ((localDualityMap (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I) tr htr).f i j h
        ((u, x) : coneT (negι (selData k GS Gv loc A ΔA)) i)) y =
      ∑ v, asDual ((orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I trv htrv v).f i j h
        (((u : ∀ w, (ΔA.U w).X i) v, (x : ∀ w, (localCx k GS Gv loc A w).X (i - 1)) v) :
          coneT (orthNeg (ΔA.i v)) i)) ((y : ∀ w, (ΔB.U w).X (3 - j)) v) := by
  subst h
  have h1 : (selCupFunT (genuinePairDataTrunc k GS Gv loc β hβ hβc ΔA ΔB I) i (3 - i) 3
      (by omega) ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
      ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i))).1 = 0 := by
    change (globalPair k GS β hβ hβc).P i (3 - i) 3 _ 0 0 = 0
    simp
  refine (localDualityMap_apply (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I) tr htr i u x
    y).trans ?_
  refine (congrArg tr (selCupFun_toSelPairData (genuinePairDataTrunc k GS Gv loc β hβ hβc ΔA ΔB I)
    i (3 - i) 3 (by omega) ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
    ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i)))).trans ?_
  refine (congrArg (fun a : (globalCx k GS T).X 3 => tr (a,
    (truncSub (localSumCx k GS Gv loc T) (3 - 1)).mkQ
      (selCupFunT (genuinePairDataTrunc k GS Gv loc β hβ hβc ΔA ΔB I) i (3 - i) 3 (by omega)
        ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
        ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i))).2)) h1).trans ?_
  refine (hsum _).trans ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Eq.trans ?_ (orthLocalMap_apply _ _ _ _ _ _ i i rfl _ _ _).symm
  congr 1
  have h0 : (localPair k GS Gv loc β hβ hβc v).P i (3 - i - 1) (3 - 1) (by omega)
      (((resS k GS Gv loc A).f i i rfl 0 : ∀ w, (localCx k GS Gv loc A w).X i) v) 0 = 0 :=
    map_zero _
  change (localPair k GS Gv loc β hβ hβc v).P (i - 1) (3 - i) (3 - 1) (by omega)
      ((x : ∀ w, (localCx k GS Gv loc A w).X (i - 1)) v)
      ((ΔB.i v).f (3 - i) (3 - i) rfl ((y : ∀ w, (ΔB.U w).X (3 - i)) v)) +
    sgn i • (localPair k GS Gv loc β hβ hβc v).P i (3 - i - 1) (3 - 1) (by omega)
      (((resS k GS Gv loc A).f i i rfl 0 : ∀ w, (localCx k GS Gv loc A w).X i) v) 0 +
    I.h v i (3 - i) (3 - 1) (by omega) ((u : ∀ w, (ΔA.U w).X i) v)
      ((y : ∀ w, (ΔB.U w).X (3 - i)) v) = _
  rw [h0, smul_zero, add_zero]
  rfl

/-- **(a), `τ≥2` form: orthogonality place by place** (Nekovář 6.2.7 and 6.3.4, generalizing
lane RC26's (strict, relaxed) splitting): for finitely many places, local conditions `ΔA`, `ΔB`
with arbitrary `τ≥2` isotropy homotopies `I`, local traces `tr_v` killing coboundaries and a global
trace on `Cone(C(G_S, T) → τ≥2 ⊕_v C(G_v, T))[−1]` whose local part is `∑_v tr_v`, if at every
place the per-place local duality map
`Cone(U_v → C(G_v, A))[−1] → Hom_k(U'_v, k)[−3]`, `(u, x) ↦ (y ↦ tr_v(x ∪ i'_v y + h_v(u, y)))`
is a quasi-isomorphism, then so is the global local duality map. PROVED. -/
theorem orth_localDualityMapT_quasiIso [Fintype V] (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB)
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d 1 2 rfl z) = 0)
    (tr : (coneCx (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), (truncSub (localSumCx k GS Gv loc T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (hloc : ∀ v, QuasiIso (GHom.toCC (orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I trv htrv v))) :
    QuasiIso (GHom.toCC (localDualityMap (genuinePairDataT k GS Gv loc β hβ hβc ΔA ΔB I) tr htr)) :=
  quasiIso_of_coneCx_acyclic _ (orthCone_acyclic (negι (selData k GS Gv loc A ΔA))
    (fun v => orthNeg (ΔA.i v)) (orth_negι_apply k GS Gv loc ΔA) _
    (fun v => orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I trv htrv v)
    (orth_localDualityMapT_apply k GS Gv loc β hβ hβc ΔA ΔB I trv htrv tr htr hsum)
    (fun v => coneCx_acyclic_of_quasiIso _ (hloc v)))

/-- **Values of the global local duality map of untruncated data, place by place** (as
`orth_localDualityMapT_apply`, for lane RC26's round-1 `IsotropyData` and a trace on the full
cone whose local part is `∑_v tr_v`). PROVED. -/
theorem orth_localDualityMap_apply (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : IsotropyData k GS Gv loc β hβ hβc ΔA ΔB)
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d 1 2 rfl z) = 0) [Fintype V]
    (tr : (coneCx (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), z) = ∑ v, trv v (z v))
    (i j : ℤ) (h : i = j) (u : (piCx ΔA.U).X i) (x : (localSumCx k GS Gv loc A).X (i - 1))
    (y : (piCx ΔB.U).X (3 - j)) :
    asDual ((localDualityMap (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) tr htr).f i j h
        ((u, x) : coneT (negι (selData k GS Gv loc A ΔA)) i)) y =
      ∑ v, asDual ((orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I.toTrunc trv htrv v).f i j h
        (((u : ∀ w, (ΔA.U w).X i) v, (x : ∀ w, (localCx k GS Gv loc A w).X (i - 1)) v) :
          coneT (orthNeg (ΔA.i v)) i)) ((y : ∀ w, (ΔB.U w).X (3 - j)) v) := by
  subst h
  have h1 : (selCupFun (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) i (3 - i) 3
      (by omega) ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
      ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i))).1 = 0 := by
    change (globalPair k GS β hβ hβc).P i (3 - i) 3 _ 0 0 = 0
    simp
  have h2 : selCupFun (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) i (3 - i) 3
      (by omega) ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
      ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i)) =
      ((0 : (globalCx k GS T).X 3), (selCupFun (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) i
        (3 - i) 3 (by omega) ((0, u, x) : selT (selData k GS Gv loc A ΔA) i)
        ((0, y, 0) : selT (selData k GS Gv loc B ΔB) (3 - i))).2) :=
    Prod.ext h1 rfl
  refine (localDualityMap_apply (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) tr htr i u x
    y).trans ?_
  refine ((congrArg tr h2).trans (hsum _)).trans ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Eq.trans ?_ (orthLocalMap_apply _ _ _ _ _ _ i i rfl _ _ _).symm
  congr 1
  have h0 : (localPair k GS Gv loc β hβ hβc v).P i (3 - i - 1) (3 - 1) (by omega)
      (((resS k GS Gv loc A).f i i rfl 0 : ∀ w, (localCx k GS Gv loc A w).X i) v) 0 = 0 :=
    map_zero _
  change (localPair k GS Gv loc β hβ hβc v).P (i - 1) (3 - i) (3 - 1) (by omega)
      ((x : ∀ w, (localCx k GS Gv loc A w).X (i - 1)) v)
      ((ΔB.i v).f (3 - i) (3 - i) rfl ((y : ∀ w, (ΔB.U w).X (3 - i)) v)) +
    sgn i • (localPair k GS Gv loc β hβ hβc v).P i (3 - i - 1) (3 - 1) (by omega)
      (((resS k GS Gv loc A).f i i rfl 0 : ∀ w, (localCx k GS Gv loc A w).X i) v) 0 +
    I.h v i (3 - i) (3 - 1) (by omega) ((u : ∀ w, (ΔA.U w).X i) v)
      ((y : ∀ w, (ΔB.U w).X (3 - i)) v) = _
  rw [h0, smul_zero, add_zero]
  rfl

/-- **(a), untruncated form** (lane RC26's round-1 `OrthogonalComplements` shape): as
`orth_localDualityMapT_quasiIso` for untruncated isotropy data `I` (the per-place maps are those of
`I.toTrunc`) and a trace on the full cone whose local part is `∑_v tr_v`. PROVED. -/
theorem orth_localDualityMap_quasiIso [Fintype V] (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : IsotropyData k GS Gv loc β hβ hβc ΔA ΔB)
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d 1 2 rfl z) = 0)
    (tr : (coneCx (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), z) = ∑ v, trv v (z v))
    (hloc : ∀ v, QuasiIso (GHom.toCC
      (orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I.toTrunc trv htrv v))) :
    QuasiIso (GHom.toCC (localDualityMap (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) tr htr)) :=
  quasiIso_of_coneCx_acyclic _ (orthCone_acyclic (negι (selData k GS Gv loc A ΔA))
    (fun v => orthNeg (ΔA.i v)) (orth_negι_apply k GS Gv loc ΔA) _
    (fun v => orthPlaceMap k GS Gv loc β hβ hβc ΔA ΔB I.toTrunc trv htrv v)
    (orth_localDualityMap_apply k GS Gv loc β hβ hβc ΔA ΔB I trv htrv tr htr hsum)
    (fun v => coneCx_acyclic_of_quasiIso _ (hloc v)))

end Generic

/-! ### (a) for the genuine Galois data -/

section Galois

variable (K : Type) [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type}
  [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- The local cup product `C(G_{K_v}, M) × C(G_{K_v}, M') → C(G_{K_v}, T)` of the genuine Galois
data at `v ∈ S`. -/
abbrev orthGaloisPair (v : Places K S) :=
  localPair R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β) v

/-- **(a), `τ≥2` form, for the genuine Galois data** (`OrthogonalComplementsT` of lane RC26 from
per-place orthogonality; Nekovář 6.2.7: `Δ(X₁) ⊥⊥ Δ(X₂)` iff `Δ_v(X₁) ⊥⊥ Δ_v(X₂)` for all
`v ∈ S_f`): for finitely many places, local traces `tr_v` on `C²_cont(G_{K_v}, T)` killing
coboundaries, a global trace on the truncated compact cone whose local part is `∑_v tr_v`, and
arbitrary `τ≥2` isotropy data `I`, if every per-place local duality map
`Cone(U_v → C(G_{K_v}, M))[−1] → Hom_R(U'_v, R)[−3]` is a quasi-isomorphism, then `ΔA` and `ΔB`
are orthogonal complements. PROVED. -/
theorem orthogonalComplementsT_of_places [Fintype (Places K S)]
    (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB)
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (hloc : ∀ v, QuasiIso (GHom.toCC (orthLocalMap (ΔA.i v) (ΔB.i v) (orthGaloisPair K β hβ v)
      (I.toLocal v) (trv v) (htrv v)))) :
    OrthogonalComplementsT K β hβ ΔA ΔB I tr htr :=
  orth_localDualityMapT_quasiIso R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ (continuous_pairing β) ΔA ΔB I trv htrv tr htr hsum hloc

/-- **(a), untruncated form, for the genuine Galois data** (lane RC26's round-1
`OrthogonalComplements`): as `orthogonalComplementsT_of_places`, for untruncated isotropy data and
a trace on the full compact cone whose local part is `∑_v tr_v`. PROVED. -/
theorem orthogonalComplements_of_places [Fintype (Places K S)]
    (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisIsotropyData K S R β hβ ΔA ΔB)
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galoisCompactT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), z) = ∑ v, trv v (z v))
    (hloc : ∀ v, QuasiIso (GHom.toCC (orthLocalMap (ΔA.i v) (ΔB.i v) (orthGaloisPair K β hβ v)
      (I.toTrunc.toLocal v) (trv v) (htrv v)))) :
    OrthogonalComplements K β hβ ΔA ΔB I tr htr :=
  orth_localDualityMap_quasiIso R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ (continuous_pairing β) ΔA ΔB I trv htrv tr htr hsum hloc

/-- **(a) for local conditions given place by place** (lane RC28's `CondAt`/`ofCondAt`, with the
per-place isotropy homotopies in the other group's per-place interface `LocalTruncIsotropy`, glued
by lane RC26's `TruncIsotropyData.ofLocal`): if at every place `v ∈ S` the per-place local duality
map of `(c v, c' v, J v, tr_v)` is a quasi-isomorphism, the local conditions `ofCondAt c` and
`ofCondAt c'` are orthogonal complements. PROVED. -/
theorem orthogonalComplementsT_ofCondAt [Fintype (Places K S)]
    (c : ∀ v : Places K S, ZInQ.Manuscript.RC.CoefModules.CondAt K S R M v)
    (c' : ∀ v : Places K S, ZInQ.Manuscript.RC.CoefModules.CondAt K S R M' v)
    (J : ∀ v : Places K S, LocalTruncIsotropy (c v).i (c' v).i (orthGaloisPair K β hβ v))
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galoisCompactTT K S R β hβ (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M c)
      (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M' c') (TruncIsotropyData.ofLocal J)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M c)
      (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M' c') (TruncIsotropyData.ofLocal J)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (hloc : ∀ v, QuasiIso (GHom.toCC (orthLocalMap (c v).i (c' v).i (orthGaloisPair K β hβ v)
      (J v) (trv v) (htrv v)))) :
    OrthogonalComplementsT K β hβ (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M c)
      (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M' c') (TruncIsotropyData.ofLocal J) tr htr :=
  orthogonalComplementsT_of_places K β hβ (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M c)
    (ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M' c')
    (TruncIsotropyData.ofLocal (ΔA := ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M c)
      (ΔB := ZInQ.Manuscript.RC.CoefModules.ofCondAt K S R M' c') J) trv htrv tr htr hsum hloc

end Galois

/-! ### Non-vacuity of the per-place hypothesis -/

section NonVacuity

variable {k : Type u} [CommRing k]

/-- `−id` is an isomorphism of complexes. -/
theorem orthNeg_idGHom_isIso (B : GCx k) : IsIso (GHom.toCC (orthNeg (idGHom B))) :=
  ⟨⟨GHom.toCC (orthNeg (idGHom B)), by
    ext i x
    exact neg_neg x, by
    ext i x
    exact neg_neg x⟩⟩

/-- The cone `Cone(id_L)[−1]` of the full condition is acyclic. PROVED. -/
theorem orthNeg_idGHom_cone_acyclic (B : GCx k) : GAcyclic (coneCx (orthNeg (idGHom B))) := by
  apply coneCx_acyclic_of_quasiIso
  have := orthNeg_idGHom_isIso B
  infer_instance

/-- **Non-vacuity of the per-place hypothesis of (a)**: for the full condition `id : L → L`
against the zero condition `0 → L'`, with any `τ≥2` isotropy homotopy and any local trace, the
per-place local duality map `Cone(id)[−1] → Hom(0, R)[−3]` is a quasi-isomorphism (both sides
are acyclic; tex 2813–2814: "A full condition is paired with the zero condition"). PROVED. -/
theorem orthLocalMap_full_zero_quasiIso {L L' E : GCx k} (P : GPair L L' E)
    (J : LocalTruncIsotropy (idGHom L) (zeroGHom (SelmerComplex.zeroCx k) L') P) (trv : E.X 2 →ₗ[k] k)
    (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0) :
    QuasiIso (GHom.toCC (orthLocalMap (idGHom L) (zeroGHom (SelmerComplex.zeroCx k) L') P J trv htrv)) := by
  apply quasiIso_of_acyclic
  · rw [acyclic_toCC_iff]
    exact orthNeg_idGHom_cone_acyclic L
  · rw [acyclic_toCC_iff]
    intro i j l hij hjl φ _
    refine ⟨0, dualCx_ext fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim (α := PUnit) x 0
    rw [hx, map_zero, map_zero]

/-- **Non-vacuity of the whole reduction**: the per-place hypothesis holds at every place for the
full conditions against the zero conditions (lane RC28's `fullAt`, `zeroAt`), for every family of
per-place `τ≥2` isotropy homotopies and every family of local traces — so
`orthogonalComplementsT_ofCondAt` recovers lane RC26's `orthogonal_relaxed_strictT` shape. -/
theorem orthLocalMap_fullAt_zeroAt_quasiIso (K : Type) [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R] {M M' T : Type}
    [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
    [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
    [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
    [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
    (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
    (v : Places K S)
    (J : LocalTruncIsotropy (ZInQ.Manuscript.RC.CoefModules.fullAt K S R M v).i
      (ZInQ.Manuscript.RC.CoefModules.zeroAt K S R M' v).i (orthGaloisPair K β hβ v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) :
    QuasiIso (GHom.toCC (orthLocalMap (ZInQ.Manuscript.RC.CoefModules.fullAt K S R M v).i
      (ZInQ.Manuscript.RC.CoefModules.zeroAt K S R M' v).i (orthGaloisPair K β hβ v) J trv htrv)) :=
  orthLocalMap_full_zero_quasiIso _ J trv htrv

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
