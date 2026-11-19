import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageActual
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Assembly

/-!
Theorem 5.3, Lane RC0 round 15: the two conventions for no condition at a new place

Tex 5056–5062: the stage complex carries no condition at the new derivative prime `q`. Two
conventions write this:

* the old places only: `q` is in the support of the global group, but there is no local term
  at `q` (the RC53 group's `ActualStageFamily.datum`);
* every place of the support carries a condition, and `q` carries the full condition
  `U_q = C^•(G_q, M)` with the identity inclusion (`fullAt`).

The local term of a full place is the cone of an identity, which is contractible. This file
proves that the two conventions agree up to homotopy equivalence, with the same global complex.

* `addFull D L r`: a Selmer datum with one more place carrying the full condition.
  `fullRetract`: its Selmer complex deformation retracts onto `selCx D`, with inclusion
  `(a, u, x) ↦ (a, (u, r a), (x, 0))`, projection `(a, (u, y), (x, z)) ↦ (a, u, x)` and
  contraction `(a, (u, y), (x, z)) ↦ (0, (0, −z), (0, 0))`. `addFullEquiv`: the homotopy
  equivalence. Both maps are the identity on the global complex.
* `splitHom`, `splitHom_isIso`: for local conditions `Δ` on places `ι'`, an embedding
  `e : ι → ι'` onto the complement of a place `q` whose condition map is bijective (the full
  condition), the genuine datum `selData Δ` is isomorphic to `addFull` of the datum restricted
  along `e`. `fullPlaceEquiv`: the homotopy equivalence
  `selCx (selData Δ) ≃ selCx (selData (Δ ∘ e))`, the identity on the global complex
  (`fullPlaceEquiv_hom_projG`, `fullPlaceEquiv_inv_projG`).
* `extendFull`: old conditions at `S₀` extended by `fullAt` at `q`; `mem_insert_new`,
  `extendFull_new`, `extendFull_at`, `extendFull_old`, `extendFull_fullOrZero`: the trivial
  instantiation lemmas.
* `insertEquiv`: the instance for `S = insert q S₀`, `q ∉ S₀`, and
  `actualStageFamily_equiv`: the RC0-style datum with the RC53 group's old conditions extended
  by `fullAt` at `q i` is homotopy equivalent to `F.globalCx i`.
* `actualSelData_refl_eq`, `actualSelData_insertEquiv`: the RC0 datum `actualSelData` with
  coefficient support and Selmer support both `insert q S₀` and old conditions `extendFull`
  is homotopy equivalent to the old-places datum with the same coefficient module.
* Towards the coefficient comparison `MinS (subset_refl S) W i α` against `Mcoef K S W i α`:
  `inflMap_refl_apply`, `minS_refl_smul` (the two actions agree), the mutually inverse global
  and local cochain comparisons `minSToMcoef`, `mcoefToMinS`, `locMinSToMcoef`,
  `locMcoefToMinS`, the transport `condToMinS` of conditions, and `selHom`, `selHom_isIso`
  (a morphism of Selmer data with bijective components is an isomorphism of Selmer complexes).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.StageSupport

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Limits (GRetract)

/-! **One more place with the full condition, abstractly** -/

section Abstract

variable {S : Type} [CommRing S]

/-- The product of two complexes, with the componentwise differential. -/
def prodGCx (A B : GCx S) : GCx S where
  X n := ModuleCat.of S (A.X n × B.X n)
  d i j h := (A.d i j h).prodMap (B.d i j h)
  d_d i j l hij hjl x := Prod.ext (A.d_d i j l hij hjl x.1) (B.d_d i j l hij hjl x.2)

/-- The product of two chain maps. -/
def prodGHom {A A' B B' : GCx S} (f : GHom A A') (g : GHom B B') :
    GHom (prodGCx A B) (prodGCx A' B') where
  f i j h := (f.f i j h).prodMap (g.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    Prod.ext (f.comm i i₁ j j₁ hij h₁ h₂ hj x.1) (g.comm i i₁ j j₁ hij h₁ h₂ hj x.2)

/-- The chain map into a product with two given components. -/
def liftGHom {A B C : GCx S} (f : GHom A B) (g : GHom A C) : GHom A (prodGCx B C) where
  f i j h := (f.f i j h).prod (g.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    Prod.ext (f.comm i i₁ j j₁ hij h₁ h₂ hj x) (g.comm i i₁ j j₁ hij h₁ h₂ hj x)

/-- The identity chain map at equal indices. -/
theorem idGHom_apply_self (B : GCx S) (i : ℤ) (h : i = i) (x : B.X i) :
    (idGHom B).f i i h x = x :=
  rfl

/-- Index transport of a chain map through the identity chain map. -/
theorem idGHom_f_ghom {A B : GCx S} (f : GHom A B) (i j l : ℤ) (hij : i = j) (hjl : j = l)
    (x : A.X i) : (idGHom B).f j l hjl (f.f i j hij x) = f.f i l (hij.trans hjl) x := by
  subst hij hjl
  rfl

/-- Index transport of a differential through the identity chain map. -/
theorem idGHom_f_d (B : GCx S) (i j l : ℤ) (hij : i + 1 = j) (hjl : j = l) (x : B.X i) :
    (idGHom B).f j l hjl (B.d i j hij x) = B.d i l (hij.trans hjl) x := by
  subst hjl
  rfl

/-- **One more place with the full condition**: local complexes `L ⊕ L_q`, conditions
`U ⊕ L_q` with condition map `ι ⊕ id`, restriction `(res, r)`; the same global complex. -/
def addFull (D : SelData S) (L : GCx S) (r : GHom D.G L) : SelData S :=
  ⟨D.G, prodGCx D.U L, prodGCx D.L L, liftGHom D.res r, prodGHom D.ι (idGHom L)⟩

variable (D : SelData S) (L : GCx S) (r : GHom D.G L)

/-- The inclusion `(a, u, x) ↦ (a, (u, r a), (x, 0))` in one degree. -/
def inclFun (n : ℤ) : selT D n →ₗ[S] selT (addFull D L r) n where
  toFun c := (c.1, (c.2.1, r.f n n rfl c.1), (c.2.2, 0))
  map_add' _ _ :=
    Prod.ext rfl (Prod.ext (Prod.ext rfl (map_add _ _ _)) (Prod.ext rfl (add_zero 0).symm))
  map_smul' t _ :=
    Prod.ext rfl (Prod.ext (Prod.ext rfl (map_smul _ _ _)) (Prod.ext rfl (smul_zero t).symm))

/-- The projection `(a, (u, y), (x, z)) ↦ (a, u, x)` in one degree. -/
def projFun (n : ℤ) : selT (addFull D L r) n →ₗ[S] selT D n where
  toFun c := (c.1, c.2.1.1, c.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The contraction `(a, (u, y), (x, z)) ↦ (0, (0, −z), (0, 0))`, of degree `−1`. -/
def homFun (a b : ℤ) (hab : b + 1 = a) : selT (addFull D L r) a →ₗ[S] selT (addFull D L r) b where
  toFun c := (0, (0, -(idGHom L).f (a - 1) b (by omega) c.2.2.2), (0, 0))
  map_add' c c' := by
    refine Prod.ext (add_zero 0).symm (Prod.ext (Prod.ext (add_zero 0).symm ?_)
      (Prod.ext (add_zero 0).symm (add_zero 0).symm))
    change -(idGHom L).f (a - 1) b _ (c.2.2.2 + c'.2.2.2) =
      -(idGHom L).f (a - 1) b _ c.2.2.2 + -(idGHom L).f (a - 1) b _ c'.2.2.2
    rw [map_add, neg_add]
  map_smul' t c := by
    refine Prod.ext (smul_zero t).symm (Prod.ext (Prod.ext (smul_zero t).symm ?_)
      (Prod.ext (smul_zero t).symm (smul_zero t).symm))
    change -(idGHom L).f (a - 1) b _ (t • c.2.2.2) = t • -(idGHom L).f (a - 1) b _ c.2.2.2
    rw [map_smul, smul_neg]

/-- The inclusion `selCx D → selCx (addFull D L r)` as a chain map. -/
def inclHom : GHom (selCx D) (selCx (addFull D L r)) where
  f i j h := by
    subst h
    exact inclFun D L r i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext (Prod.ext rfl (r.comm i i₁ i i₁ rfl h₁ h₂ rfl a))
      (Prod.ext rfl ?_))
    change (0 : L.X (i₁ - 1)) = r.f i (i₁ - 1) _ a -
      (idGHom L).f i (i₁ - 1) _ (r.f i i rfl a) - L.d (i - 1) (i₁ - 1) _ 0
    rw [idGHom_f_ghom, map_zero, sub_zero, sub_self]

/-- The projection `selCx (addFull D L r) → selCx D` as a chain map. -/
def projHom : GHom (selCx (addFull D L r)) (selCx D) where
  f i j h := by
    subst h
    exact projFun D L r i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    rfl

/-- **The Selmer complex with one more full place deformation retracts onto `selCx D`**:
`p i = 1`, `1 − i p = d h + h d`, `h² = 0`, `h i = 0`, `p h = 0`. Kind: PROVED. -/
def fullRetract : GRetract (selCx (addFull D L r)) (selCx D) where
  i := inclHom D L r
  p := projHom D L r
  h := homFun D L r
  p_i _ _ := rfl
  homotopy n c := by
    obtain ⟨a, ⟨u, y⟩, ⟨x, z⟩⟩ := c
    have e1 := idGHom_f_ghom r n (n + 1 - 1) n (by omega) (by omega) a
    have e2 := idGHom_f_ghom (idGHom L) n (n + 1 - 1) n (by omega) (by omega) y
    have e3 := idGHom_f_d L (n - 1) (n + 1 - 1) n (by omega) (by omega) z
    refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
    · change a - a = D.G.d (n - 1) n _ (0 : D.G.X (n - 1)) + (0 : D.G.X n)
      rw [map_zero, sub_self, add_zero]
      rfl
    · change u - u = D.U.d (n - 1) n _ (0 : D.U.X (n - 1)) + (0 : D.U.X n)
      rw [map_zero, sub_self, add_zero]
    · change y - r.f n n rfl a = L.d (n - 1) n _ (-(idGHom L).f (n - 1) (n - 1) rfl z) +
        -(idGHom L).f (n + 1 - 1) n _ (r.f n (n + 1 - 1) _ a -
          (idGHom L).f n (n + 1 - 1) _ y - L.d (n - 1) (n + 1 - 1) _ z)
      rw [map_sub, map_sub, e1, e2, e3, idGHom_apply_self, idGHom_apply_self, map_neg]
      abel
    · change x - x = D.res.f (n - 1) (n - 1) rfl (0 : D.G.X (n - 1)) -
        D.ι.f (n - 1) (n - 1) rfl (0 : D.U.X (n - 1)) -
        D.L.d (n - 1 - 1) (n - 1) _ (0 : D.L.X (n - 1 - 1)) + (0 : D.L.X (n - 1))
      rw [map_zero, map_zero, map_zero, sub_self, sub_self, sub_self, add_zero]
    · change z - 0 = r.f (n - 1) (n - 1) rfl (0 : D.G.X (n - 1)) -
        (idGHom L).f (n - 1) (n - 1) rfl (-(idGHom L).f (n - 1) (n - 1) rfl z) -
        L.d (n - 1 - 1) (n - 1) _ (0 : L.X (n - 1 - 1)) + (0 : L.X (n - 1))
      rw [map_zero, map_zero, idGHom_apply_self, idGHom_apply_self]
      abel
  h_h a b c hab hbc x := by
    refine Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) rfl)
    change -(idGHom L).f (b - 1) c _ 0 = 0
    rw [map_zero, neg_zero]
  h_i a b hab y := by
    refine Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) rfl)
    change -(idGHom L).f (a - 1) b _ 0 = 0
    rw [map_zero, neg_zero]
  p_h _ _ _ _ := rfl

/-- **The Selmer complex of `addFull D L r` is homotopy equivalent to that of `D`**, through
the inclusion and the projection of `fullRetract`. Kind: PROVED. -/
def addFullEquiv : HomotopyEquiv (selCx D).toCC (selCx (addFull D L r)).toCC :=
  (fullRetract D L r).homotopyEquiv

/-- Both data have the same global complex. -/
theorem addFull_G : (addFull D L r).G = D.G :=
  rfl

/-- The inclusion is the identity on the global complex. Kind: PROVED. -/
theorem inclHom_projG :
    GHom.toCC (inclHom D L r) ≫ GHom.toCC (projG (addFull D L r)) = GHom.toCC (projG D) := by
  ext n c
  rfl

/-- The projection is the identity on the global complex. Kind: PROVED. -/
theorem projHom_projG :
    GHom.toCC (projHom D L r) ≫ GHom.toCC (projG D) = GHom.toCC (projG (addFull D L r)) := by
  ext n c
  rfl

end Abstract

/-! **Places: an extra place with a bijective (full) condition map** -/

section Split

/-- A function on `ι'` is determined by its restriction along `e` and its value at `q`, and
both can be prescribed, when `e` is injective with image the complement of `q`. Kind: PROVED. -/
theorem pi_split_bijective {ι ι' : Type} {β : ι' → Type} (e : ι → ι') (q : ι')
    (he : Function.Injective e) (hq : ∀ v, e v ≠ q) (hcov : ∀ w, w ≠ q → ∃ v, e v = w) :
    Function.Bijective (fun x : (∀ w, β w) => ((fun v => x (e v)), x q)) := by
  classical
  refine ⟨fun x y hxy => ?_, fun yz => ?_⟩
  · funext w
    by_cases hw : w = q
    · subst hw
      exact congrArg Prod.snd hxy
    · obtain ⟨v, rfl⟩ := hcov w hw
      exact congrFun (congrArg Prod.fst hxy) v
  · obtain ⟨y, z⟩ := yz
    refine ⟨fun w => if hw : w = q then cast (congrArg β hw.symm) z else
      cast (congrArg β (hcov w hw).choose_spec) (y (hcov w hw).choose), Prod.ext ?_ ?_⟩
    · funext v
      have key : ∀ (v' : ι) (h : e v' = e v), cast (congrArg β h) (y v') = y v := by
        intro v' h
        obtain rfl := he h
        rfl
      change (if hw : e v = q then cast (congrArg β hw.symm) z else
        cast (congrArg β (hcov (e v) hw).choose_spec) (y (hcov (e v) hw).choose)) = y v
      rw [dite_eq_right (hq v)]
      exact key _ (hcov (e v) (hq v)).choose_spec
    · change (if hw : q = q then cast (congrArg β hw.symm) z else
        cast (congrArg β (hcov q hw).choose_spec) (y (hcov q hw).choose)) = z
      rw [dite_eq_left rfl]
      rfl

variable (k : Type) [CommRing k] (GS : Type) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι ι' : Type} (Gv : ι' → Type) [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  (e : ι → ι') (q : ι')

/-- Local conditions restricted along `e : ι → ι'` (the old places). -/
def comapConditions (Δ : LocalConditions k GS Gv loc M) :
    LocalConditions k GS (fun v => Gv (e v)) (fun v => loc (e v)) M :=
  ⟨fun v => Δ.U (e v), fun v => Δ.i (e v)⟩

/-- Restriction of global cochains to the place `q`. -/
abbrev resAt : GHom (globalCx k GS M) (localCx k GS Gv loc M q) :=
  natHom (resCochains (k := k) (M := M) (loc q))

variable (Δ : LocalConditions k GS Gv loc M)

/-- The split datum: the datum restricted along `e`, plus the place `q` with the full
condition. -/
abbrev splitData : SelData k :=
  addFull (selData k GS (fun v => Gv (e v)) (fun v => loc (e v)) M
    (comapConditions k GS Gv loc M e Δ)) (localCx k GS Gv loc M q) (resAt k GS Gv loc M q)

/-- The comparison `(a, u, x) ↦ (a, ((u ∘ e), i_q (u q)), ((x ∘ e), x q))` in one degree. -/
def splitFun (n : ℤ) :
    selT (selData k GS Gv loc M Δ) n →ₗ[k] selT (splitData k GS Gv loc M e q Δ) n where
  toFun c := (c.1, ((fun v => c.2.1 (e v)), (Δ.i q).f n n rfl (c.2.1 q)),
    ((fun v => c.2.2 (e v)), c.2.2 q))
  map_add' _ _ := Prod.ext rfl (Prod.ext (Prod.ext rfl (map_add _ _ _)) rfl)
  map_smul' _ _ := Prod.ext rfl (Prod.ext (Prod.ext rfl (map_smul _ _ _)) rfl)

/-- The comparison as a chain map. Kind: PROVED. -/
def splitHom :
    GHom (selCx (selData k GS Gv loc M Δ)) (selCx (splitData k GS Gv loc M e q Δ)) where
  f i j h := by
    subst h
    exact splitFun k GS Gv loc M e q Δ i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    have e1 := idGHom_f_ghom (Δ.i q) i i (i₁ - 1) rfl (by omega) (u q)
    refine Prod.ext rfl (Prod.ext (Prod.ext rfl ((Δ.i q).comm i i₁ i i₁ rfl h₁ h₂ rfl (u q)))
      (Prod.ext rfl ?_))
    change (resAt k GS Gv loc M q).f i (i₁ - 1) (by omega) a -
        (Δ.i q).f i (i₁ - 1) (by omega) (u q) -
        (localCx k GS Gv loc M q).d (i - 1) (i₁ - 1) (by omega) (x q) =
      (resAt k GS Gv loc M q).f i (i₁ - 1) (by omega) a -
        (idGHom (localCx k GS Gv loc M q)).f i (i₁ - 1) (by omega) ((Δ.i q).f i i rfl (u q)) -
        (localCx k GS Gv loc M q).d (i - 1) (i₁ - 1) (by omega) (x q)
    rw [e1]

variable {e q}

/-- **The comparison is bijective in every degree** when `e` is injective with image the
complement of `q` and the condition map at `q` is bijective (the full condition). PROVED. -/
theorem splitFun_bijective (he : Function.Injective e) (hq : ∀ v, e v ≠ q)
    (hcov : ∀ w, w ≠ q → ∃ v, e v = w) (hfull : ∀ n, Function.Bijective ((Δ.i q).f n n rfl))
    (n : ℤ) : Function.Bijective (splitFun k GS Gv loc M e q Δ n) := by
  have hU := pi_split_bijective (β := fun w => (Δ.U w).X n) e q he hq hcov
  have hL := pi_split_bijective (β := fun w => (localCx k GS Gv loc M w).X (n - 1)) e q he hq
    hcov
  refine ⟨fun c c' h => ?_, fun t => ?_⟩
  · obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    have h1 : a = a' := congrArg Prod.fst h
    have h2 : ((fun v => u (e v)), (Δ.i q).f n n rfl (u q)) =
        ((fun v => u' (e v)), (Δ.i q).f n n rfl (u' q)) := congrArg (fun t => t.2.1) h
    have h3 : ((fun v => x (e v)), x q) = ((fun v => x' (e v)), x' q) :=
      congrArg (fun t => t.2.2) h
    have h21 : (fun v => u (e v)) = (fun v => u' (e v)) := congrArg Prod.fst h2
    have h22 : (Δ.i q).f n n rfl (u q) = (Δ.i q).f n n rfl (u' q) := congrArg Prod.snd h2
    have h4 : ((fun v => u (e v)), u q) = ((fun v => u' (e v)), u' q) :=
      Prod.ext h21 ((hfull n).1 h22)
    have hu : u = u' := hU.1 h4
    have hx : x = x' := hL.1 h3
    rw [h1, hu, hx]
  · obtain ⟨a, ⟨y, z⟩, ⟨x, t'⟩⟩ := t
    obtain ⟨z', hz'⟩ := (hfull n).2 z
    obtain ⟨u, hu⟩ := hU.2 (y, z')
    obtain ⟨x', hx'⟩ := hL.2 (x, t')
    have hu1 : (fun v => u (e v)) = y := congrArg Prod.fst hu
    have hu2 : (Δ.i q).f n n rfl (u q) = z := by
      rw [show u q = z' from congrArg Prod.snd hu, hz']
    have hx1 : ((fun v => x' (e v)), x' q) = (x, t') := hx'
    exact ⟨(a, u, x'), Prod.ext rfl (Prod.ext (Prod.ext hu1 hu2) hx1)⟩

/-- The comparison is an isomorphism of complexes. Kind: PROVED. -/
theorem splitHom_isIso (he : Function.Injective e) (hq : ∀ v, e v ≠ q)
    (hcov : ∀ w, w ≠ q → ∃ v, e v = w) (hfull : ∀ n, Function.Bijective ((Δ.i q).f n n rfl)) :
    IsIso (GHom.toCC (splitHom k GS Gv loc M e q Δ)) := by
  have : ∀ m, IsIso ((GHom.toCC (splitHom k GS Gv loc M e q Δ)).f m) := fun m => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact splitFun_bijective k GS Gv loc M Δ he hq hcov hfull m
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **An extra place with the full condition does not change the Selmer complex up to homotopy**:
for `e : ι → ι'` injective with image the complement of `q`, and a bijective condition map at `q`
(e.g. `U_q = C^•(G_q, M)` with the identity), `selCx (selData Δ)` is homotopy equivalent to the
Selmer complex of the conditions restricted along `e`, with the same global complex: the
comparison `splitHom` followed by the projection of `fullRetract`. Kind: PROVED. -/
def fullPlaceEquiv (he : Function.Injective e) (hq : ∀ v, e v ≠ q)
    (hcov : ∀ w, w ≠ q → ∃ v, e v = w) (hfull : ∀ n, Function.Bijective ((Δ.i q).f n n rfl)) :
    HomotopyEquiv (selCx (selData k GS Gv loc M Δ)).toCC
      (selCx (selData k GS (fun v => Gv (e v)) (fun v => loc (e v)) M
        (comapConditions k GS Gv loc M e Δ))).toCC :=
  haveI := splitHom_isIso k GS Gv loc M Δ he hq hcov hfull
  (HomotopyEquiv.ofIso (asIso (GHom.toCC (splitHom k GS Gv loc M e q Δ)))).trans
    (addFullEquiv _ _ _).symm

/-- Both data have the same global complex. -/
theorem comap_G : (selData k GS (fun v => Gv (e v)) (fun v => loc (e v)) M
    (comapConditions k GS Gv loc M e Δ)).G = (selData k GS Gv loc M Δ).G :=
  rfl

/-- **The homotopy equivalence is the identity on the global complex** (`hom`). Kind:
PROVED. -/
theorem fullPlaceEquiv_hom_projG (he : Function.Injective e) (hq : ∀ v, e v ≠ q)
    (hcov : ∀ w, w ≠ q → ∃ v, e v = w) (hfull : ∀ n, Function.Bijective ((Δ.i q).f n n rfl)) :
    (fullPlaceEquiv k GS Gv loc M Δ he hq hcov hfull).hom ≫ GHom.toCC (projG _) =
      GHom.toCC (projG (selData k GS Gv loc M Δ)) := by
  ext n c
  rfl

/-- **The homotopy equivalence is the identity on the global complex** (`inv`). Kind:
PROVED. -/
theorem fullPlaceEquiv_inv_projG (he : Function.Injective e) (hq : ∀ v, e v ≠ q)
    (hcov : ∀ w, w ≠ q → ∃ v, e v = w) (hfull : ∀ n, Function.Bijective ((Δ.i q).f n n rfl)) :
    (fullPlaceEquiv k GS Gv loc M Δ he hq hcov hfull).inv ≫
        GHom.toCC (projG (selData k GS Gv loc M Δ)) =
      GHom.toCC (projG (selData k GS (fun v => Gv (e v)) (fun v => loc (e v)) M
        (comapConditions k GS Gv loc M e Δ))) := by
  have := splitHom_isIso k GS Gv loc M Δ he hq hcov hfull
  have h1 : GHom.toCC (splitHom k GS Gv loc M e q Δ) ≫
      GHom.toCC (projG (splitData k GS Gv loc M e q Δ)) =
        GHom.toCC (projG (selData k GS Gv loc M Δ)) := by
    ext n c
    rfl
  have h2 : inv (GHom.toCC (splitHom k GS Gv loc M e q Δ)) ≫
      GHom.toCC (projG (selData k GS Gv loc M Δ)) =
        GHom.toCC (projG (splitData k GS Gv loc M e q Δ)) := by
    exact (IsIso.inv_comp_eq _).2 h1.symm
  change (GHom.toCC (inclHom _ _ _) ≫ inv (GHom.toCC (splitHom k GS Gv loc M e q Δ))) ≫
      GHom.toCC (projG (selData k GS Gv loc M Δ)) = _
  rw [Category.assoc, h2]
  exact inclHom_projG _ _ _

end Split

/-! **The instance at `insert q S₀`** -/

section Galois

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (CondAt fullAt zeroAt ofCondAt)

variable {K : Type} [Field K] [NumberField K]

/-- The old places `S₀` inside `insert q S₀`. -/
abbrev oldPlace (S₀ : Set (HeightOneSpectrum (𝓞 K))) (q : HeightOneSpectrum (𝓞 K))
    (v : Places K S₀) : Places K (insert q S₀) :=
  ⟨v.1, Or.inr v.2⟩

/-- The new place `q` of `insert q S₀`. -/
abbrev newPlace (S₀ : Set (HeightOneSpectrum (𝓞 K))) (q : HeightOneSpectrum (𝓞 K)) :
    Places K (insert q S₀) :=
  ⟨q, Or.inl rfl⟩

variable (S₀ : Set (HeightOneSpectrum (𝓞 K))) (q : HeightOneSpectrum (𝓞 K))

omit [NumberField K] in
/-- **The new place is in the enlarged support**: `q ∈ insert q S₀`. Kind: PROVED. -/
theorem mem_insert_new : q ∈ insert q S₀ :=
  Set.mem_insert q S₀

omit [NumberField K] in
theorem oldPlace_injective : Function.Injective (oldPlace S₀ q) := by
  intro v w h
  have h1 : (oldPlace S₀ q v).1 = (oldPlace S₀ q w).1 := congrArg Subtype.val h
  exact Subtype.ext h1

omit [NumberField K] in
theorem oldPlace_ne (hq : q ∉ S₀) (v : Places K S₀) : oldPlace S₀ q v ≠ newPlace S₀ q := by
  intro h
  have h1 : v.1 = q := congrArg Subtype.val h
  exact hq (h1 ▸ v.2)

omit [NumberField K] in
theorem oldPlace_cover (w : Places K (insert q S₀)) (hw : w ≠ newPlace S₀ q) :
    ∃ v, oldPlace S₀ q v = w := by
  have hw1 : w.1 ≠ q := fun h => hw (Subtype.ext h)
  exact ⟨⟨w.1, (Set.mem_insert_iff.mp w.2).resolve_left hw1⟩, rfl⟩

section Extend

variable (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k] (M : Type) [AddCommGroup M]
  [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

open Classical in
/-- **Old conditions at `S₀` extended by the full condition at `q`** (the conditions of RC0's
stage complex at `S₀ i := insert q S₀`): `fullAt` at a place over `q`, the given condition
elsewhere. -/
def extendFull (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k M v) :
    ∀ v : Places K S, v.1 ∈ insert q S₀ → CondAt K S k M v :=
  fun v h => if hv : v.1 = q then fullAt K S k M v else
    c v ((Set.mem_insert_iff.mp h).resolve_left hv)

/-- **The extended family is `fullAt` at `q`**, by definition. Kind: PROVED. -/
theorem extendFull_new (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k M v) (v : Places K S)
    (h : v.1 ∈ insert q S₀) (hv : v.1 = q) : extendFull S₀ q S k M c v h = fullAt K S k M v :=
  dite_eq_left hv

/-- The extended family at `q ∈ S` itself. Kind: PROVED. -/
theorem extendFull_at (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k M v) (hqS : q ∈ S) :
    extendFull S₀ q S k M c ⟨q, hqS⟩ (mem_insert_new S₀ q) = fullAt K S k M ⟨q, hqS⟩ :=
  extendFull_new S₀ q S k M c _ _ rfl

/-- The extended family is the given one at the other places. Kind: PROVED. -/
theorem extendFull_old (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k M v) (v : Places K S)
    (h : v.1 ∈ insert q S₀) (hv : v.1 ≠ q) :
    extendFull S₀ q S k M c v h = c v ((Set.mem_insert_iff.mp h).resolve_left hv) :=
  dite_eq_right hv

/-- **Full or zero old conditions stay full or zero after the extension** (the input `hfz` of
RC0's `oldConditions_fullOrZero` for `extendFull`). Kind: PROVED. -/
theorem extendFull_fullOrZero (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k M v)
    (hc : ∀ v h, c v h = fullAt K S k M v ∨ c v h = zeroAt K S k M v) (v : Places K S)
    (h : v.1 ∈ insert q S₀) :
    extendFull S₀ q S k M c v h = fullAt K S k M v ∨
      extendFull S₀ q S k M c v h = zeroAt K S k M v := by
  by_cases hv : v.1 = q
  · exact Or.inl (extendFull_new S₀ q S k M c v h hv)
  · rw [extendFull_old S₀ q S k M c v h hv]
    exact hc v _

end Extend

section Insert

variable (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K (insert q S₀)) M] [SMulCommClass (GKS K (insert q S₀)) k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul (GKS K (insert q S₀)) M]

/-- Conditions indexed by the old places (the RC53 group's format) in RC0's format. -/
def ofOld (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    ∀ w : Places K (insert q S₀), w.1 ∈ S₀ → CondAt K (insert q S₀) k M w :=
  fun w h => c ⟨w.1, h⟩

/-- RC0's conditions at every place of `insert q S₀`: the old ones and `fullAt` at `q`. -/
def fullExt (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    ∀ w : Places K (insert q S₀), CondAt K (insert q S₀) k M w :=
  fun w => extendFull S₀ q (insert q S₀) k M (ofOld S₀ q k M c) w w.2

/-- The old-places datum (the RC53 group's convention): `q` is in the support of the global
group, with no local term. -/
abbrev oldData (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    SelData k :=
  selData k (GKS K (insert q S₀)) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K (insert q S₀) v.1) M ⟨fun v => (c v).U, fun v => (c v).i⟩

/-- RC0's datum with `fullAt` at `q` (every place of `insert q S₀` carries a condition). -/
abbrev fullData (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    SelData k :=
  galoisSelData K (insert q S₀) k M (ofCondAt K (insert q S₀) k M (fullExt S₀ q k M c))

/-- Restricted to the old places, RC0's conditions are the old conditions. Kind: PROVED. -/
theorem comap_fullExt (hq : q ∉ S₀)
    (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    comapConditions k (GKS K (insert q S₀)) (fun w : Places K (insert q S₀) => Gloc K w.1)
        (fun w => locMap K (insert q S₀) w.1) M (oldPlace S₀ q)
        (ofCondAt K (insert q S₀) k M (fullExt S₀ q k M c)) =
      ⟨fun v => (c v).U, fun v => (c v).i⟩ := by
  have h : (fun v => fullExt S₀ q k M c (oldPlace S₀ q v)) = c := by
    funext v
    exact extendFull_old S₀ q (insert q S₀) k M _ _ _ (fun h => hq (h ▸ v.2))
  exact congrArg (fun c' : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v) =>
    (⟨fun v => (c' v).U, fun v => (c' v).i⟩ : LocalConditions k (GKS K (insert q S₀))
      (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K (insert q S₀) v.1) M)) h

/-- At the new place the condition map of RC0's conditions is the identity. Kind: PROVED. -/
theorem fullExt_new_bijective
    (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) (n : ℤ) :
    Function.Bijective
      (((ofCondAt K (insert q S₀) k M (fullExt S₀ q k M c)).i (newPlace S₀ q)).f n n rfl) := by
  have h : fullExt S₀ q k M c (newPlace S₀ q) =
      fullAt K (insert q S₀) k M (newPlace S₀ q) :=
    extendFull_new S₀ q (insert q S₀) k M _ _ _ rfl
  change Function.Bijective ((fullExt S₀ q k M c (newPlace S₀ q)).i.f n n rfl)
  rw [h]
  exact ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

/-- **The two conventions agree up to homotopy equivalence** at `insert q S₀`, `q ∉ S₀`: RC0's
datum (every place carries a condition, `fullAt` at `q`) and the old-places datum have
homotopy equivalent Selmer complexes, with the same global complex `C^•(G_{K, S₀ ∪ q}, M)`.
Kind: PROVED. -/
def insertEquiv (hq : q ∉ S₀)
    (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    HomotopyEquiv (selCx (fullData S₀ q k M c)).toCC (selCx (oldData S₀ q k M c)).toCC :=
  (fullPlaceEquiv k (GKS K (insert q S₀)) (fun w : Places K (insert q S₀) => Gloc K w.1)
    (fun w => locMap K (insert q S₀) w.1) M (ofCondAt K (insert q S₀) k M (fullExt S₀ q k M c))
    (oldPlace_injective S₀ q) (oldPlace_ne S₀ q hq) (oldPlace_cover S₀ q)
    (fullExt_new_bijective S₀ q k M c)).trans
    (HomotopyEquiv.ofIso (eqToIso (congrArg (fun Δ => (selCx (selData k (GKS K (insert q S₀))
      (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K (insert q S₀) v.1) M Δ)).toCC)
      (comap_fullExt S₀ q k M hq c))))

/-- An equality of local conditions over the same places is the identity on the global
complex. Kind: PROVED. -/
theorem eqToHom_projG {Δ₁ Δ₂ : LocalConditions k (GKS K (insert q S₀))
      (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K (insert q S₀) v.1) M}
    (h : Δ₁ = Δ₂) :
    eqToHom (congrArg (fun Δ => (selCx (selData k (GKS K (insert q S₀))
        (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K (insert q S₀) v.1) M Δ)).toCC) h) ≫
      GHom.toCC (projG (selData k (GKS K (insert q S₀)) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K (insert q S₀) v.1) M Δ₂)) =
    GHom.toCC (projG (selData k (GKS K (insert q S₀)) (fun v : Places K S₀ => Gloc K v.1)
        (fun v => locMap K (insert q S₀) v.1) M Δ₁)) := by
  subst h
  simp

/-- **The homotopy equivalence `insertEquiv` is the identity on the global complex.** Kind:
PROVED. -/
theorem insertEquiv_hom_projG (hq : q ∉ S₀)
    (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    (insertEquiv S₀ q k M hq c).hom ≫ GHom.toCC (projG (oldData S₀ q k M c)) =
      GHom.toCC (projG (fullData S₀ q k M c)) := by
  change ((fullPlaceEquiv k (GKS K (insert q S₀)) (fun w : Places K (insert q S₀) => Gloc K w.1)
      (fun w => locMap K (insert q S₀) w.1) M (ofCondAt K (insert q S₀) k M (fullExt S₀ q k M c))
      (oldPlace_injective S₀ q) (oldPlace_ne S₀ q hq) (oldPlace_cover S₀ q)
      (fullExt_new_bijective S₀ q k M c)).hom ≫
    eqToHom (congrArg (fun Δ => (selCx (selData k (GKS K (insert q S₀))
      (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K (insert q S₀) v.1) M Δ)).toCC)
      (comap_fullExt S₀ q k M hq c))) ≫ _ = _
  rw [Category.assoc, eqToHom_projG S₀ q k M (comap_fullExt S₀ q k M hq c)]
  exact fullPlaceEquiv_hom_projG _ _ _ _ _ _ _ _ _ _

/-- Both data have the same global complex. -/
theorem fullData_G (c : ∀ v : Places K S₀, CondAt K (insert q S₀) k M (oldPlace S₀ q v)) :
    (fullData S₀ q k M c).G = (oldData S₀ q k M c).G :=
  rfl

end Insert

end Galois

/-! **The RC53 group's actual stage family and RC0's actual datum** -/

section Actual

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (CondAt fullAt ofCondAt Mcoef IsOpenKer MinS actualSelData
  urOutside acoefTop acoefTop_discrete)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (ActualStageFamily)

variable {K : Type} [Field K] [NumberField K]

section Family

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]

/-- **RC0's stage datum for the RC53 group's family**: support `insert (q i) S₀`, the RC53
group's coefficient module, its old conditions at `S₀` and `fullAt` at `q i`. -/
abbrev fullStageDatum (F : ActualStageFamily S₀ W α) (i : ℕ) : SelData (Acoef i) :=
  fullData S₀ (F.q i) (Acoef i) (F.coefficient i) (F.old i)

omit [W.IsElliptic] in
/-- RC0's conditions of `fullStageDatum` are `fullAt` at `q i`, by definition. Kind: PROVED. -/
theorem fullStageDatum_new (F : ActualStageFamily S₀ W α) (i : ℕ) :
    fullExt S₀ (F.q i) (Acoef i) (F.coefficient i) (F.old i) (newPlace S₀ (F.q i)) =
      fullAt K (F.support i) (Acoef i) (F.coefficient i) (newPlace S₀ (F.q i)) :=
  extendFull_new S₀ (F.q i) (F.support i) (Acoef i) (F.coefficient i) _ _ _ rfl

/-- **The two conventions agree for the RC53 group's family**: RC0's stage datum with `fullAt`
at the derivative place `q i` has Selmer complex homotopy equivalent to `F.globalCx i`, with the
same global complex. Kind: PROVED. -/
def actualStageFamily_equiv (F : ActualStageFamily S₀ W α) (i : ℕ) :
    HomotopyEquiv (selCx (fullStageDatum F i)).toCC (F.globalCx i).toCC :=
  insertEquiv S₀ (F.q i) (Acoef i) (F.coefficient i) (F.new i) (F.old i)

omit [W.IsElliptic] in
/-- The same global complex. -/
theorem fullStageDatum_G (F : ActualStageFamily S₀ W α) (i : ℕ) :
    (fullStageDatum F i).G = (F.datum i).G :=
  rfl

end Family

section RC0

variable {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]

/-- With coefficient support equal to the Selmer support there is no unramified place: RC0's
actual conditions are the given ones at every place. Kind: PROVED. -/
theorem actualSelData_refl_eq
    (c : ∀ v : Places K S, v.1 ∈ S → CondAt K S (Acoef i) (MinS (subset_refl S) W i α) v) :
    actualSelData (subset_refl S) W i α c =
      galoisSelData K S (Acoef i) (MinS (subset_refl S) W i α)
        (ofCondAt K S (Acoef i) (MinS (subset_refl S) W i α) (fun v => c v v.2)) := by
  let _ : TopologicalSpace (Acoef i) := acoefTop i
  have _ : DiscreteTopology (Acoef i) := acoefTop_discrete i
  have h : urOutside (subset_refl S) (Acoef i) (Mcoef K S W i α) c = fun v => c v v.2 :=
    funext fun v => dite_eq_left v.2
  exact congrArg (fun c' => galoisSelData K S (Acoef i) (MinS (subset_refl S) W i α)
    (ofCondAt K S (Acoef i) (MinS (subset_refl S) W i α) c')) h

/-- **RC0's actual stage datum with the full condition at `q`** (`S₀ i := insert q S₀` as both
coefficient and Selmer support, old conditions `extendFull`) is homotopy equivalent to the
old-places datum over the same coefficient module `MinS`, with the same global complex.
Kind: PROVED. -/
def actualSelData_insertEquiv (S₀ : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S₀) (α : GKS K (insert q S₀) →* (Acoef i)ˣ)
    [IsOpenKer α]
    (c : ∀ v : Places K S₀, CondAt K (insert q S₀) (Acoef i)
      (MinS (subset_refl (insert q S₀)) W i α) (oldPlace S₀ q v)) :
    HomotopyEquiv (selCx (actualSelData (subset_refl (insert q S₀)) W i α
        (extendFull S₀ q (insert q S₀) (Acoef i) (MinS (subset_refl (insert q S₀)) W i α)
          (ofOld S₀ q (Acoef i) _ c)))).toCC
      (selCx (oldData S₀ q (Acoef i) (MinS (subset_refl (insert q S₀)) W i α) c)).toCC := by
  rw [actualSelData_refl_eq]
  exact insertEquiv S₀ q (Acoef i) _ hq c

/-- Towards the remaining coefficient comparison: the inflation along `S ⊆ S` is the identity
of `G_{K,S}`. Kind: PROVED. -/
theorem inflMap_refl_apply (S' : Set (HeightOneSpectrum (𝓞 K))) (g : GKS K S') :
    inflMap K (subset_refl S') g = g :=
  Classical.choose_spec (ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_surjective K S' g)

omit [W.IsElliptic] [IsOpenKer α] in
/-- Hence `G_{K,S}` acts on RC0's coefficient module `MinS` for `S ⊆ S` as on `Mcoef`
(a propositional, not a definitional, identity of actions). Kind: PROVED. -/
theorem minS_refl_smul (g : GKS K S) (m : MinS (subset_refl S) W i α) :
    g • m = (show MinS (subset_refl S) W i α from g • (show Mcoef K S W i α from m)) := by
  rw [ZInQ.Manuscript.RC.SelmerComplex.ResMod.smul_def, inflMap_refl_apply]

end RC0

end Actual

/-! **Towards the coefficient comparison: RC0's `MinS (subset_refl S)` against `Mcoef`** -/

section SelHom

variable {S : Type} [CommRing S] {D₁ D₂ : SelData S} (φG : GHom D₁.G D₂.G)
  (φU : GHom D₁.U D₂.U) (φL : GHom D₁.L D₂.L)

/-- A morphism of Selmer data in one degree: `(a, u, x) ↦ (φ_G a, φ_U u, φ_L x)`. -/
def selHomFun (n : ℤ) : selT D₁ n →ₗ[S] selT D₂ n :=
  (φG.f n n rfl).prodMap ((φU.f n n rfl).prodMap (φL.f (n - 1) (n - 1) rfl))

/-- A morphism of Selmer data compatible with `res` and `ι`, as a chain map of Selmer
complexes. Kind: PROVED. -/
def selHom (hres : ∀ n (a : D₁.G.X n),
      φL.f n n rfl (D₁.res.f n n rfl a) = D₂.res.f n n rfl (φG.f n n rfl a))
    (hι : ∀ n (u : D₁.U.X n),
      φL.f n n rfl (D₁.ι.f n n rfl u) = D₂.ι.f n n rfl (φU.f n n rfl u)) :
    GHom (selCx D₁) (selCx D₂) where
  f i j h := by
    subst h
    exact selHomFun φG φU φL i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    obtain rfl : i = i₁ - 1 := by omega
    refine Prod.ext (φG.comm _ _ _ _ rfl h₁ h₂ rfl a)
      (Prod.ext (φU.comm _ _ _ _ rfl h₁ h₂ rfl u) ?_)
    change φL.f (i₁ - 1) (i₁ - 1) rfl (D₁.res.f (i₁ - 1) (i₁ - 1) rfl a -
        D₁.ι.f (i₁ - 1) (i₁ - 1) rfl u - D₁.L.d (i₁ - 1 - 1) (i₁ - 1) (by omega) x) =
      D₂.res.f (i₁ - 1) (i₁ - 1) rfl (φG.f (i₁ - 1) (i₁ - 1) rfl a) -
        D₂.ι.f (i₁ - 1) (i₁ - 1) rfl (φU.f (i₁ - 1) (i₁ - 1) rfl u) -
        D₂.L.d (i₁ - 1 - 1) (i₁ - 1) (by omega) (φL.f (i₁ - 1 - 1) (i₁ - 1 - 1) rfl x)
    rw [map_sub, map_sub, hres, hι,
      φL.comm (i₁ - 1 - 1) (i₁ - 1) (i₁ - 1 - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x]

/-- With bijective components the morphism of Selmer complexes is an isomorphism. PROVED. -/
theorem selHom_isIso (hres : ∀ n (a : D₁.G.X n),
      φL.f n n rfl (D₁.res.f n n rfl a) = D₂.res.f n n rfl (φG.f n n rfl a))
    (hι : ∀ n (u : D₁.U.X n),
      φL.f n n rfl (D₁.ι.f n n rfl u) = D₂.ι.f n n rfl (φU.f n n rfl u))
    (hG : ∀ n, Function.Bijective (φG.f n n rfl)) (hU : ∀ n, Function.Bijective (φU.f n n rfl))
    (hL : ∀ n, Function.Bijective (φL.f n n rfl)) :
    IsIso (GHom.toCC (selHom φG φU φL hres hι)) := by
  have : ∀ m, IsIso ((GHom.toCC (selHom φG φU φL hres hι)).f m) := fun m => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (hG m).prodMap ((hU m).prodMap (hL (m - 1)))
  exact HomologicalComplex.Hom.isIso_of_components _

end SelHom

section NatF

variable {k : Type} [CommRing k] {K₁ K₂ K₃ : CochainComplex (ModuleCat.{0} k) ℕ}

theorem natF_natF (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃) (n : ℤ) (x : natX K₁ n) :
    natF ψ n (natF φ n x) = natF (φ ≫ ψ) n x := by
  cases n <;> rfl

theorem natF_id (n : ℤ) (x : natX K₁ n) : natF (𝟙 K₁) n x = x := by
  cases n <;> rfl

theorem natF_bijective (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₁) (h₁ : φ ≫ ψ = 𝟙 _) (h₂ : ψ ≫ φ = 𝟙 _)
    (n : ℤ) : Function.Bijective (natF φ n) := by
  refine ⟨Function.LeftInverse.injective (g := natF ψ n) fun x => ?_,
    Function.RightInverse.surjective (g := natF ψ n) fun x => ?_⟩
  · rw [natF_natF, h₁, natF_id]
  · rw [natF_natF, h₂, natF_id]

end NatF

section Coef

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (CondAt fullAt ofCondAt Mcoef IsOpenKer MinS actualSelData)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]

/-- The global comparison `C^•(G_{K,S}, MinS) → C^•(G_{K,S}, Mcoef)` (identity on cochains). -/
def minSToMcoef : contCochains (Acoef i) (GKS K S) (MinS (subset_refl S) W i α) ⟶
    contCochains (Acoef i) (GKS K S) (Mcoef K S W i α) :=
  contCochainsMap (ContinuousMonoidHom.id _) LinearMap.id continuous_id
    (fun g m => minS_refl_smul W i α g m)

/-- The inverse global comparison. -/
def mcoefToMinS : contCochains (Acoef i) (GKS K S) (Mcoef K S W i α) ⟶
    contCochains (Acoef i) (GKS K S) (MinS (subset_refl S) W i α) :=
  contCochainsMap (ContinuousMonoidHom.id _) LinearMap.id continuous_id
    (fun g m => (minS_refl_smul W i α g m).symm)

/-- The local comparison at `v`. -/
def locMinSToMcoef (v : HeightOneSpectrum (𝓞 K)) :
    contCochains (Acoef i) (Gloc K v) (ResMod (locMap K S v) (MinS (subset_refl S) W i α)) ⟶
      contCochains (Acoef i) (Gloc K v) (ResMod (locMap K S v) (Mcoef K S W i α)) :=
  contCochainsMap (ContinuousMonoidHom.id _) LinearMap.id continuous_id
    (fun g m => minS_refl_smul W i α (locMap K S v g) m)

/-- The inverse local comparison at `v`. -/
def locMcoefToMinS (v : HeightOneSpectrum (𝓞 K)) :
    contCochains (Acoef i) (Gloc K v) (ResMod (locMap K S v) (Mcoef K S W i α)) ⟶
      contCochains (Acoef i) (Gloc K v) (ResMod (locMap K S v) (MinS (subset_refl S) W i α)) :=
  contCochainsMap (ContinuousMonoidHom.id _) LinearMap.id continuous_id
    (fun g m => (minS_refl_smul W i α (locMap K S v g) m).symm)

omit [W.IsElliptic] in
theorem minSToMcoef_comp : minSToMcoef W i α ≫ mcoefToMinS W i α = 𝟙 _ := by
  ext n c
  rfl

omit [W.IsElliptic] in
theorem mcoefToMinS_comp : mcoefToMinS W i α ≫ minSToMcoef W i α = 𝟙 _ := by
  ext n c
  rfl

omit [W.IsElliptic] in
theorem locMinSToMcoef_comp (v : HeightOneSpectrum (𝓞 K)) :
    locMinSToMcoef W i α v ≫ locMcoefToMinS W i α v = 𝟙 _ := by
  ext n c
  rfl

omit [W.IsElliptic] in
theorem locMcoefToMinS_comp (v : HeightOneSpectrum (𝓞 K)) :
    locMcoefToMinS W i α v ≫ locMinSToMcoef W i α v = 𝟙 _ := by
  ext n c
  rfl

omit [W.IsElliptic] in
theorem natHom_loc_inv (v : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (y : natX (contCochains (Acoef i) (Gloc K v) (ResMod (locMap K S v) (Mcoef K S W i α))) n) :
    (natHom (locMinSToMcoef W i α v)).f n n rfl ((natHom (locMcoefToMinS W i α v)).f n n rfl y) =
      y := by
  change natF (locMinSToMcoef W i α v) n (natF (locMcoefToMinS W i α v) n y) = y
  rw [natF_natF, locMcoefToMinS_comp, natF_id]

/-- A condition over `Mcoef` transported to RC0's coefficient `MinS (subset_refl S)`. -/
def condToMinS {v : Places K S} (c : CondAt K S (Acoef i) (Mcoef K S W i α) v) :
    CondAt K S (Acoef i) (MinS (subset_refl S) W i α) v :=
  ⟨c.U, ghomComp c.i (natHom (locMcoefToMinS W i α v.1))⟩

end Coef

end ZInQ.Manuscript.RC.Wiring.StageSupport
