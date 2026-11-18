import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.ConeInverse

/-!
# Selmer duality, part 2: finite Selmer duality `C_U ≃ RHom(C_{U⊥}, R)[−3]`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2806–2830 (and the
Selmer-cone form (4.3), tex L3451–3460):
```
C_U(M_i) ≃ RHom_{R_i}(C_{U^⊥}(M_i^*(1)), R_i)[−3].
```
Elliot obtains it by applying Nekovář's global Selmer duality (Sections 5.1, 5.2.4, 5.4.3, 6.3.4,
as cited at tex L3451–3452 and L3826–3836) to the actual local maps and isotropy homotopies. This
file formalizes the cochain-level deduction over an arbitrary commutative ring `S`:

* the Selmer complexes `C_U = selCx D`, `C_{U⊥} = selCx D'` and the cup product
  `C_U × C_{U⊥} → Cone(E → E_L)[−1]` built from an isotropy homotopy (`selPair`, reproved in
  `PairedFunctional/SelmerPairing.lean`), followed by a trace `tr` of degree three killing
  coboundaries, give the duality map `selmerDualityMap : C_U → Hom_S(C_{U⊥}, S)[−3]`;
* the two short exact sequences `0 → Cone(U → L)[−1] → C_U → G → 0` and
  `0 → Hom(U', S)[−3] → Hom(C_{U⊥}, S)[−3] → Hom(G'_c, S)[−3] → 0`
  (`G'_c = Cone(G' → L')[−1]`, compactly supported cochains), and the morphism between them
  induced by the duality map, whose outer components are
  - `globalDualityMap : G → Hom(G'_c, S)[−3]`, `a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))`
    (global duality / Poitou–Tate in Nekovář's cochain form), and
  - `localDualityMap : Cone(U → L)[−1] → Hom(U', S)[−3]`,
    `(u, x) ↦ (v ↦ tr(0, x ∪ ι' v + h(u, v)))` (local duality between `L/U` and `U^⊥`);
* `FiniteSelmerDualityNode` (PROVED from the two GLUE inputs): if the global duality and local
  orthogonality maps are quasi-isomorphisms (`GlobalDualityInput`, `LocalOrthogonalityInput`:
  Nekovář's conclusions assumed for the abstract model, the identification with Galois cochains
  left open), the Selmer duality map is a quasi-isomorphism, and a homotopy equivalence when the
  two Selmer complexes are bounded with free terms.

`RHom_S(C_{U⊥}, S)` is represented by the termwise dual complex `Hom_S(C_{U⊥}, S)` (`dualCx`),
and the node is stated only in the scope `TermwiseDualComputesRHom` where this computes `RHom`:
`S` self-injective (the coefficient rings `A_i`, `SelfInjective.lean`) or `C_{U⊥}` bounded with
finitely generated projective terms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

variable {S : Type u} [CommRing S]

/-! ### Generic constructions of chain maps -/

section Generic

variable {A B C : GCx S}

/-- Composition of `GHom`s. -/
def ghomComp (f : GHom A B) (g : GHom B C) : GHom A C where
  f i j h := (g.f j j rfl).comp (f.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change g.f i₁ i₁ rfl (f.f i₁ i₁ rfl (A.d i i₁ h₁ x)) = C.d i i₁ h₂ (g.f i i rfl (f.f i i rfl x))
    rw [f.comm i i₁ i i₁ rfl h₁ h₂ rfl x, g.comm i i₁ i i₁ rfl h₂ h₂ rfl]

/-- A family of linear maps whose composite with an injective chain map is a chain map is itself
a chain map. -/
def ghomOfInj (a : ∀ i j, i = j → A.X i →ₗ[S] B.X j) (g : GHom B C)
    (hg : ∀ i, Function.Injective (g.f i i rfl)) (h : GHom A C)
    (hgh : ∀ i (x : A.X i), g.f i i rfl (a i i rfl x) = h.f i i rfl x) : GHom A B where
  f := a
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    apply hg i₁
    calc g.f i₁ i₁ rfl (a i₁ i₁ rfl (A.d i i₁ h₁ x)) = h.f i₁ i₁ rfl (A.d i i₁ h₁ x) := hgh _ _
      _ = C.d i i₁ h₁ (h.f i i rfl x) := h.comm i i₁ i i₁ rfl h₁ h₁ rfl x
      _ = C.d i i₁ h₁ (g.f i i rfl (a i i rfl x)) := by rw [hgh]
      _ = g.f i₁ i₁ rfl (B.d i i₁ h₂ (a i i rfl x)) := (g.comm i i₁ i i₁ rfl h₂ h₁ rfl _).symm

/-- A chain map `β : C → E` killing the kernel of a surjective chain map `q : C → G` (with linear
sections `s`) descends to a chain map `G → E`, `x ↦ β (s x)`. -/
def ghomOfSurj {G E : GCx S} (q : GHom C G) (s : ∀ i, G.X i →ₗ[S] C.X i)
    (hs : ∀ i x, q.f i i rfl (s i x) = x) (β : GHom C E)
    (hβ : ∀ i (c : C.X i), q.f i i rfl c = 0 → β.f i i rfl c = 0) : GHom G E where
  f i j h := (β.f i j h).comp (s i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change β.f i₁ i₁ rfl (s i₁ (G.d i i₁ h₁ x)) = E.d i i₁ h₂ (β.f i i rfl (s i x))
    rw [← β.comm i i₁ i i₁ rfl h₁ h₂ rfl, ← sub_eq_zero, ← map_sub]
    apply hβ
    rw [map_sub, hs, q.comm i i₁ i i₁ rfl h₁ h₁ rfl, hs, sub_self]

theorem ghomOfSurj_comp {G E : GCx S} (q : GHom C G) (s : ∀ i, G.X i →ₗ[S] C.X i)
    (hs : ∀ i x, q.f i i rfl (s i x) = x) (β : GHom C E)
    (hβ : ∀ i (c : C.X i), q.f i i rfl c = 0 → β.f i i rfl c = 0) (i : ℤ) (c : C.X i) :
    (ghomOfSurj q s hs β hβ).f i i rfl (q.f i i rfl c) = β.f i i rfl c := by
  change β.f i i rfl (s i (q.f i i rfl c)) = β.f i i rfl c
  rw [← sub_eq_zero, ← map_sub]
  apply hβ
  rw [map_sub, hs, sub_self]

theorem GHom.toCC_comp (f : GHom A B) (g : GHom B C) :
    GHom.toCC f ≫ GHom.toCC g = GHom.toCC (ghomComp f g) :=
  rfl

theorem GHom.toCC_ext {f g : GHom A B} (h : ∀ i x, f.f i i rfl x = g.f i i rfl x) :
    GHom.toCC f = GHom.toCC g := by
  ext i x
  exact h i x

end Generic

/-! ### The pieces of the Selmer complex -/

section Pieces

variable (D : SelData S)

/-- `−ι : U → L`. -/
def negι : GHom D.U D.L where
  f i j h := -(D.ι.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    simp only [LinearMap.neg_apply, map_neg, D.ι.comm i i₁ j j₁ hij h₁ h₂ hj x]

/-- `Cone(U → L)[−1]`: `X n = U^n ⊕ L^{n−1}`, `d(u, x) = (du, −ι u − dx)`. -/
abbrev locCx : GCx S := coneCx (negι D)

/-- `G_c = Cone(G → L)[−1]`: `X n = G^n ⊕ L^{n−1}`, `d(b, y) = (db, res b − dy)`. -/
abbrev compactCx : GCx S := coneCx D.res

/-- The inclusion `Cone(U → L)[−1] → C_U`, `(u, x) ↦ (0, u, x)`. -/
def inclLoc : GHom (locCx D) (selCx D) where
  f i j h := h ▸ LinearMap.inr S (D.G.X i) (D.U.X i × D.L.X (i - 1))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨u, x⟩ := c
    change (0, D.U.d i i₁ h₁ u, -(D.ι.f i (i₁ - 1) _ u) - D.L.d (i - 1) (i₁ - 1) _ x) =
      (D.G.d i i₁ h₂ 0, D.U.d i i₁ h₂ u,
        D.res.f i (i₁ - 1) _ 0 - D.ι.f i (i₁ - 1) _ u - D.L.d (i - 1) (i₁ - 1) _ x)
    simp only [map_zero, zero_sub]

/-- The projection `C_U → G`, `(a, u, x) ↦ a`. -/
def projG : GHom (selCx D) D.G where
  f i j h := h ▸ LinearMap.fst S (D.G.X i) (D.U.X i × D.L.X (i - 1))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    rfl

/-- The inclusion `G_c → C_U`, `(b, y) ↦ (b, 0, y)`. -/
def inclCompact : GHom (compactCx D) (selCx D) where
  f i j h := h ▸ (LinearMap.fst S (D.G.X i) (D.L.X (i - 1))).prod
    ((LinearMap.inr S (D.U.X i) (D.L.X (i - 1))).comp (LinearMap.snd S (D.G.X i) (D.L.X (i - 1))))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨b, y⟩ := c
    change (D.G.d i i₁ h₁ b, 0, D.res.f i (i₁ - 1) _ b - D.L.d (i - 1) (i₁ - 1) _ y) =
      (D.G.d i i₁ h₂ b, D.U.d i i₁ h₂ 0,
        D.res.f i (i₁ - 1) _ b - D.ι.f i (i₁ - 1) _ 0 - D.L.d (i - 1) (i₁ - 1) _ y)
    simp only [map_zero, sub_zero]

/-- The projection `C_U → U`, `(b, v, y) ↦ v`. -/
def projU : GHom (selCx D) D.U where
  f i j h := h ▸ (LinearMap.fst S (D.U.X i) (D.L.X (i - 1))).comp
    (LinearMap.snd S (D.G.X i) (D.U.X i × D.L.X (i - 1)))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    rfl

/-- The section `G → C_U`, `a ↦ (a, 0, 0)`. -/
def secG (i : ℤ) : D.G.X i →ₗ[S] (selCx D).X i :=
  LinearMap.inl S (D.G.X i) (D.U.X i × D.L.X (i - 1))

/-- The section `U → C_U`, `v ↦ (0, v, 0)`. -/
def secU (i : ℤ) : D.U.X i →ₗ[S] (selCx D).X i :=
  (LinearMap.inr S (D.G.X i) (D.U.X i × D.L.X (i - 1))).comp
    (LinearMap.inl S (D.U.X i) (D.L.X (i - 1)))

/-- The retraction `C_U → G_c`, `(b, v, y) ↦ (b, y)`. -/
def retCompact (i : ℤ) : (selCx D).X i →ₗ[S] (compactCx D).X i :=
  (LinearMap.fst S (D.G.X i) (D.U.X i × D.L.X (i - 1))).prod
    ((LinearMap.snd S (D.U.X i) (D.L.X (i - 1))).comp
      (LinearMap.snd S (D.G.X i) (D.U.X i × D.L.X (i - 1))))

end Pieces

/-! ### The duality maps -/

section Maps

variable {D D' : SelData S} (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
  (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- **The Selmer duality map** `C_U → Hom_S(C_{U⊥}, S)[−3]`, `c ↦ (c' ↦ tr(c ∪ c'))`. -/
def selmerDualityMap : GHom (selCx D) (dualCx (selCx D') 3) :=
  adjHom (selPair Q) 3 tr htr

theorem selmerDualityMap_apply (i : ℤ) (c : (selCx D).X i) (c' : (selCx D').X (3 - i)) :
    asDual ((selmerDualityMap Q tr htr).f i i rfl c) c' =
      tr (selCup Q i (3 - i) 3 (by omega) c c') :=
  rfl

omit htr in
/-- `tr((0, u, x) ∪ (b, v, y))` depends only on `v`. -/
theorem tr_selCup_loc (i : ℤ) (u : D.U.X i) (x : D.L.X (i - 1)) (b : D'.G.X (3 - i))
    (v : D'.U.X (3 - i)) (y : D'.L.X (3 - i - 1)) :
    tr (selCup Q i (3 - i) 3 (by omega) (0, u, x) (b, v, y)) =
      tr (selCup Q i (3 - i) 3 (by omega) (0, u, x) (0, v, 0)) := by
  congr 1
  change (selCupFun Q i (3 - i) 3 _ (0, u, x) (b, v, y)) = selCupFun Q i (3 - i) 3 _ (0, u, x) (0, v, 0)
  simp only [selCupFun, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

omit htr in
/-- `tr((0, u, x) ∪ (b, 0, y)) = 0`. -/
theorem tr_selCup_loc_compact (i : ℤ) (u : D.U.X i) (x : D.L.X (i - 1)) (b : D'.G.X (3 - i))
    (y : D'.L.X (3 - i - 1)) :
    tr (selCup Q i (3 - i) 3 (by omega) (0, u, x) (b, 0, y)) = 0 := by
  have : selCupFun Q i (3 - i) 3 (by omega) (0, u, x) (b, 0, y) = 0 := by
    simp only [selCupFun, map_zero, LinearMap.zero_apply, smul_zero, add_zero]
    rfl
  change tr (selCupFun Q i (3 - i) 3 _ (0, u, x) (b, 0, y)) = 0
  rw [this]
  exact map_zero tr

theorem dualHom_projU_injective (i : ℤ) :
    Function.Injective ((dualHom (projU D') 3).f i i rfl) := by
  intro φ ψ h
  refine dualCx_ext fun v => ?_
  have := congrArg (fun χ => asDual χ (secU D' (3 - i) v)) h
  exact this

/-- The composite `Cone(U → L)[−1] → C_U → Hom(C_{U⊥}, S)[−3]`. -/
def locComposite : GHom (locCx D) (dualCx (selCx D') 3) :=
  ghomComp (inclLoc D) (selmerDualityMap Q tr htr)

/-- **The local duality map** `Cone(U → L)[−1] → Hom_S(U', S)[−3]`,
`(u, x) ↦ (v ↦ tr(0, x ∪ ι' v + h(u, v)))`. -/
def localDualityMap : GHom (locCx D) (dualCx D'.U 3) :=
  ghomOfInj (fun i j h => ((secU D' (3 - j)).dualMap).comp ((locComposite Q tr htr).f i j h))
    (dualHom (projU D') 3) (dualHom_projU_injective) (locComposite Q tr htr) (by
      intro i c
      refine dualCx_ext fun c' => ?_
      obtain ⟨u, x⟩ := c
      obtain ⟨b, v, y⟩ := c'
      exact (tr_selCup_loc Q tr i u x b v y).symm)

/-- The composite `C_U → Hom(C_{U⊥}, S)[−3] → Hom(G'_c, S)[−3]`. -/
def compactComposite : GHom (selCx D) (dualCx (compactCx D') 3) :=
  ghomComp (selmerDualityMap Q tr htr) (dualHom (inclCompact D') 3)

theorem compactComposite_kill (i : ℤ) (c : (selCx D).X i) (hc : (projG D).f i i rfl c = 0) :
    (compactComposite Q tr htr).f i i rfl c = 0 := by
  obtain ⟨a, u, x⟩ := c
  change a = 0 at hc
  subst hc
  refine dualCx_ext fun c' => ?_
  obtain ⟨b, y⟩ := c'
  exact tr_selCup_loc_compact Q tr i u x b y

/-- **The global duality map** `G → Hom_S(G'_c, S)[−3]`,
`a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))`. -/
def globalDualityMap : GHom D.G (dualCx (compactCx D') 3) :=
  ghomOfSurj (projG D) (secG D) (fun _ _ => rfl) (compactComposite Q tr htr)
    (compactComposite_kill Q tr htr)

end Maps

/-! ### The two short exact sequences -/

section SES

open HomologicalComplex

variable {D D' : SelData S}

/-- `0 → Cone(U → L)[−1] → C_U → G → 0`. -/
def sesTop (D : SelData S) : ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (inclLoc D)) (GHom.toCC (projG D)) (by
    rw [GHom.toCC_comp]
    ext i c
    rfl)

/-- `0 → Hom(U', S)[−3] → Hom(C_{U⊥}, S)[−3] → Hom(G'_c, S)[−3] → 0`. -/
def sesBot (D' : SelData S) : ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (dualHom (projU D') 3)) (GHom.toCC (dualHom (inclCompact D') 3)) (by
    rw [GHom.toCC_comp]
    ext i φ
    refine dualCx_ext fun c => ?_
    obtain ⟨b, y⟩ := c
    change asDual φ (0 : D'.U.X (3 - i)) = 0
    rw [map_zero])

theorem sesTop_shortExact (D : SelData S) : (sesTop D).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, u, x⟩ := c
    change a = 0 at hc
    subst hc
    exact ⟨(u, x), rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro c c' h
    obtain ⟨u, x⟩ := c
    obtain ⟨u', x'⟩ := c'
    change ((0 : D.G.X i), u, x) = (0, u', x') at h
    simp only [Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    exact ⟨(a, 0, 0), rfl⟩

theorem sesBot_shortExact (D' : SelData S) : (sesBot D').ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro φ hφ
    refine ⟨(secU D' (3 - i)).dualMap (asDual φ), dualCx_ext fun c => ?_⟩
    obtain ⟨b, v, y⟩ := c
    have h0 := congrArg (fun χ => asDual χ ((b, y) : (compactCx D').X (3 - i))) hφ
    change asDual φ (b, 0, y) = 0 at h0
    change asDual φ (0, v, 0) = asDual φ (b, v, y)
    have : ((b, v, y) : (selCx D').X (3 - i)) = (0, v, 0) + (b, 0, y) := by
      simp
    rw [this]
    erw [map_add]
    rw [h0, add_zero]
  · rw [ModuleCat.mono_iff_injective]
    exact dualHom_projU_injective (D' := D') i
  · rw [ModuleCat.epi_iff_surjective]
    intro ψ
    refine ⟨(retCompact D' (3 - i)).dualMap (asDual ψ), dualCx_ext fun c => ?_⟩
    obtain ⟨b, y⟩ := c
    rfl

variable (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
  (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- The morphism of short exact sequences induced by the Selmer duality map. -/
def sesHom : sesTop D ⟶ sesBot D' where
  τ₁ := GHom.toCC (localDualityMap Q tr htr)
  τ₂ := GHom.toCC (selmerDualityMap Q tr htr)
  τ₃ := GHom.toCC (globalDualityMap Q tr htr)
  comm₁₂ := by
    change GHom.toCC (localDualityMap Q tr htr) ≫ GHom.toCC (dualHom (projU D') 3) =
      GHom.toCC (inclLoc D) ≫ GHom.toCC (selmerDualityMap Q tr htr)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i c => ?_
    refine dualCx_ext fun c' => ?_
    obtain ⟨u, x⟩ := c
    obtain ⟨b, v, y⟩ := c'
    exact (tr_selCup_loc Q tr i u x b v y).symm
  comm₂₃ := by
    change GHom.toCC (selmerDualityMap Q tr htr) ≫ GHom.toCC (dualHom (inclCompact D') 3) =
      GHom.toCC (projG D) ≫ GHom.toCC (globalDualityMap Q tr htr)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i c => ?_
    exact (ghomOfSurj_comp (projG D) (secG D) (fun _ _ => rfl) (compactComposite Q tr htr)
      (compactComposite_kill Q tr htr) i c).symm

end SES

/-! ### The duality inputs (GLUE) and the theorem -/

section Theorem

/-- **A perfect coefficient pairing** `M × M' → S` (tex L2797–2803: the Weil pairing gives an
`R_i`-linear perfect pairing `M_i ⊗ τ*M_i → R_i(1)`, `τ*M_i ≃ M_i^*(1)`; proved for the actual
coefficients in `Duality/ConjugateDuality.lean`): both adjoints are bijective. -/
structure PerfectCoefficientPairing (S : Type u) [CommRing S] where
  /-- The coefficient module `M`. -/
  M : ModuleCat.{u} S
  /-- The dual coefficient module `M' = M^*(1)`. -/
  M' : ModuleCat.{u} S
  /-- The pairing `M × M' → S`. -/
  pair : M →ₗ[S] M' →ₗ[S] S
  perfect_left : Function.Bijective pair
  perfect_right : Function.Bijective pair.flip

/-- The scope in which the termwise dual `Hom_S(C, S)` (`dualCx`) computes `RHom_S(C, S)`: `S` is
self-injective (as the coefficient rings `A_i` are, `acoef_selfInjective`), or `C` is bounded
with finitely generated projective terms. In the self-injective case the defining property of an
`RHom` model — the termwise dual carries quasi-isomorphisms to quasi-isomorphisms — is proved in
`DualQuasiIso.lean` (`dualHom_quasiIso`). -/
def TermwiseDualComputesRHom (S : Type u) [CommRing S] (C : GCx S) : Prop :=
  Module.Injective S S ∨
    ∃ a b : ℤ, (∀ n, n < a ∨ b < n → Subsingleton (C.X n)) ∧
      ∀ n, Module.Projective S (C.X n) ∧ Module.Finite S (C.X n)

variable {D D' : SelData S} (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
  (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- **GLUE input: global duality for the abstract model** (the conclusion of Nekovář, *Selmer
complexes*, Sections 5.1, 5.2.4 and 5.4.3, as cited at tex L3451–3452: global duality /
Poitou–Tate in cochain form, assumed here for the abstract model): the global duality map
`G → Hom_S(G'_c, S)[−3]`,
`a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))`, from the global complex to the dual of the
compactly supported complex `G'_c = Cone(G' → L')[−1]` (`compactCx`), is a quasi-isomorphism.

This is *not* a printed leaf: Nekovář's theorem is about the continuous cochains of `G_{K,S}`
with coefficients `M` and `M^*(1)`, which the library does not provide in all degrees; the
identification of `G, G', L, L'`, the cup products and the trace with those cochains (and of their
coefficients with a perfect coefficient pairing) is left open. The pairing argument `_P` is unused:
it does not constrain the statement, which depends only on `Q`, `tr`, `htr`.
Classification: GLUE (assumed input). -/
def GlobalDualityInput (_P : PerfectCoefficientPairing S) : Prop :=
  QuasiIso (GHom.toCC (globalDualityMap Q tr htr))

/-- **GLUE input: local orthogonality for the abstract model** (the conclusion of Nekovář,
*Selmer complexes*, Sections 5.2.4 and 6.2–6.3, as cited at tex L3451–3452 and L3826–3836: local
duality and orthogonal local conditions, assumed here for the abstract model): the local condition
`U'` is the orthogonal complement of `U` in the derived sense, with the isotropy homotopy `h` of `Q`
(`SelPairData.isotropy`: `ι u ∪ ι' v = d h(u, v) + …`): the local duality map
`Cone(U → L)[−1] → Hom_S(U', S)[−3]`,
`(u, x) ↦ (v ↦ tr(0, x ∪ ι' v + h(u, v)))`, is a quasi-isomorphism.

A degreewise (cochain-level) annihilator condition is deliberately not imposed: for the actual
Galois cochains, `U'` is the orthogonal complement only up to the homotopy `h` and on cohomology,
and a degreewise annihilator condition fails (it would make the input vacuous for the genuine
data). The identification with the actual local cochains and Kummer conditions is left open.
The pairing argument `_P` is unused: it does not constrain the statement, which depends only on
`Q`, `tr`, `htr`. Classification: GLUE (assumed input). -/
def LocalOrthogonalityInput (_P : PerfectCoefficientPairing S) : Prop :=
  QuasiIso (GHom.toCC (localDualityMap Q tr htr))

/-- **Finite Selmer duality** (`ex:arith-conjugate-duality`, tex L2806–2830; (4.3), tex
L3451–3460). Over a commutative ring `S`, in the scope where the termwise dual computes `RHom`
(`TermwiseDualComputesRHom S (selCx D')`: `S` self-injective, or `C_{U⊥}` bounded with finitely
generated projective terms): for Selmer data `D` (`C_U`) and `D'` (`C_{U⊥}`), cup-product data `Q`
with an isotropy homotopy, a trace `tr` of degree three killing coboundaries and a perfect
coefficient pairing `P`, if the global duality and local orthogonality inputs hold
(`GlobalDualityInput`, `LocalOrthogonalityInput`: GLUE), the Selmer duality map
`C_U → Hom_S(C_{U⊥}, S)[−3] = RHom_S(C_{U⊥}, S)[−3]` is a quasi-isomorphism. -/
def FiniteSelmerDualityNode : Prop :=
  ∀ (S : Type u) [CommRing S] (D D' : SelData S) (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[S] S) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (P : PerfectCoefficientPairing S), TermwiseDualComputesRHom S (selCx D') →
    GlobalDualityInput Q tr htr P → LocalOrthogonalityInput Q tr htr P →
      QuasiIso (GHom.toCC (selmerDualityMap Q tr htr))

theorem finiteSelmerDualityNode_proof : FiniteSelmerDualityNode.{u} := by
  intro S _ D D' Q tr htr P _ hG hL
  exact quasiIso_τ₂ (sesHom Q tr htr) (sesTop_shortExact D) (sesBot_shortExact D') hL hG

/-- The homotopy-equivalence form for bounded free complexes. -/
theorem selmerDuality_homotopyEquiv (P : PerfectCoefficientPairing S)
    (hS : TermwiseDualComputesRHom S (selCx D'))
    (hG : GlobalDualityInput Q tr htr P) (hL : LocalOrthogonalityInput Q tr htr P) (a b : ℤ)
    [(selCx D).toCC.IsStrictlyGE a] [(selCx D).toCC.IsStrictlyLE b]
    [(dualCx (selCx D') 3).toCC.IsStrictlyGE a] [(dualCx (selCx D') 3).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx D).toCC.X n)] [∀ n, Module.Free S ((dualCx (selCx D') 3).toCC.X n)] :
    ∃ e : HomotopyEquiv (selCx D).toCC (dualCx (selCx D') 3).toCC,
      e.hom = GHom.toCC (selmerDualityMap Q tr htr) := by
  have := finiteSelmerDualityNode_proof S D D' Q tr htr P hS hG hL
  exact homotopyEquiv_of_quasiIso_free a b _

end Theorem

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
