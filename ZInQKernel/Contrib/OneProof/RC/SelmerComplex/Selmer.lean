import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cup
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# Lane RC26: Nekovář Selmer complexes over genuine continuous cochains

Manuscript `diophantine_zq.tex`, §8, (4.3) at tex 3455–3463:
```
C_U = Cone(RΓ(G_{K,S}, M_i) ⊕ ⊕_{v∈S} U_v → ⊕_{v∈S} RΓ(K_v, M_i))[−1],
```
following Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.1.1–6.1.2 (p. 135): local
conditions are morphisms of complexes `i_v⁺ : U_v⁺ → C^•_cont(G_v, X)` at the finite places
`v ∈ S_f`, and the Selmer complex is
`C_f = Cone(C^•_cont(G_{K,S}, X) ⊕ ⊕_v U_v⁺ → ⊕_v C^•_cont(G_v, X))[−1]` with the map
`res_{S_f} − i_S⁺`.

This file builds these complexes from the genuine continuous cochains of `Cochains.lean`, over an
arbitrary topological group `G_S` with finitely or infinitely many "places" `v`, local groups
`G_v` and continuous homomorphisms `loc_v : G_v → G_S` (for the genuine Galois groups see
`Galois.lean`), and instantiates the abstract interfaces `SelData`, `SelPairData`,
`SupportChangeData` of the Selmer-duality files:

* `natCx K`: an `ℕ`-indexed Mathlib cochain complex extended by zero, as a relation-indexed
  complex `GCx` (the format of `SelData`); `natHom`, `natPair` for cochain maps and pairings.
* `piCx`, `piLift`, `piMap`, `piPair`: the (finite) direct sum `⊕_v` of complexes, maps and
  pairings, as products.
* `globalCx`, `localCx`, `localSumCx`, `resS`: `C^•_cont(G_S, M)`, `C^•_cont(G_v, M)`,
  `⊕_v C^•_cont(G_v, M)` and `res_S = (res_v)_v` (restriction along `loc_v`, a cochain map).
* `LocalConditions`: local conditions `U_v → C^•_cont(G_v, M)` (morphisms of complexes, any
  `GCx`: e.g. the unramified complex `[M --(Φ−1)--> M]`, the Kummer condition, `0`, or the full
  complex); `selData Δ : SelData k` — **the genuine Selmer data**; `selCx (selData Δ)` is (4.3).
* `nekCx`, `nekIso`: Nekovář's sign convention `d(a, b, c) = (da, db, −res a + i b − dc)`
  (Nekovář 1.3.1, p. 41, applied in 6.1.2) is isomorphic to the convention
  `d(a, u, x) = (da, du, res a − ι u − dx)` of `selCx` (via `x ↦ −x`).
* the exact sequences of Nekovář 6.1.3 (p. 136): `0 → U_S⁻[−1] → C_f → C(G_S) → 0` (`sesTop`,
  short exact by `sesTop_shortExact`) and `0 → C_c → C_f → U_S⁺ → 0` (`sesCompact`,
  `sesCompact_shortExact`), with their long exact cohomology sequences (Mathlib's
  `ShortComplex.ShortExact.homology_exact₁/₂/₃`: `selmer_les`, `selmer_les_compact`).
* strict and relaxed conditions (`strictConditions`: `U_v = 0`; `relaxedConditions`:
  `U_v = C(G_v, M)`), the maps of Selmer complexes induced by morphisms of local conditions
  (`condMap`; `strictToSel : C_str → C_U`, `selToRelaxed : C_U → C_rel`), the short exact
  sequence `0 → C_str → C_U → ⊕_v U_v → 0` (`strictSES_shortExact`), the identification of the
  strict complex with the compactly supported cochains (`strictIso`), and the quasi-isomorphism
  `C_rel → C(G_S, M)` (`relaxed_quasiIso`).
* cup products: `contCup`, `contNatPair` (Leibniz rule on `C^•_cont`), `globalPair`, `localPair`,
  `res_cup` (restriction commutes with cup products), `IsotropyData` (Nekovář 6.2.1.3) and
  `genuinePairData : SelPairData (selData ΔA) (selData ΔB)` — **the genuine cup-product data**;
  `strictIsotropy` (non-vacuity).

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {k : Type u} [CommRing k]

/-! ### `ℕ`-indexed complexes as relation-indexed complexes -/

section Nat

theorem ofNat_add_one_ne_negSucc (n m : ℕ) : Int.ofNat n + 1 ≠ Int.negSucc m := by
  have := Int.negSucc_lt_zero m
  rw [Int.ofNat_eq_natCast]
  omega

/-- The terms of the extension by zero of an `ℕ`-indexed complex to `ℤ`. -/
def natX (K : CochainComplex (ModuleCat.{u} k) ℕ) : ℤ → ModuleCat.{u} k
  | Int.ofNat n => K.X n
  | Int.negSucc _ => ModuleCat.of k PUnit.{u + 1}

/-- The differentials of the extension by zero. -/
def natD (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    ∀ i j : ℤ, i + 1 = j → (natX K i →ₗ[k] natX K j)
  | Int.ofNat n, Int.ofNat m, _ => (K.d n m).hom
  | Int.negSucc _, _, _ => 0
  | Int.ofNat n, Int.negSucc m, h => absurd h (ofNat_add_one_ne_negSucc n m)

theorem natD_natD (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    ∀ (i j l : ℤ) (hij : i + 1 = j) (hjl : j + 1 = l) (x : natX K i),
      natD K j l hjl (natD K i j hij x) = 0
  | Int.ofNat n, Int.ofNat m, Int.ofNat r, _, _, x =>
      congrArg (fun f => (ModuleCat.Hom.hom f) (show K.X n from x)) (K.d_comp_d n m r)
  | Int.negSucc _, j, l, _, hjl, _ => by
      change natD K j l hjl 0 = 0
      exact map_zero _
  | Int.ofNat n, Int.negSucc m, _, h, _, _ => absurd h (ofNat_add_one_ne_negSucc n m)
  | Int.ofNat _, Int.ofNat m, Int.negSucc r, _, h, _ => absurd h (ofNat_add_one_ne_negSucc m r)

/-- **The extension by zero** of an `ℕ`-indexed cochain complex of `k`-modules to a
relation-indexed complex `GCx k` (terms `0` in negative degrees). -/
def natCx (K : CochainComplex (ModuleCat.{u} k) ℕ) : GCx k where
  X := natX K
  d := natD K
  d_d := natD_natD K

theorem natCx_X (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) : (natCx K).X n = K.X n :=
  rfl

theorem natCx_d (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (x : K.X n) :
    (natCx K).d n (n + 1) rfl x = (K.d n (n + 1)).hom x :=
  rfl

variable {K L N : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The components of the extension by zero of a cochain map. -/
def natF (φ : K ⟶ L) : ∀ i : ℤ, natX K i →ₗ[k] natX L i
  | Int.ofNat n => (φ.f n).hom
  | Int.negSucc _ => 0

theorem natF_comm (φ : K ⟶ L) :
    ∀ (i j : ℤ) (h : i + 1 = j) (x : natX K i), natF φ j (natD K i j h x) = natD L i j h (natF φ i x)
  | Int.ofNat n, Int.ofNat m, _, x =>
      (congrArg (fun f => (ModuleCat.Hom.hom f) (show K.X n from x)) (φ.comm n m)).symm
  | Int.negSucc _, j, h, _ => by
      change natF φ j 0 = natD L _ j h 0
      rw [map_zero, map_zero]
  | Int.ofNat n, Int.negSucc m, h, _ => absurd h (ofNat_add_one_ne_negSucc n m)

/-- **The extension by zero of a cochain map**, as a relation-indexed chain map `GHom`. -/
def natHom (φ : K ⟶ L) : GHom (natCx K) (natCx L) where
  f i j h := by subst h; exact natF φ i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact natF_comm φ i i₁ h₁ x

theorem natHom_f (φ : K ⟶ L) (n : ℕ) (x : K.X n) :
    (natHom φ).f n n rfl x = (φ.f n).hom x :=
  rfl

theorem natHom_comp_apply (φ : K ⟶ L) (ψ : L ⟶ N) (i : ℤ) (x : natX K i) :
    (natHom (φ ≫ ψ)).f i i rfl x = (natHom ψ).f i i rfl ((natHom φ).f i i rfl x) := by
  match i with
  | Int.ofNat n => rfl
  | Int.negSucc _ => rfl

/-- A pairing of `ℕ`-indexed complexes `K₁ × K₂ → K₃` satisfying the Leibniz rule
`d(x ∪ y) = dx ∪ y + (−1)^p x ∪ dy`, as bilinear components. -/
structure NatPair (K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} k) ℕ) where
  /-- The components `K₁^p × K₂^q → K₃^n`, `p + q = n`. -/
  P : ∀ p q n : ℕ, p + q = n → K₁.X p →ₗ[k] K₂.X q →ₗ[k] K₃.X n
  /-- The Leibniz rule. -/
  leib : ∀ (p q n : ℕ) (h : p + q = n) (x : K₁.X p) (y : K₂.X q),
    (K₃.d n (n + 1)).hom (P p q n h x y) =
      P (p + 1) q (n + 1) (by omega) ((K₁.d p (p + 1)).hom x) y +
        ((-1 : ℤ) ^ p) • P p (q + 1) (n + 1) (by omega) x ((K₂.d q (q + 1)).hom y)

variable {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The components of the extension by zero of a pairing. -/
def natPairP (P : NatPair K₁ K₂ K₃) :
    ∀ i j l : ℤ, i + j = l → (natX K₁ i →ₗ[k] natX K₂ j →ₗ[k] natX K₃ l)
  | Int.ofNat p, Int.ofNat q, Int.ofNat n, h =>
      P.P p q n (by simp only [Int.ofNat_eq_natCast] at h; omega)
  | Int.ofNat _, Int.ofNat _, Int.negSucc _, _ => 0
  | Int.ofNat _, Int.negSucc _, _, _ => 0
  | Int.negSucc _, _, _, _ => 0

/-- `P` at a pair of natural indices. -/
theorem natPairP_ofNat (P : NatPair K₁ K₂ K₃) (p q n : ℕ) (h : (p : ℤ) + q = n) :
    natPairP P p q n h = P.P p q n (by omega) :=
  rfl

/-- `sgn` of a natural number. -/
theorem sgn_ofNat (p : ℕ) : sgn (p : ℤ) = (-1 : ℤ) ^ p := by
  induction p with
  | zero => simp [sgn]
  | succ p ih => rw [Nat.cast_succ, sgn_succ, ih, pow_succ]; ring

/-- The Leibniz rule for the extension by zero. -/
theorem natPairP_leib (P : NatPair K₁ K₂ K₃) (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l)
    (hi : i + 1 = i₁) (hj : j + 1 = j₁) (hl : l + 1 = l₁) (x : natX K₁ i) (y : natX K₂ j) :
    natD K₃ l l₁ hl (natPairP P i j l h x y) =
      natPairP P i₁ j l₁ (by omega) (natD K₁ i i₁ hi x) y +
        sgn i • natPairP P i j₁ l₁ (by omega) x (natD K₂ j j₁ hj y) := by
  cases i with
  | negSucc a =>
    have e1 : natPairP P (Int.negSucc a) j l h = 0 := rfl
    have e2 : natD K₁ (Int.negSucc a) i₁ hi = 0 := rfl
    have e3 : natPairP P (Int.negSucc a) j₁ l₁ (by omega) = 0 := rfl
    rw [e1, e2, e3]
    simp
  | ofNat p =>
    obtain rfl : i₁ = Int.ofNat (p + 1) := by simp only [Int.ofNat_eq_natCast] at hi ⊢; omega
    cases j with
    | negSucc b =>
      have e1 : natPairP P (Int.ofNat p) (Int.negSucc b) l h = 0 := rfl
      have e2 : natPairP P (Int.ofNat (p + 1)) (Int.negSucc b) l₁ (by omega) = 0 := rfl
      have e3 : natD K₂ (Int.negSucc b) j₁ hj = 0 := rfl
      rw [e1, e2, e3]
      simp
    | ofNat q =>
      obtain rfl : j₁ = Int.ofNat (q + 1) := by simp only [Int.ofNat_eq_natCast] at hj ⊢; omega
      obtain rfl : l = Int.ofNat (p + q) := by simp only [Int.ofNat_eq_natCast] at h ⊢; omega
      obtain rfl : l₁ = Int.ofNat (p + q + 1) := by
        simp only [Int.ofNat_eq_natCast] at hl ⊢; omega
      change (K₃.d (p + q) (p + q + 1)).hom (P.P p q (p + q) _ x y) =
        P.P (p + 1) q (p + q + 1) _ ((K₁.d p (p + 1)).hom x) y +
          sgn (p : ℤ) • P.P p (q + 1) (p + q + 1) _ x ((K₂.d q (q + 1)).hom y)
      rw [P.leib p q (p + q) rfl x y, sgn_ofNat]

/-- **The extension by zero of a pairing** satisfying the Leibniz rule, as a pairing of
relation-indexed complexes `GPair`. -/
def natPair (P : NatPair K₁ K₂ K₃) : GPair (natCx K₁) (natCx K₂) (natCx K₃) where
  P := natPairP P
  leib := natPairP_leib P

end Nat

/-! ### Products of relation-indexed complexes (finite direct sums `⊕_v`) -/

section Pi

variable {ι : Type u}

/-- **The product (for finite `ι`, the direct sum) of a family of complexes**:
`X n = ∏_v A_v^n`, componentwise differential. -/
def piCx (A : ι → GCx k) : GCx k where
  X n := ModuleCat.of k (∀ v, (A v).X n)
  d i j h := LinearMap.pi fun v => ((A v).d i j h).comp (LinearMap.proj v)
  d_d i j l hij hjl x := by
    funext v
    exact (A v).d_d i j l hij hjl (x v)

theorem piCx_d_apply (A : ι → GCx k) (i j : ℤ) (h : i + 1 = j) (x : (piCx A).X i) (v : ι) :
    (piCx A).d i j h x v = (A v).d i j h (x v) :=
  rfl

/-- The map into a product given by its components. -/
def piLift {A : ι → GCx k} {B : GCx k} (f : ∀ v, GHom B (A v)) : GHom B (piCx A) where
  f i j h := LinearMap.pi fun v => (f v).f i j h
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    funext v
    exact (f v).comm i i₁ j j₁ hij h₁ h₂ hj x

/-- The product of a family of maps. -/
def piMap {A B : ι → GCx k} (f : ∀ v, GHom (A v) (B v)) : GHom (piCx A) (piCx B) where
  f i j h := LinearMap.pi fun v => ((f v).f i j h).comp (LinearMap.proj v)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    funext v
    exact (f v).comm i i₁ j j₁ hij h₁ h₂ hj (x v)

/-- The product of a family of pairings, componentwise. -/
def piPair {A B T : ι → GCx k} (P : ∀ v, GPair (A v) (B v) (T v)) :
    GPair (piCx A) (piCx B) (piCx T) where
  P i j l h := LinearMap.mk₂ k (fun x y v => (P v).P i j l h (x v) (y v))
    (fun x x' y => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun c x y => by funext v; exact LinearMap.map_smul₂ _ _ _ _)
    (fun x y y' => by funext v; exact map_add _ _ _)
    (fun c x y => by funext v; exact map_smul _ _ _)
  leib i i₁ j j₁ l l₁ h hi hj hl x y := by
    funext v
    exact (P v).leib i i₁ j j₁ l l₁ h hi hj hl (x v) (y v)

end Pi

/-! ### Selmer data over genuine continuous cochains -/

section Generic

variable (k) (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- The global complex `C^•_cont(G_S, M)` (`RΓ(G_{K,S}, M)` of (4.3)) as a `GCx`. -/
abbrev globalCx : GCx k := natCx (contCochains k GS M)

/-- The local complex `C^•_cont(G_v, M)` (`RΓ(K_v, M)` of (4.3)), `G_v` acting through `loc_v`. -/
abbrev localCx (v : ι) : GCx k := natCx (contCochains k (Gv v) (ResMod (loc v) M))

/-- `⊕_v C^•_cont(G_v, M)`. -/
abbrev localSumCx : GCx k := piCx (localCx k GS Gv loc M)

/-- **The restriction `res_S = (res_v)_v : C^•_cont(G_S, M) → ⊕_v C^•_cont(G_v, M)`**, restriction
along the localization maps `loc_v` (Nekovář 5.1, p. 113, `p_v^*`). A chain map. -/
def resS : GHom (globalCx k GS M) (localSumCx k GS Gv loc M) :=
  piLift fun v => natHom (resCochains (k := k) (M := M) (loc v))

/-- **Local conditions** (Nekovář 6.1.1, p. 135): at every place `v` a complex `U_v` of
`k`-modules with a morphism of complexes `i_v : U_v → C^•_cont(G_v, M)`. -/
structure LocalConditions where
  /-- The local condition complexes `U_v⁺`. -/
  U : ι → GCx k
  /-- The morphisms `i_v⁺ : U_v⁺ → C^•_cont(G_v, M)`. -/
  i : ∀ v, GHom (U v) (localCx k GS Gv loc M v)

/-- **The genuine Selmer data** `C^•_cont(G_S, M) --res_S--> ⊕_v C^•_cont(G_v, M) <--i_S-- ⊕_v U_v`
attached to local conditions; its Selmer complex `selCx (selData Δ)` is Nekovář's
`C^•_f(G_{K,S}, M; Δ)` (6.1.2), i.e. (4.3) of the text, up to the sign isomorphism `nekIso`. -/
def selData (Δ : LocalConditions k GS Gv loc M) : SelData k :=
  ⟨globalCx k GS M, piCx Δ.U, localSumCx k GS Gv loc M, resS k GS Gv loc M, piMap Δ.i⟩

end Generic

/-! ### Nekovář's sign convention -/

section Nekovar

variable (D : SelData k)

/-- Nekovář's differential on `C^n = G^n ⊕ U^n ⊕ L^{n−1}` (Nekovář 1.3.1, p. 41, with
`f = res`, `g = i⁺`, as in 6.1.2): `d(a, b, c) = (da, db, −res a + i b − dc)`. -/
def nekD (i j : ℤ) (h : i + 1 = j) : selT D i →ₗ[k] selT D j where
  toFun c := (D.G.d i j h c.1, D.U.d i j h c.2.1,
    -D.res.f i (j - 1) (by omega) c.1 + D.ι.f i (j - 1) (by omega) c.2.1 -
      D.L.d (i - 1) (j - 1) (by omega) c.2.2)
  map_add' c c' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [map_add, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' r c := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_sub, smul_add,
        smul_neg]

/-- **Nekovář's Selmer complex** `C_f = Cone(G ⊕ U --(res, −i)--> L)[−1]` with Nekovář's signs
(6.1.2 and 1.3.1). -/
def nekCx : GCx k where
  X := selX D
  d := nekD D
  d_d i j l hij hjl c := by
    obtain ⟨a, u, x⟩ := c
    have e1 := D.res.comm i j (j - 1) (l - 1) (by omega) hij (by omega) (by omega) a
    have e2 := D.ι.comm i j (j - 1) (l - 1) (by omega) hij (by omega) (by omega) u
    have e3 := D.L.d_d (i - 1) (j - 1) (l - 1) (by omega) (by omega) x
    change (D.G.d j l hjl (D.G.d i j hij a), D.U.d j l hjl (D.U.d i j hij u),
      -D.res.f j (l - 1) _ (D.G.d i j hij a) + D.ι.f j (l - 1) _ (D.U.d i j hij u) -
        D.L.d (j - 1) (l - 1) _ (-D.res.f i (j - 1) _ a + D.ι.f i (j - 1) _ u -
          D.L.d (i - 1) (j - 1) _ x)) = 0
    rw [D.G.d_d, D.U.d_d, e1, e2, map_sub, map_add, map_neg, e3]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change _ = (0 : D.L.X (l - 1))
    abel

/-- The sign change `(a, u, x) ↦ (a, u, −x)`. -/
def signFlip (i : ℤ) : selT D i →ₗ[k] selT D i :=
  LinearMap.id.prodMap (LinearMap.id.prodMap (-LinearMap.id))

theorem signFlip_signFlip (i : ℤ) (c : selT D i) : signFlip D i (signFlip D i c) = c := by
  obtain ⟨a, u, x⟩ := c
  simp [signFlip]

/-- `(a, u, x) ↦ (a, u, −x)` as a chain map from `selCx` to Nekovář's convention. -/
def toNek : GHom (selCx D) (nekCx D) where
  f i j h := by subst h; exact signFlip D i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    change ((D.G.d i i₁ h₁ a, D.U.d i i₁ h₁ u,
        -(D.res.f i (i₁ - 1) _ a - D.ι.f i (i₁ - 1) _ u - D.L.d (i - 1) (i₁ - 1) _ x)) :
          selT D i₁) =
      (D.G.d i i₁ h₂ a, D.U.d i i₁ h₂ u,
        -D.res.f i (i₁ - 1) _ a + D.ι.f i (i₁ - 1) _ u - D.L.d (i - 1) (i₁ - 1) _ (-x))
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [map_neg]
    abel

/-- `(a, u, x) ↦ (a, u, −x)` as a chain map from Nekovář's convention to `selCx`. -/
def fromNek : GHom (nekCx D) (selCx D) where
  f i j h := by subst h; exact signFlip D i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    change ((D.G.d i i₁ h₁ a, D.U.d i i₁ h₁ u,
        -(-D.res.f i (i₁ - 1) _ a + D.ι.f i (i₁ - 1) _ u - D.L.d (i - 1) (i₁ - 1) _ x)) :
          selT D i₁) =
      (D.G.d i i₁ h₂ a, D.U.d i i₁ h₂ u,
        D.res.f i (i₁ - 1) _ a - D.ι.f i (i₁ - 1) _ u - D.L.d (i - 1) (i₁ - 1) _ (-x))
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [map_neg]
    abel

/-- **The Selmer complex `selCx D` is isomorphic to Nekovář's `C_f`** (signs of 1.3.1/6.1.2)
through `(a, u, x) ↦ (a, u, −x)`. PROVED. -/
def nekIso : (selCx D).toCC ≅ (nekCx D).toCC where
  hom := GHom.toCC (toNek D)
  inv := GHom.toCC (fromNek D)
  hom_inv_id := by
    ext i c
    exact signFlip_signFlip D i c
  inv_hom_id := by
    ext i c
    exact signFlip_signFlip D i c

end Nekovar

/-! ### The exact sequences of Nekovář 6.1.3 and their long exact sequences -/

section Sequences

variable (D : SelData k)

/-- `0 → C_c → C_f → U_S⁺ → 0` (Nekovář 6.1.3, p. 136), with `C_c = Cone(G → L)[−1]`
(`compactCx`, the compactly supported cochains of Nekovář 5.3.1.1 for the genuine data). -/
def sesCompact : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  ShortComplex.mk (GHom.toCC (inclCompact D)) (GHom.toCC (projU D)) (by
    rw [GHom.toCC_comp]
    ext i c
    rfl)

/-- The sequence `0 → C_c → C_f → U_S⁺ → 0` is short exact. PROVED. -/
theorem sesCompact_shortExact : (sesCompact D).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, u, x⟩ := c
    change u = 0 at hc
    subst hc
    exact ⟨(a, x), rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro c c' h
    obtain ⟨b, y⟩ := c
    obtain ⟨b', y'⟩ := c'
    change ((b, (0 : D.U.X i), y) : selT D i) = (b', 0, y') at h
    simp only [Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  · rw [ModuleCat.epi_iff_surjective]
    intro u
    exact ⟨(0, u, 0), rfl⟩

/-- **The long exact sequence of the triangle `U_S⁻[−1] → C_f → C(G_S) →`** (Nekovář 6.1.3.2):
exactness of `H^i(C(G_S)) → H^{j}(U_S⁻[−1]) → H^{j}(C_f)` (with `j = i + 1`), of
`H^i(U_S⁻[−1]) → H^i(C_f) → H^i(C(G_S))` and of `H^i(C_f) → H^i(C(G_S)) → H^{j}(U_S⁻[−1])`.
PROVED (Mathlib's homology sequence of the short exact sequence `sesTop`). -/
theorem selmer_les (i j : ℤ) (hij : i + 1 = j) :
    (ShortComplex.mk _ _ ((sesTop_shortExact D).δ_comp i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap (sesTop D).f i)
      (HomologicalComplex.homologyMap (sesTop D).g i) (by
        rw [← HomologicalComplex.homologyMap_comp, (sesTop D).zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ ((sesTop_shortExact D).comp_δ i j hij)).Exact :=
  ⟨(sesTop_shortExact D).homology_exact₁ i j hij, (sesTop_shortExact D).homology_exact₂ i,
    (sesTop_shortExact D).homology_exact₃ i j hij⟩

/-- **The long exact sequence of `C_c → C_f → U_S⁺ →`** (Nekovář 6.1.3.2). PROVED. -/
theorem selmer_les_compact (i j : ℤ) (hij : i + 1 = j) :
    (ShortComplex.mk _ _ ((sesCompact_shortExact D).δ_comp i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap (sesCompact D).f i)
      (HomologicalComplex.homologyMap (sesCompact D).g i) (by
        rw [← HomologicalComplex.homologyMap_comp, (sesCompact D).zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ ((sesCompact_shortExact D).comp_δ i j hij)).Exact :=
  ⟨(sesCompact_shortExact D).homology_exact₁ i j hij, (sesCompact_shortExact D).homology_exact₂ i,
    (sesCompact_shortExact D).homology_exact₃ i j hij⟩

end Sequences

/-! ### Morphisms of local conditions; strict and relaxed conditions -/

section StrictRelaxed

variable (k) (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- The zero complex. -/
def zeroCx : GCx k where
  X _ := ModuleCat.of k PUnit.{u + 1}
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- **Strict local conditions** `U_v = 0`. Their Selmer complex is the complex of compactly
supported cochains (`strictIso`; Nekovář 5.3.1.1, 6.1.3). -/
def strictConditions : LocalConditions k GS Gv loc M :=
  ⟨fun _ => zeroCx k, fun _ => zeroGHom _ _⟩

/-- **Relaxed local conditions** `U_v = C^•_cont(G_v, M)`, `i_v = id`. -/
def relaxedConditions : LocalConditions k GS Gv loc M :=
  ⟨localCx k GS Gv loc M, fun _ => idGHom _⟩

variable {k GS Gv loc M}

/-- **The map of Selmer complexes induced by a morphism of local conditions** `F : U_v → U'_v`
with `i'_v ∘ F_v = i_v`: `(a, u, x) ↦ (a, F u, x)` (Nekovář 6.4.2(i) with `λ = id`, `v_j = 0`).
A chain map. PROVED. -/
def condMap (Δ Δ' : LocalConditions k GS Gv loc M) (F : ∀ v, GHom (Δ.U v) (Δ'.U v))
    (hF : ∀ v (i : ℤ) (u : (Δ.U v).X i), (Δ'.i v).f i i rfl ((F v).f i i rfl u) = (Δ.i v).f i i rfl u) :
    GHom (selCx (selData k GS Gv loc M Δ)) (selCx (selData k GS Gv loc M Δ')) where
  f i j h := by
    subst h
    exact (LinearMap.id).prodMap (((piMap F).f i i rfl).prodMap LinearMap.id)
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    have e1 := (piMap F).comm i i₁ i i₁ rfl h₁ h₂ rfl u
    have e2 : (piMap Δ'.i).f i (i₁ - 1) (by omega) ((piMap F).f i i rfl u) =
        (piMap Δ.i).f i (i₁ - 1) (by omega) u := by
      have hii : i = i₁ - 1 := by omega
      subst hii
      funext v
      exact hF v (i₁ - 1) (u v)
    change ((selData k GS Gv loc M Δ').G.d i i₁ h₁ a, (piMap F).f i₁ i₁ rfl ((piCx Δ.U).d i i₁ h₁ u),
        (resS k GS Gv loc M).f i (i₁ - 1) _ a - (piMap Δ.i).f i (i₁ - 1) _ u -
          (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) _ x) =
      ((selData k GS Gv loc M Δ').G.d i i₁ h₂ a, (piCx Δ'.U).d i i₁ h₂ ((piMap F).f i i rfl u),
        (resS k GS Gv loc M).f i (i₁ - 1) _ a - (piMap Δ'.i).f i (i₁ - 1) _ ((piMap F).f i i rfl u) -
          (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) _ x)
    rw [e1, e2]

/-- The comparison `C_str → C_U` (strict to arbitrary local conditions). -/
def strictToSel (Δ : LocalConditions k GS Gv loc M) :
    GHom (selCx (selData k GS Gv loc M (strictConditions k GS Gv loc M)))
      (selCx (selData k GS Gv loc M Δ)) :=
  condMap _ Δ (fun _ => zeroGHom _ _) (fun _ _ _ => by
    change (Δ.i _).f _ _ rfl 0 = 0
    exact map_zero _)

/-- The comparison `C_U → C_rel` (arbitrary to relaxed local conditions). -/
def selToRelaxed (Δ : LocalConditions k GS Gv loc M) :
    GHom (selCx (selData k GS Gv loc M Δ))
      (selCx (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))) :=
  condMap Δ _ Δ.i (fun _ _ _ => rfl)

/-- The projection `C_U → ⊕_v U_v`, `(a, u, x) ↦ u`. -/
def selToConditions (Δ : LocalConditions k GS Gv loc M) :
    GHom (selCx (selData k GS Gv loc M Δ)) (piCx Δ.U) :=
  projU (selData k GS Gv loc M Δ)

/-- `0 → C_str → C_U → ⊕_v U_v → 0`. -/
def strictSES (Δ : LocalConditions k GS Gv loc M) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  ShortComplex.mk (GHom.toCC (strictToSel Δ)) (GHom.toCC (selToConditions Δ)) (by
    rw [GHom.toCC_comp]
    ext i c
    rfl)

/-- **The strict and the arbitrary Selmer complexes differ by the local conditions**:
`0 → C_str → C_U → ⊕_v U_v → 0` is short exact (Nekovář 6.1.3 with `C_str = C_c`). PROVED. -/
theorem strictSES_shortExact (Δ : LocalConditions k GS Gv loc M) : (strictSES Δ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, u, x⟩ := c
    change u = 0 at hc
    subst hc
    exact ⟨(a, fun _ => PUnit.unit, x), rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro c c' h
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    have hu : u = u' := funext fun _ => rfl
    have h1 : a = a' := congrArg Prod.fst h
    have h3 : x = x' := congrArg (fun c => c.2.2) h
    rw [h1, hu, h3]
  · rw [ModuleCat.epi_iff_surjective]
    intro u
    exact ⟨(0, u, 0), rfl⟩

/-- `(a, 0, x) ↦ (a, x)`: the strict Selmer complex onto the compactly supported cochains. -/
def strictToCompact :
    GHom (selCx (selData k GS Gv loc M (strictConditions k GS Gv loc M)))
      (compactCx (selData k GS Gv loc M (strictConditions k GS Gv loc M))) where
  f i j h := by
    subst h
    exact (LinearMap.fst k _ _).prod ((LinearMap.snd k _ _).comp (LinearMap.snd k _ _))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl ?_
    have h0 : (piMap (strictConditions k GS Gv loc M).i).f i (i₁ - 1) (by omega) u = 0 := by
      funext v
      rfl
    change (resS k GS Gv loc M).f i (i₁ - 1) _ a -
        (piMap (strictConditions k GS Gv loc M).i).f i (i₁ - 1) _ u -
          (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) _ x =
      (resS k GS Gv loc M).f i (i₁ - 1) _ a - (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) _ x
    rw [h0, sub_zero]

/-- **The strict Selmer complex is the complex of compactly supported cochains**
`C_c = Cone(C(G_S, M) → ⊕_v C(G_v, M))[−1]` (Nekovář 5.3.1.1): the isomorphism
`(a, 0, x) ↦ (a, x)`. PROVED. -/
def strictIso :
    (selCx (selData k GS Gv loc M (strictConditions k GS Gv loc M))).toCC ≅
      (compactCx (selData k GS Gv loc M (strictConditions k GS Gv loc M))).toCC where
  hom := GHom.toCC strictToCompact
  inv := GHom.toCC (inclCompact (selData k GS Gv loc M (strictConditions k GS Gv loc M)))
  hom_inv_id := by
    ext i c
    obtain ⟨a, u, x⟩ := c
    have hu : (0 : (piCx fun _ : ι => zeroCx k).X i) = u := funext fun _ => rfl
    change ((a, (0 : (piCx fun _ : ι => zeroCx k).X i), x) : selT _ i) = (a, u, x)
    rw [hu]
  inv_hom_id := by
    ext i c
    rfl

/-- On the relaxed (full) condition, `−ι = −id` is an isomorphism of complexes. -/
theorem relaxed_negι_isIso :
    IsIso (GHom.toCC (negι (selData k GS Gv loc M (relaxedConditions k GS Gv loc M)))) :=
  ⟨⟨GHom.toCC (negι (selData k GS Gv loc M (relaxedConditions k GS Gv loc M)) :
      GHom (selData k GS Gv loc M (relaxedConditions k GS Gv loc M)).L
        (selData k GS Gv loc M (relaxedConditions k GS Gv loc M)).U), by
    ext i x
    exact neg_neg x, by
    ext i x
    exact neg_neg x⟩⟩

/-- **The local part `U_S⁻[−1] = Cone(U_S → ⊕_v C(G_v, M))[−1]` of the relaxed Selmer complex is
acyclic** (the cone of the identity, up to sign). PROVED. -/
theorem relaxed_locCx_acyclic :
    GAcyclic (locCx (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))) := by
  apply coneCx_acyclic_of_quasiIso
  have := relaxed_negι_isIso (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M)
  infer_instance

/-- **The relaxed Selmer complex computes the cohomology of `G_S`**: the projection
`C_rel → C^•_cont(G_S, M)`, `(a, u, x) ↦ a`, is a quasi-isomorphism (Nekovář 6.1.3: with
`U_v⁺ = C(G_v, M)` the triangle `U_S⁻[−1] → C_f → C(G_S) →` has acyclic first term). PROVED. -/
theorem relaxed_quasiIso :
    QuasiIso (GHom.toCC (projG (selData k GS Gv loc M (relaxedConditions k GS Gv loc M)))) := by
  have hacyc := (acyclic_toCC_iff _).2 (relaxed_locCx_acyclic (k := k) (GS := GS) (Gv := Gv)
    (loc := loc) (M := M))
  have hS := sesTop_shortExact (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))
  have hz : ∀ m, Limits.IsZero
      ((sesTop (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))).X₁.homology m) :=
    fun m => (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hacyc m)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap
      (sesTop (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))).g n) :=
    (hS.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap
      (sesTop (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))).g n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap
    (sesTop (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))).g n)

end StrictRelaxed

/-! ### Cup products on the genuine complexes -/

section CupPair

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul G A]
  [AddCommGroup B] [Module k B] [DistribMulAction G B] [SMulCommClass G k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul G B]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T]
  (β : A →ₗ[k] B →ₗ[k] T)

/-- The differential of `C^•_cont(G, M)` on underlying cochains is Mathlib's inhomogeneous
differential. -/
theorem contCochains_d_coe {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] (n : ℕ) (x : (contCochains k G M).X n) :
    (((contSubCx k G M).el (((contCochains k G M).d n (n + 1)).hom x) : contCochain k G M (n + 1)) :
      (groupCohomology.inhomogeneousCochains (rep k G M)).X (n + 1)) =
      (inhomogeneousCochains.d (rep k G M) n).hom ((contSubCx k G M).el x) := by
  rw [SubCx.toCx_d_apply, groupCohomology.inhomogeneousCochains.d_def]

/-- The underlying function `Gⁿ → M` of an element of `C^n_cont(G, M)`. -/
abbrev cFun {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] {n : ℕ} (x : (contCochains k G M).X n) : (Fin n → G) → M :=
  asFun k G M ((contSubCx k G M).el x).1

/-- **The cup product of continuous cochains** `Cᵖ_cont(G, A) × C^q_cont(G, B) → Cⁿ_cont(G, T)`,
`p + q = n`, for a bilinear pairing `β : A × B → T` jointly continuous (automatic for discrete
modules): `(a ∪ b)(g₁,…,gₙ) = β(a(g₁,…,g_p), (g₁⋯g_p) • b(g_{p+1},…,gₙ))` (Nekovář 3.4.5.1,
p. 84; Neukirch–Schmidt–Wingberg I §4). -/
def contCup (hβc : Continuous fun x : A × B => β x.1 x.2) (p q n : ℕ) (h : p + q = n) :
    (contCochains k G A).X p →ₗ[k] (contCochains k G B).X q →ₗ[k] (contCochains k G T).X n :=
  LinearMap.mk₂ k
    (fun a b => (contSubCx k G T).ofSub ⟨cupFun β p q n h (cFun a) (cFun b),
      continuous_cupFun β hβc p q n h ((contSubCx k G A).el a).2 ((contSubCx k G B).el b).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (cup β p q n h) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (cup β p q n h) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (cup β p q n h _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (cup β p q n h _) _ _))

/-- **The cup product on `C^•_cont(G, −)` satisfies the Leibniz rule**
`d(a ∪ b) = da ∪ b + (−1)^p a ∪ db` (Nekovář 3.4.5.1; from `cupFun_leibniz`), for a
`G`-equivariant pairing. PROVED. -/
def contNatPair (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
    (hβc : Continuous fun x : A × B => β x.1 x.2) :
    NatPair (contCochains k G A) (contCochains k G B) (contCochains k G T) where
  P := contCup β hβc
  leib p q n h x y := by
    apply Subtype.ext
    change ((contSubCx k G T).el (((contCochains k G T).d n (n + 1)).hom
          (contCup β hβc p q n h x y))).1 =
      cupFun β (p + 1) q (n + 1) (by omega)
          (asFun k G A ((contSubCx k G A).el (((contCochains k G A).d p (p + 1)).hom x)).1)
          (cFun y) +
        ((-1 : ℤ) ^ p) • cupFun β p (q + 1) (n + 1) (by omega) (cFun x)
          (asFun k G B ((contSubCx k G B).el (((contCochains k G B).d q (q + 1)).hom y)).1)
    rw [contCochains_d_coe, contCochains_d_coe, contCochains_d_coe]
    change (inhomogeneousCochains.d (rep k G T) n).hom (cupFun β p q n h (cFun x) (cFun y)) = _
    rw [cupFun_leibniz β hβ, ← Int.cast_smul_eq_zsmul k]
    push_cast
    rfl

end CupPair

/-- Cochain maps compatible with two pairings induce compatible maps of the extensions by zero. -/
theorem natF_natPairP {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex (ModuleCat.{u} k) ℕ}
    (P : NatPair K₁ K₂ K₃) (P' : NatPair L₁ L₂ L₃) (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
    (hφ : ∀ (p q n : ℕ) (h : p + q = n) (x : K₁.X p) (y : K₂.X q),
      (φ₃.f n).hom (P.P p q n h x y) = P'.P p q n h ((φ₁.f p).hom x) ((φ₂.f q).hom y))
    (i j l : ℤ) (h : i + j = l) (x : natX K₁ i) (y : natX K₂ j) :
    natF φ₃ l (natPairP P i j l h x y) = natPairP P' i j l h (natF φ₁ i x) (natF φ₂ j y) := by
  cases i with
  | negSucc a =>
    change natF φ₃ l 0 = 0
    exact map_zero _
  | ofNat p =>
    cases j with
    | negSucc b =>
      change natF φ₃ l 0 = 0
      exact map_zero _
    | ofNat q =>
      obtain rfl : l = Int.ofNat (p + q) := by simp only [Int.ofNat_eq_natCast] at h ⊢; omega
      exact hφ p q (p + q) _ x y

/-! ### The genuine cup-product data on Selmer complexes (`SelPairData`) -/

section PairData

variable (k) (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
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

/-- The coefficient pairing `β` on the restricted modules (the same map). -/
def resPairing {H : Type u} [Group H] [TopologicalSpace H] (φ : H →ₜ* GS) :
    ResMod φ A →ₗ[k] ResMod φ B →ₗ[k] ResMod φ T := β

omit [IsTopologicalGroup GS] in
include hβc in
/-- The restricted pairing is jointly continuous (same map, same topologies). -/
theorem resPairing_continuous {H : Type u} [Group H] [TopologicalSpace H] (φ : H →ₜ* GS) :
    Continuous fun x : ResMod φ A × ResMod φ B => resPairing k GS β φ x.1 x.2 :=
  hβc

/-- **The global cup product** `C^•_cont(G_S, A) × C^•_cont(G_S, B) → C^•_cont(G_S, T)` as a
pairing of complexes (`GPair`; Leibniz rule PROVED). -/
def globalPair : GPair (globalCx k GS A) (globalCx k GS B) (globalCx k GS T) :=
  natPair (contNatPair β hβ hβc)

/-- **The local cup product** at `v`, `C^•_cont(G_v, A) × C^•_cont(G_v, B) → C^•_cont(G_v, T)`. -/
def localPair (v : ι) :
    GPair (localCx k GS Gv loc A v) (localCx k GS Gv loc B v) (localCx k GS Gv loc T v) :=
  natPair (contNatPair (resPairing k GS β (loc v)) (fun h a b => hβ (loc v h) a b)
    (resPairing_continuous k GS β hβc (loc v)))

/-- `⊕_v` of the local cup products. -/
def localSumPair :
    GPair (localSumCx k GS Gv loc A) (localSumCx k GS Gv loc B) (localSumCx k GS Gv loc T) :=
  piPair (localPair k GS Gv loc β hβ hβc)


/-- **Restriction commutes with cup products** `res_v(a ∪ b) = res_v a ∪ res_v b` (on genuine
continuous cochains; from `cupFun_comp`). PROVED. -/
theorem res_cup (v : ι) (p q n : ℕ) (h : p + q = n) (a : (contCochains k GS A).X p)
    (b : (contCochains k GS B).X q) :
    ((resCochains (k := k) (M := T) (loc v)).f n).hom (contCup β hβc p q n h a b) =
      contCup (k := k) (G := Gv v) (resPairing k GS β (loc v))
        (resPairing_continuous k GS β hβc (loc v)) p q n h
        (((resCochains (k := k) (M := A) (loc v)).f p).hom a)
        (((resCochains (k := k) (M := B) (loc v)).f q).hom b) := by
  apply Subtype.ext
  funext x
  exact congrArg (β _) (congrArg (· • _) (map_headProd (loc v : Gv v →* GS) p n (by omega) x).symm)

/-- **Nekovář's orthogonality data** (6.2.1.3, p. 138, in untruncated form): at every place `v`
a homotopy `h_v : U_v(A) ⊗ U_v(B) → C^•_cont(G_v, T)` of degree `−1` with
`d h_v(x, y) + h_v(dx, y) + (−1)^i h_v(x, dy) = i_v x ∪ i_v y`, i.e. a null-homotopy of the local
product `prod_v`. (Nekovář's `prod_v` lands in `τ_{≥2} C(G_v, J(1))`; a null-homotopy into the
untruncated complex, as here, induces one into the truncation, so these data give Nekovář's
`Δ_v(A) ⊥_{π,h_v} Δ_v(B)`.) -/
structure IsotropyData (ΔA : LocalConditions k GS Gv loc A) (ΔB : LocalConditions k GS Gv loc B) where
  /-- The isotropy homotopies `h_v`. -/
  h : ∀ (v : ι) (i j l : ℤ), i + j = l + 1 →
    (ΔA.U v).X i →ₗ[k] (ΔB.U v).X j →ₗ[k] (localCx k GS Gv loc T v).X l
  /-- The homotopy identity. -/
  isotropy : ∀ (v : ι) (i i₁ j j₁ l l₁ : ℤ) (hh : i + j = l + 1) (hi : i + 1 = i₁)
    (hj : j + 1 = j₁) (hl : l + 1 = l₁) (x : (ΔA.U v).X i) (y : (ΔB.U v).X j),
    (localCx k GS Gv loc T v).d l l₁ hl (h v i j l hh x y) +
        h v i₁ j l₁ (by omega) ((ΔA.U v).d i i₁ hi x) y +
        sgn i • h v i j₁ l₁ (by omega) x ((ΔB.U v).d j j₁ hj y) =
      (localPair k GS Gv loc β hβ hβc v).P i j l₁ (by omega) ((ΔA.i v).f i i rfl x)
        ((ΔB.i v).f j j rfl y)

/-- **The genuine cup-product data** of Nekovář 6.3.1 on the genuine Selmer data: global and
local cup products of continuous cochains (Leibniz rule PROVED), restriction of the target
`res_S : C(G_S, T) → ⊕_v C(G_v, T)`, the compatibility `res(a ∪ b) = res a ∪ res b` (PROVED), and
the isotropy homotopies. An instance of the abstract `SelPairData`. -/
def genuinePairData (ΔA : LocalConditions k GS Gv loc A) (ΔB : LocalConditions k GS Gv loc B)
    (I : IsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    SelPairData (selData k GS Gv loc A ΔA) (selData k GS Gv loc B ΔB) where
  E := globalCx k GS T
  EL := localSumCx k GS Gv loc T
  resE := resS k GS Gv loc T
  cupG := globalPair k GS β hβ hβc
  cupL := localSumPair k GS Gv loc β hβ hβc
  compat i j l i' j' l' h h' hi hj hl a b := by
    subst hi hj hl
    funext v
    exact natF_natPairP _ _ _ _ _ (fun p q n hpq x y => res_cup k GS Gv loc β hβc v p q n hpq x y)
      i j l h a b
  hU i j l h := LinearMap.mk₂ k (fun x y v => I.h v i j l h (x v) (y v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact LinearMap.map_smul₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun _ _ _ => by funext v; exact map_smul _ _ _)
  isotropy i i₁ j j₁ l l₁ h hi hj hl x y := by
    funext v
    exact I.isotropy v i i₁ j j₁ l l₁ h hi hj hl (x v) (y v)

/-- **Non-vacuity of `IsotropyData`**: for the strict conditions (`U_v = 0`) on both sides the
zero homotopies are isotropy data. PROVED. -/
def strictIsotropy :
    IsotropyData k GS Gv loc β hβ hβc (strictConditions k GS Gv loc A)
      (strictConditions k GS Gv loc B) where
  h _ _ _ _ _ := 0
  isotropy v i i₁ j j₁ l l₁ hh hi hj hl x y := by
    change (localCx k GS Gv loc T v).d l l₁ hl 0 + 0 + sgn i • (0 : (localCx k GS Gv loc T v).X l₁) =
      (localPair k GS Gv loc β hβ hβc v).P i j l₁ _ 0 0
    simp

end PairData

end ZInQ.Manuscript.RC.SelmerComplex





