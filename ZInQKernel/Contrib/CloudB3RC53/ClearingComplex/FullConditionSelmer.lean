import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# The genuine full-condition Selmer complex at the new places and the triangle (5.6)

Manuscript `diophantine_zq.tex`, "Actual support comparisons", tex 3479–3498 ("Replacing the
unramified condition by the full condition then gives the singular quotient by a cone of Selmer
cones"), and the triangle (5.6), tex 5234–5238: `C_old → (C_b)₀ → ⊕_q Q_q → C_old[1]`.
Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.1.3, 6.4.2(i), 7.8.8(ii).

Over the new support `S' ⊇ S`, with the old local conditions at the old places, this file
constructs

* `fullSelData`: the Selmer data with the **full** condition
  `id : C^•_cont(G_q, M) → C^•_cont(G_q, M)` at every new place `q` (the complex `(C_b)₀` of (5.6));
* `urInFull`: the unramified conditions `C^•_cont(G_q/I_q, M) → C^•_cont(G_q, M)` (inflation) inside
  the full conditions, identity at the old places; `restrictData_urInFull`: restricting the full
  data along it is literally the unramified support data `newSelData` of Nekovář 7.8.8(ii) (`rfl`);
* `singQ`: the singular quotients `⊕_q C^•_cont(G_q, M) / C^•_cont(G_q/I_q, M)` (the `⊕_q Q_q` of
  (5.6); for the tame model these are `[M --(Φ_q−q)--> M]` in degrees one and two, tex 3479–3481);
  `singProj`;
* `fullSES_shortExact`: `0 → C(ur) → C(full) → ⊕_q Q_q → 0` is short exact when every
  `π_q : G_q → G_q/I_q` is surjective (PROVED: inflation along a surjection is injective on
  cochains; `relaxedQuotientNode_proof`);
* the Galois specialization `galoisFullData`, `galoisFullSES_shortExact` (the restriction
  `G_{K_q} → Gal(K_q^{ur}/K_q)` is surjective, `urRes_surjective`), with the unramified side the
  genuine `(galoisSupportData …).Dp` (`rfl`). The set of new places may be empty; then
  `singQ` is the zero complex.

All declarations are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (restrictData changeSES relaxedQuotientNode_proof idGHom
  ghomComp)
open ZInQ.Manuscript.RC.SelmerComplex

universe u

section Setup

variable {k : Type u} [CommRing k]
  {GS : Type u} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {GS' : Type u} [Group GS'] [TopologicalSpace GS'] [IsTopologicalGroup GS']
  {infl : GS' →ₜ* GS}
  {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS} {loc' : ∀ v, Gv v →ₜ* GS'}
  {κ : Type u} {Gq : κ → Type u} [∀ q, Group (Gq q)] [∀ q, TopologicalSpace (Gq q)]
  [∀ q, IsTopologicalGroup (Gq q)] {locq : ∀ q, Gq q →ₜ* GS'}
  {Gur : κ → Type u} [∀ q, Group (Gur q)] [∀ q, TopologicalSpace (Gur q)]
  [∀ q, IsTopologicalGroup (Gur q)] {π : ∀ q, Gq q →ₜ* Gur q} {ψ : ∀ q, Gur q →ₜ* GS}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

variable (k GS GS' infl Gv loc loc' Gq locq M) in
/-- **The full-condition Selmer data over the new support** (the complex `(C_b)₀` of (5.6),
tex 5234–5238): global complex `C^•_cont(G_{S'}, M)`, the old conditions at the old places and the
full condition `id : C^•_cont(G_q, M) → C^•_cont(G_q, M)` at the new places. -/
def fullSelData (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (Δ : LocalConditions k GS Gv loc M) : SelData k where
  G := globalCx k GS' (ResMod infl M)
  U := prodCx (piCx Δ.U)
    (piCx fun q => natCx (contCochains k (Gq q) (ResMod (locq q) (ResMod infl M))))
  L := prodCx (localSumCx k GS' Gv loc' (ResMod infl M))
    (piCx fun q => natCx (contCochains k (Gq q) (ResMod (locq q) (ResMod infl M))))
  res := prodLift (resS k GS' Gv loc' (ResMod infl M))
    (piLift fun q => natHom (resCochains (k := k) (M := ResMod infl M) (locq q)))
  ι := prodMapG (piMap (oldCondNew k GS GS' infl Gv loc loc' M hloc Δ).i) (idGHom _)

/-- **The unramified conditions inside the full conditions** (identity at the old places,
inflation `C^•_cont(G_q/I_q, M) → C^•_cont(G_q, M)` at the new places). -/
def urInFull (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) (Δ : LocalConditions k GS Gv loc M) :
    GHom (newSelData k GS GS' infl Gv loc loc' Gq locq Gur π ψ M hloc hψ Δ).U
      (fullSelData k GS GS' infl Gv loc loc' Gq locq M hloc Δ).U :=
  prodMapG (idGHom _) (piMap fun q => natHom (urCond (k := k) (M := M) hψ q))

/-- Relation-indexed chain maps agreeing on the diagonal components are equal. -/
theorem ghom_ext' {A B : GCx k} {φ φ' : GHom A B}
    (h : ∀ i (x : A.X i), φ.f i i rfl x = φ'.f i i rfl x) : φ = φ' := by
  cases φ
  cases φ'
  congr
  funext i j hij
  subst hij
  exact LinearMap.ext (h i)

/-- **Restricting the full condition along the unramified conditions is the unramified support
data** of Nekovář 7.8.8(ii). PROVED. -/
theorem restrictData_urInFull (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) (Δ : LocalConditions k GS Gv loc M) :
    restrictData (fullSelData k GS GS' infl Gv loc loc' Gq locq M hloc Δ) (urInFull hloc hψ Δ) =
      newSelData k GS GS' infl Gv loc loc' Gq locq Gur π ψ M hloc hψ Δ := by
  change SelData.mk _ _ _ _ _ = SelData.mk _ _ _ _ _
  congr 1
  exact ghom_ext' fun i x => rfl

/-- **The singular quotients** `⊕_q C^•_cont(G_q, M) / C^•_cont(G_q/I_q, M)` (the `⊕_q Q_q` of
(5.6)). -/
def singQ (k M) [CommRing k] [AddCommGroup M] [Module k M] [DistribMulAction GS M]
    [SMulCommClass GS k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul GS M] (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) : GCx k :=
  piCx fun q => quotCx (natHom (urCond (k := k) (M := M) hψ q))

/-- The second projection of a product of complexes. -/
def sndG (A B : GCx k) : GHom (prodCx A B) B where
  f i j h := by
    subst h
    exact LinearMap.snd k (A.X i) (B.X i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    rfl

/-- The projection of the full conditions onto the singular quotients. -/
def singProj (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) (Δ : LocalConditions k GS Gv loc M) :
    GHom (fullSelData k GS GS' infl Gv loc loc' Gq locq M hloc Δ).U (singQ k M hψ) :=
  ghomComp (sndG _ _) (piMap fun q => quotMk (natHom (urCond (k := k) (M := M) hψ q)))

/-- **Inflation along a surjection is injective on continuous cochains.** -/
theorem natHom_urCond_injective (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g))
    (hπ : ∀ q, Function.Surjective (π q)) (q : κ) (i : ℤ) :
    Function.Injective ((natHom (urCond (k := k) (M := M) hψ q)).f i i rfl) := by
  match i with
  | Int.ofNat n =>
    intro x y h
    apply Subtype.ext
    funext v
    let w : Fin n → Gq q := fun m => Function.surjInv (hπ q) (v m)
    have hw : (π q : Gq q → Gur q) ∘ w = v := funext fun m => Function.surjInv_eq (hπ q) (v m)
    have h' := congrArg (fun c : (contCochains k (Gq q) (ResMod (locq q) (ResMod infl M))).X n =>
      asFun k (Gq q) (ResMod (locq q) (ResMod infl M))
        ((contSubCx k (Gq q) (ResMod (locq q) (ResMod infl M))).el c :
          contCochain k (Gq q) (ResMod (locq q) (ResMod infl M)) n) w) h
    change asFun k (Gur q) (ResMod (ψ q) M) _ ((π q : Gq q → Gur q) ∘ w) =
      asFun k (Gur q) (ResMod (ψ q) M) _ ((π q : Gq q → Gur q) ∘ w) at h'
    rw [hw] at h'
    exact h'
  | Int.negSucc n =>
    intro x y _
    exact Subsingleton.elim (α := PUnit) x y

variable (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
  (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) (Δ : LocalConditions k GS Gv loc M)

theorem singProj_urInFull (i : ℤ)
    (u : (newSelData k GS GS' infl Gv loc loc' Gq locq Gur π ψ M hloc hψ Δ).U.X i) :
    (singProj hloc hψ Δ).f i i rfl ((urInFull hloc hψ Δ).f i i rfl u) = 0 := by
  funext q
  exact quotMk_comp_apply (natHom (urCond (k := k) (M := M) hψ q)) i (u.2 q)

/-- **The sequence `C(ur) → C(full) → ⊕_q Q_q`** (the triangle (5.6) at the level of complexes). -/
def fullSES : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  changeSES (fullSelData k GS GS' infl Gv loc loc' Gq locq M hloc Δ) (urInFull hloc hψ Δ)
    (singProj hloc hψ Δ) (singProj_urInFull hloc hψ Δ)

/-- **`0 → C(ur) → C(full) → ⊕_q Q_q → 0` is short exact** (tex 3494–3498, 5234–5238; Nekovář
6.1.3, 6.4.2(i)) when every `π_q` is surjective. PROVED. -/
theorem fullSES_shortExact (hπ : ∀ q, Function.Surjective (π q)) :
    (fullSES hloc hψ Δ).ShortExact := by
  refine relaxedQuotientNode_proof _ _ _ _ _ _ _ ?_ ?_ ?_
  · intro i a b h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext h1 (funext fun q => natHom_urCond_injective hψ hπ q i ?_)
    exact congrFun h2 q
  · intro i y
    refine ⟨(0, fun q => Classical.choose (quotMk_surjective
      (natHom (urCond (k := k) (M := M) hψ q)) i (y q))), ?_⟩
    funext q
    exact Classical.choose_spec (quotMk_surjective
      (natHom (urCond (k := k) (M := M) hψ q)) i (y q))
  · intro i u hu
    have hq : ∀ q, ∃ a, (natHom (urCond (k := k) (M := M) hψ q)).f i i rfl a = u.2 q := fun q =>
      (quotMk_eq_zero_iff (natHom (urCond (k := k) (M := M) hψ q)) i (u.2 q)).1 (congrFun hu q)
    exact ⟨(u.1, fun q => Classical.choose (hq q)),
      Prod.ext rfl (funext fun q => Classical.choose_spec (hq q))⟩

end Setup

/-! ### The Galois specialization -/

section Galois

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S ⊆ S') (k : Type) [CommRing k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- **The genuine full-condition Selmer data** over `S'`: the old conditions `Δ` at `v ∈ S` and
the full condition at every new place `q ∈ S' − S` (the complex `(C_b)₀` of (5.6),
tex 5234–5238). -/
def galoisFullData (Δ : GaloisLocalConditions K S k M) : SelData k :=
  fullSelData k (GKS K S) (GKS K S') (inflMap K hS) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (fun v => locMap K S' v.1) (fun q : NewPlaces K S S' => Gloc K q.1)
    (fun q => locMap K S' q.1) M (fun v g => locMap_compat K hS v.1 g) Δ

variable (ψ : ∀ q : NewPlaces K S S', ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1 →ₜ* GKS K S)
  (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
  (Δ : GaloisLocalConditions K S k M)

/-- The genuine unramified conditions at the new places inside the full conditions. -/
def galoisUrInFull :
    GHom (galoisSupportData K hS k M ψ hψ Δ).Dp.U (galoisFullData K hS k M Δ).U :=
  urInFull (k := k) (GS := GKS K S) (GS' := GKS K S') (infl := inflMap K hS)
    (Gv := fun v : Places K S => Gloc K v.1) (loc := fun v => locMap K S v.1)
    (loc' := fun v => locMap K S' v.1) (Gq := fun q : NewPlaces K S S' => Gloc K q.1)
    (locq := fun q => locMap K S' q.1)
    (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
    (π := fun q => urRes K q.1) (ψ := ψ) (M := M)
    (fun v g => locMap_compat K hS v.1 g)
    (fun q g => (locMap_compat K hS q.1 g).trans (hψ q g)) Δ

/-- **Restricting the genuine full condition along the unramified conditions gives the genuine
unramified support data** `(galoisSupportData …).Dp`. PROVED. -/
theorem galois_restrictData_urInFull :
    restrictData (galoisFullData K hS k M Δ) (galoisUrInFull K hS k M ψ hψ Δ) =
      (galoisSupportData K hS k M ψ hψ Δ).Dp :=
  restrictData_urInFull (k := k) (GS := GKS K S) (GS' := GKS K S') (infl := inflMap K hS)
    (Gv := fun v : Places K S => Gloc K v.1) (loc := fun v => locMap K S v.1)
    (loc' := fun v => locMap K S' v.1) (Gq := fun q : NewPlaces K S S' => Gloc K q.1)
    (locq := fun q => locMap K S' q.1)
    (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
    (π := fun q => urRes K q.1) (ψ := ψ) (M := M) _ _ Δ

/-- **The genuine singular quotients** `⊕_{q ∈ S' − S} C^•_cont(G_{K_q}, M) /
C^•_cont(Gal(K_q^{ur}/K_q), M)` (the `⊕_q Q_q` of (5.6); zero when `S' = S`). -/
def galoisSingQ : GCx k :=
  singQ k M (GS := GKS K S) (GS' := GKS K S') (infl := inflMap K hS)
    (Gq := fun q : NewPlaces K S S' => Gloc K q.1) (locq := fun q => locMap K S' q.1)
    (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
    (π := fun q => urRes K q.1) (ψ := ψ) (fun q g => (locMap_compat K hS q.1 g).trans (hψ q g))

/-- **The genuine sequence `C(ur) → C(full) → ⊕_q Q_q`** over `S'`. -/
def galoisFullSES : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  fullSES (k := k) (GS := GKS K S) (GS' := GKS K S') (infl := inflMap K hS)
    (Gv := fun v : Places K S => Gloc K v.1) (loc := fun v => locMap K S v.1)
    (loc' := fun v => locMap K S' v.1) (Gq := fun q : NewPlaces K S S' => Gloc K q.1)
    (locq := fun q => locMap K S' q.1)
    (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
    (π := fun q => urRes K q.1) (ψ := ψ) (M := M) (fun v g => locMap_compat K hS v.1 g)
    (fun q g => (locMap_compat K hS q.1 g).trans (hψ q g)) Δ

/-- **The triangle (5.6) for the genuine Galois cochains: `0 → C(ur) → C(full) → ⊕_q Q_q → 0` is
short exact** (tex 3494–3498, 5234–5238; Nekovář, *Selmer complexes*, 6.1.3, 6.4.2(i)). PROVED
(`G_{K_q} → Gal(K_q^{ur}/K_q)` is surjective). -/
theorem galoisFullSES_shortExact : (galoisFullSES K hS k M ψ hψ Δ).ShortExact :=
  fullSES_shortExact (k := k) (GS := GKS K S) (GS' := GKS K S') (infl := inflMap K hS)
    (Gv := fun v : Places K S => Gloc K v.1) (loc := fun v => locMap K S v.1)
    (loc' := fun v => locMap K S' v.1) (Gq := fun q : NewPlaces K S S' => Gloc K q.1)
    (locq := fun q => locMap K S' q.1)
    (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
    (π := fun q => urRes K q.1) (ψ := ψ) (M := M) _ _ Δ (fun q => urRes_surjective K q.1)

/-- The first term of the genuine sequence is the unramified support complex. -/
theorem galoisFullSES_X₁ :
    (galoisFullSES K hS k M ψ hψ Δ).X₁ = (selCx (galoisSupportData K hS k M ψ hψ Δ).Dp).toCC := by
  change (selCx (restrictData (galoisFullData K hS k M Δ) (galoisUrInFull K hS k M ψ hψ Δ))).toCC = _
  rw [galois_restrictData_urInFull]

/-- The second term of the genuine sequence is the full-condition Selmer complex. -/
theorem galoisFullSES_X₂ :
    (galoisFullSES K hS k M ψ hψ Δ).X₂ = (selCx (galoisFullData K hS k M Δ)).toCC :=
  rfl

/-- Non-vacuity: for `S' = S` there are no new places and the construction applies to any old
local conditions; the singular quotient is then the zero complex. -/
example (Δ : GaloisLocalConditions K S k M) :
    (galoisFullSES K (subset_refl S) k M (fun q => absurd q.2.1 q.2.2)
      (fun q => absurd q.2.1 q.2.2) Δ).ShortExact :=
  galoisFullSES_shortExact K (subset_refl S) k M _ _ Δ

end Galois

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
