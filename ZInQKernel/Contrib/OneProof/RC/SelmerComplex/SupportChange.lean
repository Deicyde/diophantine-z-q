import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# Lane RC26: the genuine support change (Nekovář 7.8.8(ii)) as `SupportChangeData`

Manuscript `diophantine_zq.tex`, "Actual support comparisons", tex 3470–3499: "The support-change
theorem [Nekovář, Proposition 7.8.8(ii)] retains arbitrary old local conditions and puts the
unramified condition at new places."

Nekovář, *Selmer complexes*, 7.8.8 (pp. 186–187): for `S' ⊃ S` and local conditions `Δ_v` at
`v ∈ S_f`, put `U_v⁺ = C^•_ur(G_v, X) = C^•_cont(G_v/I_v, X)` (inflated to `C^•_cont(G_v, X)`) at
the new places `v ∈ S' − S`; then inflation `C^•_cont(G_{K,S}, X) → C^•_cont(G_{K,S'}, X)` induces
`RΓ_f(G_{K,S}, X; Δ) ≅ RΓ_f(G_{K,S'}, X; Δ ∪ (ur)_{S'−S})`.

This file constructs, over genuine continuous cochains and for abstract topological groups (the
genuine Galois groups are in `Galois.lean`), the data of this comparison as an instance of the
abstract `SupportChangeData` of the Selmer-duality files:

* old support: `G_S`, places `ι`, local groups `G_v` with `loc_v : G_v → G_S`, local conditions
  `Δ`;
* new support: `G_{S'}` with the restriction `infl : G_{S'} → G_S` (cochains are inflated along
  it), the old places with `loc'_v : G_v → G_{S'}` and `infl ∘ loc'_v = loc_v`, and new places `κ`
  with local groups `G_q`, `loc_q : G_q → G_{S'}`, the unramified quotients `π_q : G_q → G_q/I_q`
  and the factorization `ψ_q : G_q/I_q → G_S` with `infl ∘ loc_q = ψ_q ∘ π_q` (the extension
  `K_S/K` is unramified at `q ∉ S`);
* `newSelData`: the Selmer data over `G_{S'}` with the old conditions at the old places and the
  unramified conditions `C^•_cont(G_q/I_q, M) → C^•_cont(G_q, M)` at the new places;
* `supportData Δ : SupportChangeData k` with `g` = inflation, `λ`, `μ` the inclusions of the old
  local data, and `r` the new local components of inflated cochains, which lie in the unramified
  conditions (`r_q = ψ_q^*`). The identities `res⁺ ∘ g = λ ∘ res + ι⁺ ∘ r` and `ι⁺ ∘ μ = λ ∘ ι`
  are PROVED (they are exact cochain identities, from `infl ∘ loc'_v = loc_v` and
  `infl ∘ loc_q = ψ_q ∘ π_q`).

The genuine statement of Nekovář 7.8.8(ii) — that `supportMap (supportData Δ)` is a
quasi-isomorphism — is the PRINT `NekovarProp788ii` of `Prints.lean`.

Kinds: genuine definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {k : Type u} [CommRing k]

/-! ### Binary products of relation-indexed complexes -/

section Prod

/-- The product `A ⊕ B` of two complexes (componentwise). -/
def prodCx (A B : GCx k) : GCx k where
  X n := ModuleCat.of k (A.X n × B.X n)
  d i j h := (A.d i j h).prodMap (B.d i j h)
  d_d i j l hij hjl x := Prod.ext (A.d_d i j l hij hjl x.1) (B.d_d i j l hij hjl x.2)

/-- The map into a product given by its components. -/
def prodLift {C A B : GCx k} (f : GHom C A) (g : GHom C B) : GHom C (prodCx A B) where
  f i j h := (f.f i j h).prod (g.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    Prod.ext (f.comm i i₁ j j₁ hij h₁ h₂ hj x) (g.comm i i₁ j j₁ hij h₁ h₂ hj x)

/-- The product of two maps. -/
def prodMapG {A A' B B' : GCx k} (f : GHom A A') (g : GHom B B') :
    GHom (prodCx A B) (prodCx A' B') where
  f i j h := (f.f i j h).prodMap (g.f i j h)
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    Prod.ext (f.comm i i₁ j j₁ hij h₁ h₂ hj x.1) (g.comm i i₁ j j₁ hij h₁ h₂ hj x.2)

end Prod

/-! ### Extension by zero commutes with composition and agrees on equal cochain maps -/

theorem natHom_f_eq_natF {K L : CochainComplex (ModuleCat.{u} k) ℕ} (φ : K ⟶ L) (i j : ℤ)
    (h : i = j) (x : natX K i) : (natHom φ).f i j h x = h ▸ natF φ i x := by
  subst h
  rfl

/-- Two cochain maps with equal components give equal extensions by zero. -/
theorem natF_congr {K L : CochainComplex (ModuleCat.{u} k) ℕ} (φ ψ : K ⟶ L)
    (h : ∀ (n : ℕ) (x : K.X n), (φ.f n).hom x = (ψ.f n).hom x) :
    ∀ (i : ℤ) (x : natX K i), natF φ i x = natF ψ i x
  | Int.ofNat n, x => h n x
  | Int.negSucc _, _ => rfl

/-- Two cochain maps with equal components give equal extensions by zero (as `GHom`s). -/
theorem natHom_congr {K L : CochainComplex (ModuleCat.{u} k) ℕ} (φ ψ : K ⟶ L)
    (h : ∀ (n : ℕ) (x : K.X n), (φ.f n).hom x = (ψ.f n).hom x) (i : ℤ) (x : (natCx K).X i) :
    (natHom φ).f i i rfl x = (natHom ψ).f i i rfl x :=
  natF_congr φ ψ h i x

theorem natF_comp {K L N : CochainComplex (ModuleCat.{u} k) ℕ} (φ : K ⟶ L) (ψ : L ⟶ N) :
    ∀ (i : ℤ) (x : natX K i), natF (φ ≫ ψ) i x = natF ψ i (natF φ i x)
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => rfl

/-! ### The support-change setup -/

section Setup

variable (k)
  (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  (GS' : Type u) [Group GS'] [TopologicalSpace GS'] [IsTopologicalGroup GS']
  (infl : GS' →ₜ* GS)
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS) (loc' : ∀ v, Gv v →ₜ* GS')
  {κ : Type u} (Gq : κ → Type u) [∀ q, Group (Gq q)] [∀ q, TopologicalSpace (Gq q)]
  [∀ q, IsTopologicalGroup (Gq q)] (locq : ∀ q, Gq q →ₜ* GS')
  (Gur : κ → Type u) [∀ q, Group (Gur q)] [∀ q, TopologicalSpace (Gur q)]
  [∀ q, IsTopologicalGroup (Gur q)] (π : ∀ q, Gq q →ₜ* Gur q) (ψ : ∀ q, Gur q →ₜ* GS)
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

variable {k GS GS' infl Gv loc loc' Gq locq Gur π ψ M}

/-- The comparison of the two restricted modules at an old place
(`C(G_v, M)` for `G_v` acting through `loc_v`, resp. through `infl ∘ loc'_v`). -/
def oldPairMap (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g) (v : ι) :
    contCochains k (Gv v) (ResMod (loc v) M) ⟶
      contCochains k (Gv v) (ResMod (loc' v) (ResMod infl M)) :=
  contCochainsMap (ContinuousMonoidHom.id (Gv v))
    (LinearMap.id : M →ₗ[k] M) continuous_id (fun g m => by
      change (loc v g • (show M from m) : M) = (infl (loc' v g) • (show M from m) : M)
      rw [hloc])

/-- **The unramified local condition at a new place** `q`:
`C^•_cont(G_q/I_q, M) → C^•_cont(G_q, M)`, inflation along `π_q` (Nekovář 7.6.5, 7.8.8(ii);
the module is unramified at `q`: `G_q` acts through `G_q/I_q`, via `ψ_q`). -/
def urCond (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g)) (q : κ) :
    contCochains k (Gur q) (ResMod (ψ q) M) ⟶
      contCochains k (Gq q) (ResMod (locq q) (ResMod infl M)) :=
  contCochainsMap (π q) (LinearMap.id : M →ₗ[k] M) continuous_id (fun g m => by
    change (ψ q (π q g) • (show M from m) : M) = (infl (locq q g) • (show M from m) : M)
    rw [hψ])

variable (k GS GS' infl Gv loc loc' Gq locq Gur π ψ M)

/-- The old local conditions, transported to the new support (`i'_v = (comparison) ∘ i_v`). -/
def oldCondNew (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (Δ : LocalConditions k GS Gv loc M) :
    LocalConditions k GS' Gv loc' (ResMod infl M) :=
  ⟨Δ.U, fun v => ghomComp (Δ.i v) (natHom (oldPairMap (k := k) (M := M) hloc v))⟩

/-- **The Selmer data over the new support** `S' = S ⊔ κ`: global complex
`C^•_cont(G_{S'}, M)`, at the old places the old conditions, at the new places the unramified
conditions `C^•_cont(G_q/I_q, M)` (Nekovář 7.8.8(ii)); the local complex is
`⊕_{v ∈ S} C(G_v, M) ⊕ ⊕_{q ∈ κ} C(G_q, M)`. -/
def newSelData (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g))
    (Δ : LocalConditions k GS Gv loc M) : SelData k where
  G := globalCx k GS' (ResMod infl M)
  U := prodCx (piCx Δ.U) (piCx fun q => natCx (contCochains k (Gur q) (ResMod (ψ q) M)))
  L := prodCx (localSumCx k GS' Gv loc' (ResMod infl M))
    (piCx fun q => natCx (contCochains k (Gq q) (ResMod (locq q) (ResMod infl M))))
  res := prodLift (resS k GS' Gv loc' (ResMod infl M))
    (piLift fun q => natHom (resCochains (k := k) (M := ResMod infl M) (locq q)))
  ι := prodMapG (piMap (oldCondNew k GS GS' infl Gv loc loc' M hloc Δ).i)
    (piMap fun q => natHom (urCond (k := k) (M := M) hψ q))

/-- Inflation `C^•_cont(G_S, M) → C^•_cont(G_{S'}, M)` along `infl : G_{S'} → G_S`
(Nekovář 3.4.1.6, used in 7.8.8). -/
def inflG : GHom (globalCx k GS M) (globalCx k GS' (ResMod infl M)) :=
  natHom (resCochains (k := k) (M := M) infl)

/-- `λ`: the old local complexes into the new ones (the comparison at old places, `0` at new). -/
def lamG (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g) :
    GHom (localSumCx k GS Gv loc M)
      (prodCx (localSumCx k GS' Gv loc' (ResMod infl M))
        (piCx fun q => natCx (contCochains k (Gq q) (ResMod (locq q) (ResMod infl M))))) :=
  prodLift (piMap fun v => natHom (oldPairMap (k := k) (M := M) hloc v)) (zeroGHom _ _)

/-- `μ`: the old local conditions into the new ones (identity at old places, `0` at new). -/
def muG (Δ : LocalConditions k GS Gv loc M) :
    GHom (piCx Δ.U)
      (prodCx (piCx Δ.U) (piCx fun q => natCx (contCochains k (Gur q) (ResMod (ψ q) M)))) :=
  prodLift (idGHom _) (zeroGHom _ _)

/-- `r`: the new local components of inflated cochains, in the unramified conditions:
`r_q = ψ_q^* : C^•_cont(G_S, M) → C^•_cont(G_q/I_q, M)` (`0` at old places). -/
def rG (Δ : LocalConditions k GS Gv loc M) :
    GHom (globalCx k GS M)
      (prodCx (piCx Δ.U) (piCx fun q => natCx (contCochains k (Gur q) (ResMod (ψ q) M)))) :=
  prodLift (zeroGHom _ _) (piLift fun q => natHom (resCochains (k := k) (M := M) (ψ q)))

/-- **The genuine support-change data** (Nekovář 7.8.8(ii), tex 3470–3499) as an instance of
the abstract `SupportChangeData`: old Selmer data `selData Δ` over `G_S`, new Selmer data
`newSelData` over `G_{S'}`, `g` = inflation, `λ`, `μ`, `r` as above. The two identities
`res⁺ ∘ g = λ ∘ res + ι⁺ ∘ r` and `ι⁺ ∘ μ = λ ∘ ι` are PROVED. -/
def supportData (hloc : ∀ v (g : Gv v), infl (loc' v g) = loc v g)
    (hψ : ∀ q (g : Gq q), infl (locq q g) = ψ q (π q g))
    (Δ : LocalConditions k GS Gv loc M) : SupportChangeData k where
  D := selData k GS Gv loc M Δ
  Dp := newSelData k GS GS' infl Gv loc loc' Gq locq Gur π ψ M hloc hψ Δ
  g := inflG k GS GS' infl M
  lam := lamG k GS GS' infl Gv loc loc' Gq locq M hloc
  mu := muG (k := k) (GS := GS) (Gv := Gv) (loc := loc) (Gur := Gur) (ψ := ψ) (M := M) Δ
  r := rG (k := k) (GS := GS) (Gv := Gv) (loc := loc) (Gur := Gur) (ψ := ψ) (M := M) Δ
  hres i j h a := by
    subst h
    change (natCx (contCochains k GS M)).X i at a
    refine Prod.ext ?_ ?_
    · funext v
      show (natHom (resCochains (k := k) (M := ResMod infl M) (loc' v))).f i i rfl
            ((natHom (resCochains (k := k) (M := M) infl)).f i i rfl a) =
          (natHom (oldPairMap (k := k) (M := M) hloc v)).f i i rfl
            ((natHom (resCochains (k := k) (M := M) (loc v))).f i i rfl a) +
          (ghomComp (Δ.i v) (natHom (oldPairMap (k := k) (M := M) hloc v))).f i i rfl 0
      have key : ∀ (n : ℕ) (x : (contCochains k GS M).X n),
          ((resCochains (k := k) (M := M) infl ≫
              resCochains (k := k) (M := ResMod infl M) (loc' v)).f n).hom x =
            ((resCochains (k := k) (M := M) (loc v) ≫
              oldPairMap (k := k) (M := M) hloc v).f n).hom x := by
        intro n x
        apply Subtype.ext
        funext y
        exact congrArg (asFun k GS M ((contSubCx k GS M).el x).1) (funext fun m => hloc v (y m))
      rw [map_zero, add_zero]
      exact (natF_comp _ _ i a).symm.trans ((natF_congr _ _ key i a).trans (natF_comp _ _ i a))
    · funext q
      show (natHom (resCochains (k := k) (M := ResMod infl M) (locq q))).f i i rfl
            ((natHom (resCochains (k := k) (M := M) infl)).f i i rfl a) =
          0 + (natHom (urCond (k := k) (M := M) hψ q)).f i i rfl
            ((natHom (resCochains (k := k) (M := M) (ψ q))).f i i rfl a)
      have key : ∀ (n : ℕ) (x : (contCochains k GS M).X n),
          ((resCochains (k := k) (M := M) infl ≫
              resCochains (k := k) (M := ResMod infl M) (locq q)).f n).hom x =
            ((resCochains (k := k) (M := M) (ψ q) ≫
              urCond (k := k) (M := M) hψ q).f n).hom x := by
        intro n x
        apply Subtype.ext
        funext y
        exact congrArg (asFun k GS M ((contSubCx k GS M).el x).1) (funext fun m => hψ q (y m))
      rw [zero_add]
      exact (natF_comp _ _ i a).symm.trans ((natF_congr _ _ key i a).trans (natF_comp _ _ i a))
  hι i j h u := by
    subst h
    refine Prod.ext ?_ ?_
    · rfl
    · funext q
      exact map_zero ((natHom (urCond (k := k) (M := M) hψ q)).f i i rfl)

end Setup

/-! ### Non-vacuity of the support-change hypotheses -/

section NonVacuity

variable (k)
  (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- **Non-vacuity of the hypotheses of `supportData`**: with `G_{S'} = G_S`, `infl = id`, the
same old places, and one new place `q` with `G_q = G_S`, `loc_q = id`, `G_q/I_q = G_S`,
`π_q = id`, `ψ_q = id`, both compatibilities hold, so the construction applies (to any local
conditions, e.g. `strictConditions`). PROVED. -/
def supportData_example (Δ : LocalConditions k GS Gv loc M) : SupportChangeData k :=
  supportData k GS GS (ContinuousMonoidHom.id GS) Gv loc loc (fun _ : PUnit.{u + 1} => GS)
    (fun _ => ContinuousMonoidHom.id GS) (fun _ => GS) (fun _ => ContinuousMonoidHom.id GS)
    (fun _ => ContinuousMonoidHom.id GS) M (fun _ _ => rfl) (fun _ _ => rfl) Δ

end NonVacuity

end ZInQ.Manuscript.RC.SelmerComplex
