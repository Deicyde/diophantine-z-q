import ZInQKernel.Contrib.CloudB3E2Norm.H20Ring

/-!
# The coefficient push (H20) on Selmer complexes: the semilinear push and `H20CoefficientPush`

Manuscript `diophantine_zq.tex`, tex 3203–3215 and 3262–3270 (the coefficient push (H20) and the
survival of the local conditions). For a ring homomorphism `φ : k₁ →+* k₂` (for the text,
`ℤ[Δ_f] → A_i`, `h20RingHom θ`), a **semilinear push of Selmer data** `SelPush φ D₁ D₂` is a
family of `φ`-semilinear maps on the global complex (degrees `0`, `1`), the local conditions
(degrees `0`, `1`) and the local complex (degrees `−1`, `0`) compatible with the differentials,
the restriction and the local condition maps: exactly what the degree-`0`/`1` part of the Selmer
cone `C^n = G^n ⊕ U^n ⊕ L^{n−1}` needs.

* `SelPush.push0`, `SelPush.push1` (definitions): the induced `φ`-semilinear maps on the Selmer
  cone in degrees `0`, `1`; `SelPush.push1_d` (PROVED): they commute with `d⁰`.
* `SelPush.restrict` (definition): the push of the primitive data `selRestrict D f` from a push of
  `D` and a push of the primitive condition compatible with `f`.
* **`h20CoefficientPush_of_selPush`** (PROVED): `H20CoefficientPush` holds for the pushed classes
  `z_R² = Φ¹(z_R¹)`, `z_P² = Φ¹_P(z_P¹)` and `e₂ = φ(e₁)`; with `hzR_of_H20` the norm identity
  holds at the target (`hzR_of_selPush`).
* Non-vacuity: `SelPush.id`, `nonVacuity_selPush`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)

/-- **A semilinear push of Selmer data in degrees `0`, `1`** (tex 3203–3215, 3262–3270).
Kind: definition (data with identities). -/
structure SelPush (D₁ : SelData k₁) (D₂ : SelData k₂) where
  /-- the global complex, degree `0` -/
  g0 : D₁.G.X 0 →ₛₗ[φ] D₂.G.X 0
  /-- the global complex, degree `1` -/
  g1 : D₁.G.X 1 →ₛₗ[φ] D₂.G.X 1
  /-- the local conditions, degree `0` -/
  u0 : D₁.U.X 0 →ₛₗ[φ] D₂.U.X 0
  /-- the local conditions, degree `1` -/
  u1 : D₁.U.X 1 →ₛₗ[φ] D₂.U.X 1
  /-- the local complex, degree `−1` -/
  lm : D₁.L.X (0 - 1) →ₛₗ[φ] D₂.L.X (0 - 1)
  /-- the local complex, degree `0` -/
  l0 : D₁.L.X (1 - 1) →ₛₗ[φ] D₂.L.X (1 - 1)
  /-- compatibility with the global differential -/
  hg : ∀ a, g1 (D₁.G.d 0 1 rfl a) = D₂.G.d 0 1 rfl (g0 a)
  /-- compatibility with the differential of the local conditions -/
  hu : ∀ u, u1 (D₁.U.d 0 1 rfl u) = D₂.U.d 0 1 rfl (u0 u)
  /-- compatibility with the restriction -/
  hres : ∀ a, l0 (D₁.res.f 0 (1 - 1) (by omega) a) = D₂.res.f 0 (1 - 1) (by omega) (g0 a)
  /-- compatibility with the local condition maps -/
  hι : ∀ u, l0 (D₁.ι.f 0 (1 - 1) (by omega) u) = D₂.ι.f 0 (1 - 1) (by omega) (u0 u)
  /-- compatibility with the local differential -/
  hL : ∀ x, l0 (D₁.L.d (0 - 1) (1 - 1) (by omega) x) = D₂.L.d (0 - 1) (1 - 1) (by omega) (lm x)

namespace SelPush

variable {φ} {D₁ : SelData k₁} {D₂ : SelData k₂} (P : SelPush φ D₁ D₂)

/-- **The push on the Selmer cone in degree `0`**: `(a, u, x) ↦ (g⁰ a, u⁰ u, l⁻¹ x)`.
Kind: definition. -/
def push0 : (selCx D₁).X 0 →ₛₗ[φ] (selCx D₂).X 0 where
  toFun c := ((P.g0 (c : selT D₁ 0).1, P.u0 (c : selT D₁ 0).2.1, P.lm (c : selT D₁ 0).2.2) :
    selT D₂ 0)
  map_add' _ _ := Prod.ext (map_add _ _ _) (Prod.ext (map_add _ _ _) (map_add _ _ _))
  map_smul' _ _ := Prod.ext (LinearMap.map_smulₛₗ _ _ _)
    (Prod.ext (LinearMap.map_smulₛₗ _ _ _) (LinearMap.map_smulₛₗ _ _ _))

/-- **The push on the Selmer cone in degree `1`**: `(a, u, x) ↦ (g¹ a, u¹ u, l⁰ x)`.
Kind: definition. -/
def push1 : (selCx D₁).X 1 →ₛₗ[φ] (selCx D₂).X 1 where
  toFun c := ((P.g1 (c : selT D₁ 1).1, P.u1 (c : selT D₁ 1).2.1, P.l0 (c : selT D₁ 1).2.2) :
    selT D₂ 1)
  map_add' _ _ := Prod.ext (map_add _ _ _) (Prod.ext (map_add _ _ _) (map_add _ _ _))
  map_smul' _ _ := Prod.ext (LinearMap.map_smulₛₗ _ _ _)
    (Prod.ext (LinearMap.map_smulₛₗ _ _ _) (LinearMap.map_smulₛₗ _ _ _))

/-- **The push commutes with `d⁰` of the Selmer cone** (PROVED). -/
theorem push1_d (b : (selCx D₁).X 0) :
    P.push1 ((selCx D₁).d 0 1 rfl b) = (selCx D₂).d 0 1 rfl (P.push0 b) := by
  obtain ⟨a, u, x⟩ := b
  change ((P.g1 (D₁.G.d 0 1 rfl a), P.u1 (D₁.U.d 0 1 rfl u),
      P.l0 (D₁.res.f 0 (1 - 1) (by omega) a - D₁.ι.f 0 (1 - 1) (by omega) u -
        D₁.L.d (0 - 1) (1 - 1) (by omega) x)) : selT D₂ 1) =
    ((D₂.G.d 0 1 rfl (P.g0 a), D₂.U.d 0 1 rfl (P.u0 u),
      D₂.res.f 0 (1 - 1) (by omega) (P.g0 a) - D₂.ι.f 0 (1 - 1) (by omega) (P.u0 u) -
        D₂.L.d (0 - 1) (1 - 1) (by omega) (P.lm x)) : selT D₂ 1)
  rw [map_sub, map_sub, P.hg, P.hu, P.hres, P.hι, P.hL]

/-- **The push of the primitive data** `selRestrict D f` (Kind: definition): from a push of `D` and
semilinear maps `u'⁰`, `u'¹` on the primitive condition compatible with its differential and with
`f`. -/
def restrict {U₁ : GCx k₁} {U₂ : GCx k₂} (f₁ : GHom U₁ D₁.U) (f₂ : GHom U₂ D₂.U)
    (v0 : U₁.X 0 →ₛₗ[φ] U₂.X 0) (v1 : U₁.X 1 →ₛₗ[φ] U₂.X 1)
    (hv : ∀ u, v1 (U₁.d 0 1 rfl u) = U₂.d 0 1 rfl (v0 u))
    (hf0 : ∀ u, P.u0 (f₁.f 0 0 rfl u) = f₂.f 0 0 rfl (v0 u)) :
    SelPush φ (selRestrict D₁ f₁) (selRestrict D₂ f₂) where
  g0 := P.g0
  g1 := P.g1
  u0 := v0
  u1 := v1
  lm := P.lm
  l0 := P.l0
  hg := P.hg
  hu := hv
  hres := P.hres
  hι u := by
    change P.l0 (D₁.ι.f 0 (1 - 1) (by omega) (f₁.f 0 0 rfl u)) =
      D₂.ι.f 0 (1 - 1) (by omega) (f₂.f 0 0 rfl (v0 u))
    rw [P.hι]
    exact congrArg (D₂.ι.f 0 (1 - 1) (by omega)) (hf0 u)
  hL := P.hL

/-- The global component of the push. Kind: PROVED. -/
theorem push1_fst (c : (selCx D₁).X 1) : ((P.push1 c : (selCx D₂).X 1) : selT D₂ 1).1 =
    P.g1 (c : selT D₁ 1).1 := rfl

end SelPush

/-- **`H20CoefficientPush` from a semilinear push of Selmer data** (PROVED; tex 3203–3215,
3262–3270, 3281–3290): with `z_R² = Φ¹(z_R¹)`, `z_P² = Φ¹_P(z_P¹)` and `e₂ = φ(e₁)`, for pushes
`P` of `D` and `P'` of the primitive data whose condition maps commute with `f` in degree one. -/
theorem h20CoefficientPush_of_selPush {D₁ : SelData k₁} {D₂ : SelData k₂}
    (P : SelPush φ D₁ D₂) {U₁ : GCx k₁} {U₂ : GCx k₂} (f₁ : GHom U₁ D₁.U) (f₂ : GHom U₂ D₂.U)
    (v0 : U₁.X 0 →ₛₗ[φ] U₂.X 0) (v1 : U₁.X 1 →ₛₗ[φ] U₂.X 1)
    (hv : ∀ u, v1 (U₁.d 0 1 rfl u) = U₂.d 0 1 rfl (v0 u))
    (hf0 : ∀ u, P.u0 (f₁.f 0 0 rfl u) = f₂.f 0 0 rfl (v0 u))
    (hf1 : ∀ u, P.u1 (f₁.f 1 1 rfl u) = f₂.f 1 1 rfl (v1 u))
    (zR₁ : (selCx D₁).X 1) (zP₁ : (selCx (selRestrict D₁ f₁)).X 1) (e₁ : k₁) :
    H20CoefficientPush D₁ f₁ zR₁ zP₁ e₁ D₂ f₂ (P.push1 zR₁)
      ((P.restrict f₁ f₂ v0 v1 hv hf0).push1 zP₁) (φ e₁) := by
  refine ⟨φ, P.push0, P.push1, rfl, P.push1_d, rfl, ?_⟩
  obtain ⟨a, u, x⟩ := zP₁
  exact Prod.ext rfl (Prod.ext (hf1 u) rfl)

/-- **The norm identity at the target of a semilinear push** (PROVED): from the identity
`z_R¹ = e₁ • i(z_P¹) + d b` at the source, `Φ¹(z_R¹) = φ(e₁) • i(Φ¹_P(z_P¹)) + d b'`. -/
theorem hzR_of_selPush {D₁ : SelData k₁} {D₂ : SelData k₂}
    (P : SelPush φ D₁ D₂) {U₁ : GCx k₁} {U₂ : GCx k₂} (f₁ : GHom U₁ D₁.U) (f₂ : GHom U₂ D₂.U)
    (v0 : U₁.X 0 →ₛₗ[φ] U₂.X 0) (v1 : U₁.X 1 →ₛₗ[φ] U₂.X 1)
    (hv : ∀ u, v1 (U₁.d 0 1 rfl u) = U₂.d 0 1 rfl (v0 u))
    (hf0 : ∀ u, P.u0 (f₁.f 0 0 rfl u) = f₂.f 0 0 rfl (v0 u))
    (hf1 : ∀ u, P.u1 (f₁.f 1 1 rfl u) = f₂.f 1 1 rfl (v1 u))
    (zR₁ : (selCx D₁).X 1) (zP₁ : (selCx (selRestrict D₁ f₁)).X 1) (e₁ : k₁)
    (h₁ : ∃ b, zR₁ = e₁ • (changeMap D₁ f₁).f 1 1 rfl zP₁ + (selCx D₁).d 0 1 rfl b) :
    ∃ b, P.push1 zR₁ = φ e₁ • (changeMap D₂ f₂).f 1 1 rfl
      ((P.restrict f₁ f₂ v0 v1 hv hf0).push1 zP₁) + (selCx D₂).d 0 1 rfl b :=
  hzR_of_H20 D₁ f₁ zR₁ zP₁ e₁ D₂ f₂ _ _ _ h₁
    (h20CoefficientPush_of_selPush φ P f₁ f₂ v0 v1 hv hf0 hf1 zR₁ zP₁ e₁)

/-! ### Non-vacuity -/

/-- **The identity push** of any Selmer data (`φ = id`). Kind: definition. -/
def SelPush.id (D : SelData k₁) : SelPush (RingHom.id k₁) D D where
  g0 := LinearMap.id
  g1 := LinearMap.id
  u0 := LinearMap.id
  u1 := LinearMap.id
  lm := LinearMap.id
  l0 := LinearMap.id
  hg _ := rfl
  hu _ := rfl
  hres _ := rfl
  hι _ := rfl
  hL _ := rfl

/-- **Non-vacuity of the hypotheses of `h20CoefficientPush_of_selPush`**: the identity push with
the identity on the primitive condition. Kind: PROVED. -/
theorem nonVacuity_selPush (D : SelData k₁) {U : GCx k₁} (f : GHom U D.U) (zR : (selCx D).X 1)
    (zP : (selCx (selRestrict D f)).X 1) (e : k₁) :
    H20CoefficientPush D f zR zP e D f ((SelPush.id D).push1 zR)
      (((SelPush.id D).restrict f f LinearMap.id LinearMap.id (fun _ => rfl)
        (fun _ => rfl)).push1 zP) e :=
  h20CoefficientPush_of_selPush (RingHom.id k₁) (SelPush.id D) f f LinearMap.id LinearMap.id
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) zR zP e

end ZInQ.Contrib.CloudB3E2.NormCochain
