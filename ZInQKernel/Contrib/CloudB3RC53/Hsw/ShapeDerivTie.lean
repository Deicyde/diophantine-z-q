import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeUrTieGen
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ConeFinite
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeCoords

/-!
# RC53 `hsw` shape: the tie for the switch of a derivative family

`derivSwitch F eR` (`GenuineInst/ConeFinite.lean`) is the genuine switch of a derivative family
`F`. Its relaxed and strict local conditions are subcomplexes of the genuine local complexes, and
its switch quotient is `W_rel = ⊕ rel/str`. This file supplies, for this switch, the tie of the
finite plane to the unramified classes. That tie, through `ShapeUrTie.lean` and
`ShapeUnramified.lean`, makes the finite plane isotropic for the residue form.

## Field-generic part

* `relSingle`, `relSingle_d`: a local `1`-cocycle at `q` as a relaxed cocycle supported at `q`.
* `derivSwitch_hrep`: the representatives of `hUrRep_of_vanish`, from two hypotheses. First,
  every local cocycle at `q` is relaxed (`hrelq`). Second, the coordinates `eR` send the classes of
  cocycles vanishing on `ker(urRes)` onto the finite plane (`hcoord`).
* `derivSwitch_switchCoordinates_char2`, `derivSwitch_switchCoordinates_of_two_ne_zero`:
  `SwitchCoordinates` for `derivSwitch F eR` over a field of characteristic two (polarized
  pairing), resp. with `2 ≠ 0` (`c`-symmetric pairing, `c² = 1`). Nondegeneracy (local Tate
  duality) is the only remaining input. `derivSwitch_switchCoordinates_of_two_ne_zero_ur`: the
  same for unramified, not necessarily trivial, actions at `q` (through a compatible `ψ`).

**Scope (residual case only).** All three theorems assume a finite target module `T`, which is
how `localSumPair_urAt` obtains `H²(Gal(K_q^ur/K_q), T) = 0`. Over a field of characteristic zero
a finite module is zero (a nonzero `t` would give an injection `a ↦ a • t` of the infinite field
into `T`), so these hypotheses force `T = 0`. The theorems therefore say nothing at the
characteristic-zero fibres, and no characteristic-zero claim is made. Two further facts bear on
this:
* at a single derivative prime with characteristic-zero coefficients the singular part vanishes
  (`q = ℓ² ≠ 1`), and the `2 + 2` switch shape exists only in the inner limit `ℓᵢ → −1`
  (tex L3298–3300, L5030–5032);
* the `𝔭`-adic coefficient modules there are neither finite nor discrete.

`genuine_finIso_of_ur_cd` (`ShapeUrTieGen.lean`) takes the `H²` vanishing as an explicit input.
It covers any discrete target for which that vanishing is available, but still not `𝔭`-adic
`V_P`.

## The tame instance over `𝔽₂`

The derivative coordinates `eRAt` (`SwitchInputs/DerivativeCoords.lean`) are specialised to `𝔽₂`.
They do not apply at the switching primes with characteristic-zero coefficient fields; for those,
`hcoord` stays an input of the field-generic theorems.

* `hrelq_of_relAt`: for a family switched at `q`.
* `hcoord_of_tame`: from `finite_side_iff`, `coordC_phiAt`, `coordAt_mk` and the bijectivity of
  the tame coordinates, given that inertia contains `ker(urRes)`.
* `derivSwitch_switchCoordinates_tame`: the combination.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.GenuineInst

section Generic

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  [DecidableEq (Places K S)] (F : DerivFamily (galLv (k := k) K S M)) (q : Places K S)
  (hrelq : ∀ z : (galLv (k := k) K S M q).X 1, (galLv (k := k) K S M q).d 1 2 rfl z = 0 →
    z ∈ (F.rel q).S 1)

/-- A local `1`-cocycle at `q`, as a relaxed `1`-cochain supported at `q`. -/
def relSingle (z : (galLv (k := k) K S M q).X 1) (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0) :
    F.Urel.X 1 :=
  Pi.single (M := fun v => ((F.rel v).S 1 : Type)) q ⟨z, hrelq z hz⟩

theorem relSingle_apply_ne (z : (galLv (k := k) K S M q).X 1)
    (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0) (v : Places K S) (hv : v ≠ q) :
    relSingle F q hrelq z hz v = 0 :=
  Pi.single_eq_of_ne hv _

theorem relSingle_apply_self (z : (galLv (k := k) K S M q).X 1)
    (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0) :
    (show ((F.rel q).S 1 : Type) from relSingle F q hrelq z hz q).1 = z :=
  congrArg Subtype.val (Pi.single_eq_same (M := fun v => ((F.rel v).S 1 : Type)) q _)

/-- `relSingle` is a relaxed cocycle. -/
theorem relSingle_d (z : (galLv (k := k) K S M q).X 1)
    (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0) :
    F.Urel.d 1 2 rfl (relSingle F q hrelq z hz) = 0 := by
  funext v
  by_cases hv : v = q
  · subst hv
    apply Subtype.ext
    change (galLv (k := k) K S M v).d 1 2 rfl
      (show ((F.rel v).S 1 : Type) from relSingle F v hrelq z hz v).1 = 0
    rw [relSingle_apply_self]
    exact hz
  · change (F.rel v).cx.d 1 2 rfl (relSingle F q hrelq z hz v) = 0
    rw [relSingle_apply_ne F q hrelq z hz v hv, map_zero]

/-- **The tie for the switch of a derivative family** (`PROVED`, any coefficient field). Suppose
the relaxed condition at `q` contains every local `1`-cocycle (`hrelq`). Suppose also that every
finite-plane vector is the class of such a cocycle, supported at `q`, that vanishes on
`ker(urRes)`: the finite side is the unramified condition, in the coordinates `eR`. Then the
representatives required by `hUrRep_of_vanish` exist for `derivSwitch F eR`. -/
theorem derivSwitch_hrep (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (hcoord : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (z : (galLv (k := k) K S M q).X 1) (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F eR).toQuasi (relSingle F q hrelq z hz)
            (relSingle_d F q hrelq z hz) = a) :
    ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : (derivSwitch F eR).toQuasi.D.U.X 1)
        (ht : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl t = 0),
        gClass (derivSwitch F eR).toQuasi t ht = a ∧
          (∀ v, v ≠ q → (derivSwitch F eR).toQuasi.D.ι.f 1 1 rfl t v = 0) ∧
          ∀ g, urRes K q.1 g = 1 →
            cFun ((derivSwitch F eR).toQuasi.D.ι.f 1 1 rfl t q) (fun _ => g) = 0 := by
  intro a ha
  obtain ⟨z, hz, hI, hza⟩ := hcoord a ha
  refine ⟨relSingle F q hrelq z hz, relSingle_d F q hrelq z hz, hza, fun v hv => ?_,
    fun g hg => ?_⟩
  · change (show ((F.rel v).S 1 : Type) from relSingle F q hrelq z hz v).1 = 0
    rw [relSingle_apply_ne F q hrelq z hz v hv]
    rfl
  · change cFun (show ((F.rel q).S 1 : Type) from relSingle F q hrelq z hz q).1 (fun _ => g) = 0
    rw [relSingle_apply_self]
    exact hI g hg

variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- **`SwitchCoordinates` for the switch of a derivative family in characteristic two**
(`PROVED` from the inputs; any coefficient field of characteristic two). Inputs:
* a polarized equivariant pairing (e.g. Weil on `𝔽₂²`);
* isotropy data;
* strict complexes vanishing in degree two;
* trivial action of `G_{K_q}` on `M` and `T`;
* the coordinates `eR` sending the finite side (local cocycles vanishing on inertia, at `q`) onto
  the finite plane.

Nondegeneracy of the residue form (local Tate duality) is the only remaining input. -/
theorem derivSwitch_switchCoordinates_char2 (h2 : (2 : k) = 0)
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (β γ : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x)
    (I : GaloisIsotropyData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hcoord : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (z : (galLv (k := k) K S M q).X 1) (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F eR).toQuasi (relSingle F q hrelq z hz)
            (relSingle_d F q hrelq z hz) = a)
    (hnd : ∀ t (ht : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F eR).toQuasi (piCx (derivSwitch F eR).US)
          (piMap (derivSwitch F eR).φ)
          (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr t u = 0) →
        gClass (derivSwitch F eR).toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ derivSwitch F eR with eR := (derivSwitch F eR).eR.trans Φ } :
        GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr ε (-(-1)) J :=
  genuine_switchCoordinates_char2_vanish h2 (derivSwitch F eR) β γ hβ hγ hpol I tr htr hUS2 hε
    hJ2 q htriv htrivT (derivSwitch_hrep F q hrelq eR hcoord) hnd

/-- **`SwitchCoordinates` for the switch of a derivative family when `2 ≠ 0`, finite target**
(`PROVED` from the inputs; a coefficient field with `2 ≠ 0` and a finite target module `T`, i.e.
the residual case). Scope: the section assumes `[Finite T]`, which is needed for the vanishing
of `H²(Gal(K_q^ur/K_q), T)` in `localSumPair_urAt`. Over a field of characteristic zero a finite
module is zero, so these hypotheses force `T = 0` there, and this theorem makes no
characteristic-zero claim. See also `genuine_finIso_of_ur_cd`, which takes the `H²` vanishing as
an input. Inputs:
* a `c`-symmetric equivariant self-pairing with `c² = 1` (`σ = −c`);
* isotropy data;
* strict complexes vanishing in degree two;
* trivial action of `G_{K_q}` on `M` and `T`;
* `hrelq`, `hcoord`: the coordinates `eR` send the finite side (cocycles vanishing on inertia,
  at `q`) onto the finite plane.

Nondegeneracy of the residue form (local Tate duality) is the only remaining input. -/
theorem derivSwitch_switchCoordinates_of_two_ne_zero (h2 : (2 : k) ≠ 0)
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (c : k) (hc : ∀ x y, β x y = c • β y x) (hc2 : c * c = 1)
    (I : GaloisIsotropyData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hcoord : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (z : (galLv (k := k) K S M q).X 1) (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F eR).toQuasi (relSingle F q hrelq z hz)
            (relSingle_d F q hrelq z hz) = a)
    (hnd : ∀ t (ht : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F eR).toQuasi (piCx (derivSwitch F eR).US)
          (piMap (derivSwitch F eR).φ)
          (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr t u = 0) →
        gClass (derivSwitch F eR).toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ derivSwitch F eR with eR := (derivSwitch F eR).eR.trans Φ } :
        GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr ε (-c) J :=
  genuine_switchCoordinates_of_localDuality (derivSwitch F eR) β hβ c hc I tr htr hUS2 hε hJ2
    (genuine_finIso_of_ur (derivSwitch F eR) β hβ c hc I tr htr hUS2 q 1 (urCompat_one q htriv)
      (urCompat_one_T q htrivT)
      (hUrRep_of_vanish (derivSwitch F eR) q htriv (derivSwitch_hrep F q hrelq eR hcoord)))
    hnd (Or.inl ⟨h2, hc2⟩)

/-- **The same, for unramified (not necessarily trivial) actions at `q`, finite target**
(`PROVED` from the inputs; a field with `2 ≠ 0` and finite `T`, i.e. the residual case). The
triviality of the action is replaced by a continuous `ψ : Gal(K_q^ur/K_q) → G_{K,S}` through which
the actions of `G_{K_q}` on `M` and `T` factor. The same scope restriction as for
`derivSwitch_switchCoordinates_of_two_ne_zero` applies: it is not a characteristic-zero
statement. -/
theorem derivSwitch_switchCoordinates_of_two_ne_zero_ur (h2 : (2 : k) ≠ 0)
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (c : k) (hc : ∀ x y, β x y = c • β y x) (hc2 : c * c = 1)
    (I : GaloisIsotropyData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ (derivSwitch F eR).ΔS
      (derivSwitch F eR).ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hψT : ∀ g (m : T), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hcoord : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (z : (galLv (k := k) K S M q).X 1) (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F eR).toQuasi (relSingle F q hrelq z hz)
            (relSingle_d F q hrelq z hz) = a)
    (hnd : ∀ t (ht : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F eR).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F eR).toQuasi (piCx (derivSwitch F eR).US)
          (piMap (derivSwitch F eR).φ)
          (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr t u = 0) →
        gClass (derivSwitch F eR).toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ derivSwitch F eR with eR := (derivSwitch F eR).eR.trans Φ } :
        GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR I) tr ε (-c) J :=
  genuine_switchCoordinates_of_localDuality (derivSwitch F eR) β hβ c hc I tr htr hUS2 hε hJ2
    (genuine_finIso_of_ur (derivSwitch F eR) β hβ c hc I tr htr hUS2 q ψ hψ hψT
      (hUrRep_of_vanish_gen (derivSwitch F eR) q ψ hψ (derivSwitch_hrep F q hrelq eR hcoord)))
    hnd (Or.inl ⟨h2, hc2⟩)

end Generic

/-! ### The tame instance over `𝔽₂` -/

section Tame

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [DecidableEq (Places K S)]
  (F : DerivFamily (galLv (k := ZMod 2) K S M)) {q : Places K S}
  (hR : RelAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) F.str F.rel q)

omit [DecidableEq (Places K S)] in
include hR in
/-- For a family switched at `q`, the relaxed condition at `q` contains every local cocycle. -/
theorem hrelq_of_relAt (z : (galLv (k := ZMod 2) K S M q).X 1)
    (hz : (galLv (k := ZMod 2) K S M q).d 1 2 rfl z = 0) : z ∈ (F.rel q).S 1 :=
  (hR.rel1 z).2 hz

/-- **The derivative coordinates send the finite side onto the finite plane, and the finite side is
unramified** (`PROVED`, from the tame coordinates at `q`). Take the coordinates
`eR = eRAt (Frobenius φ, tame generator σ)` of the switch of a family switched at `q`, and suppose
the inertia subgroup `I` contains `ker(urRes)`. Then every finite-plane vector is the class of a
local cocycle at `q` that vanishes on `ker(urRes)`. This is the hypothesis `hcoord` of
`derivSwitch_switchCoordinates_char2`. -/
theorem hcoord_of_tame (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (T : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I) :
    ∀ a, a ∈ finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) →
      ∃ (z : (galLv (k := ZMod 2) K S M q).X 1)
        (hz : (galLv (k := ZMod 2) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F (eRAt (derivHsr F) hR φ σ eM T)).toQuasi
            (relSingle F q (hrelq_of_relAt F hR) z hz)
            (relSingle_d F q (hrelq_of_relAt F hR) z hz) = a := by
  intro a ha
  obtain ⟨u, hu⟩ := (coordEquiv T eM).surjective a
  obtain ⟨zz, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have hcz : coordAt (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) q φ σ eM
      (zz : (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) M)).X 1) = a :=
    (coordAt_mk (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) (q := q) φ σ eM T zz).trans hu
  have hBF := (finite_side_iff (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) (q := q) φ σ eM T zz).2
    (hcz.symm ▸ ha)
  rw [mem_sideOfSet_BF] at hBF
  refine ⟨zz.1, zz.2, fun g hg => hBF g (hIur g hg), ?_⟩
  change coordC (derivHsr F) hR φ σ eM T.hφ T.hσ
    (phiAt (derivHsr F) hR (Submodule.Quotient.mk zz)) = a
  rw [coordC_phiAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M)]
  exact hcz

variable {T : Type} [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- **`SwitchCoordinates` for the switch of a family switched at `q`, with the tame coordinates**
(`PROVED` from the inputs; coefficients `𝔽₂`). Use the coordinates `eRAt` of the derivative
coordinates, a polarized equivariant pairing (e.g. the Weil pairing on trivial `𝔽₂²`), isotropy
data, strict complexes vanishing in degree two, and trivial action of `G_{K_q}` on `M` and `T`.
The finite plane is isotropic by the tie (`hcoord_of_tame`) and cohomological dimension one, and
the residue form is alternating. Nondegeneracy (local Tate duality) is the only remaining input. -/
theorem derivSwitch_switchCoordinates_tame (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (β γ : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0) {ε : ZMod 2} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hnd : ∀ t (ht : (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi
          (piCx (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).US)
          (piMap (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).φ)
          (galoisPairData K S (ZMod 2) β hβ (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
            (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso) tr t u = 0) →
        gClass (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc) with
          eR := (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).eR.trans Φ } :
        GenuineSwitch K S (ZMod 2) M).SwitchCoordinates
        (galoisPairData K S (ZMod 2) β hβ (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
          (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso) tr ε (-(-1)) J :=
  derivSwitch_switchCoordinates_char2 F q (hrelq_of_relAt F hR) (by decide)
    (eRAt (derivHsr F) hR φ σ eM Tc) β γ hβ hγ hpol Iso tr htr hUS2 hε hJ2 htriv htrivT
    (hcoord_of_tame F hR φ σ eM Tc hIur) hnd

end Tame

end ZInQ.Contrib.CloudB3RC53.Hsw
