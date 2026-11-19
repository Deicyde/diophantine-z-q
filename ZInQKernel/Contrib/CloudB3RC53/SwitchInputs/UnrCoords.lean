import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericNonVacuity

/-!
# RC53 SwitchInputs: unramified tame coordinates `H¹ ≅ M/(Φ−1)M × ker(Φ − q)`

Manuscript `diophantine_zq.tex`, tex L3298–3306, L5026–5037 (the coordinates of `H¹(W_rel)` at an
inert derivative prime from the tame quotient `⟨φ, σ | φσφ⁻¹ = σ^q⟩`) and the side conditions of tex
L5060–5082.

`TameCoordinatesTrivialK` (`GenericSides.lean`) asks the whole group to act trivially, and in
characteristic zero it is then refuted by `not_tameCoordinatesTrivialK_of_tame`
(`GenericNonVacuity.lean`). This file replaces it by the coordinates of an *unramified* module:
inertia acts trivially, the Frobenius lift `φ` acts by `Φ`, and the coordinates are
`[z] ↦ (z(φ) mod (Φ − 1)M, z(σ))` with values in `M/(Φ−1)M × ker(Φ − q)`.

Nodes:
* `ev1K_one_unr`, `ev1K_inv_unr`, `ev1K_pow_unr`, `ev1K_zpow_eq_zero`, `mem_Z1K_of_cocycle`
  (PROVED): the cocycle identity `z(gh) = z(g) + g • z(h)` and its consequences.
* `ev1K_sigma_mem_ker` (PROVED): if `σ` acts trivially and `φσφ⁻¹ = σ^q`, then
  `z(σ) ∈ ker(Φ − q)` for every `1`-cocycle `z`.
* `coordLUnr_relaxedD` (PROVED): a coboundary `d⁰a` has coordinates `((Φ−1)a mod, 0) = 0`; so
  `coordQUnr : H1WrelK → M/(Φ−1)M × ker(Φ − q)` is well defined.
* `TameCoordinatesUnr k M I φ σ q` (GLUE): inertia acts trivially, `σ ∈ I`, `φσφ⁻¹ = σ^q`,
  `coordQUnr` is bijective, and a cocycle with `z(σ) = 0` vanishes on `I`.
* `coordEquivUnr` (PROVED from the GLUE input): `H1WrelK ≃ M/(Φ−1)M × ker(Φ − q)`, under which the
  finite side is `coker × 0` (`finite_side_imageUnr`; at cocycle level `finite_side_iffUnr`)
  and the singular side is `0 × ker` (`singular_side_imageUnr`; only up to coboundaries when
  `Φ ≠ 1`).
* Dimension bookkeeping (PROVED): `finrank_H1WrelK_of_q_ne_one`, `finrank_H1WrelK_of_q_eq_one`,
  `singular_zero_of_q_ne_one`, `two_plus_two_iff_q_eq_one`, `no_k2k2_coords_of_q_ne_one`,
  `two_plus_two_iff_ell`, `h1_trivial_of_eigen`.
* Non-vacuity (PROVED): `tameCoordinatesUnr_J` (`Φ = diag(1, −1)` nontrivial, `q = 2`, over the
  discrete group `ℤ`); `tameCoordinatesUnr_derivative`, `derivative_example_two_plus_zero`
  (`Φ = 1`, `q = 2`: `dim H¹ = 2 + 0`, no `ℚ² × ℚ²`); and `tameCoordinatesUnr_q_one`,
  `two_plus_two_q_one` (`Φ = 1`, `q = 1`, recovering `2 + 2`).

**Finding (dimension count at the derivative prime).** At an inert derivative prime the text
uses `Φ = J² = 1` and `q = ℓ²` (tex L3298–3300). Then `M/(Φ−1)M = M` has dimension `2` and
`ker(Φ − q) = 0` as soon as `(q : k) ≠ 1`, so `H¹(W_rel)` has dimension `2 + 0`, not `2 + 2`
(`finrank_H1WrelK_of_q_ne_one`, `singular_zero_of_q_ne_one`). The `2 + 2` count holds iff
`(q : k) = 1` (`two_plus_two_iff_q_eq_one`); in characteristic zero with `q = ℓ²` this means `ℓ = 1`
(`two_plus_two_iff_ell`), which no prime satisfies. So `QuasiNonquadStep`, (5.5a) and
`RelaxedImageFinite`, which take `finPlane`/`singPlane` inside `(Fin 2 → k) × (Fin 2 → k)`, can only
be fed from these coordinates where `ℓ² ≡ 1` in `k` (e.g. `k = 𝔽₂` with `ℓ` odd), i.e. in the text's
limit `ℓ → −1` (2-adically), not at a fixed characteristic-zero fibre.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Uniform Module

section Unr

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-! ### The cocycle identity and its consequences -/

/-- `z(1) = 0` for a `1`-cocycle. PROVED. -/
theorem ev1K_one_unr (z : Z1K k G M) : ev1K (z : (contCochains k G M).X 1) 1 = 0 := by
  have h := ev1K_mul z 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

/-- `z(g⁻¹) = −g⁻¹ • z(g)` for a `1`-cocycle. PROVED. -/
theorem ev1K_inv_unr (z : Z1K k G M) (g : G) :
    ev1K (z : (contCochains k G M).X 1) g⁻¹ = -(g⁻¹ • ev1K (z : (contCochains k G M).X 1) g) := by
  have h := ev1K_mul z g⁻¹ g
  rw [inv_mul_cancel, ev1K_one_unr] at h
  exact eq_neg_of_add_eq_zero_left h.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousSMul G M] in
/-- `σⁿ` acts trivially when `σ` does. -/
theorem pow_smul_of_fix {σ : G} (hσ : ∀ m : M, σ • m = m) (n : ℕ) (m : M) : σ ^ n • m = m := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ, mul_smul, hσ, ih]

/-- `z(σⁿ) = n • z(σ)` when `σ` acts trivially. PROVED. -/
theorem ev1K_pow_unr {σ : G} (hσ : ∀ m : M, σ • m = m) (z : Z1K k G M) (n : ℕ) :
    ev1K (z : (contCochains k G M).X 1) (σ ^ n) = n • ev1K (z : (contCochains k G M).X 1) σ := by
  induction n with
  | zero => rw [pow_zero, ev1K_one_unr, zero_smul]
  | succ n ih => rw [pow_succ, ev1K_mul, pow_smul_of_fix hσ, ih, succ_nsmul]

/-- A `1`-cocycle vanishing at `φ` vanishes on `⟨φ⟩`. PROVED. -/
theorem ev1K_zpow_eq_zero {φ : G} (z : Z1K k G M) (hz : ev1K (z : (contCochains k G M).X 1) φ = 0)
    (n : ℤ) : ev1K (z : (contCochains k G M).X 1) (φ ^ n) = 0 := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [zpow_zero, ev1K_one_unr]
  · intro i ih
    rw [zpow_add_one, ev1K_mul, ih, hz, smul_zero, add_zero]
  · intro i ih
    have h := ev1K_mul z (φ ^ (-(i : ℤ) - 1)) φ
    rw [← zpow_add_one, sub_add_cancel, ih, hz, smul_zero, add_zero] at h
    exact h.symm

/-- A `1`-cocycle vanishing everywhere is zero. PROVED. -/
theorem Z1K_eq_zero_of_ev (z : Z1K k G M) (h : ∀ g, ev1K (z : (contCochains k G M).X 1) g = 0) :
    z = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : x = fun _ => x 0 := by funext i; fin_cases i; rfl
  rw [hx]
  change ev1K (z : (contCochains k G M).X 1) (x 0) = 0
  exact h (x 0)

/-- A `1`-cochain satisfying the cocycle identity `c(gh) = c(g) + g • c(h)` is a cocycle (for any
action). PROVED. -/
theorem mem_Z1K_of_cocycle (c : (contCochains k G M).X 1)
    (hc : ∀ g h : G, ev1K c (g * h) = ev1K c g + g • ev1K c h) : c ∈ Z1K k G M := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext g
  have hd := contCochains_d_apply (k := k) (G := G) (M := M) 1 c g
  refine hd.trans ?_
  have e0 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) g = fun _ => g 0 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2]
  change g 0 • ev1K c (g 1) + ((-1 : k) ^ ((0 : ℕ) + 1) • ev1K c (g 0 * g 1) +
    (-1 : k) ^ ((1 : ℕ) + 1) • ev1K c (g 0)) = (0 : M)
  rw [hc, show ((-1 : k) ^ ((0 : ℕ) + 1)) = -1 by norm_num,
    show ((-1 : k) ^ ((1 : ℕ) + 1)) = 1 by norm_num, neg_smul, one_smul, one_smul]
  abel

/-- The constant `0`-cochain with value `m`. -/
def const0K (m : M) : (contCochains k G M).X 0 :=
  ⟨(fun _ => m : (groupCohomology.inhomogeneousCochains (rep k G M)).X 0),
    mem_contCochain.mpr continuous_const⟩

theorem ev0K_const0K (m : M) : ev0K (const0K (k := k) (G := G) m) = m := rfl

/-! ### `Φ − c`, the cokernel of `Φ − 1` and the kernel of `Φ − q` -/

variable (k M) in
/-- `Φ − c` on `M`, where `Φ = φ •` (the Frobenius lift acting on `M`). -/
def frobSub (φ : G) (c : k) : M →ₗ[k] M := DistribSMul.toLinearMap k M φ - c • LinearMap.id

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
theorem frobSub_apply (φ : G) (c : k) (m : M) : frobSub k M φ c m = φ • m - c • m := rfl

variable (k M) in
/-- `M/(Φ − 1)M`, the target of the finite (unramified) coordinate. -/
abbrev CokerFrob (φ : G) : Type := M ⧸ LinearMap.range (frobSub k M φ 1)

variable (k M) in
/-- `ker(Φ − q)`, the target of the singular (tame) coordinate. -/
abbrev KerFrob (φ : G) (q : ℕ) : Submodule k M := LinearMap.ker (frobSub k M φ (q : k))

/-- **`z(σ) ∈ ker(Φ − q)`** (tex L3298–3306, L5026–5037): if `σ` acts trivially and `φσφ⁻¹ = σ^q`,
then `z(φσφ⁻¹) = z(φ) + φ • z(σ) − (φσφ⁻¹) • z(φ) = φ • z(σ)` and `z(σ^q) = q • z(σ)`. PROVED. -/
theorem ev1K_sigma_mem_ker {φ σ : G} (hσ : ∀ m : M, σ • m = m) (q : ℕ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (z : Z1K k G M) :
    ev1K (z : (contCochains k G M).X 1) σ ∈ KerFrob k M φ q := by
  have hconj : ev1K (z : (contCochains k G M).X 1) (φ * σ * φ⁻¹) =
      φ • ev1K (z : (contCochains k G M).X 1) σ := by
    rw [ev1K_mul, ev1K_mul, ev1K_inv_unr, smul_neg, ← mul_smul, hrel, pow_smul_of_fix hσ]
    abel
  rw [hrel, ev1K_pow_unr hσ, ← Nat.cast_smul_eq_nsmul k] at hconj
  rw [LinearMap.mem_ker, frobSub_apply, ← hconj, sub_self]

/-! ### The coordinate map `[z] ↦ (z(φ) mod (Φ−1)M, z(σ))` -/

/-- The coordinates `z ↦ (z(φ) mod (Φ − 1)M, z(σ))` on `1`-cocycles. -/
def coordLUnr (φ σ : G) (q : ℕ) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    Z1K k G M →ₗ[k] CokerFrob k M φ × KerFrob k M φ q :=
  ((LinearMap.range (frobSub k M φ 1)).mkQ ∘ₗ ev1LK φ ∘ₗ (Z1K k G M).subtype).prod
    (LinearMap.codRestrict (KerFrob k M φ q) (ev1LK σ ∘ₗ (Z1K k G M).subtype)
      fun z => ev1K_sigma_mem_ker hσ q hrel z)

/-- **Coboundaries have zero coordinates** (tex L3298–3306, L5026–5037): `(d⁰a)(φ) = (Φ − 1)a` is
zero in `M/(Φ − 1)M`, and `(d⁰a)(σ) = σ • a − a = 0`. PROVED. -/
theorem coordLUnr_relaxedD (φ σ : G) (q : ℕ) (hσ : ∀ m : M, σ • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (a : (contCochains k G M).X 0) :
    coordLUnr φ σ q hσ hrel (relaxedDK k G M a) = 0 := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · change (Submodule.Quotient.mk
      (ev1K ((relaxedDK k G M a : Z1K k G M) : (contCochains k G M).X 1) φ) : CokerFrob k M φ) = 0
    rw [Submodule.Quotient.mk_eq_zero, relaxedDK_ev]
    exact ⟨ev0K a, by rw [frobSub_apply, one_smul]⟩
  · change ev1K ((relaxedDK k G M a : Z1K k G M) : (contCochains k G M).X 1) σ = 0
    rw [relaxedDK_ev, hσ, sub_self]

/-- The coordinates on `H¹(W_rel) = Z¹ ⧸ d⁰C⁰`: `[z] ↦ (z(φ) mod (Φ − 1)M, z(σ))`. -/
def coordQUnr (φ σ : G) (q : ℕ) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    H1WrelK k G M →ₗ[k] CokerFrob k M φ × KerFrob k M φ q :=
  (LinearMap.range (relaxedDK k G M)).liftQ (coordLUnr φ σ q hσ hrel) (by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (coordLUnr_relaxedD φ σ q hσ hrel a))

theorem coordQUnr_mk (φ σ : G) (q : ℕ) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (z : Z1K k G M) :
    coordQUnr φ σ q hσ hrel (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ),
        ⟨ev1K (z : (contCochains k G M).X 1) σ, ev1K_sigma_mem_ker hσ q hrel z⟩) :=
  rfl

variable (k M) in
/-- **GLUE: the unramified tame coordinates** (tex L3298–3306, L5026–5037). The inertia subgroup `I`
acts trivially on `M` (`M` unramified), `σ ∈ I`, the tame relation `φσφ⁻¹ = σ^q` holds in `G`, the
coordinate map `[z] ↦ (z(φ) mod (Φ − 1)M, z(σ))` is a bijection
`H¹(W_rel) ≅ M/(Φ − 1)M × ker(Φ − q)`, and a cocycle with `z(σ) = 0` vanishes on `I`. This is the
inflation–restriction computation of `H¹` of the tame quotient `⟨φ, σ | φσφ⁻¹ = σ^q⟩` with
coefficients in an unramified module (wild inertia pro-`p`, `I/P` procyclic); the well-definedness
and the values of the coordinates are PROVED (`coordLUnr_relaxedD`, `ev1K_sigma_mem_ker`). Unlike
`TameCoordinatesTrivialK`, `φ` may act nontrivially. Classification: GLUE. -/
structure TameCoordinatesUnr (I : Subgroup G) (φ σ : G) (q : ℕ) : Prop where
  hItriv : ∀ h ∈ I, ∀ m : M, h • m = m
  hσI : σ ∈ I
  hrel : φ * σ * φ⁻¹ = σ ^ q
  hbij : Function.Bijective (coordQUnr (k := k) (M := M) φ σ q (hItriv σ hσI) hrel)
  hI : ∀ z : Z1K k G M, ev1K (z : (contCochains k G M).X 1) σ = 0 →
    ∀ h ∈ I, ev1K (z : (contCochains k G M).X 1) h = 0

variable {I : Subgroup G} {φ σ : G} {q : ℕ}

/-- **The coordinates** `H¹(W_rel) ≃ M/(Φ − 1)M × ker(Φ − q)` (tex L3298–3306, L5026–5037). PROVED
from the GLUE input. -/
def coordEquivUnr (T : TameCoordinatesUnr k M I φ σ q) :
    H1WrelK k G M ≃ₗ[k] CokerFrob k M φ × KerFrob k M φ q :=
  LinearEquiv.ofBijective _ T.hbij

theorem coordEquivUnr_mk (T : TameCoordinatesUnr k M I φ σ q) (z : Z1K k G M) :
    coordEquivUnr T (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ),
        ⟨ev1K (z : (contCochains k G M).X 1) σ,
          ev1K_sigma_mem_ker (T.hItriv σ T.hσI) q T.hrel z⟩) :=
  rfl

/-! ### The sides in the coordinates -/

/-- **The finite side at cocycle level** (tex L5026–5037, L5060–5061): `z(h) = 0` on `I` iff the
class of `z` lies in `finPlane = coker(Φ − 1) × 0`. PROVED. -/
theorem finite_side_iffUnr (T : TameCoordinatesUnr k M I φ σ q) (z : Z1K k G M) :
    z ∈ (sideOfSetK k M (I : Set G)).BF ↔
      coordEquivUnr T (Submodule.Quotient.mk z) ∈
        finPlane k (CokerFrob k M φ) (KerFrob k M φ q) := by
  rw [mem_sideOfSetK_BF, mem_finPlane, coordEquivUnr_mk]
  constructor
  · intro h
    exact Subtype.ext (h σ T.hσI)
  · intro h g hg
    exact T.hI z (congrArg Subtype.val h) g hg

/-- **The finite side is `coker(Φ − 1) × 0`** (tex L5026–5027, L5060–5061): the image of the finite
side in `H¹(W_rel)`, transported by `coordEquivUnr`, is `finPlane`. PROVED. -/
theorem finite_side_imageUnr (T : TameCoordinatesUnr k M I φ σ q) :
    ((sideOfSetK k M (I : Set G)).BF.map (LinearMap.range (relaxedDK k G M)).mkQ).map
      (coordEquivUnr T).toLinearMap = finPlane k (CokerFrob k M φ) (KerFrob k M φ q) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact (finite_side_iffUnr T z).mp hz
  · intro hx
    obtain ⟨y, rfl⟩ := (coordEquivUnr T).surjective x
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      exact Submodule.mem_map.mpr ⟨Submodule.Quotient.mk z,
        Submodule.mem_map.mpr ⟨z, (finite_side_iffUnr T z).mpr hx, rfl⟩, rfl⟩

/-- A cocycle of the singular side has first coordinate `0`. PROVED. -/
theorem singular_side_fstUnr (T : TameCoordinatesUnr k M I φ σ q) (z : Z1K k G M)
    (hz : z ∈ (sideOfSetK k M ({φ} : Set G)).BF) :
    coordEquivUnr T (Submodule.Quotient.mk z) ∈
      singPlane k (CokerFrob k M φ) (KerFrob k M φ q) := by
  rw [mem_singPlane, coordEquivUnr_mk]
  change (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ) : CokerFrob k M φ) = 0
  rw [(mem_sideOfSetK_BF _ z).mp hz φ (Set.mem_singleton φ), Submodule.Quotient.mk_zero]

/-- **The singular side is `0 × ker(Φ − q)`** (tex L5073–5083): the image of the singular side
`{z | z(φ) = 0}` in `H¹(W_rel)`, transported by `coordEquivUnr`, is `singPlane`. When `Φ ≠ 1`
this holds only up to coboundaries (a cocycle with `z(φ) ∈ (Φ − 1)M` is cohomologous to one with
`z(φ) = 0`, via `d⁰` of a constant). PROVED. -/
theorem singular_side_imageUnr (T : TameCoordinatesUnr k M I φ σ q) :
    ((sideOfSetK k M ({φ} : Set G)).BF.map (LinearMap.range (relaxedDK k G M)).mkQ).map
      (coordEquivUnr T).toLinearMap = singPlane k (CokerFrob k M φ) (KerFrob k M φ q) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact singular_side_fstUnr T z hz
  · intro hx
    obtain ⟨y, rfl⟩ := (coordEquivUnr T).surjective x
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [mem_singPlane, coordEquivUnr_mk] at hx
      change (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ) :
        CokerFrob k M φ) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨m, hm⟩ := hx
      refine Submodule.mem_map.mpr ⟨Submodule.Quotient.mk (z - relaxedDK k G M (const0K m)),
        Submodule.mem_map.mpr ⟨z - relaxedDK k G M (const0K m), ?_, rfl⟩, ?_⟩
      · rw [mem_sideOfSetK_BF]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        change ev1K (z : (contCochains k G M).X 1) φ -
          ev1K ((relaxedDK k G M (const0K m) : Z1K k G M) : (contCochains k G M).X 1) φ = 0
        rw [relaxedDK_ev, ev0K_const0K, ← hm, frobSub_apply, one_smul, sub_self]
      · change coordEquivUnr T (Submodule.Quotient.mk (z - relaxedDK k G M (const0K m))) =
          coordEquivUnr T (Submodule.Quotient.mk z)
        rw [Submodule.Quotient.mk_sub,
          (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _), sub_zero]

/-! ### Dimension bookkeeping -/

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- With `φ` acting trivially, `Φ − c = (1 − c)`. -/
theorem frobSub_of_fix (hφ : ∀ m : M, φ • m = m) (c : k) (m : M) :
    frobSub k M φ c m = (1 - c) • m := by
  rw [frobSub_apply, hφ, sub_smul, one_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- With `Φ = 1`, `(Φ − 1)M = 0`. PROVED. -/
theorem range_frobSub_one_eq_bot (hφ : ∀ m : M, φ • m = m) :
    LinearMap.range (frobSub k M φ 1) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  ext m
  rw [frobSub_of_fix hφ, sub_self, zero_smul, LinearMap.zero_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- With `Φ = 1` and `(q : k) ≠ 1`, `ker(Φ − q) = 0`. PROVED. -/
theorem kerFrob_eq_bot_of_q_ne_one (hφ : ∀ m : M, φ • m = m) (hq : (q : k) ≠ 1) :
    KerFrob k M φ q = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  have h := LinearMap.mem_ker.mp hm
  rw [frobSub_of_fix hφ] at h
  exact (Submodule.mem_bot k).mpr ((smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hq.symm))

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- With `Φ = 1` and `(q : k) = 1`, `ker(Φ − q) = M`. PROVED. -/
theorem kerFrob_eq_top_of_q_eq_one (hφ : ∀ m : M, φ • m = m) (hq : (q : k) = 1) :
    KerFrob k M φ q = ⊤ := by
  rw [eq_top_iff]
  intro m _
  exact LinearMap.mem_ker.mpr (by rw [frobSub_of_fix hφ, hq, sub_self, zero_smul])

omit [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] in
/-- A submodule equal to `⊥` has only the zero element. -/
theorem subtype_eq_zero_of_eq_bot {p : Submodule k M} (hp : p = ⊥) (v : p) : v = 0 := by
  subst hp
  exact Subsingleton.elim _ _

/-- **The dimension of `H¹(W_rel)` at a derivative prime, `(q : k) ≠ 1`** (tex L3298–3306,
L5026–5037, with `Φ = J² = 1`): `dim H¹ = dim M + 0`. PROVED. -/
theorem finrank_H1WrelK_of_q_ne_one [FiniteDimensional k M] (T : TameCoordinatesUnr k M I φ σ q)
    (hφ : ∀ m : M, φ • m = m) (hq : (q : k) ≠ 1) :
    finrank k (H1WrelK k G M) = finrank k M + 0 := by
  rw [(coordEquivUnr T).finrank_eq, Module.finrank_prod,
    (Submodule.quotEquivOfEqBot _ (range_frobSub_one_eq_bot hφ)).finrank_eq,
    (LinearEquiv.ofEq _ _ (kerFrob_eq_bot_of_q_ne_one hφ hq)).finrank_eq, finrank_bot k M]

/-- **The dimension of `H¹(W_rel)` at a derivative prime, `(q : k) = 1`** (tex L3298–3306,
L5026–5037, with `Φ = J² = 1`): `dim H¹ = dim M + dim M`. PROVED. -/
theorem finrank_H1WrelK_of_q_eq_one [FiniteDimensional k M] (T : TameCoordinatesUnr k M I φ σ q)
    (hφ : ∀ m : M, φ • m = m) (hq : (q : k) = 1) :
    finrank k (H1WrelK k G M) = finrank k M + finrank k M := by
  rw [(coordEquivUnr T).finrank_eq, Module.finrank_prod,
    (Submodule.quotEquivOfEqBot _ (range_frobSub_one_eq_bot hφ)).finrank_eq,
    (LinearEquiv.ofEq _ _ (kerFrob_eq_top_of_q_eq_one hφ hq)).finrank_eq, finrank_top k M]

/-- **Finding: the singular plane is zero when `(q : k) ≠ 1`** (tex L3298–3306, L5026–5037,
L5073–5083). With `Φ = 1` (the derivative prime, `Φ = J² = 1`) and `(q : k) ≠ 1` (e.g. `q = ℓ²` in
characteristic zero), every `1`-cocycle has `z(σ) = 0`, and the singular side has zero image in
`H¹(W_rel)`. PROVED. -/
theorem singular_zero_of_q_ne_one (T : TameCoordinatesUnr k M I φ σ q)
    (hφ : ∀ m : M, φ • m = m) (hq : (q : k) ≠ 1) :
    (∀ z : Z1K k G M, ev1K (z : (contCochains k G M).X 1) σ = 0) ∧
      (sideOfSetK k M ({φ} : Set G)).BF.map (LinearMap.range (relaxedDK k G M)).mkQ = ⊥ := by
  have h1 : ∀ z : Z1K k G M, ev1K (z : (contCochains k G M).X 1) σ = 0 := fun z => by
    have h := ev1K_sigma_mem_ker (T.hItriv σ T.hσI) q T.hrel z
    rw [kerFrob_eq_bot_of_q_ne_one hφ hq] at h
    exact (Submodule.mem_bot k).mp h
  refine ⟨h1, ?_⟩
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [Submodule.mem_bot]
  apply (coordEquivUnr T).injective
  rw [map_zero]
  change coordEquivUnr T (Submodule.Quotient.mk z) = 0
  rw [coordEquivUnr_mk]
  refine Prod.ext ?_ (Subtype.ext (h1 z))
  change (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ) : CokerFrob k M φ) = 0
  rw [(mem_sideOfSetK_BF _ z).mp hz φ (Set.mem_singleton φ), Submodule.Quotient.mk_zero]

/-- **Finding: `2 + 2` iff `(q : k) = 1`** (tex L3298–3306, L5026–5037). With `Φ = 1` and
`dim M = 2`, `H¹(W_rel) ≃ k² × k²` (the shape `finPlane`/`singPlane` in `(Fin 2 → k) × (Fin 2 → k)`
asked for by `QuasiNonquadStep`, (5.5a) and `RelaxedImageFinite`) iff `(q : k) = 1`. PROVED. -/
theorem two_plus_two_iff_q_eq_one [FiniteDimensional k M] (T : TameCoordinatesUnr k M I φ σ q)
    (hφ : ∀ m : M, φ • m = m) (hM : finrank k M = 2) :
    Nonempty (H1WrelK k G M ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) ↔ (q : k) = 1 := by
  have h4 : finrank k ((Fin 2 → k) × (Fin 2 → k)) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  have : FiniteDimensional k (H1WrelK k G M) :=
    LinearEquiv.finiteDimensional (coordEquivUnr T).symm
  constructor
  · rintro ⟨e⟩
    by_contra h
    have hfin := finrank_H1WrelK_of_q_ne_one T hφ h
    rw [hM, e.finrank_eq, h4] at hfin
    omega
  · intro h
    have hfin := finrank_H1WrelK_of_q_eq_one T hφ h
    rw [hM] at hfin
    exact ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hfin, h4])⟩

/-- **No `k² × k²` coordinates when `(q : k) ≠ 1`** (tex L3298–3306, L5026–5037). PROVED. -/
theorem no_k2k2_coords_of_q_ne_one [FiniteDimensional k M] (T : TameCoordinatesUnr k M I φ σ q)
    (hφ : ∀ m : M, φ • m = m) (hM : finrank k M = 2) (hq : (q : k) ≠ 1) :
    ¬ Nonempty (H1WrelK k G M ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) :=
  fun h => hq ((two_plus_two_iff_q_eq_one T hφ hM).mp h)

/-- **Finding: in characteristic zero, `2 + 2` at `q = ℓ²` iff `ℓ = 1`** (tex L3298–3300,
L5030–5032). So no prime `ℓ` gives the `2 + 2` count at a characteristic-zero fibre; it is the
text's limit `ℓ → −1` (where `ℓ² → 1`). PROVED. -/
theorem two_plus_two_iff_ell [CharZero k] [FiniteDimensional k M] {ℓ : ℕ}
    (T : TameCoordinatesUnr k M I φ σ (ℓ ^ 2)) (hφ : ∀ m : M, φ • m = m)
    (hM : finrank k M = 2) :
    Nonempty (H1WrelK k G M ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) ↔ ℓ = 1 := by
  rw [two_plus_two_iff_q_eq_one T hφ hM, Nat.cast_eq_one]
  constructor
  · intro h
    exact Nat.pow_left_injective two_ne_zero (h.trans (one_pow 2).symm)
  · rintro rfl
    rfl

/-- **`H¹(W_rel) = 0` when `Φ − 1` is onto and `Φ − q` is injective** (tex L3298–3306, L5026–5037):
e.g. at a good inert prime in characteristic zero, where by the Weil bounds neither `1` nor `q` is
an eigenvalue of Frobenius. PROVED. -/
theorem h1_trivial_of_eigen (T : TameCoordinatesUnr k M I φ σ q)
    (hsurj : LinearMap.range (frobSub k M φ 1) = ⊤) (hinj : KerFrob k M φ q = ⊥)
    (x : H1WrelK k G M) : x = 0 := by
  apply (coordEquivUnr T).injective
  rw [map_zero]
  refine Prod.ext ?_ (subtype_eq_zero_of_eq_bot hinj _)
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ ((coordEquivUnr T x).1)
  rw [← hm, Prod.fst_zero, Submodule.Quotient.mk_eq_zero, hsurj]
  exact Submodule.mem_top

/-- **From the trivial-action coordinates to the unramified ones** (`q = 1`): with `G` acting
trivially, `M/(Φ − 1)M = M` and `ker(Φ − 1) = M`, and `coordQUnr` is `coordQK` up to these
identifications. PROVED. -/
theorem TameCoordinatesTrivialK.toUnr (T : TameCoordinatesTrivialK k M I φ σ)
    (hrel : φ * σ * φ⁻¹ = σ ^ 1) : TameCoordinatesUnr k M I φ σ 1 where
  hItriv h _ m := T.htriv h m
  hσI := T.hσI
  hrel := hrel
  hbij := by
    have hb := range_frobSub_one_eq_bot (k := k) (T.htriv φ)
    have ht := kerFrob_eq_top_of_q_eq_one (k := k) (q := 1) (T.htriv φ) Nat.cast_one
    let e : (M × M) ≃ₗ[k] CokerFrob k M φ × KerFrob k M φ 1 :=
      LinearEquiv.prodCongr (Submodule.quotEquivOfEqBot _ hb).symm (LinearEquiv.ofTop _ ht).symm
    have he : ⇑(coordQUnr (k := k) (M := M) φ σ 1 (T.htriv σ) hrel) =
        ⇑e ∘ ⇑(coordQK (k := k) (M := M) φ σ (T.htriv φ) (T.htriv σ)) := by
      funext y
      induction y using Submodule.Quotient.induction_on with
      | H z => rfl
    have hbij := e.bijective.comp T.hbij
    rw [← he] at hbij
    exact hbij
  hI := T.hI

end Unr

/-! ### Non-vacuity -/

section Example

/-- The discrete group `ℤ`, written multiplicatively. -/
abbrev GZ : Type := Multiplicative ℤ

/-- The generator `φ = 1`. -/
abbrev φZ : GZ := Multiplicative.ofAdd 1

theorem gZ_eq (g : GZ) : g = φZ ^ (Multiplicative.toAdd g) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_one]

/-- The sign `(−1)ⁿ` of `g = φⁿ`. -/
def sgnZ (g : GZ) : ℚ := (((Multiplicative.toAdd g).negOnePow : ℤˣ) : ℤ)

theorem sgnZ_mul (g h : GZ) : sgnZ (g * h) = sgnZ g * sgnZ h := by
  simp only [sgnZ, toAdd_mul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

theorem sgnZ_one : sgnZ 1 = 1 := by
  simp only [sgnZ, toAdd_one, Int.negOnePow_zero, Units.val_one, Int.cast_one]

theorem sgnZ_φZ : sgnZ φZ = -1 := by
  simp only [sgnZ, toAdd_ofAdd, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one]

/-- `ℚ²` on which `φⁿ` acts by `diag(1, (−1)ⁿ)`. -/
def JMod : Type := ℚ × ℚ

instance : AddCommGroup JMod := inferInstanceAs (AddCommGroup (ℚ × ℚ))
instance : Module ℚ JMod := inferInstanceAs (Module ℚ (ℚ × ℚ))
instance : TopologicalSpace JMod := inferInstanceAs (TopologicalSpace (ℚ × ℚ))
instance : ContinuousAdd JMod := inferInstanceAs (ContinuousAdd (ℚ × ℚ))
instance : ContinuousConstSMul ℚ JMod := inferInstanceAs (ContinuousConstSMul ℚ (ℚ × ℚ))

/-- `JMod` read as `ℚ × ℚ`. -/
def toP (v : JMod) : ℚ × ℚ := v

/-- `ℚ × ℚ` read as `JMod`. -/
def ofP (p : ℚ × ℚ) : JMod := p

theorem JMod.ext {v w : JMod} (h1 : (toP v).1 = (toP w).1) (h2 : (toP v).2 = (toP w).2) :
    v = w :=
  Prod.ext h1 h2

/-- The action `φⁿ • (a, b) = (a, (−1)ⁿ b)`. -/
def jsmul (g : GZ) (v : JMod) : JMod := ofP ((toP v).1, sgnZ g * (toP v).2)

theorem jsmul_one (v : JMod) : jsmul 1 v = v :=
  JMod.ext rfl (by
    change sgnZ 1 * (toP v).2 = (toP v).2
    rw [sgnZ_one, one_mul])

theorem jsmul_mul (g h : GZ) (v : JMod) : jsmul (g * h) v = jsmul g (jsmul h v) :=
  JMod.ext rfl (by
    change sgnZ (g * h) * (toP v).2 = sgnZ g * (sgnZ h * (toP v).2)
    rw [sgnZ_mul, mul_assoc])

theorem jsmul_zero (g : GZ) : jsmul g 0 = 0 :=
  JMod.ext rfl (by
    change sgnZ g * 0 = 0
    rw [mul_zero])

theorem jsmul_add (g : GZ) (v w : JMod) : jsmul g (v + w) = jsmul g v + jsmul g w :=
  JMod.ext rfl (by
    change sgnZ g * ((toP v).2 + (toP w).2) = sgnZ g * (toP v).2 + sgnZ g * (toP w).2
    rw [mul_add])

instance : DistribMulAction GZ JMod where
  smul := jsmul
  one_smul := jsmul_one
  mul_smul := jsmul_mul
  smul_zero := jsmul_zero
  smul_add := jsmul_add

theorem toP_gsmul (g : GZ) (v : JMod) : toP (g • v) = ((toP v).1, sgnZ g * (toP v).2) := rfl

instance : SMulCommClass GZ ℚ JMod where
  smul_comm g c v := JMod.ext rfl (by
    change sgnZ g * (c * (toP v).2) = c * (sgnZ g * (toP v).2)
    rw [mul_left_comm])

instance : ContinuousSMul GZ JMod where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun g => by
    change Continuous (fun v : ℚ × ℚ => (v.1, sgnZ g * v.2))
    exact continuous_fst.prodMk (continuous_const.mul continuous_snd)

/-- `ker(Φ − 2) = 0` for `Φ = diag(1, −1)`. PROVED. -/
theorem kerFrob_J : KerFrob ℚ JMod φZ 2 = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  have h := LinearMap.mem_ker.mp hm
  rw [frobSub_apply] at h
  have h1 := congrArg (fun v : JMod => (toP v).1) h
  have h2 := congrArg (fun v : JMod => (toP v).2) h
  change (toP m).1 - ((2 : ℕ) : ℚ) * (toP m).1 = (0 : ℚ) at h1
  change sgnZ φZ * (toP m).2 - ((2 : ℕ) : ℚ) * (toP m).2 = (0 : ℚ) at h2
  rw [sgnZ_φZ] at h2
  push_cast at h1 h2
  rw [Submodule.mem_bot]
  exact JMod.ext (by change (toP m).1 = 0; linarith) (by change (toP m).2 = 0; linarith)

/-- The cocycle `z(φⁿ) = (n x₁, ((1 − (−1)ⁿ)/2) x₂)` with `z(φ) = x`. -/
def FJ (x : JMod) (g : GZ) : JMod :=
  ofP (((Multiplicative.toAdd g : ℤ) : ℚ) * (toP x).1, (1 - sgnZ g) / 2 * (toP x).2)

theorem FJ_mul (x : JMod) (g h : GZ) : FJ x (g * h) = FJ x g + g • FJ x h :=
  JMod.ext (by
    change ((Multiplicative.toAdd (g * h) : ℤ) : ℚ) * (toP x).1 =
      ((Multiplicative.toAdd g : ℤ) : ℚ) * (toP x).1 +
        ((Multiplicative.toAdd h : ℤ) : ℚ) * (toP x).1
    rw [toAdd_mul, Int.cast_add, add_mul]) (by
    change (1 - sgnZ (g * h)) / 2 * (toP x).2 =
      (1 - sgnZ g) / 2 * (toP x).2 + sgnZ g * ((1 - sgnZ h) / 2 * (toP x).2)
    rw [sgnZ_mul]
    ring)

/-- `FJ x` as a continuous `1`-cochain. -/
def zJ (x : JMod) : (contCochains ℚ GZ JMod).X 1 :=
  ⟨(fun y => FJ x (y 0) : (groupCohomology.inhomogeneousCochains (rep ℚ GZ JMod)).X 1),
    mem_contCochain.mpr continuous_of_discreteTopology⟩

theorem zJ_mem (x : JMod) : zJ x ∈ Z1K ℚ GZ JMod :=
  mem_Z1K_of_cocycle (zJ x) fun g h => FJ_mul x g h

/-- **Non-vacuity of `TameCoordinatesUnr` with `Φ` nontrivial** (tex L3298–3306, L5026–5037): over
`ℚ`, the discrete group `G = ℤ = ⟨φ⟩`, `M = ℚ²` with `φ` acting by `Φ = diag(1, −1)`, `σ = 1`,
`I = 1`, `q = 2`. Here `H¹ = M/(Φ − 1)M ≅ ℚ` and `ker(Φ − 2) = 0`. PROVED. -/
theorem tameCoordinatesUnr_J : TameCoordinatesUnr ℚ JMod (⊥ : Subgroup GZ) φZ 1 2 := by
  have hItriv : ∀ h ∈ (⊥ : Subgroup GZ), ∀ m : JMod, h • m = m := fun h hh m => by
    rw [Subgroup.mem_bot.mp hh, one_smul]
  have hrel : φZ * 1 * φZ⁻¹ = (1 : GZ) ^ 2 := by rw [mul_one, mul_inv_cancel, one_pow]
  refine ⟨hItriv, Subgroup.one_mem _, hrel, ⟨?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [LinearMap.mem_ker, coordQUnr_mk, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨⟨m, hm⟩, -⟩ := hy
      have hz'φ : ev1K ((z - relaxedDK ℚ GZ JMod (const0K m) : Z1K ℚ GZ JMod) :
          (contCochains ℚ GZ JMod).X 1) φZ = 0 := by
        change ev1K (z : (contCochains ℚ GZ JMod).X 1) φZ -
          ev1K ((relaxedDK ℚ GZ JMod (const0K m) : Z1K ℚ GZ JMod) :
            (contCochains ℚ GZ JMod).X 1) φZ = 0
        rw [relaxedDK_ev, ev0K_const0K, ← hm, frobSub_apply, one_smul, sub_self]
      have hz' : z - relaxedDK ℚ GZ JMod (const0K m) = 0 :=
        Z1K_eq_zero_of_ev _ fun g => by
          rw [gZ_eq g]
          exact ev1K_zpow_eq_zero _ hz'φ _
      rw [Submodule.mem_bot, sub_eq_zero.mp hz', Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
  · rintro ⟨u, v⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain rfl : v = 0 := subtype_eq_zero_of_eq_bot kerFrob_J v
    refine ⟨Submodule.Quotient.mk ⟨zJ x, zJ_mem x⟩, ?_⟩
    rw [coordQUnr_mk]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change (Submodule.Quotient.mk (FJ x φZ) : CokerFrob ℚ JMod φZ) = Submodule.Quotient.mk x
      congr 1
      refine JMod.ext ?_ ?_
      · change ((Multiplicative.toAdd φZ : ℤ) : ℚ) * (toP x).1 = (toP x).1
        rw [toAdd_ofAdd, Int.cast_one, one_mul]
      · change (1 - sgnZ φZ) / 2 * (toP x).2 = (toP x).2
        rw [sgnZ_φZ]
        ring
    · change FJ x 1 = 0
      refine JMod.ext ?_ ?_
      · change ((Multiplicative.toAdd (1 : GZ) : ℤ) : ℚ) * (toP x).1 = 0
        rw [toAdd_one, Int.cast_zero, zero_mul]
      · change (1 - sgnZ 1) / 2 * (toP x).2 = 0
        rw [sgnZ_one, sub_self, zero_div, zero_mul]
  · intro z _ h hh
    rw [Subgroup.mem_bot.mp hh, ev1K_one_unr]

/-- `ℚ²` with the trivial action of `ℤ`. -/
abbrev MQZ : Type := TrivMod GZ (Fin 2 → ℚ)

/-- **Non-vacuity at the derivative-prime shape** (tex L3298–3306, L5026–5037): over `ℚ`,
`G = ℤ = ⟨φ⟩` discrete, `M = ℚ²` with `Φ = 1`, `σ = 1`, `I = 1`, `q = 2`; so the hypotheses of
`singular_zero_of_q_ne_one`, `no_k2k2_coords_of_q_ne_one` are satisfiable. PROVED. -/
theorem tameCoordinatesUnr_derivative : TameCoordinatesUnr ℚ MQZ (⊥ : Subgroup GZ) φZ 1 2 := by
  have htriv : ∀ (g : GZ) (m : MQZ), g • m = m := fun _ _ => rfl
  have hrel : φZ * 1 * φZ⁻¹ = (1 : GZ) ^ 2 := by rw [mul_one, mul_inv_cancel, one_pow]
  have hq : ((2 : ℕ) : ℚ) ≠ 1 := by norm_num
  refine ⟨fun h _ m => htriv h m, Subgroup.one_mem _, hrel, ⟨?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [LinearMap.mem_ker, coordQUnr_mk, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero,
        range_frobSub_one_eq_bot (htriv φZ), Submodule.mem_bot] at hy
      have hz : z = 0 := Z1K_eq_zero_of_ev z fun g => by
        rw [gZ_eq g]
        exact ev1K_zpow_eq_zero z hy.1 _
      rw [Submodule.mem_bot, hz, Submodule.Quotient.mk_zero]
  · rintro ⟨u, v⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain rfl : v = 0 :=
      subtype_eq_zero_of_eq_bot (kerFrob_eq_bot_of_q_ne_one (htriv φZ) hq) v
    let cF : (contCochains ℚ GZ MQZ).X 1 :=
      ⟨(fun y => ((Multiplicative.toAdd (y 0) : ℤ) • x : MQZ) :
          (groupCohomology.inhomogeneousCochains (rep ℚ GZ MQZ)).X 1),
        mem_contCochain.mpr continuous_of_discreteTopology⟩
    have hZ : cF ∈ Z1K ℚ GZ MQZ := mem_Z1K_of_additive htriv cF fun g h => by
      change (Multiplicative.toAdd (g * h) : ℤ) • x =
        (Multiplicative.toAdd g : ℤ) • x + (Multiplicative.toAdd h : ℤ) • x
      rw [toAdd_mul, add_smul]
    refine ⟨Submodule.Quotient.mk ⟨cF, hZ⟩, ?_⟩
    rw [coordQUnr_mk]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change (Submodule.Quotient.mk ((Multiplicative.toAdd φZ : ℤ) • x) : CokerFrob ℚ MQZ φZ) =
        Submodule.Quotient.mk x
      rw [toAdd_ofAdd, one_smul]
    · change (Multiplicative.toAdd (1 : GZ) : ℤ) • x = 0
      rw [toAdd_one, zero_smul]
  · intro z _ h hh
    rw [Subgroup.mem_bot.mp hh, ev1K_one_unr]

/-- **At the derivative-prime shape, `2 + 0`, not `2 + 2`** (tex L3298–3306, L5026–5037): in the
example `tameCoordinatesUnr_derivative` (`Φ = 1`, `q = 2`), `dim H¹(W_rel) = 2 + 0` and there is no
`H¹(W_rel) ≃ ℚ² × ℚ²`. PROVED. -/
theorem derivative_example_two_plus_zero :
    finrank ℚ (H1WrelK ℚ GZ MQZ) = 2 + 0 ∧
      ¬ Nonempty (H1WrelK ℚ GZ MQZ ≃ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ)) := by
  have : FiniteDimensional ℚ MQZ := inferInstanceAs (FiniteDimensional ℚ (Fin 2 → ℚ))
  have hM : finrank ℚ MQZ = 2 := Module.finrank_fin_fun ℚ
  have hq : ((2 : ℕ) : ℚ) ≠ 1 := by norm_num
  refine ⟨?_, no_k2k2_coords_of_q_ne_one tameCoordinatesUnr_derivative (fun _ => rfl) hM hq⟩
  rw [finrank_H1WrelK_of_q_ne_one tameCoordinatesUnr_derivative (fun _ => rfl) hq, hM]

/-- **Non-vacuity of `TameCoordinatesUnr` with `q = 1`** (tex L3298–3306, L5026–5037): `G = ℤ²`
discrete, `M = ℚ²` with the trivial action, `φ = (1, 0)`, `σ = (0, 1)`, `I = ⟨σ⟩` (the example of
`tameCoordinatesTrivialK_example`). PROVED. -/
theorem tameCoordinatesUnr_q_one : TameCoordinatesUnr ℚ MQ2 IZ2 φZ2 σZ2 1 :=
  tameCoordinatesTrivialK_example.toUnr (by
    rw [pow_one, mul_comm φZ2 σZ2, mul_assoc, mul_inv_cancel, mul_one])

/-- **`q = 1` recovers `2 + 2`** (tex L3298–3306, L5026–5037): in the example
`tameCoordinatesUnr_q_one` (`Φ = 1`, `q = 1`, `dim M = 2`), `H¹(W_rel) ≃ ℚ² × ℚ²`. PROVED. -/
theorem two_plus_two_q_one : Nonempty (H1WrelK ℚ GZ2 MQ2 ≃ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ)) := by
  have : FiniteDimensional ℚ MQ2 := inferInstanceAs (FiniteDimensional ℚ (Fin 2 → ℚ))
  have hM : finrank ℚ MQ2 = 2 := Module.finrank_fin_fun ℚ
  exact (two_plus_two_iff_q_eq_one tameCoordinatesUnr_q_one (fun _ => rfl) hM).mpr Nat.cast_one

end Example

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
