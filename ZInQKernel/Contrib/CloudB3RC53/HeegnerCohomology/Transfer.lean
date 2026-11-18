import Mathlib

/-!
# HeegnerCohomology, part 5: the twisted transfer (H21) in every degree

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7
"The actual coefficient push and its local conditions", tex 3219–3250.

Elliot writes the integral Shapiro-plus-coefficient map as an explicit cochain map.  With
representatives `r_δ` of `G_K/G_{H_f}` (`Δ_f = G_K/G_{H_f}` the normal quotient) and
`g r_δ = r_{gδ} h(g,δ)`, `h(g,δ) ∈ G_{H_f}`, `R(g) = θ(g) ρ_T(g)`, and for `g_1, …, g_n`,
`δ_i = g_{i+1} ⋯ g_n δ`, the degree-`n` map is (tex 3237–3242)

`(𝒯_θ c)(g_1, …, g_n) = ∑_{δ ∈ Δ_f} R(r_{g_1⋯g_n δ}) c(h(g_1,δ_1), …, h(g_n,δ_n))`,

and "with the ordinary inhomogeneous differential, the relation for `h` above gives
`d𝒯_θ = 𝒯_θ d`" (tex 3243–3244).

RC10 proves this identity in degrees `0 → 1`, `1 → 2`, `2 → 3` (`T0_comm_d`, `T1_comm_d`,
`T2_comm_d` in `ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Transfer.lean`).
Here it is proved in every degree (`dT_eq_Td`), `PROVED`, for an arbitrary group `G`, normal
subgroup `H` of finite index, section `r` of `G → G/H`, representation `ρ` of `G` on an
`A`-module `M` and character `θ` of `G/H` with values in `Aˣ`.  The differential is Mathlib's
inhomogeneous one (`inhomogeneousCochains.d`):
`(d f)(g_0, …, g_n) = g_0 • f(g_1, …, g_n) + ∑_{j=0}^{n} (-1)^{j+1} f(…, g_j g_{j+1}, …)` where the
`j = n` term drops the last argument.

The indices are 0-based: for `g : Fin n → G`, `δ_k = g_{k+1} ⋯ g_{n-1} δ`; this is Elliot's
formula with `g_i ↦ g (i - 1)`.  The tuple `(h(g_k, δ_k))_k` is built recursively (`hTuple`):
its head is `h(g_0, (g_1 ⋯ g_{n-1}) δ)` and its tail is the tuple of the tail.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset

/-! ## Tuples -/

section Tuple

variable {α : Type*}

/-- `contractNth 0` on a tuple of length `n + 2` merges its first two entries. -/
theorem contractNth_zero (op : α → α → α) {n : ℕ} (g : Fin (n + 2) → α) :
    Fin.contractNth (0 : Fin (n + 2)) op g =
      Fin.cons (op (g 0) (g 1)) (Fin.tail (Fin.tail g)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.contractNth]
  · simp only [Fin.contractNth, Fin.cons_succ, Fin.tail]
    rw [ite_eq_right_iff.mpr (by simp), ite_eq_right_iff.mpr (by simp)]

/-- `contractNth (j+1)` on a tuple keeps the head and contracts the tail at `j`. -/
theorem contractNth_succ (op : α → α → α) {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 2) → α) :
    Fin.contractNth j.succ op g = Fin.cons (g 0) (Fin.contractNth j op (Fin.tail g)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.contractNth]
  · simp only [Fin.contractNth, Fin.cons_succ, Fin.tail, Fin.val_succ]
    split_ifs <;> first | rfl | (exfalso; omega)

end Tuple

/-! ## Products and the `h`-tuple -/

variable {G : Type*} [Group G]

/-- The ordered product `g_0 g_1 ⋯ g_{n-1}` of a tuple. -/
def tprod : (n : ℕ) → (Fin n → G) → G
  | 0, _ => 1
  | n + 1, g => g 0 * tprod n (Fin.tail g)

@[simp] theorem tprod_zero (g : Fin 0 → G) : tprod 0 g = 1 := rfl

theorem tprod_succ (n : ℕ) (g : Fin (n + 1) → G) : tprod (n + 1) g = g 0 * tprod n (Fin.tail g) :=
  rfl

/-- Contracting at an interior index does not change the product. -/
theorem tprod_contract_castSucc : ∀ (n : ℕ) (j : Fin n) (g : Fin (n + 1) → G),
    tprod n (Fin.contractNth j.castSucc (· * ·) g) = tprod (n + 1) g
  | 0, j, _ => j.elim0
  | n + 1, j, g => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [show (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) from rfl, contractNth_zero,
        tprod_succ, Fin.cons_zero, Fin.tail_cons, tprod_succ (n + 1), tprod_succ n (Fin.tail g)]
      simp [Fin.tail, mul_assoc]
    · rw [show (Fin.succ j).castSucc = (Fin.castSucc j).succ from (Fin.succ_castSucc j).symm,
        contractNth_succ, tprod_succ, Fin.cons_zero, Fin.tail_cons,
        tprod_contract_castSucc n j (Fin.tail g), tprod_succ (n + 1)]

/-- Dropping the last entry: `g_0 ⋯ g_n = (g_0 ⋯ g_{n-1}) g_n`. -/
theorem tprod_contract_last : ∀ (n : ℕ) (g : Fin (n + 1) → G),
    tprod (n + 1) g = tprod n (Fin.contractNth (Fin.last n) (· * ·) g) * g (Fin.last n)
  | 0, g => by simp [tprod_succ]
  | n + 1, g => by
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, contractNth_succ, tprod_succ (n + 1) g,
      tprod_contract_last n (Fin.tail g), tprod_succ n (Fin.cons _ _), Fin.cons_zero, Fin.tail_cons,
      mul_assoc]
    rfl

variable (H : Subgroup G) [H.Normal] (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

/-- `h(g, δ) = r_{gδ}⁻¹ g r_δ` (tex 3222). -/
def hc (g : G) (δ : G ⧸ H) : G := (r ((g : G ⧸ H) * δ))⁻¹ * g * r δ

include hr in
theorem hc_mem (g : G) (δ : G ⧸ H) : hc H r g δ ∈ H := by
  rw [← QuotientGroup.eq_one_iff, hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, hr, hr]
  group

/-- `h(gk, δ) = h(g, kδ) h(k, δ)` (tex 3229–3230). -/
theorem hc_mul (g k : G) (δ : G ⧸ H) : hc H r (g * k) δ = hc H r g (k * δ) * hc H r k δ := by
  simp only [hc, QuotientGroup.mk_mul, mul_assoc, mul_inv_cancel_left]

/-- The tuple `(h(g_k, δ_k))_k`, `δ_k = g_{k+1} ⋯ g_{n-1} δ`. -/
def hTuple : (n : ℕ) → G ⧸ H → (Fin n → G) → (Fin n → H)
  | 0, _, _ => fun k => k.elim0
  | n + 1, δ, g => Fin.cons ⟨hc H r (g 0) (((tprod n (Fin.tail g) : G) : G ⧸ H) * δ),
      hc_mem H r hr _ _⟩ (hTuple n δ (Fin.tail g))

theorem hTuple_zero (n : ℕ) (δ : G ⧸ H) (g : Fin (n + 1) → G) :
    ((hTuple H r hr (n + 1) δ g 0 : H) : G) = hc H r (g 0) (((tprod n (Fin.tail g) : G) : G ⧸ H) * δ) :=
  rfl

theorem hTuple_tail (n : ℕ) (δ : G ⧸ H) (g : Fin (n + 1) → G) :
    Fin.tail (hTuple H r hr (n + 1) δ g) = hTuple H r hr n δ (Fin.tail g) := rfl

/-- Extensionality for the `h`-tuple: a tuple equals `hTuple (n+1) δ g` when its head is
`h(g_0, (g_1 ⋯ g_n) δ)` and its tail is the `h`-tuple of the tail. -/
theorem hTuple_ext (n : ℕ) (δ : G ⧸ H) (g : Fin (n + 1) → G) (v : Fin (n + 1) → H)
    (h0 : (v 0 : G) = hc H r (g 0) (((tprod n (Fin.tail g) : G) : G ⧸ H) * δ))
    (ht : Fin.tail v = hTuple H r hr n δ (Fin.tail g)) : v = hTuple H r hr (n + 1) δ g := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Subtype.ext h0
  · rw [show hTuple H r hr (n + 1) δ g k.succ = hTuple H r hr n δ (Fin.tail g) k from rfl]
    exact congrFun ht k

/-- Contraction at an interior index commutes with the `h`-tuple (the relation for `h`). -/
theorem hTuple_contract_castSucc : ∀ (n : ℕ) (j : Fin n) (δ : G ⧸ H) (g : Fin (n + 1) → G),
    Fin.contractNth j.castSucc (· * ·) (hTuple H r hr (n + 1) δ g) =
      hTuple H r hr n δ (Fin.contractNth j.castSucc (· * ·) g)
  | 0, j, _, _ => j.elim0
  | n + 1, j, δ, g => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [show (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) from rfl, contractNth_zero,
        contractNth_zero]
      apply hTuple_ext
      · rw [Fin.cons_zero, Fin.cons_zero, Subgroup.coe_mul, Fin.tail_cons, hc_mul]
        show hc H r (g 0) _ * hc H r (g 1) _ = _
        congr 2
        rw [tprod_succ, QuotientGroup.mk_mul, mul_assoc]
        rfl
      · rw [Fin.tail_cons, Fin.tail_cons]
        rfl
    · rw [show (Fin.succ j).castSucc = (Fin.castSucc j).succ from (Fin.succ_castSucc j).symm,
        contractNth_succ, contractNth_succ]
      apply hTuple_ext
      · rw [Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, tprod_contract_castSucc n j (Fin.tail g)]
        rfl
      · rw [Fin.tail_cons, Fin.tail_cons, hTuple_tail]
        exact hTuple_contract_castSucc n j δ (Fin.tail g)

/-- Dropping the last argument: the `h`-tuple of `g_0, …, g_n` at `δ`, without its last entry, is
the `h`-tuple of `g_0, …, g_{n-1}` at `g_n δ`. -/
theorem hTuple_contract_last : ∀ (n : ℕ) (δ : G ⧸ H) (g : Fin (n + 1) → G),
    Fin.contractNth (Fin.last n) (· * ·) (hTuple H r hr (n + 1) δ g) =
      hTuple H r hr n ((g (Fin.last n) : G ⧸ H) * δ) (Fin.contractNth (Fin.last n) (· * ·) g)
  | 0, _, _ => funext fun k => k.elim0
  | n + 1, δ, g => by
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, contractNth_succ, contractNth_succ]
    apply hTuple_ext
    · rw [Fin.cons_zero, Fin.cons_zero, Fin.tail_cons]
      show hc H r (g 0) _ = hc H r (g 0) _
      rw [tprod_contract_last n (Fin.tail g), QuotientGroup.mk_mul, mul_assoc]
      rfl
    · rw [Fin.tail_cons, Fin.tail_cons, hTuple_tail]
      exact hTuple_contract_last n δ (Fin.tail g)

/-! ## The twisted transfer and the differential -/

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

/-- `R(g) = θ(g) ρ_T(g)` (tex 3235). -/
def R (g : G) : Module.End A M := (θ (g : G ⧸ H) : A) • ρ g

theorem R_mul (g k : G) : R H ρ θ (g * k) = R H ρ θ g * R H ρ θ k := by
  simp only [R, map_mul, QuotientGroup.mk_mul, Units.val_mul, smul_mul_smul_comm]

theorem R_of_mem {x : G} (hx : x ∈ H) : R H ρ θ x = ρ x := by
  rw [R, (QuotientGroup.eq_one_iff x).mpr hx, map_one, Units.val_one, one_smul]

/-- The inhomogeneous differential `d : Cⁿ → Cⁿ⁺¹` for an action `act` (Mathlib's
`inhomogeneousCochains.d`). -/
def dInh {Γ : Type*} [Mul Γ] (act : Γ → M → M) (n : ℕ) (f : (Fin n → Γ) → M)
    (g : Fin (n + 1) → Γ) : M :=
  act (g 0) (f (Fin.tail g)) +
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1)) • f (Fin.contractNth j (· * ·) g)

variable [Fintype (G ⧸ H)]

/-- **The degree-`n` twisted transfer** (tex 3237–3242):
`(𝒯_θ c)(g) = ∑_δ R(r_{g_0⋯g_{n-1}δ}) c(h(g_0,δ_0), …, h(g_{n-1},δ_{n-1}))`. -/
def T (n : ℕ) (c : (Fin n → H) → M) (g : Fin n → G) : M :=
  ∑ δ : G ⧸ H, R H ρ θ (r (((tprod n g : G) : G ⧸ H) * δ)) (c (hTuple H r hr n δ g))

omit [Fintype (G ⧸ H)] in
include hr in
/-- The key identity `R(r_{gδ}) ρ_T(h(g,δ)) = R(g) R(r_δ)`, from `r_{gδ} h(g,δ) = g r_δ`. -/
theorem R_r_mul_hc (g : G) (δ : G ⧸ H) :
    R H ρ θ (r ((g : G ⧸ H) * δ)) * ρ (hc H r g δ) = R H ρ θ g * R H ρ θ (r δ) := by
  rw [← R_of_mem H ρ θ (hc_mem H r hr g δ), ← R_mul, ← R_mul, hc]
  congr 1
  group

/-- **`d 𝒯_θ = 𝒯_θ d` in every degree** (tex 3243–3244), `PROVED`. -/
theorem dT_eq_Td (n : ℕ) (c : (Fin n → H) → M) (g : Fin (n + 1) → G) :
    dInh (fun x m => R H ρ θ x m) n (T H r hr ρ θ n c) g =
      T H r hr ρ θ (n + 1) (dInh (fun (x : H) m => ρ (x : G) m) n c) g := by
  simp only [T, dInh, map_add, map_sum, map_zsmul, sum_add_distrib]
  congr 1
  · -- the first term
    refine sum_congr rfl fun δ _ => ?_
    rw [hTuple_tail, hTuple_zero, ← Module.End.mul_apply (R H ρ θ _) (ρ _), tprod_succ,
      QuotientGroup.mk_mul, mul_assoc, R_r_mul_hc H r hr ρ θ, Module.End.mul_apply]
  · rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← smul_sum]
    congr 1
    refine Fin.lastCases ?_ (fun j => ?_) j
    · -- the last term: reindex `δ ↦ g_n δ`
      simp only [hTuple_contract_last]
      symm
      refine Fintype.sum_equiv (Equiv.mulLeft ((g (Fin.last n) : G ⧸ H))) _ _ (fun δ => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [tprod_contract_last n g, QuotientGroup.mk_mul, mul_assoc]
    · refine sum_congr rfl fun δ _ => ?_
      rw [hTuple_contract_castSucc, tprod_contract_castSucc]

/-- In degree one the transfer is Elliot's (H21) (tex 3224–3227):
`(𝒯_θ b)(g) = ∑_δ θ(r_{gδ}) ρ_T(r_{gδ}) b(h(g,δ))`. -/
theorem T_one (c : (Fin 1 → H) → M) (g : Fin 1 → G) :
    T H r hr ρ θ 1 c g = ∑ δ : G ⧸ H, R H ρ θ (r ((g 0 : G ⧸ H) * δ))
      (c (Fin.cons ⟨hc H r (g 0) δ, hc_mem H r hr _ _⟩ (fun k => k.elim0))) := by
  refine sum_congr rfl fun δ _ => ?_
  have h1 : ((tprod 1 g : G) : G ⧸ H) * δ = (g 0 : G ⧸ H) * δ := by simp [tprod_succ]
  have h2 : hTuple H r hr 1 δ g = Fin.cons ⟨hc H r (g 0) δ, hc_mem H r hr _ _⟩ (fun k => k.elim0) := by
    symm
    apply hTuple_ext
    · simp [tprod]
    · funext k; exact k.elim0
  rw [h1, h2]

/-- Cocycles go to cocycles (tex 3229–3231, all degrees), `PROVED`. -/
theorem T_cocycle (n : ℕ) (c : (Fin n → H) → M)
    (hc : dInh (fun (x : H) m => ρ (x : G) m) n c = 0) :
    dInh (fun x m => R H ρ θ x m) n (T H r hr ρ θ n c) = 0 := by
  funext g
  rw [dT_eq_Td, hc]
  simp [T]

/-- **Kummer of the weighted sum is the transfer of the Kummer cocycle** (tex 3232–3234 and
3258–3262: "in degree zero the formula is the weighted sum `∑_δ θ(r_δ) ρ_T(r_δ) Q`; applying its
boundary gives (H21) applied to the boundary of `Q`"; "Kummer of this sum equals the cohomological
transfer"), `PROVED`.  If `k • Q̃ = Q` (a division point of `Q`; `k = 2^m`), the Kummer cocycle
`h ↦ ρ(h) Q̃ - Q̃` of `Q` has transfer `g ↦ R(g) P̃ - P̃`, where `P̃ = ∑_δ R(r_δ) Q̃` is a division
point of the weighted sum: `k • P̃ = ∑_δ R(r_δ) Q`. -/
theorem kummer_weighted_sum (k : ℤ) (Q Qt : M) (hQ : k • Qt = Q) :
    k • (∑ δ : G ⧸ H, R H ρ θ (r δ) Qt) = ∑ δ : G ⧸ H, R H ρ θ (r δ) Q ∧
    ∀ g : Fin 1 → G, T H r hr ρ θ 1 (fun x => ρ (x 0 : G) Qt - Qt) g =
      R H ρ θ (g 0) (∑ δ : G ⧸ H, R H ρ θ (r δ) Qt) - ∑ δ : G ⧸ H, R H ρ θ (r δ) Qt := by
  refine ⟨by rw [smul_sum]; simp [← hQ, map_zsmul], fun g => ?_⟩
  have h := dT_eq_Td H r hr ρ θ 0 (fun _ => Qt) g
  have e1 : dInh (fun (x : H) m => ρ (x : G) m) 0 (fun _ => Qt) = fun x => ρ (x 0 : G) Qt - Qt := by
    funext x; simp [dInh, sub_eq_add_neg]
  rw [e1] at h
  rw [← h]
  simp [dInh, T, sub_eq_add_neg]

/-! ## Localization: the decomposition-group orbit terms (the local Mackey formula) -/

/-- The partial transfer over a subset `O ⊆ Δ`: `∑_{δ ∈ O} R(r_{g_0⋯g_{n-1}δ}) c(h-tuple)`. -/
def TO (O : Finset (G ⧸ H)) (n : ℕ) (c : (Fin n → H) → M) (g : Fin n → G) : M :=
  ∑ δ ∈ O, R H ρ θ (r (((tprod n g : G) : G ⧸ H) * δ)) (c (hTuple H r hr n δ g))

theorem T_eq_TO_univ (n : ℕ) (c : (Fin n → H) → M) :
    T H r hr ρ θ n c = TO H r hr ρ θ Finset.univ n c := rfl

omit [Fintype (G ⧸ H)] in
/-- **The orbit terms are cochain maps on the decomposition group** (tex 3251–3256: "localizing
(H21) separates the cosets into decomposition-group orbits: this is the local Mackey formula, a
sum of the local corestrictions from the transported places"), `PROVED` in every degree: for a
subgroup `D ≤ G` (the decomposition group at a place) and a `D`-stable subset `O ⊆ Δ` (a union of
`D`-orbits), the partial transfer over `O` commutes with the differentials on `D`-cochains. -/
theorem dTO_eq_TOd (D : Subgroup G) (O : Finset (G ⧸ H))
    (hO : ∀ d ∈ D, ∀ δ ∈ O, ((d : G) : G ⧸ H) * δ ∈ O)
    (n : ℕ) (c : (Fin n → H) → M) (g : Fin (n + 1) → D) :
    dInh (fun x m => R H ρ θ x m) n (TO H r hr ρ θ O n c) (fun i => (g i : G)) =
      TO H r hr ρ θ O (n + 1) (dInh (fun (x : H) m => ρ (x : G) m) n c) (fun i => (g i : G)) := by
  simp only [TO, dInh, map_add, map_sum, map_zsmul, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun δ _ => ?_
    rw [hTuple_tail, hTuple_zero, ← Module.End.mul_apply (R H ρ θ _) (ρ _), tprod_succ,
      QuotientGroup.mk_mul, mul_assoc, R_r_mul_hc H r hr ρ θ, Module.End.mul_apply]
  · rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← smul_sum]
    congr 1
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hTuple_contract_last]
      symm
      set x : G ⧸ H := ((g (Fin.last n) : G) : G ⧸ H)
      refine Finset.sum_nbij' (fun δ => x * δ) (fun δ => x⁻¹ * δ)
        (fun δ hδ => hO _ (g (Fin.last n)).2 δ hδ)
        (fun δ hδ => by
          have := hO _ (D.inv_mem (g (Fin.last n)).2) δ hδ
          simpa [x] using this)
        (fun δ _ => by simp) (fun δ _ => by simp) (fun δ _ => ?_)
      rw [tprod_contract_last n, QuotientGroup.mk_mul, mul_assoc]
    · refine sum_congr rfl fun δ _ => ?_
      rw [hTuple_contract_castSucc, tprod_contract_castSucc]

/-- The Mackey decomposition: for a partition of `Δ` into finitely many subsets (the
`D`-orbits), the transfer is the sum of the orbit terms (tex 3251–3253). -/
theorem T_eq_sum_TO [DecidableEq (G ⧸ H)] {ι : Type*} (s : Finset ι) (O : ι → Finset (G ⧸ H))
    (hdisj : (s : Set ι).PairwiseDisjoint O) (hcover : s.biUnion O = Finset.univ)
    (n : ℕ) (c : (Fin n → H) → M) (g : Fin n → G) :
    T H r hr ρ θ n c g = ∑ i ∈ s, TO H r hr ρ θ (O i) n c g := by
  rw [T_eq_TO_univ, TO, ← hcover, Finset.sum_biUnion hdisj]
  rfl

end TwistedTransfer

/-- **Node (H21) in every degree**, tex 3237–3244 (ex:arith-finite-heegner, paragraph 7),
`PROVED`: for every group `G`, normal subgroup `H` of finite index, section `r` of `G → G/H`,
representation `ρ` of `G` on an `A`-module `M` and character `θ : G/H → Aˣ`, the degree-`n`
twisted transfer commutes with the inhomogeneous differentials (of `ρ|_H` on `H`-cochains and of
`R = θρ` on `G`-cochains), for every `n`. -/
def TransferCommNode : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)] (r : G ⧸ H → G)
    (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (n : ℕ) (c : (Fin n → H) → M),
    TwistedTransfer.dInh (fun x m => TwistedTransfer.R H ρ θ x m) n
        (TwistedTransfer.T H r hr ρ θ n c) =
      TwistedTransfer.T H r hr ρ θ (n + 1)
        (TwistedTransfer.dInh (fun (x : H) m => ρ (x : G) m) n c)

theorem transferCommNode_proof : TransferCommNode := by
  intro G _ H _ _ r hr A M _ _ _ ρ θ n c
  funext g
  exact TwistedTransfer.dT_eq_Td H r hr ρ θ n c g

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
