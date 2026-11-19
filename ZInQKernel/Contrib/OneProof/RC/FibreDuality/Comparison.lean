import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Print
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Fibre
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateBasis

/-!
# Lane RC31, part 6: the fibre `V_𝔭` is an admissible module in Nekovář's sense

Manuscript `diophantine_zq.tex`, the height-one regularity step (tex 4976–5200): the fibres
`V_𝔭 = 𝕋 ⊗_Λ k(𝔭)` (lane RC28, `VP`), their lattice `latt` and their natural topology (`vpTop`,
neighbourhood basis `2^n latt`), and lane RC26's continuous cochains `contCochain` with values in
`V_𝔭`.

Source: J. Nekovář, *Selmer complexes*, Astérisque 310 (2006): 3.3.1, 3.3.4 (p. 79, ind-admissible
modules), 3.4.1.1 (p. 82: `C^i_cont(G, M) = lim→_{M_α ∈ S(M)} C^i_cont(G, M_α)`, each `M_α` with
its `𝔪`-adic topology), 3.7.2–3.7.4 (pp. 93–94; 3.7.4(ii): `𝒮⁻¹RΓ_cont(G, M) ≅ RΓ_cont(G, 𝒮⁻¹M)`),
4.1–4.2 (pp. 95–100).

Contents.
* **(A)** `isLatticeTop_vp`: `V_𝔭` carries exactly the topology `IsLatticeTop` of `Print.lean`,
  with lattice `Y = latt` (finitely generated over `Λ`: `latt_eq_span_tateBasis`, `latt_fg`).
  The version `isLatticeTop_vp_of_fg` only asks that `T_2E` be a finitely generated `ℤ₂`-module.
* **(B)** `exists_two_pow_smul_mem_latt_of_continuous`: a continuous map from a compact space to
  `V_𝔭` lands in some `2^{−N} latt`; `compactSpace_GKS`; `contCochain_bounded` and
  `contCochain_bounded_loc` for `G_{K,S}` and `G_{K_v}` (acting through `p_v`). Conversely
  (`continuous_iff_isLocallyConstant_mod`): for a map `f` with `2^N f` valued in `latt`, `f` is
  continuous into `V_𝔭` iff every reduction `x ↦ 2^N f(x) mod 2^m latt` is locally constant,
  i.e. iff `2^N f` is continuous for the `2`-adic (inverse-limit) topology of the lattice. Hence
  (`mem_contCochain_iff`, `mem_contCochain_loc_iff`) **the continuous cochains of lane RC26 with
  values in `V_𝔭` are exactly Nekovář's** `lim→_N C_cont(G, 2^{−N} latt)` (3.4.1.1): the cochain
  level localization `C_cont(G, V_𝔭) = ⋃_N 2^{−N} C_cont(G, latt)`.
* **(C)** `NekovarFibreComparison` (PRINT: Nekovář 3.7.4(ii) p. 94, 4.1.2–4.1.3 pp. 95–96,
  4.2.2 p. 96, 5.1.1 p. 113): `H^i_cont(G, V_𝔭) ≅ k(𝔭) ⊗_Λ lim_m H^i(G, latt/2^m latt)` for
  `G = G_{K,S}` and `G = G_{K_v}`, with the finite discrete levels `LattQuot m = latt/2^m latt`
  and their transition maps (definitions, PROVED to be continuous `G`-modules).

Kinds: PROVED (A), (B); definitions; PRINT (C).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain Filter Topology TensorProduct
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open scoped Pointwise

section Fibre

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} (P : Ideal Lambda) [P.IsPrime] {α : GKS K S →* Lambdaˣ}

/-! ### (A) The lattice is finitely generated; `V_𝔭` carries Nekovář's topology -/

/-- The `ℤ₂`-linear map `T_2E → V_𝔭`, `Q ↦ 1 ⊗ Q` (tex 4976–5200). Kind: definition. -/
def oneTmul : TateS K S W →ₗ[ℤ_[2]] VP K S W P α :=
  TensorProduct.mk ℤ_[2] (ResAt P) (TateS K S W) 1

/-- `oneTmul Q = 1 ⊗ Q`. Kind: PROVED (definitional). -/
theorem oneTmul_apply (Q : TateS K S W) :
    oneTmul (α := α) P Q = show VP K S W P α from (1 : ResAt P) ⊗ₜ Q :=
  rfl

/-- **`latt` is the `Λ`-span of `1 ⊗ s` for any `ℤ₂`-spanning set `s` of `T_2E`**
(`1 ⊗ (a • Q) = a • (1 ⊗ Q)`). Kind: PROVED (tex 4976–5200). -/
theorem latt_eq_span_image (s : Set (TateS K S W)) (hs : Submodule.span ℤ_[2] s = ⊤) :
    latt K S W P α = Submodule.span Lambda (oneTmul (α := α) P '' s) := by
  apply le_antisymm
  · rw [latt, Submodule.span_le]
    rintro _ ⟨Q, rfl⟩
    have hQ : Q ∈ Submodule.span ℤ_[2] s := hs ▸ Submodule.mem_top
    have h1 : oneTmul (α := α) P Q ∈ Submodule.span ℤ_[2] (oneTmul (α := α) P '' s) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hQ
    exact Submodule.span_le_restrictScalars ℤ_[2] Lambda _ h1
  · rw [Submodule.span_le]
    rintro _ ⟨Q, -, rfl⟩
    exact one_tmul_mem_latt P Q

/-- **`latt = Λ (1 ⊗ b₀) + Λ (1 ⊗ b₁)`** for the basis `tateBasis` of `T_2E`. Kind: PROVED
(tex 2780, tex 4976–5200). -/
theorem latt_eq_span_tateBasis [W.IsElliptic] [HasFullTwoTorsion K S W] :
    latt K S W P α = Submodule.span Lambda
      (Set.range fun i : Fin 2 => oneTmul (α := α) P (tateBasis (K := K) (S := S) (W := W) i)) := by
  rw [latt_eq_span_image P _ (tateBasis (K := K) (S := S) (W := W)).span_eq, ← Set.range_comp]
  rfl

/-- **`latt` is a finitely generated `Λ`-module as soon as `T_2E` is a finitely generated
`ℤ₂`-module.** Kind: PROVED (tex 4976–5200). -/
theorem latt_fg_of_fg (h : (⊤ : Submodule ℤ_[2] (TateS K S W)).FG) : (latt K S W P α).FG := by
  classical
  obtain ⟨s, hs⟩ := h
  exact ⟨s.image (oneTmul (α := α) P), by rw [Finset.coe_image, latt_eq_span_image P _ hs]⟩

/-- **`latt` is a finitely generated `Λ`-module.** Kind: PROVED (tex 2780, tex 4976–5200). -/
theorem latt_fg [W.IsElliptic] [HasFullTwoTorsion K S W] : (latt K S W P α).FG :=
  latt_fg_of_fg P Module.Finite.fg_top

/-- **(A), conditional form: `V_𝔭` carries Nekovář's topology** (3.3.1, 3.3.4, 3.7.2, 3.7.3,
pp. 79, 93; the hypothesis `IsLatticeTop` of `Print.lean`) as soon as `T_2E` is a finitely
generated `ℤ₂`-module: `Y = latt`, `G_{K,S}`-stable (`smul_mem_latt`), exhausting
(`exists_two_pow_smul_mem_latt`), with neighbourhood basis `2^n latt` (`fib_hasBasis_nhds_zero`).
Kind: PROVED (tex 4976–5200). -/
theorem isLatticeTop_vp_of_fg [IsHeightOneOdd P] (h : (⊤ : Submodule ℤ_[2] (TateS K S W)).FG) :
    IsLatticeTop (GKS K S) (VP K S W P α) :=
  ⟨⟨latt K S W P α, latt_fg_of_fg P h, fun g _ hy => smul_mem_latt P g hy,
    exists_two_pow_smul_mem_latt P, fib_hasBasis_nhds_zero P⟩⟩

/-- **(A): lane RC28's fibre `V_𝔭` carries exactly Nekovář's ind-admissible topology**
(`IsLatticeTop`, Nekovář 3.3.1, 3.3.4, 3.7.2–3.7.3, pp. 79, 93), with `Y = latt`. Kind: PROVED
(tex 4976–5200). -/
theorem isLatticeTop_vp [IsHeightOneOdd P] [W.IsElliptic] [HasFullTwoTorsion K S W] :
    IsLatticeTop (GKS K S) (VP K S W P α) :=
  isLatticeTop_vp_of_fg P Module.Finite.fg_top

/-! #### `T_2E` is finitely generated over `ℤ₂` without `HasFullTwoTorsion` -/

omit [P.IsPrime] in
/-- `K_S ⊆ K_{all primes}`. Kind: PROVED. -/
theorem unramifiedOutside_le_univ :
    unramifiedOutside K S ≤ unramifiedOutside K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [unramifiedOutside_univ]
  exact le_top

variable (K S) in
/-- The inclusion `K_S → K_{all primes}` (`= K̄`). Kind: definition. -/
def toKSUniv : ZInQ.Manuscript.RC.CoefModules.KS K S →ₐ[K]
    ZInQ.Manuscript.RC.CoefModules.KS K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) :=
  IntermediateField.inclusion unramifiedOutside_le_univ

variable (W) in
/-- The level map `E(K_S)[2^n] → E(K̄)[2^n]` (the point map along `K_S ⊆ K̄`; `K̄` is
`K_{all primes}`, `unramifiedOutside_univ`). Kind: definition. -/
def levUniv (n : ℕ) : Lev K S W n →+ Lev K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) W n where
  toFun Q := ⟨WeierstrassCurve.Affine.Point.map (toKSUniv K S) (Q : Pt K S W), by
    rw [mem_lev_iff, ← map_nsmul, two_pow_nsmul_lev Q, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' Q R := Subtype.ext (map_add _ _ _)

omit [P.IsPrime] in
/-- The level maps are injective (`K_S → K̄` is injective). Kind: PROVED. -/
theorem levUniv_injective (n : ℕ) : Function.Injective (levUniv (S := S) W n) := fun _ _ h =>
  Subtype.ext (WeierstrassCurve.Affine.Point.map_injective (toKSUniv K S) (congrArg Subtype.val h))

omit [P.IsPrime] in
/-- The level maps commute with the transition maps `P ↦ 2P`. Kind: PROVED. -/
theorem levUniv_transLev (n : ℕ) (Q : Lev K S W (n + 1)) :
    levUniv W n (transLev K S W n Q) = transLev K _ W n (levUniv W (n + 1) Q) :=
  Subtype.ext
    (map_nsmul (WeierstrassCurve.Affine.Point.map (W' := W) (toKSUniv K S)) 2 (Q : Pt K S W))

variable (W) in
/-- **The `ℤ₂`-linear map `T_2E(K_S) → T_2E(K̄)`** induced by the level maps. Kind: definition. -/
def tateUniv : TateS K S W →ₗ[ℤ_[2]] TateS K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) W where
  toFun Q := ⟨fun n => levUniv W n ((Q : ∀ n, Lev K S W n) n), fun n => by
    change transLev K _ W n (levUniv W (n + 1) ((Q : ∀ n, Lev K S W n) (n + 1))) = _
    rw [← levUniv_transLev, Q.2 n]⟩
  map_add' Q R := Subtype.ext (funext fun n => map_add _ _ _)
  map_smul' a Q := TateS.ext' fun n =>
    (map_nsmul (WeierstrassCurve.Affine.Point.map (W' := W) (toKSUniv K S)) (resN n a) (Q.pt n) :)

omit [P.IsPrime] in
/-- `T_2E(K_S) → T_2E(K̄)` is injective. Kind: PROVED (tex 2780). -/
theorem tateUniv_injective : Function.Injective (tateUniv (S := S) W) := fun _ _ h =>
  Subtype.ext (funext fun n => levUniv_injective n
    (congrArg (fun T : TateS K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) W =>
      (T : ∀ n, Lev K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) W n) n) h))

omit [P.IsPrime] in
/-- **`T_2E` (over `K_S`) is a finitely generated `ℤ₂`-module for every `S`**: it embeds into
`T_2E` over `K̄`, which is free of rank two (`hasFullTwoTorsion_univ`, `finite_tate`), and `ℤ₂`
is Noetherian. No `HasFullTwoTorsion` hypothesis. Kind: PROVED (tex 2780). -/
theorem tate_fg [W.IsElliptic] : (⊤ : Submodule ℤ_[2] (TateS K S W)).FG :=
  haveI : Module.Finite ℤ_[2] (TateS K S W) :=
    Module.Finite.of_injective (tateUniv W) tateUniv_injective
  Module.Finite.fg_top

/-- **(A), unconditional form: `V_𝔭` carries Nekovář's topology for every `S`** (no
`HasFullTwoTorsion`; Nekovář 3.3.1, 3.3.4, 3.7.2–3.7.3, pp. 79, 93). Kind: PROVED
(tex 4976–5200). -/
theorem isLatticeTop_vp' [IsHeightOneOdd P] [W.IsElliptic] :
    IsLatticeTop (GKS K S) (VP K S W P α) :=
  isLatticeTop_vp_of_fg P tate_fg

/-! ### (B) Bounded images and the `2`-adic topology of the lattice -/

/-- The sublattice-scaled module `{v | 2^N v ∈ latt} = 2^{−N} latt`. Kind: definition
(Nekovář 3.4.1.1, p. 82: the members `M_α` of `S(V_𝔭)` used below). -/
def lattScaled (N : ℕ) : Submodule Lambda (VP K S W P α) :=
  (latt K S W P α).comap (((2 : Lambda) ^ N) • LinearMap.id)

/-- Membership in `2^{−N} latt`. Kind: PROVED (definitional). -/
theorem mem_lattScaled {N : ℕ} {v : VP K S W P α} :
    v ∈ lattScaled P N ↔ ((2 : Lambda) ^ N) • v ∈ latt K S W P α :=
  Iff.rfl

/-- `latt` is a neighbourhood of zero (it is `fibNbhd 0`). Kind: PROVED. -/
theorem latt_mem_nhds : (latt K S W P α : Set (VP K S W P α)) ∈ 𝓝 (0 : VP K S W P α) := by
  refine Filter.mem_of_superset ((fib_hasBasis_nhds_zero P).mem_of_mem (i := 0) trivial) ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [pow_zero, one_smul]
  exact hy

/-- `2^{−N} latt` is an open subgroup of `V_𝔭` (it contains the open subgroup `latt`). Kind:
PROVED. -/
theorem isOpen_lattScaled (N : ℕ) :
    IsOpen (lattScaled (W := W) (α := α) P N : Set (VP K S W P α)) :=
  (lattScaled (W := W) (α := α) P N).toAddSubgroup.isOpen_of_mem_nhds
    (Filter.mem_of_superset (latt_mem_nhds P) fun _ hy => Submodule.smul_mem _ _ hy)

/-- The `2^{−N} latt` increase with `N`. Kind: PROVED. -/
theorem lattScaled_mono : Monotone (lattScaled (W := W) (α := α) P) := by
  intro a b h v hv
  rw [mem_lattScaled, ← Nat.add_sub_cancel' h, pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hv

/-- **(B): a continuous map from a compact space to `V_𝔭` has image in some `2^{−N} latt`**
(the open subgroups `2^{−N} latt` increase and cover `V_𝔭`). Kind: PROVED (Nekovář 3.4.1.1, p. 82;
tex 4976–5200). -/
theorem exists_two_pow_smul_mem_latt_of_continuous [IsHeightOneOdd P] {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (f : X → VP K S W P α) (hf : Continuous f) :
    ∃ N : ℕ, ∀ x, ((2 : Lambda) ^ N) • f x ∈ latt K S W P α := by
  obtain ⟨N, hN⟩ := isCompact_univ.elim_directed_cover
    (fun N => f ⁻¹' (lattScaled (W := W) (α := α) P N : Set (VP K S W P α)))
    (fun N => (isOpen_lattScaled P N).preimage hf)
    (fun x _ => Set.mem_iUnion.mpr (exists_two_pow_smul_mem_latt P (f x)))
    (Monotone.directed_le fun a b h => Set.preimage_mono (lattScaled_mono P h))
  exact ⟨N, fun x => hN (Set.mem_univ x)⟩

/-- **Continuity into `V_𝔭`, after scaling by `2^N`**: `f` is continuous iff for every `m` the
differences `2^N (f y − f x)` lie in `2^m latt` for `y` near `x`. Kind: PROVED. -/
theorem continuous_iff_eventually_two_pow [IsHeightOneOdd P] {X : Type*} [TopologicalSpace X]
    (f : X → VP K S W P α) (N : ℕ) :
    Continuous f ↔ ∀ x (m : ℕ), ∀ᶠ y in 𝓝 x,
      ((2 : Lambda) ^ N) • (f y - f x) ∈ fibNbhd K S W P α m := by
  have key : ∀ (u : VP K S W P α) (m : ℕ),
      ((2 : Lambda) ^ N) • u ∈ fibNbhd K S W P α (m + N) ↔ u ∈ fibNbhd K S W P α m := by
    intro u m
    constructor
    · intro hu
      obtain ⟨z, hz, hzu⟩ := (mem_fibNbhd P).mp hu
      have e : u = ((2 : Lambda) ^ m) • z := by
        apply two_pow_smul_injective P N
        change ((2 : Lambda) ^ N) • u = ((2 : Lambda) ^ N) • (((2 : Lambda) ^ m) • z)
        rw [← hzu, smul_smul, ← pow_add, add_comm]
      rw [e]
      exact two_pow_smul_mem_fibNbhd P hz
    · intro hu
      obtain ⟨z, hz, rfl⟩ := (mem_fibNbhd P).mp hu
      rw [smul_smul, ← pow_add, add_comm]
      exact two_pow_smul_mem_fibNbhd P hz
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun x => ?_
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, (fib_hasBasis_nhds_zero P).tendsto_right_iff]
  constructor
  · intro h m
    filter_upwards [h m trivial] with y hy
    exact fibNbhd_antitone P (Nat.le_add_right m N) ((key _ m).mpr hy)
  · intro h m _
    filter_upwards [h (m + N)] with y hy
    exact (key _ m).mp hy

/-! #### The finite levels `latt / 2^m latt` -/

/-- `2^m latt` as a submodule of `latt`. Kind: definition. -/
def lattLevel (m : ℕ) : Submodule Lambda (latt K S W P α) :=
  ((2 : Lambda) ^ m) • (⊤ : Submodule Lambda (latt K S W P α))

/-- Membership in `2^m latt ⊆ latt` is membership of the underlying vector in `fibNbhd m`.
Kind: PROVED. -/
theorem mem_lattLevel {m : ℕ} {y : latt K S W P α} :
    y ∈ lattLevel P m ↔ (y : VP K S W P α) ∈ fibNbhd K S W P α m := by
  rw [lattLevel, Submodule.mem_smul_pointwise_iff_exists, mem_fibNbhd]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨⟨z, hz⟩, Submodule.mem_top, Subtype.ext h⟩

/-- `2^{m+1} latt ⊆ 2^m latt`. Kind: PROVED. -/
theorem lattLevel_succ_le (m : ℕ) :
    lattLevel (W := W) (α := α) P (m + 1) ≤ lattLevel P m := fun _ hy =>
  (mem_lattLevel P).mpr (fibNbhd_antitone P (Nat.le_succ m) ((mem_lattLevel P).mp hy))

/-- **The finite level `latt / 2^m latt`** (Nekovář 3.4.1.1: the `𝔪`-adic, here `2`-adic,
quotients of the lattice; tex 4976–5200), as a type synonym. Kind: definition. -/
def LattQuot (m : ℕ) : Type := latt K S W P α ⧸ lattLevel P m

/-- Equality in `latt/2^m latt`. Kind: PROVED. -/
theorem lattQuot_mk_eq_iff {m : ℕ} (y z : latt K S W P α) :
    (show LattQuot (W := W) (α := α) P m from Submodule.Quotient.mk (p := lattLevel P m) y) =
        (show LattQuot (W := W) (α := α) P m from Submodule.Quotient.mk (p := lattLevel P m) z) ↔
      (y : VP K S W P α) - z ∈ fibNbhd K S W P α m :=
  (Submodule.Quotient.eq (lattLevel P m)).trans (mem_lattLevel P)

/-- **`(latt/2^m latt, 2^N f mod 2^m)` for a map with values in `2^{−N} latt`.** Kind:
definition. -/
def reduceMod {X : Type*} (f : X → VP K S W P α) (N : ℕ)
    (hN : ∀ x, ((2 : Lambda) ^ N) • f x ∈ latt K S W P α) (m : ℕ) (x : X) :
    LattQuot (W := W) (α := α) P m :=
  Submodule.Quotient.mk (p := lattLevel P m) ⟨((2 : Lambda) ^ N) • f x, hN x⟩

/-- **(B), converse direction, in Nekovář's form** (3.4.1.1, p. 82): for `f` with values in
`2^{−N} latt`, `f` is continuous into `V_𝔭` iff every reduction `x ↦ 2^N f(x) mod 2^m latt` is
locally constant, i.e. iff `2^N f : X → latt` is continuous for the `2`-adic topology of `latt`
(the inverse-limit topology of the discrete `latt/2^m latt`; for `R = Λ/𝔭` finite over `ℤ₂` this is
the `𝔪`-adic topology). The subspace topology of `2^{−N} latt ⊆ V_𝔭` is thereby the `2`-adic
one. Kind: PROVED (tex 4976–5200). -/
theorem continuous_iff_isLocallyConstant_mod [IsHeightOneOdd P] {X : Type*} [TopologicalSpace X]
    (f : X → VP K S W P α) (N : ℕ) (hN : ∀ x, ((2 : Lambda) ^ N) • f x ∈ latt K S W P α) :
    Continuous f ↔ ∀ m : ℕ, IsLocallyConstant (reduceMod P f N hN m) := by
  rw [continuous_iff_eventually_two_pow P f N, forall_comm]
  refine forall_congr' fun m => ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  refine forall_congr' fun x => ?_
  refine Filter.eventually_congr (Eventually.of_forall fun y => ?_)
  rw [reduceMod, reduceMod, lattQuot_mk_eq_iff, smul_sub]

/-- **Continuous maps from a compact space to `V_𝔭` are Nekovář's** (3.4.1.1, p. 82):
`f` is continuous iff for some `N` it takes values in `2^{−N} latt` and `2^N f` is continuous for
the `2`-adic topology of `latt`. Kind: PROVED (tex 4976–5200). -/
theorem continuous_iff_exists_lattice [IsHeightOneOdd P] {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : X → VP K S W P α) :
    Continuous f ↔ ∃ (N : ℕ) (hN : ∀ x, ((2 : Lambda) ^ N) • f x ∈ latt K S W P α),
      ∀ m : ℕ, IsLocallyConstant (reduceMod P f N hN m) := by
  constructor
  · intro hf
    obtain ⟨N, hN⟩ := exists_two_pow_smul_mem_latt_of_continuous P f hf
    exact ⟨N, hN, (continuous_iff_isLocallyConstant_mod P f N hN).mp hf⟩
  · rintro ⟨N, hN, h⟩
    exact (continuous_iff_isLocallyConstant_mod P f N hN).mpr h

/-! #### The cochain form for `G_{K,S}` and `G_{K_v}` -/

/-- `K_S/K` is Galois (normal by construction, `normal_unramifiedOutside`; separable in
characteristic zero). Kind: PROVED. -/
instance isGalois_unramifiedOutside : IsGalois K (unramifiedOutside K S) := IsGalois.mk

/-- **`G_{K,S}` is compact** (profinite; Mathlib's compactness of `Gal(L/K)` for `L/K` Galois).
Kind: PROVED. -/
instance compactSpace_GKS : CompactSpace (GKS K S) :=
  inferInstanceAs (CompactSpace (unramifiedOutside K S ≃ₐ[K] unramifiedOutside K S))

/-- **`G_{K_v}` is compact** (Mathlib: the absolute Galois group of a field is profinite). Kind:
PROVED. -/
theorem compactSpace_Gloc (v : HeightOneSpectrum (𝓞 K)) : CompactSpace (Gloc K v) :=
  inferInstance

/-- **(B), cochain form for `G_{K,S}`: a continuous `n`-cochain with values in `V_𝔭` takes values
in some `2^{−N} latt`** (`G_{K,S}^n` is compact). Kind: PROVED (Nekovář 3.4.1.1, p. 82). -/
theorem contCochain_bounded [IsHeightOneOdd P] (n : ℕ) (f : (Fin n → GKS K S) → VP K S W P α)
    (hf : Continuous f) : ∃ N : ℕ, ∀ g, ((2 : Lambda) ^ N) • f g ∈ latt K S W P α :=
  exists_two_pow_smul_mem_latt_of_continuous P f hf

/-- **(B), cochain form for `G_{K_v}`** acting on `V_𝔭` through `p_v = locMap K S v`: a continuous
`n`-cochain takes values in some `2^{−N} latt`. Kind: PROVED (Nekovář 3.4.1.1, p. 82). -/
theorem contCochain_bounded_loc [IsHeightOneOdd P] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (f : (Fin n → Gloc K v) → ResMod (locMap K S v) (VP K S W P α)) (hf : Continuous f) :
    ∃ N : ℕ, ∀ g, ((2 : Lambda) ^ N) • (show VP K S W P α from f g) ∈ latt K S W P α :=
  exists_two_pow_smul_mem_latt_of_continuous (X := Fin n → Gloc K v) P f hf

/-- **Lane RC26's continuous cochains of `G_{K,S}` with values in `V_𝔭` are Nekovář's**
(3.4.1.1, p. 82: `C^n_cont(G, M) = lim→_{M_α ∈ S(M)} C^n_cont(G, M_α)`, `M_α = 2^{−N} latt` with its
`𝔪`-adic = `2`-adic topology): a cochain is continuous iff it takes values in some `2^{−N} latt`
and all its reductions mod `2^m latt` are locally constant. This is the cochain-level
localization `C_cont(G_{K,S}, V_𝔭) = ⋃_N 2^{−N} C_cont(G_{K,S}, latt)` (Nekovář 3.7.4(ii), p. 94,
at cochain level). Kind: PROVED (tex 4976–5200). -/
theorem mem_contCochain_iff [IsHeightOneOdd P] (n : ℕ)
    (c : (groupCohomology.inhomogeneousCochains
      (rep (ResAt P) (GKS K S) (VP K S W P α))).X n) :
    c ∈ contCochain (ResAt P) (GKS K S) (VP K S W P α) n ↔
      ∃ (N : ℕ) (hN : ∀ g, ((2 : Lambda) ^ N) •
          asFun (ResAt P) (GKS K S) (VP K S W P α) c g ∈ latt K S W P α),
        ∀ m : ℕ,
          IsLocallyConstant (reduceMod P (asFun (ResAt P) (GKS K S) (VP K S W P α) c) N hN m) :=
  continuous_iff_exists_lattice P _

/-- **The same for `G_{K_v}`** acting through `p_v`: lane RC26's local continuous cochains with
values in `V_𝔭` are Nekovář's (3.4.1.1, p. 82). Kind: PROVED (tex 4976–5200). -/
theorem mem_contCochain_loc_iff [IsHeightOneOdd P] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (c : (groupCohomology.inhomogeneousCochains
      (rep (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)))).X n) :
    c ∈ contCochain (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)) n ↔
      ∃ (N : ℕ) (hN : ∀ g, ((2 : Lambda) ^ N) • (show VP K S W P α from
          asFun (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)) c g) ∈
            latt K S W P α),
        ∀ m : ℕ, IsLocallyConstant (reduceMod P (fun g => show VP K S W P α from
          asFun (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)) c g) N hN m) :=
  continuous_iff_exists_lattice (X := Fin n → Gloc K v) P _

/-! ### The finite levels as discrete `G_{K,S}`-modules -/

/-- The additive group `latt/2^m latt`. Kind: definition. -/
instance lattQuot_addCommGroup (m : ℕ) : AddCommGroup (LattQuot (W := W) (α := α) P m) :=
  inferInstanceAs (AddCommGroup (latt K S W P α ⧸ lattLevel P m))

/-- The `Λ`-module `latt/2^m latt`. Kind: definition. -/
instance lattQuot_module (m : ℕ) : Module Lambda (LattQuot (W := W) (α := α) P m) :=
  inferInstanceAs (Module Lambda (latt K S W P α ⧸ lattLevel P m))

/-- The discrete topology on the finite level. Kind: definition. -/
instance lattQuot_top (m : ℕ) : TopologicalSpace (LattQuot (W := W) (α := α) P m) := ⊥

/-- The finite level is discrete. Kind: PROVED. -/
instance lattQuot_discrete (m : ℕ) : DiscreteTopology (LattQuot (W := W) (α := α) P m) := ⟨rfl⟩

/-- The Galois action restricted to the lattice, `Λ`-linear. Kind: definition. -/
def lattAct (σ : GKS K S) : latt K S W P α →ₗ[Lambda] latt K S W P α where
  toFun y := ⟨σ • (y : VP K S W P α), smul_mem_latt P σ y.2⟩
  map_add' y z := Subtype.ext (smul_add σ (y : VP K S W P α) z)
  map_smul' l y := Subtype.ext (VP.smul_lambda_comm P σ l (y : VP K S W P α))

/-- The Galois action preserves `2^m latt`. Kind: PROVED. -/
theorem lattLevel_le_comap (σ : GKS K S) (m : ℕ) :
    lattLevel (W := W) (α := α) P m ≤ (lattLevel P m).comap (lattAct P σ) := fun _ hy =>
  (mem_lattLevel P).mpr (smul_mem_fibNbhd P σ m ((mem_lattLevel P).mp hy))

/-- The Galois action on `latt/2^m latt`. Kind: definition. -/
def quotAct (m : ℕ) (σ : GKS K S) :
    LattQuot (W := W) (α := α) P m →ₗ[Lambda] LattQuot (W := W) (α := α) P m :=
  Submodule.mapQ (lattLevel P m) (lattLevel P m) (lattAct P σ) (lattLevel_le_comap P σ m)

/-- The action on classes. Kind: PROVED (definitional). -/
theorem quotAct_mk (m : ℕ) (σ : GKS K S) (y : latt K S W P α) :
    quotAct P m σ (Submodule.Quotient.mk (p := lattLevel P m) y) =
      Submodule.Quotient.mk (p := lattLevel P m) (lattAct P σ y) :=
  rfl

/-- **The Galois action on the finite level `latt/2^m latt`.** Kind: definition (PROVED to be an
action). -/
instance lattQuot_distribMulAction (m : ℕ) :
    DistribMulAction (GKS K S) (LattQuot (W := W) (α := α) P m) where
  smul σ x := quotAct P m σ x
  one_smul x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change quotAct P m 1 _ = _
    rw [quotAct_mk]
    exact congrArg _ (Subtype.ext (one_smul _ (y : VP K S W P α)))
  mul_smul σ τ x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change quotAct P m (σ * τ) _ = quotAct P m σ (quotAct P m τ _)
    rw [quotAct_mk, quotAct_mk, quotAct_mk]
    exact congrArg _ (Subtype.ext (mul_smul σ τ (y : VP K S W P α)))
  smul_zero σ := map_zero (quotAct P m σ)
  smul_add σ := map_add (quotAct P m σ)

/-- The Galois action on classes in `latt/2^m latt`. Kind: PROVED (definitional). -/
theorem lattQuot_smul_mk (m : ℕ) (σ : GKS K S) (y : latt K S W P α) :
    σ • (show LattQuot (W := W) (α := α) P m from Submodule.Quotient.mk (p := lattLevel P m) y) =
      show LattQuot (W := W) (α := α) P m from
        Submodule.Quotient.mk (p := lattLevel P m) (lattAct P σ y) :=
  rfl

/-- The Galois action on `latt/2^m latt` is `Λ`-linear. Kind: PROVED. -/
instance lattQuot_smulCommClass (m : ℕ) :
    SMulCommClass (GKS K S) Lambda (LattQuot (W := W) (α := α) P m) where
  smul_comm σ l x := (quotAct P m σ).map_smul l x

/-- **The Galois action on the discrete level `latt/2^m latt` is continuous** (stabilizers are
open: lane RC28's `eventually_latt`). Kind: PROVED. -/
instance lattQuot_continuousSMul [IsHeightOneOdd P] [IsContChar α] (m : ℕ) :
    ContinuousSMul (GKS K S) (LattQuot (W := W) (α := α) P m) := by
  refine ⟨continuous_prod_of_discrete_right.mpr fun x => ?_⟩
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun σ₀ => ?_)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← map_mul_left_nhds_one σ₀, eventually_map]
  filter_upwards [eventually_latt P α y.2 m] with τ hτ
  change (show LattQuot (W := W) (α := α) P m from _) = show LattQuot (W := W) (α := α) P m from _
  rw [lattQuot_smul_mk, lattQuot_smul_mk, lattQuot_mk_eq_iff]
  change (σ₀ * τ) • (y : VP K S W P α) - σ₀ • (y : VP K S W P α) ∈ fibNbhd K S W P α m
  rw [mul_smul, ← smul_sub]
  exact smul_mem_fibNbhd P σ₀ m hτ

/-- The transition map `latt/2^{m+1} latt → latt/2^m latt`. Kind: definition. -/
def lattTrans (m : ℕ) :
    LattQuot (W := W) (α := α) P (m + 1) →ₗ[Lambda] LattQuot (W := W) (α := α) P m :=
  Submodule.factor (lattLevel_succ_le P m)

/-- The transition map on classes. Kind: PROVED. -/
theorem lattTrans_mk (m : ℕ) (y : latt K S W P α) :
    lattTrans P m
        (show LattQuot (W := W) (α := α) P (m + 1) from
          Submodule.Quotient.mk (p := lattLevel P (m + 1)) y) =
      show LattQuot (W := W) (α := α) P m from Submodule.Quotient.mk (p := lattLevel P m) y :=
  Submodule.factor_mk (lattLevel_succ_le P m) y

/-- The transition maps are Galois equivariant. Kind: PROVED. -/
theorem lattTrans_smul (m : ℕ) (σ : GKS K S) (x : LattQuot (W := W) (α := α) P (m + 1)) :
    lattTrans P m (σ • x) = σ • lattTrans P m x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [lattQuot_smul_mk, lattTrans_mk, lattTrans_mk, lattQuot_smul_mk]

/-! ### (C) The comparison with the finite levels (PRINT) -/

variable [IsHeightOneOdd P] [IsContChar α]

/-- The transition maps on continuous cohomology
`H^i(H, latt/2^{m+1} latt) → H^i(H, latt/2^m latt)` for `H` acting through `φ : H → G_{K,S}`.
Kind: definition. -/
abbrev levelTransH {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →ₜ* GKS K S) (i m : ℕ) :
    contCohomology Lambda H (ResMod φ (LattQuot (W := W) (α := α) P (m + 1))) i ⟶
      contCohomology Lambda H (ResMod φ (LattQuot (W := W) (α := α) P m)) i :=
  contCohomologyMap (ContinuousMonoidHom.id H)
    (show ResMod φ (LattQuot (W := W) (α := α) P (m + 1)) →ₗ[Lambda]
        ResMod φ (LattQuot (W := W) (α := α) P m) from
      lattTrans P m)
    continuous_of_discreteTopology (fun h x => lattTrans_smul P m (φ h) x) i

/-- **`lim_m H^i(H, latt/2^m latt)`**, as the `Λ`-submodule of compatible families of
`∏_m H^i(H, latt/2^m latt)`, for `H` acting through `φ : H → G_{K,S}` (`H = G_{K,S}`, `φ = id`;
`H = G_{K_v}`, `φ = p_v`). Kind: definition (Nekovář 4.1.2–4.1.3, pp. 95–96; Jannsen 1988,
(2.1)). -/
def towerLim {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →ₜ* GKS K S) (i : ℕ) :
    Submodule Lambda
      (∀ m : ℕ, contCohomology Lambda H (ResMod φ (LattQuot (W := W) (α := α) P m)) i) :=
  ⨅ m : ℕ, LinearMap.ker
    ((levelTransH P φ i m).hom ∘ₗ
        LinearMap.proj (R := Lambda)
          (φ := fun m : ℕ => contCohomology Lambda H (ResMod φ (LattQuot (W := W) (α := α) P m)) i)
          (m + 1) -
      LinearMap.proj (R := Lambda)
        (φ := fun m : ℕ => contCohomology Lambda H (ResMod φ (LattQuot (W := W) (α := α) P m)) i) m)

end Fibre

variable (K : Type) [Field K] [NumberField K]

/-- **PRINT — Nekovář, *Selmer complexes* (Astérisque 310, 2006), 3.7.4(ii) (p. 94) with 4.2.2
(p. 96) and 5.1.1 (p. 113): the comparison for the fibres.** For a height-one prime `𝔭 ≠ (2)` of
`Λ`, `S` finite containing the primes above `2`, an elliptic `W`, a continuous `Λ`-adic character
`α` and every degree `i`, there are `k(𝔭)`-linear isomorphisms
`H^i_cont(G, V_𝔭) ≅ k(𝔭) ⊗_Λ lim_m H^i(G, latt/2^m latt)` for `G = G_{K,S}` (acting through the
identity; `ResMod id` is definitionally `V_𝔭` with its action) and for `G = G_{K_v}` (acting
through `p_v`). The left sides are lane RC26's continuous cohomology with values in lane RC28's
`V_𝔭` (natural topology); the right sides are built from the finite discrete levels `LattQuot`.

Printed statements used (with `R = Λ/𝔭`, `𝒮 = R ∖ {0}`, `R_𝒮 = k(𝔭)`, `T = latt`; the `𝔪`-adic
and `2`-adic filtrations of `latt` are cofinal since `R` is finite over `ℤ₂`):
* 3.7.4(ii), p. 94: "If `M ∈ D⁺(ind-ad R[G]Mod)`, then the canonical map
  `𝒮⁻¹RΓ_cont(G, M) → RΓ_cont(G, 𝒮⁻¹M)` is an isomorphism in `D⁺(R_𝒮 Mod)`" (here `𝒮⁻¹ latt = V_𝔭`,
  `isLatticeTop_vp'`; at cochain level `mem_contCochain_iff`, `mem_contCochain_loc_iff`, PROVED);
* 4.1.2, p. 95: `C•_cont(G, T) → lim←_n C•_cont(G, T/𝔪ⁿT)` is an isomorphism of complexes;
  4.1.3, p. 96: `0 → lim←^(1) H^{i−1}(G, T/𝔪ⁿT) → H^i_cont(G, T) → lim← H^i(G, T/𝔪ⁿT) → 0`;
* 4.2.1–4.2.2, p. 96: condition (F) (finite length of `H^i(G, M)` for discrete `M` of finite
  length), and "(F′) ⟺ (F) ⟹ `H^i_cont(G, T) ≅ lim← H^i(G, T/𝔪ⁿT)` (∀ i ≥ 0)";
* 5.1.1, p. 113: `G_v` and `G_{K,S}` satisfy (F′); 4.2.10, p. 100: `H^i_cont(G, V_𝔭)` is finite
  dimensional over `k(𝔭)`.
Secondary references: U. Jannsen, *Continuous étale cohomology*, Math. Ann. 280 (1988): (2.1)
(the `lim¹` sequence), Theorem (2.2) (continuous cohomology of the limit of a Mittag-Leffler
system), Definition (5.13) and Theorem (5.15)(c) (`⊗ ℚ_ℓ` coefficients); J. Tate, *Relations between
K₂ and Galois cohomology*, Invent. Math. 36 (1976), §2 (Propositions 2.2–2.3: UNVERIFIED, not
read).

Kind: PRINT (stated, not proved). DEPARTURE (form): an abstract `k(𝔭)`-linear isomorphism is
asserted; the printed one is the canonical composite of
`k(𝔭) ⊗_Λ H^i_cont(G, latt) → H^i_cont(G, V_𝔭)` (3.7.4(ii)) and
`H^i_cont(G, latt) → lim_m H^i(G, latt/2^m latt)` (4.2.2), and the `2`-power levels replace the
`𝔪`-power levels (cofinal filtrations). -/
def NekovarFibreComparison : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P],
    NekovarFibreSetting K S →
    ∀ (W : WeierstrassCurve K) [W.IsElliptic] (α : GKS K S →* Lambdaˣ) [IsContChar α] (i : ℕ),
      Nonempty (contCohomology (ResAt P) (GKS K S)
          (ResMod (ContinuousMonoidHom.id (GKS K S)) (VP K S W P α)) i ≃ₗ[ResAt P]
        ResAt P ⊗[Lambda] towerLim (W := W) (α := α) P (ContinuousMonoidHom.id (GKS K S)) i) ∧
      ∀ v : HeightOneSpectrum (𝓞 K),
        Nonempty (contCohomology (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)) i
          ≃ₗ[ResAt P] ResAt P ⊗[Lambda] towerLim (W := W) (α := α) P (locMap K S v) i)

end ZInQ.Manuscript.RC.FibreDuality
