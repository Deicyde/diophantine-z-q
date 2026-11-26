import Mathlib

/-! # Graded pieces of a filtered invariant space

Abstract linear algebra behind "de Rham implies Hodge–Tate, with matching multiplicities".

Data, over a field `K`: a `K`-vector space `B` with a decreasing, exhaustive, separated filtration
`F : ℤ → Submodule K B`, stable under linear maps `a σ` (`σ ∈ G`); a `K`-vector space `C` with
linear maps `c i σ`; `K`-linear maps `g i : F i → C` with kernel `F (i+1)`, intertwining `a σ`
with `c i σ`; a finite-dimensional `V` with linear maps `r σ`. Put
`D = (B ⊗ V)^G`, `Fil^i D = D ∩ (F i ⊗ V)`, and `H_i = (C ⊗ V)^G` (for the actions `c i σ ⊗ r σ`).

Then `g i ⊗ id` embeds `Fil^i D / Fil^{i+1} D` into `H_i` (`finrank_filD_le`). If moreover
`dim D = dim V` and `Σ_{i ∈ J} dim H_i ≤ dim V` for every finite `J` (with each `H_i` finite
dimensional), then `dim (Fil^i D / Fil^{i+1} D) = dim H_i` for every `i` (`finrank_grD_eq`).
-/

set_option autoImplicit false

namespace DeRhamHTMult

open Module TensorProduct

noncomputable section

section Graded

variable {K B C V G : Type*} [Field K] [AddCommGroup B] [Module K B] [AddCommGroup C]
  [Module K C] [AddCommGroup V] [Module K V]

/-- `(X ⊗ V)^G` for the actions `a σ ⊗ r σ`. -/
def invT {X : Type*} [AddCommGroup X] [Module K X] (a : G → X →ₗ[K] X)
    (r : G → V →ₗ[K] V) : Submodule K (X ⊗[K] V) where
  carrier := {x | ∀ σ, TensorProduct.map (a σ) (r σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' c x hx σ := by rw [map_smul, hx σ]

theorem mem_invT {X : Type*} [AddCommGroup X] [Module K X] (a : G → X →ₗ[K] X)
    (r : G → V →ₗ[K] V) (x : X ⊗[K] V) :
    x ∈ invT a r ↔ ∀ σ, TensorProduct.map (a σ) (r σ) x = x := Iff.rfl

variable (V) (F : ℤ → Submodule K B)

/-- `F^i B ⊗ V`, as a subspace of `B ⊗ V`. -/
def filT (i : ℤ) : Submodule K (B ⊗[K] V) := LinearMap.range ((F i).subtype.rTensor V)

theorem rTensor_subtype_injective (i : ℤ) :
    Function.Injective ((F i).subtype.rTensor V) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

theorem filT_anti (hF : Antitone F) {i j : ℤ} (hij : i ≤ j) : filT V F j ≤ filT V F i := by
  rintro x ⟨z, rfl⟩
  refine ⟨(Submodule.inclusion (hF hij)).rTensor V z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

theorem filT_exhaustive (hF : Antitone F) (hexh : ∀ b : B, ∃ i, b ∈ F i) (x : B ⊗[K] V) :
    ∃ i, x ∈ filT V F i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul b v =>
    obtain ⟨i, hi⟩ := hexh b
    exact ⟨i, ⟨(⟨b, hi⟩ : F i) ⊗ₜ v, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨min i j, Submodule.add_mem _ (filT_anti V F hF (min_le_left i j) hi)
      (filT_anti V F hF (min_le_right i j) hj)⟩

theorem equivFinsupp_rTensor {ι : Type*} [DecidableEq ι] (bV : Basis ι K V) {N : Type*}
    [AddCommGroup N] [Module K N] (f : N →ₗ[K] B) (z : N ⊗[K] V) :
    TensorProduct.equivFinsuppOfBasisRight bV (f.rTensor V z) =
      Finsupp.mapRange f f.map_zero (TensorProduct.equivFinsuppOfBasisRight bV z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    rw [LinearMap.rTensor_tmul, equivFinsuppOfBasisRight_apply_tmul,
      equivFinsuppOfBasisRight_apply_tmul]
    ext k
    simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, Finsupp.mapRange_add f.map_add]

theorem filT_separated (hsep : ∀ b : B, (∀ i, b ∈ F i) → b = 0) (x : B ⊗[K] V)
    (hx : ∀ i, x ∈ filT V F i) : x = 0 := by
  classical
  let bV := Basis.ofVectorSpace K V
  have hcoord : ∀ k, TensorProduct.equivFinsuppOfBasisRight bV x k = 0 := by
    intro k
    refine hsep _ fun i => ?_
    obtain ⟨z, hz⟩ := hx i
    rw [← hz, equivFinsupp_rTensor, Finsupp.mapRange_apply]
    exact SetLike.coe_mem _
  have : TensorProduct.equivFinsuppOfBasisRight bV x = 0 := Finsupp.ext hcoord
  simpa using this

variable {V}

/-- `Fil^i D = D ∩ (F^i B ⊗ V)`. -/
def filD (a : G → B →ₗ[K] B) (r : G → V →ₗ[K] V) (i : ℤ) : Submodule K (B ⊗[K] V) :=
  invT a r ⊓ filT V F i

theorem filD_anti (hF : Antitone F) (a : G → B →ₗ[K] B) (r : G → V →ₗ[K] V) {i j : ℤ}
    (hij : i ≤ j) : filD F a r j ≤ filD F a r i :=
  inf_le_inf_left _ (filT_anti V F hF hij)

/-- `gr^i D = Fil^i D / Fil^{i+1} D`. -/
abbrev grD (a : G → B →ₗ[K] B) (r : G → V →ₗ[K] V) (i : ℤ) : Type _ :=
  ↥(filD F a r i) ⧸ (filD F a r (i + 1)).comap (filD F a r i).subtype

variable (g : ∀ i, F i →ₗ[K] C)

/-- `g i ⊗ id` on `F^i B ⊗ V`, read on its image in `B ⊗ V`. -/
def grT (i : ℤ) : filT V F i →ₗ[K] C ⊗[K] V :=
  ((g i).rTensor V).comp
    (LinearEquiv.ofInjective _ (rTensor_subtype_injective V F i)).symm.toLinearMap

theorem grT_apply (i : ℤ) (z : F i ⊗[K] V) :
    grT F g i ⟨(F i).subtype.rTensor V z, z, rfl⟩ = (g i).rTensor V z := by
  show (g i).rTensor V ((LinearEquiv.ofInjective _ (rTensor_subtype_injective V F i)).symm
    (LinearEquiv.ofInjective _ (rTensor_subtype_injective V F i) z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The kernel of `g i ⊗ id` is `F^{i+1} B ⊗ V` (flatness of `V`). -/
theorem grT_eq_zero_iff (hF : Antitone F) (hex : ∀ i (x : F i), g i x = 0 ↔ (x : B) ∈ F (i + 1))
    (i : ℤ) (x : filT V F i) : grT F g i x = 0 ↔ (x : B ⊗[K] V) ∈ filT V F (i + 1) := by
  obtain ⟨_, z, rfl⟩ := x
  rw [grT_apply]
  let ι := Submodule.inclusion (hF (Int.le_add_one (le_refl i)) : F (i + 1) ≤ F i)
  have hexact : Function.Exact ι (g i) := by
    intro y
    rw [hex i y]
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y', rfl⟩
      exact y'.2
  have hexT := Module.Flat.rTensor_exact V hexact
  have hcomp : (F i).subtype.comp ι = (F (i + 1)).subtype := rfl
  rw [hexT z]
  constructor
  · rintro ⟨z', rfl⟩
    refine ⟨z', ?_⟩
    rw [← hcomp, LinearMap.rTensor_comp, LinearMap.comp_apply]
  · rintro ⟨z', hz'⟩
    refine ⟨z', rTensor_subtype_injective V F i ?_⟩
    change (F (i + 1)).subtype.rTensor V z' = (F i).subtype.rTensor V z at hz'
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp]
    exact hz'

variable (a : G → B →ₗ[K] B) (c : ℤ → G → C →ₗ[K] C) (r : G → V →ₗ[K] V)

theorem map_filT (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i) (i : ℤ) (σ : G)
    (z : F i ⊗[K] V) :
    TensorProduct.map (a σ) (r σ) ((F i).subtype.rTensor V z) =
      (F i).subtype.rTensor V (TensorProduct.map ((a σ).restrict (hFst i σ)) (r σ) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem mem_filT_map (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i) (i : ℤ) (σ : G)
    {x : B ⊗[K] V} (hx : x ∈ filT V F i) : TensorProduct.map (a σ) (r σ) x ∈ filT V F i := by
  obtain ⟨z, rfl⟩ := hx
  rw [map_filT F a r hFst]
  exact ⟨_, rfl⟩

theorem rTensor_map_restrict (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x))
    (i : ℤ) (σ : G) (z : F i ⊗[K] V) :
    (g i).rTensor V (TensorProduct.map ((a σ).restrict (hFst i σ)) (r σ) z) =
      TensorProduct.map (c i σ) (r σ) ((g i).rTensor V z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact hgeq i σ m _
  | add x y hx hy => simp only [map_add, hx, hy]

theorem grT_map (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x))
    (i : ℤ) (σ : G) (x : filT V F i) :
    grT F g i ⟨TensorProduct.map (a σ) (r σ) x, mem_filT_map F a r hFst i σ x.2⟩ =
      TensorProduct.map (c i σ) (r σ) (grT F g i x) := by
  obtain ⟨_, z, rfl⟩ := x
  have e : (⟨TensorProduct.map (a σ) (r σ) ((F i).subtype.rTensor V z),
      mem_filT_map F a r hFst i σ ⟨z, rfl⟩⟩ : filT V F i) =
      ⟨(F i).subtype.rTensor V (TensorProduct.map ((a σ).restrict (hFst i σ)) (r σ) z), _, rfl⟩ :=
    Subtype.ext (map_filT F a r hFst i σ z)
  rw [e, grT_apply, grT_apply, rTensor_map_restrict F g a c r hFst hgeq]

/-- `g i ⊗ id : Fil^i D → H_i`. -/
def grDMap (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x)) (i : ℤ) :
    filD F a r i →ₗ[K] invT (c i) r where
  toFun x := ⟨grT F g i ⟨x, x.2.2⟩, fun σ => by
    rw [← grT_map F g a c r hFst hgeq i σ ⟨x, x.2.2⟩]
    congr 2
    exact x.2.1 σ⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [← map_add]
    rfl
  map_smul' t x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [← map_smul]
    rfl

theorem ker_grDMap (hF : Antitone F) (hex : ∀ i (x : F i), g i x = 0 ↔ (x : B) ∈ F (i + 1))
    (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x)) (i : ℤ) :
    LinearMap.ker (grDMap F g a c r hFst hgeq i) =
      (filD F a r (i + 1)).comap (filD F a r i).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    have h' : grT F g i ⟨(x : B ⊗[K] V), x.2.2⟩ = 0 := by
      have := congrArg Subtype.val h
      exact this
    exact ⟨x.2.1, (grT_eq_zero_iff F g hF hex i ⟨(x : B ⊗[K] V), x.2.2⟩).mp h'⟩
  · intro h
    apply Subtype.ext
    exact (grT_eq_zero_iff F g hF hex i ⟨(x : B ⊗[K] V), x.2.2⟩).mpr h.2

theorem finrank_comap_filD (hF : Antitone F) (i : ℤ) :
    finrank K ((filD F a r (i + 1)).comap (filD F a r i).subtype) =
      finrank K (filD F a r (i + 1)) :=
  (Submodule.comapSubtypeEquivOfLe (filD_anti F hF a r (Int.le_add_one (le_refl i)))).finrank_eq

/-- `dim gr^i D + dim Fil^{i+1} D = dim Fil^i D`. -/
theorem finrank_grD_add (hF : Antitone F) [FiniteDimensional K (invT a r)] (i : ℤ) :
    finrank K (grD F a r i) + finrank K (filD F a r (i + 1)) = finrank K (filD F a r i) := by
  haveI : FiniteDimensional K (filD F a r i) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [← finrank_comap_filD F a r hF i]
  exact Submodule.finrank_quotient_add_finrank _

/-- **`gr^i D` embeds in `H_i`.** -/
theorem finrank_grD_le (hF : Antitone F) (hex : ∀ i (x : F i), g i x = 0 ↔ (x : B) ∈ F (i + 1))
    (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x))
    [FiniteDimensional K (invT a r)] (i : ℤ) [FiniteDimensional K (invT (c i) r)] :
    finrank K (grD F a r i) ≤ finrank K (invT (c i) r) := by
  haveI : FiniteDimensional K (filD F a r i) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h1 := LinearMap.finrank_range_add_finrank_ker (grDMap F g a c r hFst hgeq i)
  rw [ker_grDMap F g a c r hF hex hFst hgeq, finrank_comap_filD F a r hF i] at h1
  have h2 := finrank_grD_add F a r hF i
  have h3 := Submodule.finrank_le (LinearMap.range (grDMap F g a c r hFst hgeq i))
  omega

theorem finiteDimensional_invT [FiniteDimensional K V] (hdR : finrank K (invT a r) = finrank K V) :
    FiniteDimensional K (invT a r) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · let bV := Module.finBasis K V
    have hsub : Subsingleton (B ⊗[K] V) := by
      have e := TensorProduct.equivFinsuppOfBasisRight (M := B) bV
      rw [h0] at e
      exact e.toEquiv.subsingleton
    haveI : Subsingleton (invT a r) := inferInstance
    haveI : Finite (invT a r) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · exact Module.finite_of_finrank_pos (hdR ▸ hpos)

theorem exists_eq_sInf (f : ℤ → ℕ) : ∃ b, f b = sInf (Set.range f) :=
  Nat.sInf_mem (Set.range_nonempty f)

/-- **Graded pieces of `D` have the dimensions of the `H_i`.** -/
theorem finrank_grD_eq [FiniteDimensional K V] (hF : Antitone F)
    (hexh : ∀ b : B, ∃ i, b ∈ F i) (hsep : ∀ b : B, (∀ i, b ∈ F i) → b = 0)
    (hex : ∀ i (x : F i), g i x = 0 ↔ (x : B) ∈ F (i + 1))
    (hFst : ∀ i σ (x : B), x ∈ F i → a σ x ∈ F i)
    (hgeq : ∀ i σ (x : F i) (hx : a σ x ∈ F i), g i ⟨a σ x, hx⟩ = c i σ (g i x))
    (hHfin : ∀ i, FiniteDimensional K (invT (c i) r))
    (hHsum : ∀ J : Finset ℤ, ∑ i ∈ J, finrank K (invT (c i) r) ≤ finrank K V)
    (hdR : finrank K (invT a r) = finrank K V) (i₀ : ℤ) :
    finrank K (grD F a r i₀) = finrank K (invT (c i₀) r) := by
  classical
  haveI := finiteDimensional_invT a r hdR
  set D := invT a r
  set S := filD F a r
  set f : ℤ → ℕ := fun i => finrank K (S i)
  set gg : ℤ → ℕ := fun i => finrank K (grD F a r i)
  set h : ℤ → ℕ := fun i => finrank K (invT (c i) r)
  have hS_le : ∀ i, S i ≤ D := fun i => inf_le_left
  haveI hSfin : ∀ i, FiniteDimensional K (S i) := fun i =>
    Submodule.finiteDimensional_of_le (hS_le i)
  have hgg : ∀ i, gg i + f (i + 1) = f i := fun i => finrank_grD_add F a r hF i
  have hgh : ∀ i, gg i ≤ h i := fun i => by
    haveI := hHfin i
    exact finrank_grD_le F g a c r hF hex hFst hgeq i
  have hSanti : ∀ {i j : ℤ}, i ≤ j → S j ≤ S i := fun hij => filD_anti F hF a r hij
  have hfanti : ∀ {i j : ℤ}, i ≤ j → f j ≤ f i := fun hij => Submodule.finrank_mono (hSanti hij)
  have hf_le : ∀ i, f i ≤ finrank K D := fun i => Submodule.finrank_mono (hS_le i)
  -- `S b = ⊥` for some `b`
  obtain ⟨b, hb⟩ : ∃ b, S b = ⊥ := by
    obtain ⟨b, hb⟩ := exists_eq_sInf f
    have hconst : ∀ i, b ≤ i → S i = S b := fun i hi =>
      Submodule.eq_of_le_of_finrank_eq (hSanti hi)
        (le_antisymm (hfanti hi) (by show f b ≤ f i; rw [hb]; exact Nat.sInf_le ⟨i, rfl⟩))
    refine ⟨b, eq_bot_iff.mpr fun x hx => ?_⟩
    rw [Submodule.mem_bot]
    refine filT_separated V F hsep x fun i => ?_
    rcases le_total b i with hbi | hib
    · rw [← hconst i hbi] at hx
      exact hx.2
    · exact (hSanti hib hx).2
  -- `S a = D` for some `a`
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, S a₀ = D := by
    have hbdd : BddAbove (Set.range f) := ⟨finrank K D, by rintro _ ⟨i, rfl⟩; exact hf_le i⟩
    obtain ⟨a₀, ha₀⟩ := Nat.sSup_mem (Set.range_nonempty f) hbdd
    have hconst : ∀ i, i ≤ a₀ → S i = S a₀ := fun i hi =>
      (Submodule.eq_of_le_of_finrank_eq (hSanti hi)
        (le_antisymm (hfanti hi)
          (by show f i ≤ f a₀; rw [ha₀]; exact le_csSup hbdd ⟨i, rfl⟩))).symm
    refine ⟨a₀, le_antisymm (hS_le a₀) fun x hx => ?_⟩
    obtain ⟨j, hj⟩ := filT_exhaustive V F hF hexh x
    have hx' : x ∈ S (min j a₀) := ⟨hx, filT_anti V F hF (min_le_left j a₀) hj⟩
    rwa [hconst _ (min_le_right j a₀)] at hx'
  -- normalize `a ≤ b`
  set a := min a₀ b
  have ha : S a = D := le_antisymm (hS_le a) (ha₀ ▸ hSanti (min_le_left a₀ b))
  have hab : a ≤ b := min_le_right a₀ b
  set N := (b - a).toNat
  have hbN : a + N = b := by omega
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range m, gg (a + k) + f (a + m) = f a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_assoc, Nat.cast_succ, ← add_assoc a, hgg, ih]
  have hfa : f a = finrank K V := by
    simp only [f]
    rw [ha]
    exact hdR
  have hfb : f (a + N) = 0 := by
    simp only [f]
    rw [hbN, hb, finrank_bot]
  have hsumg : ∑ k ∈ Finset.range N, gg (a + k) = finrank K V := by
    have := htel N
    rw [hfb, add_zero, hfa] at this
    exact this
  let emb : ℕ ↪ ℤ := ⟨fun k => a + k, fun k k' e => by simpa using e⟩
  let J := (Finset.range N).map emb
  have hsumh : ∑ k ∈ Finset.range N, h (a + k) ≤ finrank K V := by
    have := hHsum J
    rwa [Finset.sum_map] at this
  have hgh_sum : ∑ k ∈ Finset.range N, gg (a + k) = ∑ k ∈ Finset.range N, h (a + k) :=
    le_antisymm (Finset.sum_le_sum fun k _ => hgh _) (hsumg ▸ hsumh)
  have heq := (Finset.sum_eq_sum_iff_of_le (fun (k : ℕ) _ => hgh (a + (k : ℤ)))).mp hgh_sum
  by_cases hin : a ≤ i₀ ∧ i₀ < b
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, i₀ = a + k := ⟨(i₀ - a).toNat, by omega⟩
    have hkN : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have := heq k hkN
    simp only [gg, h] at this
    rw [hk]
    exact this
  · -- outside `[a, b)` the graded piece is `0`, and so is `H_{i₀}`
    have hg0 : gg i₀ = 0 := by
      have hS : S i₀ = S (i₀ + 1) := by
        rcases not_and_or.mp hin with h1 | h1
        · push Not at h1
          have e1 : S i₀ = D := le_antisymm (hS_le _) (ha ▸ hSanti h1.le)
          have e2 : S (i₀ + 1) = D := le_antisymm (hS_le _) (ha ▸ hSanti (by omega))
          rw [e1, e2]
        · push Not at h1
          have e1 : S i₀ = ⊥ := eq_bot_iff.mpr (hb ▸ hSanti h1)
          have e2 : S (i₀ + 1) = ⊥ := eq_bot_iff.mpr (hb ▸ hSanti (by omega))
          rw [e1, e2]
      have := hgg i₀
      simp only [f] at this
      rw [hS] at this
      omega
    have hnot : i₀ ∉ J := by
      intro hmem
      obtain ⟨k, hk, hke⟩ := Finset.mem_map.mp hmem
      have hk' := Finset.mem_range.mp hk
      have hke' : a + (k : ℤ) = i₀ := hke
      exact hin ⟨by omega, by omega⟩
    have hH := hHsum (insert i₀ J)
    rw [Finset.sum_insert hnot, Finset.sum_map] at hH
    have e : ∑ x ∈ Finset.range N, h (emb x) = ∑ k ∈ Finset.range N, h (a + k) := rfl
    have h0 : h i₀ = 0 := by
      have h1 : finrank K V ≤ ∑ k ∈ Finset.range N, h (a + k) := hsumg ▸ hgh_sum ▸ le_refl _
      have h2 : h i₀ + ∑ k ∈ Finset.range N, h (a + k) ≤ finrank K V := by
        rw [← e]; exact hH
      omega
    simp only [gg, h] at hg0 h0
    rw [hg0, h0]

end Graded

end

end DeRhamHTMult
