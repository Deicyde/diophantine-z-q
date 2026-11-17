import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: compatible finite free models and the inverse limit (tex 7386–7426)

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, proof of Proposition `ex:app-even-scalar`,
first paragraphs (tex 7386–7426; announced in Section 7.1, tex 1912–1916). Over the successive
Artin quotients, continuous cochains have minimal finite free models (by the nilpotent
perturbation calculation of Section 9 — lane RC6-limits); Elliot then makes them compatible and
passes to the limit. This file proves the three algebraic steps of that passage:

* `homotopyEquiv_minimal_bijective` — two minimal finite models (differentials into `𝔪·`) that
  are homotopy equivalent are degreewise isomorphic: "reducing a homotopy inverse modulo the
  maximal ideal shows that the comparison is degreewise invertible" (tex 7393–7395, 7399–7402);
* `exists_compatible_comparison` — "Since reduction of continuous cochains is termwise surjective,
  lift that homotopy and adjust the upper comparison by its boundary. The comparison maps are now
  exactly compatible and remain quasi-isomorphisms" (tex 7404–7409): a homotopy through a
  termwise surjection lifts from a degreewise projective complex, and the adjusted comparison is
  homotopic to the original one;
* `invlim_acyclic` — "Their acyclic, termwise surjective comparison cones have acyclic inverse
  limit" (tex 7396–7397, 7411–7421), proved by Elliot's route: the sequence
  `0 → lim K_n → ∏ K_n →(1−s) ∏ K_n → 0` is exact by successive lifting, products of acyclic
  complexes are acyclic, and the long exact cohomology sequence (here: its diagram chase) makes the
  limit acyclic.

Complexes are Mathlib's `CochainComplex (ModuleCat R) ℤ`; the inverse limit is described by its
elements, compatible sequences. Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Even

open CategoryTheory

universe u v

/-! ### Minimal models: Nakayama (tex 7393–7395, 7399–7402) -/

/-- A linear map sends `I • ⊤` into `I • ⊤` (used for `h ∘ d` in `gf − 1 = dh + hd`,
tex 7401). -/
theorem map_mem_ideal_smul_top {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I • (⊤ : Submodule R N) :=
  Submodule.smul_top_le_comap_smul_top I f hx

/-- **Nakayama** ("Nakayama applies", tex 7395): an endomorphism `u` of a finite module over a
local ring such that `u − 1` lands in `𝔪 · M` is surjective. -/
theorem surjective_of_sub_mem_maximalIdeal_smul_top {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (u : M →ₗ[R] M)
    (hu : ∀ x, u x - x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)) :
    Function.Surjective u := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) fun x _ => ?_
  have h : u x - (u x - x) ∈ LinearMap.range u ⊔ (IsLocalRing.maximalIdeal R) • ⊤ :=
    Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self u x))
      (Submodule.mem_sup_right (hu x))
  rwa [sub_sub_cancel] at h

/-- If a chain endomorphism `g` of a complex whose differentials land in `I · (target)` is
homotopic to the identity, then `g − 1 = dh + hd` lands in `I · (target)` in every degree
("reducing a homotopy inverse modulo the maximal ideal", tex 7400–7402). -/
theorem homotopy_id_sub_mem_smul_top {R : Type u} [CommRing R] (I : Ideal R)
    {E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hE : ∀ i j, LinearMap.range (E.d i j).hom ≤ I • ⊤) {g : E ⟶ E} (h : Homotopy g (𝟙 E))
    (i : ℤ) (x : E.X i) : (g.f i).hom x - x ∈ I • (⊤ : Submodule R (E.X i)) := by
  have hc := h.comm i
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)] at hc
  have hx : (g.f i).hom x - x = (h.hom (i + 1) i).hom ((E.d i (i + 1)).hom x) +
      (E.d (i - 1) i).hom ((h.hom i (i - 1)).hom x) := by
    rw [hc]; simp
  rw [hx]
  exact Submodule.add_mem _ (map_mem_ideal_smul_top I _ (hE _ _ (LinearMap.mem_range_self _ x)))
    (hE _ _ (LinearMap.mem_range_self _ _))

/-- **Minimal models are degreewise isomorphic** (tex 7393–7395, 7399–7402; PROVED). Over a local
ring `R`, let `C, D` be complexes of finitely generated modules whose differentials land in
`𝔪 · (target)` (minimal models). Then every homotopy equivalence `C ≃ D` is an isomorphism in each
degree: `gf − 1 = dh + hd` has image in `𝔪 C`, so `gf` is onto by Nakayama and bijective, and
likewise `fg`. -/
theorem homotopyEquiv_minimal_bijective {R : Type u} [CommRing R] [IsLocalRing R]
    {C D : CochainComplex (ModuleCat.{v} R) ℤ} [∀ i, Module.Finite R (C.X i)]
    [∀ i, Module.Finite R (D.X i)]
    (hC : ∀ i j, LinearMap.range (C.d i j).hom ≤ (IsLocalRing.maximalIdeal R) • ⊤)
    (hD : ∀ i j, LinearMap.range (D.d i j).hom ≤ (IsLocalRing.maximalIdeal R) • ⊤)
    (e : HomotopyEquiv C D) (i : ℤ) : Function.Bijective (e.hom.f i).hom := by
  -- `gf` is onto by Nakayama, hence bijective (finite module over a commutative ring)
  have hgf : Function.Bijective ((e.hom ≫ e.inv).f i).hom := by
    have hs : Function.Surjective ((e.hom ≫ e.inv).f i).hom :=
      surjective_of_sub_mem_maximalIdeal_smul_top _
        (homotopy_id_sub_mem_smul_top _ hC e.homotopyHomInvId i)
    exact ⟨OrzechProperty.injective_of_surjective_endomorphism _ hs, hs⟩
  -- `fg` is onto by Nakayama
  have hfg : Function.Surjective ((e.inv ≫ e.hom).f i).hom :=
    surjective_of_sub_mem_maximalIdeal_smul_top _
      (homotopy_id_sub_mem_smul_top _ hD e.homotopyInvHomId i)
  refine ⟨fun a b hab => hgf.1 ?_, fun y => ?_⟩
  · simp [hab]
  · obtain ⟨x, hx⟩ := hfg y
    exact ⟨(e.inv.f i).hom x, by simpa using hx⟩

/-! ### Compatible comparisons (tex 7404–7409) -/

/-- **Adjusting the comparison by a lifted homotopy** (tex 7404–7409; PROVED). Let `P` be
degreewise projective (a finite free model), `π : C → C'` termwise surjective (reduction of
continuous cochains), `φ : P → C` and `ψ : P → C'` chain maps with `φπ ≃ ψ`. Then there is a chain
map `φ' : P → C` homotopic to `φ` (so it induces the same maps on cohomology, and remains a
quasi-isomorphism) with `φ'π = ψ` exactly. -/
theorem exists_compatible_comparison {R : Type u} [Ring R]
    {P C C' : CochainComplex (ModuleCat.{v} R) ℤ} [∀ i, Module.Projective R (P.X i)]
    (π : C ⟶ C') (hπ : ∀ i, Function.Surjective (π.f i).hom) (φ : P ⟶ C) (ψ : P ⟶ C')
    (H : Homotopy (φ ≫ π) ψ) :
    ∃ φ' : P ⟶ C, φ' ≫ π = ψ ∧ Nonempty (Homotopy φ φ') := by
  -- lift every component of the homotopy through the termwise surjection `π`
  have hlift : ∀ i j, ∃ k : P.X i ⟶ C.X j, k ≫ π.f j = H.hom i j := by
    intro i j
    obtain ⟨k, hk⟩ := Module.projective_lifting_property (π.f j).hom (H.hom i j).hom (hπ j)
    exact ⟨ModuleCat.ofHom k, ModuleCat.hom_ext (by simpa using hk)⟩
  choose k hk using hlift
  -- adjust `φ` by the boundary of the lifted homotopy
  refine ⟨φ - Homotopy.nullHomotopicMap' (fun i j _ => k i j), ?_,
    ⟨Homotopy.equivSubZero.symm ?_⟩⟩
  · have hN : Homotopy.nullHomotopicMap' (fun i j _ => k i j) ≫ π =
        Homotopy.nullHomotopicMap H.hom := by
      rw [Homotopy.nullHomotopicMap'_comp]
      simp only [hk]
      unfold Homotopy.nullHomotopicMap'
      congr 1
      funext i j
      split_ifs with hij
      · rfl
      · exact (H.zero i j hij).symm
    rw [Preadditive.sub_comp, hN]
    ext i : 1
    rw [HomologicalComplex.sub_f_apply, H.comm i]
    change dNext i H.hom + prevD i H.hom + ψ.f i - (dNext i H.hom + prevD i H.hom) = ψ.f i
    abel
  · rw [sub_sub_cancel]
    exact Homotopy.nullHomotopy' _

/-! ### The inverse limit (tex 7411–7421) -/

/-- **Diagram chase for a degreewise short exact sequence of complexes** (the step "the long exact
cohomology sequence makes the limit acyclic", tex 7420–7421), stated elementwise for families of
linear maps. Subscripts are consecutive degrees. Let `ι : A → B`, `p : B → C` be chain maps with
`ι` injective and `p ∘ ι = 0` in degree 2, `ker p ⊆ im ι` in degree 1 and `p` surjective in
degree 0. If `B` is exact in degree 2 and `C` is exact in degree 1, then every cocycle of `A` in
degree 2 is a boundary. -/
theorem acyclic_of_shortExact_elementwise {R : Type u} [Ring R]
    {A₁ A₂ A₃ B₀ B₁ B₂ B₃ C₀ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup A₃] [Module R A₃]
    [AddCommGroup B₀] [Module R B₀] [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂]
    [AddCommGroup B₃] [Module R B₃]
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    (dA₁ : A₁ →ₗ[R] A₂) (dA₂ : A₂ →ₗ[R] A₃)
    (dB₀ : B₀ →ₗ[R] B₁) (dB₁ : B₁ →ₗ[R] B₂) (dB₂ : B₂ →ₗ[R] B₃)
    (dC₀ : C₀ →ₗ[R] C₁) (dC₁ : C₁ →ₗ[R] C₂)
    (ι₁ : A₁ →ₗ[R] B₁) (ι₂ : A₂ →ₗ[R] B₂) (ι₃ : A₃ →ₗ[R] B₃)
    (p₀ : B₀ →ₗ[R] C₀) (p₁ : B₁ →ₗ[R] C₁) (p₂ : B₂ →ₗ[R] C₂)
    (hι₁ : ∀ a, dB₁ (ι₁ a) = ι₂ (dA₁ a)) (hι₂ : ∀ a, dB₂ (ι₂ a) = ι₃ (dA₂ a))
    (hp₀ : ∀ b, dC₀ (p₀ b) = p₁ (dB₀ b)) (hp₁ : ∀ b, dC₁ (p₁ b) = p₂ (dB₁ b))
    (hdd : ∀ b, dB₁ (dB₀ b) = 0)
    (hinj : Function.Injective ι₂) (hpι : ∀ a, p₂ (ι₂ a) = 0)
    (hker : ∀ b, p₁ b = 0 → ∃ a, ι₁ a = b) (hsurj : Function.Surjective p₀)
    (hB : ∀ b, dB₂ b = 0 → ∃ b', dB₁ b' = b) (hC : ∀ c, dC₁ c = 0 → ∃ c', dC₀ c' = c)
    (a : A₂) (ha : dA₂ a = 0) : ∃ a', dA₁ a' = a := by
  obtain ⟨b, hb⟩ := hB (ι₂ a) (by rw [hι₂, ha, map_zero])
  obtain ⟨c', hc'⟩ := hC (p₁ b) (by rw [hp₁, hb, hpι])
  obtain ⟨b', rfl⟩ := hsurj c'
  obtain ⟨a', ha'⟩ := hker (b - dB₀ b') (by rw [map_sub, ← hp₀, hc', sub_self])
  refine ⟨a', hinj ?_⟩
  rw [← hι₁, ha', map_sub, hdd, sub_zero, hb]

/-- The componentwise differential `∏ₙ Kₙ^j → ∏ₙ Kₙ^k` of the product complex (tex 7416). -/
def invlimProdD {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ) (j k : ℤ) :
    (∀ n, (K n).X j) →ₗ[R] (∀ n, (K n).X k) :=
  LinearMap.pi fun n => ((K n).d j k).hom ∘ₗ LinearMap.proj n

/-- The map `1 − s` on `∏ₙ Kₙ^j`, `s` the transition shift: `(bₙ) ↦ (bₙ − πₙ bₙ₊₁)`
(tex 7412–7418). Its kernel is the inverse limit (compatible sequences). -/
def invlimOneSubShift {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (π : ∀ n, K (n + 1) ⟶ K n) (j : ℤ) : (∀ n, (K n).X j) →ₗ[R] (∀ n, (K n).X j) :=
  LinearMap.id - LinearMap.pi fun n => ((π n).f j).hom ∘ₗ LinearMap.proj (n + 1)

/-- Components of the product differential. -/
@[simp]
theorem invlimProdD_apply {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (j k : ℤ) (b : ∀ n, (K n).X j) (n : ℕ) : invlimProdD K j k b n = ((K n).d j k).hom (b n) :=
  rfl

/-- Components of `1 − s`. -/
@[simp]
theorem invlimOneSubShift_apply {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (π : ∀ n, K (n + 1) ⟶ K n) (j : ℤ) (b : ∀ n, (K n).X j) (n : ℕ) :
    invlimOneSubShift K π j b n = b n - ((π n).f j).hom (b (n + 1)) :=
  rfl

/-- `1 − s` is a chain map: it commutes with the product differential. -/
theorem invlimProdD_oneSubShift {R : Type u} [Ring R]
    (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ) (π : ∀ n, K (n + 1) ⟶ K n) (j k : ℤ)
    (b : ∀ n, (K n).X j) :
    invlimProdD K j k (invlimOneSubShift K π j b) =
      invlimOneSubShift K π k (invlimProdD K j k b) := by
  funext n
  simp only [invlimProdD_apply, invlimOneSubShift_apply, map_sub]
  congr 1
  have := congrArg (fun g => g.hom (b (n + 1))) ((π n).comm j k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

/-- The product differential squares to zero. -/
theorem invlimProdD_comp {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (j k l : ℤ) (b : ∀ n, (K n).X j) : invlimProdD K k l (invlimProdD K j k b) = 0 := by
  funext n
  have := congrArg (fun g => g.hom (b n)) ((K n).d_comp_d j k l)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at this
  exact this

/-- **Successive lifting** (tex 7412–7413): for termwise surjective transition maps, `1 − s` is
surjective. Given `(cₙ)`, put `b₀ = 0` and let `bₙ₊₁` be a lift of `bₙ − cₙ`. -/
theorem invlimOneSubShift_surjective {R : Type u} [Ring R]
    (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ) (π : ∀ n, K (n + 1) ⟶ K n) (j : ℤ)
    (hsurj : ∀ n, Function.Surjective ((π n).f j).hom) :
    Function.Surjective (invlimOneSubShift K π j) := by
  intro c
  have hsurj' : ∀ n (z : (K n).X j), ∃ w, ((π n).f j).hom w = z := hsurj
  choose g hg using hsurj'
  let b : ∀ n, (K n).X j := fun n =>
    Nat.rec (motive := fun n => (K n).X j) 0 (fun n bn => g n (bn - c n)) n
  refine ⟨b, funext fun n => ?_⟩
  rw [invlimOneSubShift_apply]
  show b n - ((π n).f j).hom (g n (b n - c n)) = c n
  rw [hg, sub_sub_cancel]

/-- A cocycle of a cochain complex of modules that is exact at `j` is a boundary. -/
theorem exactAt_exists_preimage {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}
    {i j k : ℤ} (hij : i + 1 = j) (hjk : j + 1 = k) (h : K.ExactAt j) (x : K.X j)
    (hx : (K.d j k).hom x = 0) : ∃ y : K.X i, (K.d i j).hom y = x := by
  rw [HomologicalComplex.exactAt_iff' K i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk), ShortComplex.moduleCat_exact_iff] at h
  exact h x hx

/-- **Products of acyclic complexes are acyclic** (tex 7420): a cocycle of `∏ₙ Kₙ` in degree `j`
is a boundary when every `Kₙ` is exact at `j`. -/
theorem invlimProdD_exact {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    {i j k : ℤ} (hex : ∀ n, (K n).ExactAt j) (hij : i + 1 = j) (hjk : j + 1 = k)
    (b : ∀ n, (K n).X j) (hb : invlimProdD K j k b = 0) : ∃ b', invlimProdD K i j b' = b := by
  choose b' hb' using fun n => exactAt_exists_preimage hij hjk (hex n) (b n) (congrFun hb n)
  exact ⟨b', funext hb'⟩

/-- **The inverse limit of acyclic complexes with termwise surjective transition maps is acyclic**
(tex 7411–7421; PROVED, by Elliot's route through `0 → lim → ∏ →(1−s) ∏ → 0`). Elements of the
limit in degree `i` are compatible sequences `(x_n)`; a compatible sequence of cocycles is the
boundary of a compatible sequence. -/
theorem invlim_acyclic {R : Type u} [Ring R] (K : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (π : ∀ n, K (n + 1) ⟶ K n) (hsurj : ∀ n i, Function.Surjective ((π n).f i).hom)
    (hex : ∀ n i, (K n).ExactAt i) (i : ℤ) (x : ∀ n, (K n).X i)
    (hx : ∀ n, ((π n).f i).hom (x (n + 1)) = x n)
    (hcyc : ∀ n, ((K n).d i (i + 1)).hom (x n) = 0) :
    ∃ y : ∀ n, (K n).X (i - 1), (∀ n, ((π n).f (i - 1)).hom (y (n + 1)) = y n) ∧
      ∀ n, ((K n).d (i - 1) i).hom (y n) = x n := by
  -- the limit complex `A = ker (1 − s)` is a subcomplex of the product `B = ∏ₙ Kₙ`
  have hmaps : ∀ j k, ∀ b ∈ LinearMap.ker (invlimOneSubShift K π j),
      invlimProdD K j k b ∈ LinearMap.ker (invlimOneSubShift K π k) := by
    intro j k b hb
    rw [LinearMap.mem_ker] at hb ⊢
    rw [← invlimProdD_oneSubShift, hb, map_zero]
  have hxL : x ∈ LinearMap.ker (invlimOneSubShift K π i) := by
    rw [LinearMap.mem_ker]
    funext n
    simp [hx n]
  -- the diagram chase for `0 → A → B →(1−s) B → 0`, with `B` acyclic and `1 − s` onto
  obtain ⟨a', ha'⟩ := acyclic_of_shortExact_elementwise (R := R)
    ((invlimProdD K (i - 1) i).restrict (hmaps (i - 1) i))
    ((invlimProdD K i (i + 1)).restrict (hmaps i (i + 1)))
    (invlimProdD K (i - 1 - 1) (i - 1)) (invlimProdD K (i - 1) i) (invlimProdD K i (i + 1))
    (invlimProdD K (i - 1 - 1) (i - 1)) (invlimProdD K (i - 1) i)
    (LinearMap.ker (invlimOneSubShift K π (i - 1))).subtype
    (LinearMap.ker (invlimOneSubShift K π i)).subtype
    (LinearMap.ker (invlimOneSubShift K π (i + 1))).subtype
    (invlimOneSubShift K π (i - 1 - 1)) (invlimOneSubShift K π (i - 1))
    (invlimOneSubShift K π i)
    (fun _ => rfl) (fun _ => rfl)
    (invlimProdD_oneSubShift K π _ _) (invlimProdD_oneSubShift K π _ _)
    (invlimProdD_comp K _ _ _)
    (Submodule.injective_subtype _) (fun a => LinearMap.mem_ker.mp a.2)
    (fun b hb => ⟨⟨b, LinearMap.mem_ker.mpr hb⟩, rfl⟩)
    (invlimOneSubShift_surjective K π _ (fun n => hsurj n _))
    (invlimProdD_exact K (fun n => hex n i) (sub_add_cancel i 1) rfl)
    (invlimProdD_exact K (fun n => hex n (i - 1)) (sub_add_cancel (i - 1) 1) (sub_add_cancel i 1))
    ⟨x, hxL⟩ (Subtype.ext (funext hcyc))
  refine ⟨a'.1, fun n => ?_, fun n => ?_⟩
  · have h := congrFun (LinearMap.mem_ker.mp a'.2) n
    simp only [invlimOneSubShift_apply, Pi.zero_apply, sub_eq_zero] at h
    exact h.symm
  · exact congrFun (congrArg Subtype.val ha') n

end ZInQ.Manuscript.RC.Even
