import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Print

/-!
# Lane RC31, part 3: joint continuity of lattice-bounded pairings

Manuscript `diophantine_zq.tex`, tex 4976–5200 (the characteristic-zero fibres): the coefficient
pairing `V_𝔭 × V'_𝔭 → k(𝔭)(1)` used by the fibre duality must be jointly continuous for the natural
(lattice) topologies (the hypothesis `hβc` of lane RC26's pairing data). For finitely generated
lattices over the `ℤ₂`-finite ring `Λ/𝔭` this is automatic in Nekovář's formalism (*Selmer
complexes*, 3.1.2, p. 75: `R`-linear maps between modules of finite type are continuous); here it is
PROVED from a lattice bound.

* `continuous_of_lattice_bound`: if `X`, `X'`, `T` are topological groups whose neighbourhoods of
  `0` are the `2^n Y`, `2^n Y'`, `2^n Z` for `Λ`-lattices `Y`, `Y'`, `Z`, every vector of `X`, `X'`
  is `2^{−n}` times a lattice vector, and the `k`-bilinear map `β` sends `Y × Y'` into `Z`, then `β`
  is jointly continuous.

Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open scoped Pointwise

variable {k : Type*} [CommRing k] [Algebra Lambda k] {X X' T : Type*}
  [AddCommGroup X] [Module k X] [Module Lambda X] [IsScalarTower Lambda k X]
  [AddCommGroup X'] [Module k X'] [Module Lambda X'] [IsScalarTower Lambda k X']
  [AddCommGroup T] [Module k T] [Module Lambda T] [IsScalarTower Lambda k T]

omit [Module Lambda X'] [IsScalarTower Lambda k X'] in
/-- A `k`-bilinear map is `Λ`-bilinear on the left (`Λ` acting through `k`). Kind: PROVED. -/
theorem bilin_lambda_smul_left (β : X →ₗ[k] X' →ₗ[k] T) (l : Lambda) (x : X) (y : X') :
    β (l • x) y = l • β x y := by
  rw [← algebraMap_smul k l x, map_smul, LinearMap.smul_apply, algebraMap_smul]

omit [Module Lambda X] [IsScalarTower Lambda k X] in
/-- A `k`-bilinear map is `Λ`-bilinear on the right (`Λ` acting through `k`). Kind: PROVED. -/
theorem bilin_lambda_smul_right (β : X →ₗ[k] X' →ₗ[k] T) (l : Lambda) (x : X) (y : X') :
    β x (l • y) = l • β x y := by
  rw [← algebraMap_smul k l y, map_smul, algebraMap_smul]

omit [Module k X] [IsScalarTower Lambda k X] in
/-- Membership in `2^n • Y` for a submodule `Y`. -/
theorem mem_two_pow_smul_iff (Y : Submodule Lambda X) (n : ℕ) (x : X) :
    x ∈ (((2 : Lambda) ^ n) • Y : Submodule Lambda X) ↔ ∃ y ∈ Y, ((2 : Lambda) ^ n) • y = x :=
  Submodule.mem_smul_pointwise_iff_exists x _ Y

omit [Module k X] [IsScalarTower Lambda k X] in
/-- The translated basis of neighbourhoods `x₀ + 2^n Y` of a point `x₀`. Kind: PROVED. -/
theorem hasBasis_nhds_translate [TopologicalSpace X] [IsTopologicalAddGroup X]
    (Y : Submodule Lambda X)
    (hX : (𝓝 (0 : X)).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • Y : Submodule Lambda X) : Set X))) (x₀ : X) :
    (𝓝 x₀).HasBasis (fun _ : ℕ => True)
      (fun n => {x : X | x - x₀ ∈ (((2 : Lambda) ^ n) • Y : Submodule Lambda X)}) := by
  have h := hX.map (x₀ + ·)
  rw [map_add_left_nhds_zero] at h
  refine h.to_hasBasis (fun n _ => ⟨n, trivial, ?_⟩) (fun n _ => ⟨n, trivial, ?_⟩)
  · intro x hx
    exact ⟨x - x₀, hx, add_sub_cancel x₀ x⟩
  · rintro x ⟨u, hu, rfl⟩
    show x₀ + u - x₀ ∈ (((2 : Lambda) ^ n) • Y : Submodule Lambda X)
    rwa [add_sub_cancel_left]

/-- **A lattice-bounded bilinear map is jointly continuous**: if the neighbourhoods of `0` of `X`,
`X'`, `T` are the `2^n Y`, `2^n Y'`, `2^n Z`, every vector of `X`, `X'` has a multiple `2^n x` in
the lattice, and `β (Y × Y') ⊆ Z`, then `(x, y) ↦ β x y` is continuous. (Write
`β x y − β x₀ y₀ = β (x − x₀) y₀ + β x₀ (y − y₀) + β (x − x₀) (y − y₀)` and move the powers of `2`
across `β`.) Kind: PROVED. -/
theorem continuous_of_lattice_bound [TopologicalSpace X] [IsTopologicalAddGroup X]
    [TopologicalSpace X'] [IsTopologicalAddGroup X'] [TopologicalSpace T] [IsTopologicalAddGroup T]
    (β : X →ₗ[k] X' →ₗ[k] T) (Y : Submodule Lambda X)
    (Y' : Submodule Lambda X') (Z : Submodule Lambda T)
    (hX : (𝓝 (0 : X)).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • Y : Submodule Lambda X) : Set X)))
    (hX' : (𝓝 (0 : X')).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • Y' : Submodule Lambda X') : Set X')))
    (hT : (𝓝 (0 : T)).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • Z : Submodule Lambda T) : Set T)))
    (hexX : ∀ x : X, ∃ n : ℕ, ((2 : Lambda) ^ n) • x ∈ Y)
    (hexX' : ∀ y : X', ∃ n : ℕ, ((2 : Lambda) ^ n) • y ∈ Y')
    (hb : ∀ x ∈ Y, ∀ y ∈ Y', β x y ∈ Z) :
    Continuous fun p : X × X' => β p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  obtain ⟨A, hA⟩ := hexX x₀
  obtain ⟨B, hB⟩ := hexX' y₀
  have hTb := hasBasis_nhds_translate Z hT (β x₀ y₀)
  rw [ContinuousAt, nhds_prod_eq, hTb.tendsto_right_iff]
  intro n _
  refine Filter.mem_of_superset (Filter.prod_mem_prod
    ((hasBasis_nhds_translate Y hX x₀).mem_of_mem (i := n + B) trivial)
    ((hasBasis_nhds_translate Y' hX' y₀).mem_of_mem (i := n + A) trivial)) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  obtain ⟨u, hu, hux⟩ := (mem_two_pow_smul_iff Y (n + B) (x - x₀)).mp hx
  obtain ⟨u', hu', huy⟩ := (mem_two_pow_smul_iff Y' (n + A) (y - y₀)).mp hy
  have hxe : x = x₀ + ((2 : Lambda) ^ (n + B)) • u := by rw [hux]; abel
  have hye : y = y₀ + ((2 : Lambda) ^ (n + A)) • u' := by rw [huy]; abel
  have e1 : β (((2 : Lambda) ^ (n + B)) • u) y₀ =
      ((2 : Lambda) ^ n) • β u (((2 : Lambda) ^ B) • y₀) := by
    rw [bilin_lambda_smul_left, bilin_lambda_smul_right, pow_add, mul_smul]
  have e2 : β x₀ (((2 : Lambda) ^ (n + A)) • u') =
      ((2 : Lambda) ^ n) • β (((2 : Lambda) ^ A) • x₀) u' := by
    rw [bilin_lambda_smul_left, bilin_lambda_smul_right, pow_add, mul_smul]
  have e3 : β (((2 : Lambda) ^ (n + B)) • u) (((2 : Lambda) ^ (n + A)) • u') =
      ((2 : Lambda) ^ n) • (((2 : Lambda) ^ (B + (n + A))) • β u u') := by
    rw [bilin_lambda_smul_left, bilin_lambda_smul_right, smul_smul, smul_smul, ← pow_add,
      ← pow_add]
    congr 2
    omega
  rw [mem_two_pow_smul_iff]
  refine ⟨β u (((2 : Lambda) ^ B) • y₀) + β (((2 : Lambda) ^ A) • x₀) u' +
    ((2 : Lambda) ^ (B + (n + A))) • β u u', ?_, ?_⟩
  · exact Z.add_mem (Z.add_mem (hb u hu _ hB) (hb _ hA u' hu')) (Z.smul_mem _ (hb u hu u' hu'))
  · rw [smul_add, smul_add, ← e1, ← e2, ← e3, hxe, hye]
    simp only [map_add, LinearMap.add_apply]
    abel

end ZInQ.Manuscript.RC.FibreDuality
