/-!
# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Appended (by `build.sh`) to verbatim copies of frob-trace's three source parts
(`src_part_tate_src.lean`, `src_part_bridge_src.lean`, `src_part_frob.lean`, i.e.
`scratch/frob-trace/FrobTrace.lean` without its first import line, which `build.sh` re-adds).

Main results (namespace `AlgFrobRedRed`):
* `algFrobRed_of_at : AlgFrobRedAt → FrobTrace.AlgFrobRed` (proved): the place `g(v)` and the
  Frobenius `gτg⁻¹` are absorbed (`liesOver_smul`, `isArithFrob_conj`).
* `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` (proved): the finite
  set `S` is the set of primes of bad reduction (leaf `GoodRedCofinite`); what remains is local
  at one place of good reduction (`AlgFrobRedGood`).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate
open scoped Pointwise

/-! ## 1. Conjugating the place -/

/-- Nonunits move with the place: `z ∈ v.nonunits → g z ∈ (g • v).nonunits`. -/
theorem smul_mem_nonunits (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {z : PkgI4.Qbar}
    (hz : z ∈ v.nonunits) : g z ∈ (g • v).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hz ⊢
  rcases hz with hz | hz
  · left; rw [hz, map_zero]
  · right
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact hz

/-- `g(v)` lies over `p` if `v` does. -/
theorem liesOver_smul (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hv : PkgI4.LiesOver v p) : PkgI4.LiesOver (g • v) p := by
  have := smul_mem_nonunits g hv
  rwa [map_natCast] at this

/-- `gτg⁻¹` is an arithmetic Frobenius at `g(v)` if `τ` is one at `v`. -/
theorem isArithFrob_conj (g : PkgI4.GQ) {τ : PkgI4.GQ} {v : ValuationSubring PkgI4.Qbar}
    {p : ℕ} (hτ : PkgI4.IsArithFrob τ v p) : PkgI4.IsArithFrob (g * τ * g⁻¹) (g • v) p := by
  obtain ⟨hD, hF⟩ := hτ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff] at hD ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hD]
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def] at hx
    have h := smul_mem_nonunits g (hF _ hx)
    have e1 : g (τ (g⁻¹ x)) = (g * τ * g⁻¹) x := rfl
    have e2 : g (g⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rwa [map_sub, map_pow, e1, e2] at h

/-- **`AlgFrobRedAt` (GLUE, AV side; Glazer N5 L777-786; the reduction map at the place of the
Frobenius).** `FrobTrace.AlgFrobRed` with the Frobenius `σ` at the place `v` itself (no
conjugating `g`): for `A/L`, `F : A → A` finite surjective there is a finite `S` such that for
`p ∉ S`, `v ∣ p`, `σ` an arithmetic Frobenius at `v` and `f(x) = F ∘ x ∘ Spec(σ)` additive, there
are `Ā/k` (`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with
`red ∘ (N·f) = α' ∘ red`, injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every
prime `ℓ ≠ p`. -/
def AlgFrobRedAt : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRed` from `AlgFrobRedAt` (proved):** apply `AlgFrobRedAt` at the place `g(v)` to
the arithmetic Frobenius `gτg⁻¹` there. -/
theorem algFrobRed_of_at (h : AlgFrobRedAt) : FrobTrace.AlgFrobRed := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := h L A F hF1 hF2
  exact ⟨S, fun p hp hpS v τ hv hτ g f hf =>
    hS p hp hpS (g • v) (g * τ * g⁻¹) (liesOver_smul g hv) (isArithFrob_conj g hτ) f hf⟩

/-! ## 2. Isolating the finite set: good reduction outside finitely many primes -/

/-- **`GoodRedCofinite` (LEAF candidate; good reduction almost everywhere).** An abelian variety
`A` over a number field `L ⊆ ℚ̄` has good reduction at every place of `L` above all but finitely
many primes `p`: there is a finite `S` with `A` having good reduction (I2's `HasGoodReduction`:
an abelian scheme over the valuation ring with generic fibre `≅ A`) at `v ∩ L` for every place
`v` of `ℚ̄` above `p ∉ S`. Source: spreading out, EGA IV₃ §8 (8.8.2, 8.10.5) and EGA IV₄ 17.7.8
for smoothness, with properness and geometric connectedness of fibres; in this form e.g.
Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), §1, and
Milne, *Abelian varieties* (in Cornell–Silverman, *Arithmetic Geometry*, 1986), §20
(all locators UNVERIFIED). -/
def GoodRedCofinite : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar))

/-- **`AlgFrobRedGood` (GLUE, AV side; Glazer N5 L777-786; the reduction map at one place of
good reduction).** `AlgFrobRedAt` at a single place `v ∣ p` at which `A` has good reduction
(`HasGoodReduction` at `v ∩ L`), with no finite set: for `σ` an arithmetic Frobenius at `v` and
`f(x) = F ∘ x ∘ Spec(σ)` additive (`F : A → A` finite surjective), there are `Ā/k`
(`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`,
injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`): `𝒜/O_w` (`w = v ∩ L`) the abelian
scheme, `Ā` its special fibre over `k = κ(w)`; `red` is `A(ℚ̄) = 𝒜(O_v) → Ā(κ(v)) ≅ Ā(k̄)`
(valuative criterion); `F` is an `L`-morphism `A → A^{(s)}`, `s = σ⁻¹|_L ∈ D(w)`, and `A^{(s)}`
has good reduction at `s(w) = w`, so `F` extends to `𝒜 → 𝒜^{(s)}` (leaf I2-NMP); `f` reduces to
`F̄ ∘ Fr_Ā`, a `k`-morphism fixing `0`, hence `α' ∈ End(Ā)` (rigidity); the torsion clauses are
leaf I2-Red. -/
def AlgFrobRedGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar)) →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRedAt` from the leaf `GoodRedCofinite` and the local glue `AlgFrobRedGood`
(proved):** `S` is the finite set of `GoodRedCofinite` for `A`. -/
theorem algFrobRedAt_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) : AlgFrobRedAt := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hG L A
  exact ⟨S, fun p hp hpS v σ hv hσ f hf =>
    hL L A F hF1 hF2 p hp v σ hv hσ (hS p hp hpS v hv) f hf⟩

/-- **`AlgFrobRed` from `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem algFrobRed_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_at (algFrobRedAt_of_good hG hL)

/-- **`TateBridge35` from I3.M0, `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem tateBridge35_of_good (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hL : AlgFrobRedGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_good hG hL)

end AlgFrobRedRed

end

#print axioms AlgFrobRedRed.algFrobRed_of_at
#print axioms AlgFrobRedRed.algFrobRedAt_of_good
#print axioms AlgFrobRedRed.algFrobRed_of_good
#print axioms AlgFrobRedRed.tateBridge35_of_good
