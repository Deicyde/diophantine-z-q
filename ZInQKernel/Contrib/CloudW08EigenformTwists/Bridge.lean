import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# H-33 (T24): twisting a normalized eigenform by a Dirichlet character, unfolded

Row H-33 of `docs/research/frontier.md` (issue elliotglazer/diophantine-z-q#83). This file proves
the statement of `PkgI4.EigenformTwist` (`ZInQKernel/HDecomp/ModCurves/C9.lean` §7, fixed at fork
`main` `cba8157f7d5d09a4a3c8462aba2f3245494a870e` and byte-identical at the working base
`f70ec251fd4bca6ae3115741c21fe661e7aaac3e`) with its definitions unfolded to those of
`PkgI4` in `ZInQKernel/HDecomp/Conductor/LadicCond.lean` (`CF`, `coeff`, `HasNebentypus`,
`IsNormalizedEigenform`; nothing is redefined here). The closed theorem
`EigenformTwist_proof : PkgI4.EigenformTwist` is in `EigenformTwist.lean`.

For `g ∈ S_k(Γ₁(N))` with `IsNormalizedEigenform g χ` and any Dirichlet character `ψ` modulo
`M > 0` (not necessarily primitive), the witness is Tau Ceti's twist
`g' := CuspForm.twist ψ … g = Σ ψ(n) aₙ(g) qⁿ`, a cusp form for `Γ₁(N M²)`, and
`χ' := twistChar χ ψ`, the zero extension of `χψ²` read at level `N M²`:

* `CuspForm.qExpansion_twist_coeff` (Tau Ceti): `aₙ(g') = ψ(n) aₙ(g)` for every `n`, so in
  particular at every prime `p ∤ N M`;
* `CuspForm.twist_mem_cuspFormCharSpace` (Tau Ceti): `g' ∈ S_k(Γ₁(N M²), χψ²)`, which through
  Tau Ceti's `mem_cuspFormCharSpace_iff_nebentypus` is `HasNebentypus g' χ'`;
* `a₁(g') = ψ(1) a₁(g) = 1`;
* the coefficient identity `a_m(g') a_n(g') = Σ_{d ∣ (m,n)} χ'(d) d^{k-1} a_{mn/d²}(g')` for all
  `m, n ≥ 1`, from that of `g`: `χ'(d) = χ(d) ψ(d)²` for every natural `d`
  (`twistChar_natCast`; both sides vanish unless `d` is prime to `N M`), and
  `ψ(d)² ψ(mn/d²) = ψ(mn) = ψ(m) ψ(n)` because `d² ∣ mn`.

Mathematical source: G. Shimura, *Introduction to the arithmetic theory of automorphic functions*
(1971), Prop. 3.64 (stated there for primitive `ψ`); for arbitrary `ψ` the same formula works by
finite Fourier expansion on `ℤ/M`, as recorded in `docs/research/leaf-review-a.md` §F.5 and
formalized (without primitivity) by Tau Ceti's file.

Reused code, with credit:
* Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit `5a01f5fe3621`, Apache-2.0),
  vendored unchanged on the fork under `ZInQKernel/Contrib/TauCeti/`: the module
  `TauCeti.NumberTheory.ModularForms.Twist.Basic` (© 2026 The Tau Ceti contributors) for
  `CuspForm.twist`, `CuspForm.qExpansion_twist_coeff`, `CuspForm.twist_mem_cuspFormCharSpace`,
  and `TauCeti.NumberTheory.ModularForms.DiamondOperators` (© 2026 Chris Birkbeck) for
  `cuspFormCharSpace` and `mem_cuspFormCharSpace_iff_nebentypus`. This file only imports them;
  no Tau Ceti file is modified. Tau Ceti's `main` as of 2026-11-14, commit `ca32605ff539` (Lean
  `v4.36.0-rc2`), has the same `Twist/Basic.lean` as the vendored copy up to the vendoring
  comment line and the `ZInQKernel.Contrib.` import prefix; its `Twist/Hecke.lean` (`T_p`
  commutes with twisting at primes `p ∤ L`) is not needed here and not vendored.
* `slash_SL_eq_mapGL`, `mem_cuspFormCharSpace_of_hasNebentypus` and
  `hasNebentypus_of_mem_cuspFormCharSpace` are copied from the fork's
  `ZInQKernel/Contrib/T25/Bridge.lean` (task t25-newform), without its unused `[NeZero N]`
  binders, so that this module does not import Tau Ceti's newform theory.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.CloudW08EigenformTwists

open PkgI4 (CF coeff HasNebentypus IsNormalizedEigenform)

variable {N : ℕ} {k : ℤ}

/-! ### Slash action and nebentypus (copied from `ZInQKernel/Contrib/T25/Bridge.lean`) -/

/-- Slashing by `γ ∈ SL(2, ℤ)` is slashing by its image `mapGL ℝ γ` in `GL(2, ℝ)`. -/
theorem slash_SL_eq_mapGL (f : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] mapGL ℝ γ := by
  rw [ModularForm.SL_slash]
  rfl

/-- The leaf's slash-form nebentypus `χ` (a Dirichlet character) puts a cusp form in Tau Ceti's
character space of `MulChar.toUnitHom χ`. -/
theorem mem_cuspFormCharSpace_of_hasNebentypus {f : CF N k} {χ : DirichletCharacter ℂ N}
    (h : HasNebentypus f χ) : f ∈ cuspFormCharSpace k (MulChar.toUnitHom χ) := by
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  intro g
  rw [← slash_SL_eq_mapGL, h (g : SL(2, ℤ)) g.2, MulChar.coe_toUnitHom]
  congr 2

/-- Tau Ceti's character space of `χ₀` gives the leaf's slash-form nebentypus for the zero
extension `MulChar.ofUnitHom χ₀`. -/
theorem hasNebentypus_of_mem_cuspFormCharSpace {f : CF N k} {χ₀ : (ZMod N)ˣ →* ℂˣ}
    (h : f ∈ cuspFormCharSpace k χ₀) : HasNebentypus f (MulChar.ofUnitHom χ₀) := by
  intro γ hγ
  have h' := (mem_cuspFormCharSpace_iff_nebentypus k χ₀ f).mp h ⟨γ, hγ⟩
  rw [slash_SL_eq_mapGL]
  refine h'.trans ?_
  congr 1
  rw [← MulChar.ofUnitHom_coe]
  congr 1

/-! ### The level `N M²` and the character `χψ²` -/

/-- `N M ∣ N M²`, the first divisibility Tau Ceti's twist asks of its level. -/
theorem dvd_level_left (N M : ℕ) : N * M ∣ N * M ^ 2 :=
  mul_dvd_mul_left N (dvd_pow_self M two_ne_zero)

/-- `M M ∣ N M²`, the second divisibility Tau Ceti's twist asks of its level. -/
theorem dvd_level_right (N M : ℕ) : M * M ∣ N * M ^ 2 := by
  rw [← sq]
  exact dvd_mul_left _ _

/-- The nebentypus `χψ²` of the twist on the units modulo `N M²`, in the form of Tau Ceti's
`CuspForm.twist_mem_cuspFormCharSpace` (both characters read at level `N M²` through the
reduction maps on units). -/
def twistCharUnits (χ : DirichletCharacter ℂ N) {M : ℕ} (ψ : DirichletCharacter ℂ M) :
    (ZMod (N * M ^ 2))ˣ →* ℂˣ :=
  (MulChar.toUnitHom χ).comp (ZMod.unitsMap (dvd_of_mul_right_dvd (dvd_level_left N M))) *
    ((MulChar.toUnitHom ψ).comp (ZMod.unitsMap (dvd_of_mul_left_dvd (dvd_level_right N M)))) ^ 2

/-- The twist's Dirichlet character `χ' = χψ²` modulo `N M²` (zero off the units). -/
def twistChar (χ : DirichletCharacter ℂ N) {M : ℕ} (ψ : DirichletCharacter ℂ M) :
    DirichletCharacter ℂ (N * M ^ 2) :=
  MulChar.ofUnitHom (twistCharUnits χ ψ)

/-- `χ'(d) = χ(d) ψ(d)²` for every natural number `d`: on a unit modulo `N M²` this is the
definition, and otherwise `d` shares a prime with `N` or with `M`, so both sides vanish. -/
theorem twistChar_natCast (χ : DirichletCharacter ℂ N) {M : ℕ} (ψ : DirichletCharacter ℂ M)
    (d : ℕ) : twistChar χ ψ (d : ZMod (N * M ^ 2)) = χ (d : ZMod N) * ψ (d : ZMod M) ^ 2 := by
  by_cases hd : IsUnit (d : ZMod (N * M ^ 2))
  · obtain ⟨u, hu⟩ := hd
    rw [twistChar, ← hu, MulChar.ofUnitHom_coe, twistCharUnits, MonoidHom.mul_apply,
      MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, ZMod.unitsMap_val,
      ZMod.unitsMap_val, hu,
      ZMod.cast_natCast (R := ZMod N) (dvd_of_mul_right_dvd (dvd_level_left N M)),
      ZMod.cast_natCast (R := ZMod M) (dvd_of_mul_left_dvd (dvd_level_right N M))]
  · rw [MulChar.map_nonunit (twistChar χ ψ) hd]
    have hcop : ¬ (d.Coprime N ∧ d.Coprime M) := by
      rintro ⟨h1, h2⟩
      exact hd ((ZMod.isUnit_iff_coprime d _).mpr
        (Nat.Coprime.mul_right h1 (Nat.Coprime.pow_right 2 h2)))
    rcases not_and_or.mp hcop with h | h
    · rw [MulChar.map_nonunit χ (fun h' => h ((ZMod.isUnit_iff_coprime d N).mp h')), zero_mul]
    · rw [MulChar.map_nonunit ψ (fun h' => h ((ZMod.isUnit_iff_coprime d M).mp h')),
        zero_pow two_ne_zero, mul_zero]

/-! ### The twist -/

/-- **H-33 / T24, unfolded.** The statement of `PkgI4.EigenformTwist`
(`ZInQKernel/HDecomp/ModCurves/C9.lean` §7) over the definitions of
`ZInQKernel/HDecomp/Conductor/LadicCond.lean`: for `N, m > 0`, a Dirichlet character `χ` mod `N`,
any Dirichlet character `ψ` mod `m` and a normalized eigenform `g ∈ S_k(Γ₁(N))` with nebentypus
`χ`, there are `χ'` mod `N m²` and a normalized eigenform `g' ∈ S_k(Γ₁(N m²))` with nebentypus
`χ'` and `a_p(g') = ψ(p) a_p(g)` for every prime `p ∤ N m`. Witnesses: `g' = g ⊗ ψ` (Tau Ceti's
`CuspForm.twist`) and `χ' = twistChar χ ψ`. -/
theorem eigenformTwist :
    ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
      0 < N → 0 < m → IsNormalizedEigenform g χ →
      ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
        IsNormalizedEigenform g' χ' ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p := by
  intro N M k χ ψ g _hN hM hg
  have : NeZero M := ⟨hM.ne'⟩
  let g' : CF (N * M ^ 2) k := CuspForm.twist ψ (dvd_level_left N M) (dvd_level_right N M) g
  have hcoeff : ∀ n : ℕ, coeff g' n = ψ (n : ZMod M) * coeff g n := fun n =>
    CuspForm.qExpansion_twist_coeff ψ (dvd_level_left N M) (dvd_level_right N M) g n
  refine ⟨twistChar χ ψ, g', ⟨?_, ?_, ?_⟩, fun p _ _ => hcoeff p⟩
  · -- the nebentypus `χψ²`
    exact hasNebentypus_of_mem_cuspFormCharSpace
      (CuspForm.twist_mem_cuspFormCharSpace ψ (dvd_level_left N M) (dvd_level_right N M)
        (mem_cuspFormCharSpace_of_hasNebentypus hg.1))
  · -- `a₁(g') = ψ(1) a₁(g) = 1`
    rw [hcoeff, hg.2.1, Nat.cast_one, map_one, one_mul]
  · -- the coefficient identity, from that of `g`
    intro a b ha hb
    calc coeff g' a * coeff g' b
        = ψ (a : ZMod M) * ψ (b : ZMod M) * (coeff g a * coeff g b) := by
          rw [hcoeff, hcoeff]
          ring
      _ = ∑ d ∈ (Nat.gcd a b).divisors, ψ (a : ZMod M) * ψ (b : ZMod M) *
            (χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff g (a * b / d ^ 2)) := by
          rw [hg.2.2 a b ha hb, Finset.mul_sum]
      _ = ∑ d ∈ (Nat.gcd a b).divisors, twistChar χ ψ (d : ZMod (N * M ^ 2)) *
            (d : ℂ) ^ (k - 1) * coeff g' (a * b / d ^ 2) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hdab : d ∣ Nat.gcd a b := Nat.dvd_of_mem_divisors hd
          have hdd : d ^ 2 ∣ a * b := by
            rw [sq]
            exact Nat.mul_dvd_mul (hdab.trans (Nat.gcd_dvd_left a b))
              (hdab.trans (Nat.gcd_dvd_right a b))
          have h2 : (a : ZMod M) * b = (d : ZMod M) ^ 2 * ((a * b / d ^ 2 : ℕ) : ZMod M) := by
            rw [← Nat.cast_mul, ← Nat.cast_pow, ← Nat.cast_mul, Nat.mul_div_cancel' hdd]
          rw [twistChar_natCast, hcoeff, ← map_mul ψ, h2, map_mul ψ, map_pow ψ]
          ring

end ZInQ.Contrib.CloudW08EigenformTwists
