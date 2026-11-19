import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Centre

/-!
# Theorem 5.3, Lane RC32 round 5: `DecompositionFrobeniusQ` from the local Galois decomposition

`DecompositionFrobeniusQ r hr` (round four) is reduced to `LocalGaloisDecomposition r hr`, the
classical description of the local Galois group inside `G_ℚ` (Neukirch, *Algebraic Number Theory*,
II.8–9; Serre, *Local Fields*, II §3, I §7): a valuation `w` of `ℚ̄_r` extending `v_r` such that

* (inv) `w` is invariant under `Gal(ℚ̄_r/ℚ_r)` (uniqueness of the extension, Neukirch II.4.8);
* (res) for every embedding `ι : ℚ̄ → ℚ̄_r`, every `w`-integral element of `ℚ̄_r` is congruent to an
  element of `ι(ℤ̄)` modulo the maximal ideal (the residue field of `ℚ̄_r` is `𝔽̄_r`, the image of
  `ℤ̄`; Neukirch II.7);
* (dec) for every embedding `ι`, every element of the decomposition group of its centre extends to
  `Gal(ℚ̄_r/ℚ_r)` along `ι` (`D_P = ι⁻¹ Gal(ℚ̄_r/ℚ_r) ι`, Neukirch II.9.6).

PROVED here:

* `frobAtPrime_transfer`: if `σ ∘ ι = ι ∘ h` and `h` is a Frobenius element at the centre of `ι`,
  then `σ` is an arithmetic Frobenius for `w` (the RC53 group's `IsArithmeticFrobeniusOnClosureQ`),
  from (inv) and (res): `σ y − y^r ≡ ι(h x − x^r) ≡ 0` for `y ≡ ι x`;
* `decompositionFrobeniusQ_of_local : LocalGaloisDecomposition r hr → DecompositionFrobeniusQ r hr`
  (the centre `P` of a Frobenius element, an embedding with centre `P`, `h • P = P`, (dec));
* `frobeniusTrace_of_RD_local : (R) → (D) → (∀ odd r, LocalGaloisDecomposition r) →
  FrobeniusTrace E`.

Kinds: definitions, PROVED; `LocalGaloisDecomposition` is the named GLUE input (a hypothesis).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar coe_smul_Zbar)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ primeIdealQ_absNorm
  IsArithmeticFrobeniusOnClosureQ)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree)
open scoped WithZero Pointwise

variable {r : ℕ} {hr : r.Prime}

/-- **The local Galois decomposition at `r`** (GLUE: Neukirch ANT II.4.8, II.7, II.9.6; Serre,
Local Fields, II §3): a `Gal(ℚ̄_r/ℚ_r)`-invariant valuation of `ℚ̄_r` extending `v_r`, whose residue
field is reached from `ℤ̄` along every embedding, and along which every element of the decomposition
group of the centre of an embedding extends to `Gal(ℚ̄_r/ℚ_r)`. -/
def LocalGaloisDecomposition (r : ℕ) (hr : r.Prime) : Prop :=
  ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (w : Valuation (Qrbar r hr) Γ)
    (hw : ExtendsVr w),
    (∀ (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (y : Qrbar r hr), w (σ y) = w y) ∧
    (∀ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr), w y ≤ 1 →
      ∃ x : Zbar, w (y - ι x) < 1) ∧
    (∀ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ), g • centre hw ι = centre hw ι →
      ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr, ∀ x : Qbar, σ (ι x) = ι (g x))

section Transfer

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {w : Valuation (Qrbar r hr) Γ}

/-- `(a + m)^n − a^n` is a multiple of `m` with an integral cofactor (PROVED). -/
theorem add_pow_sub_pow_lt (a m : Qrbar r hr) (ha : w a ≤ 1) (hm : w m < 1) (n : ℕ) :
    w ((a + m) ^ n - a ^ n) < 1 := by
  have hgeom := geom_sum₂_mul (a + m) a n
  rw [add_sub_cancel_left] at hgeom
  rw [← hgeom, map_mul]
  have ham : w (a + m) ≤ 1 := le_trans (w.map_add _ _) (max_le ha hm.le)
  have hsum : w (∑ i ∈ Finset.range n, (a + m) ^ i * a ^ (n - 1 - i)) ≤ 1 := by
    refine Valuation.map_sum_le w fun i _ => ?_
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ham i) (pow_le_one' ha _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hsum) hm

/-- **The Frobenius transfer** (PROVED): if `σ ∘ ι = ι ∘ h`, `h` is a Frobenius element at the
centre of `ι`, `w` is `σ`-invariant and the residues of `w` are reached from `ι(ℤ̄)`, then `σ` is an
arithmetic Frobenius for `w`. -/
theorem frobAtPrime_transfer (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (h : GalQ)
    (hF : FrobAtPrime h r (centre hw ι)) (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr)
    (hσ : ∀ x : Qbar, σ (ι x) = ι (h x)) (hinv : ∀ y, w (σ y) = w y)
    (hres : ∀ y, w y ≤ 1 → ∃ x : Zbar, w (y - ι x) < 1) :
    IsArithmeticFrobeniusOnClosureQ (primeIdealQ r hr) Γ w σ := by
  intro y hy
  rw [primeIdealQ_absNorm]
  obtain ⟨x, hx⟩ := hres y hy
  set m := y - ι x with hm
  have hy' : y = ι x + m := by rw [hm]; ring
  have h1 : w (ι ((h • x - x ^ r : Zbar) : Qbar)) < 1 := hF.2.2 x
  have h1' : ι ((h • x - x ^ r : Zbar) : Qbar) = σ (ι x) - (ι x) ^ r := by
    push_cast
    rw [coe_smul_Zbar, map_sub, map_pow, hσ]
  have key : σ y - y ^ r =
      ι ((h • x - x ^ r : Zbar) : Qbar) + σ m - ((ι x + m) ^ r - (ι x) ^ r) := by
    rw [h1', hy', map_add]
    ring
  rw [key]
  have h2 : w (σ m) < 1 := by rw [hinv]; exact hx
  have h3 := add_pow_sub_pow_lt (ι x) m (le_one_of_mem_Zbar hw ι x) hx r
  refine lt_of_le_of_lt (w.map_sub _ _) (max_lt ?_ h3)
  exact lt_of_le_of_lt (w.map_add _ _) (max_lt h1 h2)

end Transfer

/-- **`DecompositionFrobeniusQ` from the local Galois decomposition** (PROVED): the centre `P` of a
Frobenius element `h`, an embedding `ι` with centre `P` (`exists_embedding_centre`), `h • P = P`
(`FrobAtPrime.smul_eq`), the extension `σ` of `h` (dec), and the Frobenius transfer. -/
theorem decompositionFrobeniusQ_of_local (H : LocalGaloisDecomposition r hr) :
    DecompositionFrobeniusQ r hr := by
  intro h hF
  obtain ⟨Γ, inst, w, hw, hinv, hres, hdec⟩ := H
  obtain ⟨P, hP⟩ := (isFrobAtC10_iff h r).mp hF
  have := hP.1
  obtain ⟨ι, hι⟩ := exists_embedding_centre hw P hP.2.1
  have hPc : FrobAtPrime h r (centre hw ι) := by rw [hι]; exact hP
  have hfix : h • centre hw ι = centre hw ι := hPc.smul_eq hr
  obtain ⟨σ, hσ⟩ := hdec ι h hfix
  exact ⟨ι, Γ, inst, w, hw, σ, frobAtPrime_transfer hw ι h hPc σ hσ (hinv σ) (hres ι), hσ⟩

/-- **`FrobeniusTrace` from (R), (D) and the local Galois decompositions** (PROVED, for every
elliptic `E`). -/
theorem frobeniusTrace_of_RD_local (hR : TateReductionComparison) (hD : DetEqDegree)
    (hLoc : ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → LocalGaloisDecomposition r hr)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : FrobeniusTrace E :=
  frobeniusTrace_of_RD_decomposition hR hD
    (fun r hr hr2 => decompositionFrobeniusQ_of_local (hLoc r hr hr2)) E

end ZInQ.Manuscript.RC.Wiring
