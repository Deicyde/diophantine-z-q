import ZInQKernel.Contrib.CloudB3RC53.TraceWitness.DihedralConstituentModel
import ZInQKernel.Contrib.RC53Assist.RelBridge.Reduced

/-!
# The dihedral constituent model as a reduced constituent model

Consistency check, not part of the manuscript (non-vacuity). `DihedralConstituentModel.lean`
builds `dihModel T ap B : ConstituentModelRel T (Rd T) ap B`, a constituent model whose reading is
nonzero (`constituentModelRel_nonzero`). Its reading of a vector `v` of the congruence lattice
`Lam` is `Σ_k c_k · (v_{(b,k)} − v_{(b,0)})/2 mod 2` over the block `b` of `U`. It does not factor
through the coordinatewise reduction of `v` modulo `2`: `v` and `v + 2·e_{(b,1)}` have the same
coordinates modulo `2` but readings differing by `c_1`.

The reduced constituent model `ConstituentModelRed` (`RC53Assist/RelBridge/Reduced.lean`) reads
the forms through an integral expansion `expand : Λ → (C → ℤ)` reduced coefficientwise modulo `2`.
This file supplies an expansion containing the half-difference coordinates:

* `C = Iw ⊕ Iw`: the coordinates `v_i` (`inl i`) and the half-differences
  `(v_{(b,k)} − v_{(b,0)})/2` (`inr (b, k)`), which are integers on `Lam`;
* `coefK` (over `ℚ`), `expand` (over `ℤ`, the floor of `coefK`, which is exact on `Lam`) and
  `expand_spec`;
* `readRed T U`: the reading on reduced expansions, `Σ_k c_k · r_{inr (b,k)}` in `ℤ/2`;
* `dih_hread` (PROVED): `dihModel`'s reading of `v mod 2Λ` equals `readRed` of the reduced
  expansion of `v` (the `hread` hypothesis of `ConstituentModelRed.ofConstituentModelRel_inputs`).

Results (all PROVED):
* `dihModelRed T ap B : ConstituentModelRed T (Rd T) ap B` and `dihModelRed_inputs` (with even
  `a_p` and `B ≤ 2`), through `ConstituentModelRed.ofConstituentModelRel`;
* `constituentModelRed_nonzero`: a reduced constituent model with its inputs and reading one at
  `{3}` for the sign type data, so the reduced interface is inhabited with a nonzero reading;
* `rulesUpTo_dihModelRed`: RC2's rules up to `1` through `rulesUpTo_of_constituentsRed`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TraceWitness.Dih

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.AddressGenuine ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open ZInQ.Contrib.RC53Assist.RelBridge

/-- The expansion coordinates: the entries (`inl`) and the half-differences (`inr`). -/
abbrev Cw : Type := Iw ⊕ Iw

/-- **The rational expansion**: entries and half-differences `(w_{(b,k)} − w_{(b,0)})/2`. -/
def coefKw : (Iw → ℚ) →ₗ[ℚ] (Cw → ℚ) where
  toFun w := Sum.elim w (fun i => (w i - w (i.1, 0)) / 2)
  map_add' w w' := by
    funext n; rcases n with i | i
    · rfl
    · simp only [Sum.elim_inr, Pi.add_apply]; ring
  map_smul' c w := by
    funext n; rcases n with i | i
    · rfl
    · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- On the lattice, every expansion coordinate is an integer. -/
theorem coefKw_int (v : Lam) (n : Cw) : ∃ z : ℤ, coefKw (v : Iw → ℚ) n = z := by
  rcases n with i | ⟨b, k⟩
  · exact v.2.1 i
  · obtain ⟨z, hz⟩ := v.2.2 b k 0
    refine ⟨z, ?_⟩
    change ((v : Iw → ℚ) (b, k) - (v : Iw → ℚ) (b, 0)) / 2 = z
    rw [hz]; ring

theorem cast_floor_coefKw (v : Lam) (n : Cw) :
    ((⌊coefKw (v : Iw → ℚ) n⌋ : ℤ) : ℚ) = coefKw (v : Iw → ℚ) n := by
  obtain ⟨z, hz⟩ := coefKw_int v n
  rw [hz, Int.floor_intCast]

/-- **The integral expansion** (exact: the floor of an integer). -/
def expandw : Lam →ₗ[ℤ] (Cw → ℤ) where
  toFun v n := ⌊coefKw (v : Iw → ℚ) n⌋
  map_add' v w := by
    funext n
    apply Int.cast_injective (α := ℚ)
    simp only [Pi.add_apply, Int.cast_add, cast_floor_coefKw]
    rw [Submodule.coe_add, map_add]
    rfl
  map_smul' c v := by
    funext n
    apply Int.cast_injective (α := ℚ)
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, cast_floor_coefKw, RingHom.id_apply]
    rw [Submodule.coe_smul, show (c • (v : Iw → ℚ)) = (c : ℚ) • (v : Iw → ℚ) by
      ext i; simp [zsmul_eq_mul], map_smul]
    rfl

theorem expandw_spec (v : Lam) (n : Cw) :
    algebraMap ℤ ℚ (expandw v n) = coefKw (v : Iw → ℚ) n := by
  rw [algebraMap_int_eq, eq_intCast]
  exact cast_floor_coefKw v n

/-- `ℤ/2ℤ` (as the quotient by the ideal `(2)`) to `ZMod 2`. -/
def quot2 : (ℤ ⧸ Ideal.span {(2 : ℤ)}) →+ ZMod 2 :=
  (Ideal.Quotient.lift (Ideal.span {(2 : ℤ)}) (Int.castRingHom (ZMod 2)) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    simp only [eq_intCast, Int.cast_mul]
    rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul])).toAddMonoidHom

theorem quot2_mk (a : ℤ) : quot2 (Ideal.Quotient.mk _ a) = (a : ZMod 2) := rfl

variable {ε : ZMod 2 →+ ZMod 2}

/-- **The reading on reduced expansions**: `Σ_k c_k · r_{inr (b,k)}` over the block of `U`. -/
def readRed (T : TypeData (ZMod 2) ε) (U : Finset ℕ) :
    (Cw → ℤ ⧸ Ideal.span {(2 : ℤ)}) →+ ZMod 2 where
  toFun r := match blockOf U with
    | none => 0
    | some b => ∑ k : Fin 4, coefB T b k * quot2 (r (Sum.inr (b, k)))
  map_zero' := by cases blockOf U <;> simp
  map_add' r r' := by
    cases blockOf U with
    | none => simp
    | some b =>
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- **`hread`**: the reading of `dihModel` on `Λ/2Λ` is the reading of the reduced expansion.
PROVED. -/
theorem dih_hread (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) (ap : ℕ → ℤ) (B : ℕ)
    (U : Finset ℕ) (v : (dihModel T ap B).Λ) :
    (dihModel T ap B).read U (Submodule.Quotient.mk v) =
      readRed T U (redExpOf (dihModel T ap B).m expandw v) := by
  change readFun T U v = readRed T U (redExpOf (Ideal.span {(2 : ℤ)}) expandw v)
  unfold readFun readRed
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  cases blockOf U with
  | none => rfl
  | some b =>
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1

/-- **The dihedral model as a reduced constituent model.** -/
def dihModelRed (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) (ap : ℕ → ℤ) (B : ℕ) :
    ConstituentModelRed T (Rd T) ap B :=
  ConstituentModelRed.ofConstituentModelRel (dihModel T ap B) coefKw expandw expandw_spec
    (readRed T)

/-- **Its inputs** (even `a_p`, `B ≤ 2`). PROVED. -/
theorem dihModelRed_inputs (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) (ap : ℕ → ℤ)
    (hap : ∀ p, Even (ap p)) (B : ℕ) (hB : B ≤ 2) : (dihModelRed T ap B).Inputs :=
  ConstituentModelRed.ofConstituentModelRel_inputs (dihModel T ap B) coefKw expandw expandw_spec
    (readRed T) (dih_hread T ap B) (dihModel_inputs T ap hap B hB)

/-- **Non-vacuity of `ConstituentModelRed` with a nonzero reading**: for the sign type data, a
reduced constituent model with its inputs whose reading is one at `{3}`. PROVED. -/
theorem constituentModelRed_nonzero (B : ℕ) (hB : B ≤ 2) :
    ∃ R : Finset ℕ → ZMod 2,
      (∃ X : ConstituentModelRed signTypeData R (fun _ => 0) B, X.Inputs) ∧ R {3} = 1 :=
  ⟨Rd signTypeData, ⟨dihModelRed signTypeData _ B,
    dihModelRed_inputs signTypeData _ (fun _ => ⟨0, rfl⟩) B hB⟩, Rd_three⟩

/-- **RC2's rules up to `1` from the reduced dihedral model.** PROVED. -/
theorem rulesUpTo_dihModelRed :
    RulesUpTo (AddMonoidHom.id (ZMod 2)) (symb signTypeData (Rd signTypeData)) 1 :=
  rulesUpTo_of_constituentsRed (dihModelRed signTypeData (fun _ => 0) 2)
    (dihModelRed_inputs signTypeData _ (fun _ => ⟨0, rfl⟩) 2 le_rfl) (fun _ _ => ⟨0, rfl⟩)

end ZInQ.Contrib.CloudB3RC53.TraceWitness.Dih
