import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates

/-! Descend exactly the moving and unary blocks in a fixed test. The odd
descent argument works on each column set separately; no spanning at
unrelated characters or levels is needed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion ModularForm ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {I J K L₀ : Type} [Fintype I] [Field K] [AddCommGroup L₀]
variable {ε : L₀ →+ ZMod 2} {T : TypeData L₀ ε} {N : ℕ}

/-- The complex columns supported at one intrinsic level and character.
The zero slot is the formal zero of the inventory convention. -/
def blockColumns (Y : Inventory I J K T N) (κ : K →+* ℂ)
    (m : ℕ) (χ : (ZMod N)ˣ →* Kˣ) : Set (ℕ → ℂ) :=
  {c | ∃ x, Y.level x ∣ m ∧ Y.χ (Y.origin x) = χ ∧
    (fun n => κ (Y.expansion x n)) = c}

/-- The pointwise version of `spansAt_of_complex`, followed by
`coordinates_of_span`. Only the span of this one series is used. -/
theorem coordinates_of_block_span (Y : Inventory I J K T N) {avoid : Finset ℕ}
    (hc : ∀ q, Test T avoid q → q.Coprime N) (κ : K →+* ℂ)
    (m : ℕ) (χ : (ZMod N)ˣ →* Kˣ) (a : ℕ → K)
    (ha : (fun n => κ (a n)) ∈ Submodule.span ℂ (blockColumns Y κ m χ)) :
    ∃ v : I → K, (∀ n, (Y.toBasis hc).eval n v = a n) ∧
      ∀ x, v x ≠ 0 → Y.level x ∣ m ∧ Y.χ (Y.origin x) = χ := by
  classical
  let S := {x : I // Y.level x ∣ m ∧ Y.χ (Y.origin x) = χ}
  let col : S → ℕ → K := fun x => Y.expansion x.val
  have hset : blockColumns Y κ m χ = Set.range (fun (x : S) n => κ (col x n)) := by
    ext c
    exact ⟨fun ⟨x, hm, hχ, h⟩ => ⟨⟨x, hm, hχ⟩, h⟩,
      fun ⟨x, h⟩ => ⟨x.val, x.property.1, x.property.2, h⟩⟩
  rw [hset] at ha
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ha
  let : Algebra K ℂ := κ.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap K ℂ) := κ.injective
  obtain ⟨r, hr⟩ := (Algebra.linearMap K ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hleft (k : K) : r (κ k) = k := DFunLike.congr_fun hr k
  have hrange : a ∈ Submodule.span K (Set.range col) := by
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun x => r (z x), ?_⟩
    funext n
    have h := congrArg (fun b : ℕ → ℂ => r (b n)) hz
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, hleft] at h ⊢
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_comm (z x)]
    change r (z x) * col x n = r (col x n • z x)
    rw [map_smul, smul_eq_mul, mul_comm]
  apply coordinates_of_span Y hc (m := m) (χ := χ)
  refine Submodule.span_mono ?_ hrange
  rintro _ ⟨x, rfl⟩
  exact ⟨x.val, x.property.1, x.property.2, rfl⟩

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {O : Type} [CommRing O] [Algebra O K]

/-- The moving and unary spans for a single set furnish a vector for the
actual joined form, using the division already computed from the source.
Each span uses only columns with the block's own level and character. -/
theorem joined_coordinates_of_block_spans {avoid : Finset ℕ}
    (C : SourceAtPlace P O K) (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (Y : Inventory I J K (evenTypes W.S hS.1) N)
    (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
    (κ : K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
    (χB : (ZMod N)ˣ →* Kˣ) (χJ : ℕ → (ZMod N)ˣ →* Kˣ)
    (hB : (fun n => κ (timesTheta (TL (fun p => C.eK (C.η₀ p)) U.toList
      (fun k => C.eK (C.c k))) n)) ∈ Submodule.span ℂ
        (blockColumns Y κ (movingLevel P U) χB))
    (hJ : ∀ j ∈ subscripts U, (fun n => κ (timesTheta
      (unaryCoeff (evenTypes W.S hS.1).Good (fun p => C.eK (C.η₀ p)) i j) n)) ∈
        Submodule.span ℂ (blockColumns Y κ (maskedLevel P * j) (χJ j))) :
    ∃ v : I → K, ∀ n, κ ((Y.toBasis hc).eval n v) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  classical
  let phase : ℕ → K := fun p => C.eK (C.η₀ p)
  let a : ℕ → K := fun n => C.eK (C.c n)
  let good := (evenTypes W.S hS.1).Good
  obtain ⟨b, hb, _⟩ := coordinates_of_block_span Y hc κ _ _ _ hB
  have hu (j : ℕ) (hj : j ∈ subscripts U) :=
    coordinates_of_block_span Y hc κ _ _ _ (hJ j hj)
  choose u hu' _ using hu
  let un : ℕ → I → K := fun j => if hj : j ∈ subscripts U then u j hj else 0
  refine ⟨(2 : K) ^ (-(P.δ + U.card + 1)) •
    (b - ∑ j ∈ subscripts U, TL phase U.toList a j • un j), fun n => ?_⟩
  rw [evenVector_eval _ good phase a P.δ i U b un hb
    (fun j hj k => by simpa only [un, dite_eq_left hj] using hu' j hj k) n, joinedForm_coeff]
  have hη (p : ℕ) : κ (phase p) = P.phaseData.η p := by
    rw [← RingHom.comp_apply, hκ, C.complex_eta]
  have ha (k : ℕ) : κ (a k) = P.sievedCoeff k := by
    rw [← RingHom.comp_apply, hκ, C.complex_coeff]
  simp only [timesTheta, map_add, map_mul, map_sum, map_ofNat, halfDivided, map_zpow₀,
    map_rawNumerator_scaled κ hη (fun k => (ha k).trans (one_mul _).symm), one_mul, good]

end ZInQ.Manuscript.RC.EvenJoin
