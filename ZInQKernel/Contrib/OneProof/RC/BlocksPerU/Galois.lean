import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Constituents

/-! Use the intrinsic good attachment once per source, including all its
dilations. The Eisenstein representation is the direct sum of the two
characters, with the cyclotomic twist on the second line. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff O12Formwise AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {K L : Type} [Field K] [TopologicalSpace K] [AddCommGroup L]
variable {ε : L →+ ZMod 2} {T : TypeData L ε} {frob : ℕ → GalQ}

def GoodValues (ρ : GalQ →* GL (Fin 2) K) (frob : ℕ → GalQ)
    (a χ : ℕ → K) (q : ℕ) : Prop :=
  ((ρ (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = a q ∧
  ((ρ (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (q : K) * χ q

def UnramifiedAt (ρ : GalQ →* GL (Fin 2) K) (q : ℕ) : Prop :=
  ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
    ∀ σ ∈ Q.inertia GalQ, ρ σ = 1

/-- One intrinsic attachment. In the cuspidal case the same existing good
Carayol assertion is used at every good prime away from the source level.
In the Eisenstein case the fields identify the actual Dirichlet pair. -/
structure SourceAttachment (m : ℕ) (frob : ℕ → GalQ)
    (s : EigenSource K (IntrinsicGood T m)) where
  ρ : GalQ →* GL (Fin 2) K
  continuous : Continuous fun g => ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  unramified : ∀ q, IntrinsicGood T m q → UnramifiedAt ρ q
  cusp : ∀ a χ hz hr, s = .cusp a χ hz hr →
    ∀ q, IntrinsicGood T m q → GoodValues ρ frob a χ q
  eis : ∀ α β, s = .eis α β →
    ∃ Eχ : EisensteinCharacters α β m, ∀ g,
      ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(Eχ.first g : K), (Eχ.second g : K)]

/-- Specialize the existing good cuspidal attachment to the embedded
coefficients, with matrix continuity and arithmetic Frobenius. -/
def SourceAttachment.ofCusp {m : ℕ} (a χ : ℕ → K) (hz : a 0 = 0)
    (hr : ∀ q, IntrinsicGood T m q → GoodRec a (a q) (χ q) q)
    (ρ : GalQ →* GL (Fin 2) K)
    (hcont : Continuous fun g => ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (hgood : ∀ q, IntrinsicGood T m q → UnramifiedAt ρ q ∧ GoodValues ρ frob a χ q) :
    SourceAttachment m frob (.cusp a χ hz hr) where
  ρ := ρ
  continuous := hcont
  unramified q hq := (hgood q hq).1
  cusp a' χ' _ _ h q hq := by cases h; exact (hgood q hq).2
  eis _ _ h := by contradiction

private def diagonalPair (a b : Kˣ) : GL (Fin 2) K where
  val := Matrix.diagonal ![(a : K), (b : K)]
  inv := Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; fin_cases i <;> simp

private def eisRepresentation {α β : ℕ →* K} {m : ℕ}
    (Eχ : EisensteinCharacters α β m) : GalQ →* GL (Fin 2) K where
  toFun g := diagonalPair (Eχ.first g) (Eχ.second g)
  map_one' := by
    apply Units.ext
    simp [diagonalPair, ← Matrix.diagonal_one]
  map_mul' g h := by
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; fin_cases i <;> simp

/-- Construct the Eisenstein attachment from the two actual characters.
Continuity of the two scalar characters suffices. -/
def SourceAttachment.ofEis {m : ℕ} {α β : ℕ →* K} (Eχ : EisensteinCharacters α β m)
    (h₁ : Continuous fun g => (Eχ.first g : K))
    (h₂ : Continuous fun g => (Eχ.second g : K)) :
    SourceAttachment (T := T) m frob (.eis α β) where
  ρ := eisRepresentation Eχ
  continuous := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [eisRepresentation, diagonalPair, h₁, h₂, continuous_const]
  unramified q hq Q hQ hqQ σ hσ := by
    obtain ⟨hfirst, hsecond⟩ :=
      Eχ.inertia_values hq.1.1 hq.1.ne_two hq.2 hQ hqQ hσ
    apply Units.ext
    change Matrix.diagonal ![(Eχ.first σ : K), (Eχ.second σ : K)] = 1
    rw [hfirst, hsecond, ← Matrix.diagonal_one]
    congr 1; funext i; fin_cases i <;> simp
  cusp _ _ _ _ h := by contradiction
  eis _ _ h := by cases h; exact ⟨Eχ, fun _ => rfl⟩

private theorem SourceAttachment.cusp_restrict {m : ℕ}
    {s : EigenSource K (IntrinsicGood T m)} (A : SourceAttachment m frob s)
    {Q : ℕ → Prop} (hQ : ∀ q, Q q → IntrinsicGood T m q) {a χ hz hr}
    (h : restrictSource hQ s = .cusp a χ hz hr)
    (q : ℕ) (hq : IntrinsicGood T m q) :
    GoodRec a (a q) (χ q) q ∧ GoodValues A.ρ frob a χ q := by
  cases s with
  | cusp a' χ' hz' hr' =>
    change EigenSource.cusp a' χ' hz' _ = _ at h
    cases h
    exact ⟨hr' q hq, A.cusp _ _ _ _ rfl q hq⟩
  | eis α β => contradiction

private theorem SourceAttachment.eis_restrict {m : ℕ}
    {s : EigenSource K (IntrinsicGood T m)} (A : SourceAttachment m frob s)
    {Q : ℕ → Prop} (hQ : ∀ q, Q q → IntrinsicGood T m q) {α β}
    (h : restrictSource hQ s = .eis α β) :
    ∃ Eχ : EisensteinCharacters α β m, ∀ g,
      ((A.ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(Eχ.first g : K), (Eχ.second g : K)] := by
  cases s with
  | cusp a χ hz hr => contradiction
  | eis α' β' =>
    change EigenSource.eis α' β' = _ at h
    cases h
    exact A.eis _ _ rfl

variable {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
variable (X : Inventory I J K T N) (hc : ∀ q, Test T avoid q → q.Coprime N)
variable (H : ∀ s : J, SourceAttachment (X.sourceLevel s) frob (X.source s))

omit [TopologicalSpace K] in
theorem Inventory.sourceLevel_dvd (i : I) : X.sourceLevel (X.origin i) ∣ N :=
  (dvd_mul_right _ _).trans (X.level_dvd i)

theorem Inventory.cusp_data {i : I} {a χ hz hr}
    (h : (X.toBasis hc).base i = .cusp a χ hz hr) (q : ℕ) (hq : T.Good q)
    (hcop : q.Coprime (X.level i)) :
    GoodRec a (a q) (χ q) q ∧ GoodValues (H (X.origin i)).ρ frob a χ q :=
  (H (X.origin i)).cusp_restrict
    (fun q hq => ⟨hq.1, (hc q hq).of_dvd_right (X.sourceLevel_dvd i)⟩) h q
    ⟨hq, hcop.of_dvd_right (dvd_mul_right _ _)⟩

theorem Inventory.eis_data {i : I} {α β}
    (h : (X.toBasis hc).base i = .eis α β) :
    ∃ Eχ : EisensteinCharacters α β (X.sourceLevel (X.origin i)), ∀ g,
      (((H (X.origin i)).ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(Eχ.first g : K), (Eχ.second g : K)] :=
  (H (X.origin i)).eis_restrict
    (fun q hq => ⟨hq.1, (hc q hq).of_dvd_right (X.sourceLevel_dvd i)⟩) h

def Inventory.attachment (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) :
    Attachment (X.toBasis hc) frob where
  ρ i := (H (X.origin i)).ρ
  continuous i := (H (X.origin i)).continuous
  unramified q hq hqa Q hQ hqQ σ hσ i :=
    (H (X.origin i)).unramified q
      ⟨hq, (hc q ⟨hq, hqa⟩).of_dvd_right (X.sourceLevel_dvd i)⟩ Q hQ hqQ σ hσ
  cusp i a χ hz hr h q :=
    (X.cusp_data hc H h q.val q.property.1 ((hc q.val q.property).of_dvd_right
      (X.level_dvd i))).2
  eis i α β h := by
    obtain ⟨Eχ, he⟩ := X.eis_data hc H h
    refine ⟨Eχ.first, Eχ.second, he, fun q => ?_⟩
    exact Eχ.frob_values q.property.1.1 q.property.1.ne_two
      ((hc q.val q.property).of_dvd_right (X.sourceLevel_dvd i))
      (hfrob q.val q.property.1)

#print axioms SourceAttachment.ofCusp
#print axioms SourceAttachment.ofEis
#print axioms SourceAttachment.cusp_restrict
#print axioms SourceAttachment.eis_restrict
#print axioms Inventory.sourceLevel_dvd
#print axioms Inventory.cusp_data
#print axioms Inventory.eis_data
#print axioms Inventory.attachment

end ZInQ.Manuscript.RC.BlocksPerU
