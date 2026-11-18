import ZInQKernel.Contrib.OneProof.RC.O12Local.Ramified
import ZInQKernel.Contrib.OneProof.RC.O12Local.Whittaker
import ZInQKernel.Contrib.OneProof.RC.O12.Inputs

/-! The local direct sum and its interface with (O.12) (tex 9754–9771, 9857–9873).
The Eisenstein sector and its Fourier shift are separate inputs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix AddressGenuine PrintsArith Symbols
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}
variable {p : ℕ} {P : O12.LocalPair p}

def SupportedOn {I E : Type*} [Zero E] (S : Set I) (v : I → E) : Prop :=
  ∀ i, i ∉ S → v i = 0

/-- Retain exactly the coordinates of one summand. Provenance (c). -/
def mask {I E : Type*} [Field E] (S : Set I) : (I → E) →ₗ[E] (I → E) := by
  classical
  exact {
    toFun := fun v i => if i ∈ S then v i else 0
    map_add' := by intro v w; funext i; by_cases h : i ∈ S <;> simp [h]
    map_smul' := by intro c v; funext i; by_cases h : i ∈ S <;> simp [h] }

theorem mask_apply {I E : Type*} [Field E] (S : Set I) (v : I → E) (i : I) :
    mask S v i = @ite E (i ∈ S) (Classical.propDecidable _) (v i) 0 := rfl

theorem mask_supported {I E : Type*} [Field E] {S S' : Set I} {v : I → E}
    (hv : SupportedOn S' v) : SupportedOn (S ∩ S') (mask S v) := by
  intro i hi
  rw [mask_apply]
  split
  · rename_i h
    exact hv i (fun h' => hi ⟨h, h'⟩)
  · rfl

theorem split_supported {I E : Type*} [Field E] {S S' : Set I} (hd : Disjoint S S')
    {v : I → E} (hv : SupportedOn (S ∪ S') v) : v = mask S v + mask S' v := by
  classical
  funext i
  change v i = mask S v i + mask S' v i
  rw [mask_apply, mask_apply]
  by_cases h : i ∈ S
  · have h' : i ∉ S' := fun h' => Set.disjoint_left.mp hd h h'
    simp [h, h']
  · by_cases h' : i ∈ S'
    · simp [h, h']
    · simp [h, h', hv i (fun hi => hi.elim h h')]

/-- A sector of the ambient coordinate space, before asking which vectors of it
occur in the particular form (F_U). Provenance (c). -/
structure Sector (X : GaloisConstituentModel T R ap B chiType) (P : O12.LocalPair p) where
  active : Set X.I
  ramified : Set X.I
  ramified_active : ramified ⊆ active
  Up : (X.I → X.K) →ₗ[X.K] (X.I → X.K)
  active_stable : ∀ v, SupportedOn active v → SupportedOn active (Up v)
  ramified_stable : ∀ v, SupportedOn ramified v → SupportedOn ramified (Up v)
  old : ∀ i ∈ active, i ∉ ramified → X.ρ i P.τ = 1
  newLine : ∀ i ∈ ramified, ∃ (b : GL (Fin 2) X.K) (lam mu : X.K),
    (↑(b * X.ρ i P.τ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
    (↑(b * X.ρ i P.φ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] ∧
    ∀ v, SupportedOn active v → Up v i = lam * v i

/-- The two types of cuspidal block in tex 9754–9759. -/
inductive CuspidalKind
  | thetaB
  | unary (J : Finset ℕ)

def CuspidalKind.ramifiedAt (p : ℕ) : CuspidalKind → Prop
  | .thetaB => True
  | .unary J => p ∈ J

variable [Fact p.Prime]

/-- The cuspidal coordinates of the actual summands (tex 9754–9771).
All copies indexed by the same factor use one local representation and
one Galois representation. On the unused ambient coordinates the
cuspidal operator will be extended by zero. -/
structure CuspidalData (X : GaloisConstituentModel T R ap B chiType) (P : O12.LocalPair p) where
  Factor : Type
  kind : Factor → CuspidalKind
  factor : X.I → Option Factor
  ρ : Factor → GalQ →* GL (Fin 2) X.K
  coordinate : ∀ i j, factor i = some j → X.ρ i = ρ j
  ram : ∀ j, (kind j).ramifiedAt p → RamifiedFactor X.K P (ρ j)
  /-- The unary blocks omitting (p) are degeneracies of forms of level prime to (p)
  (tex 9757–9760). Here is the Carayol unramified comparison for those source forms. -/
  primeTo : ∀ j, ¬ (kind j).ramifiedAt p → CarayolUnramified P (ρ j)
  /-- The actual action on the sum of the level-prime-to-(p) degeneracy spaces.
  No scalar or diagonal form for this action is required by (O.12). -/
  oldUp : (X.I → X.K) →ₗ[X.K] (X.I → X.K)

namespace CuspidalData

variable (D : CuspidalData X P)

def active : Set X.I := {i | ∃ j, D.factor i = some j}

def ramified : Set X.I := {i | ∃ j, D.factor i = some j ∧ (D.kind j).ramifiedAt p}

def oldCoordinates : Set X.I := D.active \ D.ramified

def generator (j : D.Factor) (h : (D.kind j).ramifiedAt p) : RamifiedLine (D.ram j h) :=
  Classical.choice (D.ram j h).line

/-- Ramified summands carry the computed operator; the old-space action may
mix its degeneracy coordinates. Restrict it to the old coordinate subspace. -/
def diagonalEntry (i : X.I) : X.K := by
  classical
  exact match D.factor i with
  | none => 0
  | some j => if h : (D.kind j).ramifiedAt p then (D.generator j h).eigenvalue else 0

def up : (X.I → X.K) →ₗ[X.K] (X.I → X.K) :=
  scalarOp D.diagonalEntry + (mask D.oldCoordinates).comp (D.oldUp.comp (mask D.oldCoordinates))

theorem diagonalEntry_eq {i : X.I} {j : D.Factor} (hj : D.factor i = some j)
    (h : (D.kind j).ramifiedAt p) : D.diagonalEntry i = (D.generator j h).eigenvalue := by
  classical
  simp [diagonalEntry, hj, h]

theorem diagonalEntry_eq_zero {i : X.I} (hi : i ∉ D.ramified) : D.diagonalEntry i = 0 := by
  classical
  cases e : D.factor i with
  | none => simp [diagonalEntry, e]
  | some j =>
      have h : ¬ (D.kind j).ramifiedAt p := fun h => hi ⟨j, e, h⟩
      simp [diagonalEntry, e, h]

theorem up_on_ramified {i : X.I} (hi : i ∈ D.ramified) (v : X.I → X.K) :
    D.up v i = D.diagonalEntry i * v i := by
  classical
  change D.diagonalEntry i * v i + mask D.oldCoordinates (D.oldUp (mask D.oldCoordinates v)) i = _
  rw [mask_apply, ite_eq_right (fun h => h.2 hi), add_zero]

/-- In every coordinate attached to a factor, the cuspidal operator agrees
with the action of the finite Hecke sum on the corresponding local copy. -/
theorem up_on_copy {i : X.I} {j : D.Factor} (hj : D.factor i = some j)
    (h : (D.kind j).ramifiedAt p) (v : X.I → X.K) :
    localHecke (D.ram j h).π (v i • (D.generator j h).gen) =
      D.up v i • (D.generator j h).gen := by
  rw [(D.generator j h).on_copy, D.up_on_ramified ⟨j, hj, h⟩, D.diagonalEntry_eq hj h]

theorem old_unramified {i : X.I} (hi : i ∈ D.active) (hr : i ∉ D.ramified) :
    X.ρ i P.τ = 1 := by
  obtain ⟨j, hj⟩ := hi
  rw [D.coordinate i j hj]
  exact D.primeTo j (fun h => hr ⟨j, hj, h⟩) _ P.inertia

/-- The cuspidal sector of `LocalBlocks`: coordinate support makes preservation
of the ramified subspace formal; its new lines come from the local calculation. -/
def sector : Sector X P where
  active := D.active
  ramified := D.ramified
  ramified_active := fun _ ⟨j, h, _⟩ => ⟨j, h⟩
  Up := D.up
  active_stable := by
    classical
    intro v _ i hi
    have hn : i ∉ D.ramified := fun ⟨j, h, _⟩ => hi ⟨j, h⟩
    change D.diagonalEntry i * v i + mask D.oldCoordinates (D.oldUp (mask D.oldCoordinates v)) i = 0
    rw [D.diagonalEntry_eq_zero hn, zero_mul, mask_apply, ite_eq_right (fun h => hi h.1), add_zero]
  ramified_stable := by
    classical
    intro v hv i hi
    have hm : mask D.oldCoordinates v = 0 := by
      funext k
      rw [mask_apply]
      split
      · rename_i hk
        exact hv k hk.2
      · rfl
    change D.diagonalEntry i * v i + mask D.oldCoordinates (D.oldUp (mask D.oldCoordinates v)) i = 0
    rw [D.diagonalEntry_eq_zero hi, zero_mul, hm, map_zero, map_zero, Pi.zero_apply, add_zero]
  old := fun _ => D.old_unramified
  newLine := by
    intro i hi
    obtain ⟨j, hj, h⟩ := hi
    let C := D.generator j h
    refine ⟨C.basis, C.eigenvalue, C.other, ?_, ?_, ?_⟩
    · rw [D.coordinate i j hj]
      exact C.inertia
    · rw [D.coordinate i j hj]
      exact C.frobenius
    · intro v _
      rw [D.up_on_ramified ⟨j, hj, h⟩, D.diagonalEntry_eq hj h]

end CuspidalData

omit [Fact p.Prime] in
/-- Assemble both sectors, using disjoint coordinate masks and the actual support
of (F_U). The Eisenstein hypothesis is the sector with its own local proofs. -/
def combine {U : Finset ℕ} (C E : Sector X P) (hd : Disjoint C.active E.active)
    (hF : SupportedOn (C.active ∪ E.active) (X.F U : X.I → X.K)) :
    O12.LocalBlocks X U P where
  active := C.active ∪ E.active
  ramified := C.ramified ∪ E.ramified
  Up := C.Up.comp (mask C.active) + E.Up.comp (mask E.active)
  supported := hF
  preserves_ramified := by
    intro v hv i hi
    have use (D : Sector X P) (h₁ : D.active ⊆ C.active ∪ E.active)
        (h₂ : D.ramified ⊆ C.ramified ∪ E.ramified)
        (hr : ∀ j ∈ D.active, j ∈ C.ramified ∪ E.ramified → j ∈ D.ramified) :
        D.Up (mask D.active v) i = 0 := by
      classical
      apply D.ramified_stable
      · intro j hj
        rw [mask_apply]
        split
        · rename_i ha
          exact hv j (fun h => hj (hr j ha h.2))
        · rfl
      · exact fun h => hi ⟨h₁ (D.ramified_active h), h₂ h⟩
    have hc := use C (fun _ h => Or.inl h) (fun _ h => Or.inl h)
      (fun _ hj h => h.elim id
        (fun he => False.elim (Set.disjoint_left.mp hd hj (E.ramified_active he))))
    have he := use E (fun _ h => Or.inr h) (fun _ h => Or.inr h)
      (fun _ hj h => h.elim
        (fun hc => False.elim (Set.disjoint_left.mp hd (C.ramified_active hc) hj)) id)
    change C.Up (mask C.active v) i + E.Up (mask E.active v) i = 0
    rw [hc, he, add_zero]
  old := by
    intro i hi hr
    exact hi.elim (fun h => C.old i h (fun h' => hr (Or.inl h')))
      (fun h => E.old i h (fun h' => hr (Or.inr h')))
  newLine := by
    classical
    intro i hi
    have supp (D : Sector X P) (v : X.I → X.K) : SupportedOn D.active (mask D.active v) := by
      intro j hj
      rw [mask_apply, ite_eq_right hj]
    rcases hi.2 with hc | he
    · obtain ⟨b, lam, mu, ht, hf, h⟩ := C.newLine i hc
      refine ⟨b, lam, mu, ht, hf, fun v _ => ?_⟩
      have hca := C.ramified_active hc
      have hea : i ∉ E.active := fun hh => Set.disjoint_left.mp hd hca hh
      change C.Up (mask C.active v) i + E.Up (mask E.active v) i = _
      rw [h _ (supp C v), E.active_stable _ (supp E v) i hea, add_zero, mask_apply, ite_eq_left hca]
    · obtain ⟨b, lam, mu, ht, hf, h⟩ := E.newLine i he
      refine ⟨b, lam, mu, ht, hf, fun v _ => ?_⟩
      have hea := E.ramified_active he
      have hca : i ∉ C.active := fun hh => Set.disjoint_left.mp hd hh hea
      change C.Up (mask C.active v) i + E.Up (mask E.active v) i = _
      rw [C.active_stable _ (supp C v) i hca, h _ (supp E v), zero_add, mask_apply, ite_eq_left hea]

/-- The Fourier condition on just one sector. Its Eisenstein instance is the
remaining hypothesis for tex 9862–9864. -/
def Sector.UpAtOne (A : O12.FourierData X) (D : Sector X P) (hp : p ≠ 0) : Prop :=
  ∀ v, SupportedOn D.active v →
    X.coefK (D.Up v) (A.index ⟨1, one_ne_zero⟩) = X.coefK v (A.index ⟨p, hp⟩)

omit [Fact p.Prime] in
/-- On a normalized eigenvector the scalar is its coefficient at (p) (tex 9855–9857).
In particular it is algebraic whenever that Fourier coefficient is algebraic. -/
theorem Sector.scalar_eq_p_coeff (A : O12.FourierData X) (D : Sector X P)
    {hp : p ≠ 0} (hs : D.UpAtOne A hp) {v : X.I → X.K} (hv : SupportedOn D.active v)
    {lam : X.K} (he : D.Up v = lam • v)
    (h₁ : X.coefK v (A.index ⟨1, one_ne_zero⟩) = 1) :
    lam = X.coefK v (A.index ⟨p, hp⟩) := by
  simpa only [he, map_smul, Pi.smul_apply, h₁, smul_eq_mul, mul_one] using hs v hv

/-- The cuspidal sector satisfies the coefficient-one shift from Whittaker data. -/
theorem cuspidal_upAtOne [CharZero X.K] (A : O12.FourierData X) (D : CuspidalData X P)
    (hp : p ≠ 0)
    (W : WhittakerComparison p hp {v | SupportedOn D.active v} D.up
      (fun n v => X.coefK v (A.index n))) :
    D.sector.UpAtOne A hp :=
  fun v hv => W.coeff_shift hv (D.sector.active_stable v hv)

omit [Fact p.Prime] in
/-- The two Fourier shifts add on the actual active space. -/
theorem combine_upAtOne {U : Finset ℕ} (A : O12.FourierData X) (C E : Sector X P)
    (hd : Disjoint C.active E.active)
    (hF : SupportedOn (C.active ∪ E.active) (X.F U : X.I → X.K)) (hp : p ≠ 0)
    (hc : C.UpAtOne A hp) (he : E.UpAtOne A hp) : A.UpAtOne (combine C E hd hF) hp := by
  classical
  intro v hv
  have supp (D : Sector X P) : SupportedOn D.active (mask D.active v) := by
    intro i hi
    rw [mask_apply, ite_eq_right hi]
  change X.coefK (C.Up (mask C.active v) + E.Up (mask E.active v)) (A.index ⟨1, one_ne_zero⟩) =
    X.coefK v (A.index ⟨p, hp⟩)
  rw [map_add, Pi.add_apply, hc _ (supp C), he _ (supp E), ← Pi.add_apply, ← map_add,
    ← split_supported hd hv]

/-- Data at one stage of `O12.LocalInput`, including the deferred Eisenstein
hypothesis and the support of the actual form in these two sectors. -/
structure Stage (A : O12.FourierData X) (U : Finset ℕ) (P : O12.LocalPair p) (hp : p ≠ 0) where
  cusp : CuspidalData X P
  eisenstein : Sector X P
  disjoint : Disjoint cusp.active eisenstein.active
  support : SupportedOn (cusp.active ∪ eisenstein.active) (X.F U : X.I → X.K)
  whittaker : WhittakerComparison p hp {v | SupportedOn cusp.active v} cusp.up
    (fun n v => X.coefK v (A.index n))
  eisenstein_shift : eisenstein.UpAtOne A hp

omit [Fact p.Prime] in
/-- A stage of cuspidal and Eisenstein data at each tested prime gives the
local input consumed by the existing `O12.inputs_of_theta`. -/
theorem localInput [CharZero X.K] (A : O12.FourierData X)
    (data : ∀ (U : Finset ℕ) (q : ℕ) (hqU : q ∈ U) (hU : ∀ s ∈ U, T.Good s),
      U.card + 1 ≤ B → ∀ Q : O12.LocalPair q,
      let : Fact q.Prime := ⟨(hU q hqU).1⟩
      Nonempty (Stage A U Q (hU q hqU).1.ne_zero)) : O12.LocalInput A := by
  intro U q hqU hU hB Q
  let : Fact q.Prime := ⟨(hU q hqU).1⟩
  obtain ⟨D⟩ := data U q hqU hU hB Q
  refine ⟨combine D.cusp.sector D.eisenstein D.disjoint D.support, ?_⟩
  exact combine_upAtOne A _ _ D.disjoint D.support _ (cuspidal_upAtOne A _ _ D.whittaker)
    D.eisenstein_shift

#print axioms mask_apply
#print axioms mask_supported
#print axioms split_supported
#print axioms CuspidalData.diagonalEntry_eq
#print axioms CuspidalData.diagonalEntry_eq_zero
#print axioms CuspidalData.up_on_ramified
#print axioms CuspidalData.up_on_copy
#print axioms CuspidalData.old_unramified
#print axioms Sector.scalar_eq_p_coeff
#print axioms cuspidal_upAtOne
#print axioms combine_upAtOne
#print axioms localInput

end ZInQ.Manuscript.RC.O12Local
