import Mathlib

/-!
# Colmez's ring `R`, as printed, is Mathlib's `PreTilt`

Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), 629-644, §2, p. 632
(GDZ scan PPN235181684_0292, LOG_0042, PDF page 5):

* "Soit R l'ensemble des suites x=(x^{(n)}), n∈ℕ d'éléments de O_{C_p} vérifiant
  (x^{(n+1)})^p = x^{(n)}."
* "x+y=s avec s^{(n)} = lim_{m→∞} (x^{(n+m)}+y^{(n+m)})^{p^m} et xy=t avec t^{(n)}=x^{(n)}y^{(n)}."

Here `O` is any commutative ring that is `p`-adically complete with `p` not a unit (Mathlib's
standing hypotheses for `PreTilt.untilt` and `fontaineTheta`); the file `Cp.lean` specializes to
`O = 𝓞_ℂ_[p]`, Colmez's `O_{C_p}`.

* `ColmezR O p`: the p-power-compatible sequences, exactly as printed.
* `IsPAdicLim`: the printed `lim`, as a `p`-adic limit; limits are unique (`IsPAdicLim.unique`).
* `exists_isPAdicLim_addApprox`: **the printed limit exists**; `+` on `ColmezR` is defined as
  this limit (`add_seq_isPAdicLim`), `*` componentwise (`mul_seq`).
* `colmezEquiv : ColmezR O p ≃+* PreTilt O p`: **the ring isomorphism**, `x ↦ (x^{(n)} mod p)_n`,
  with inverse `y ↦ (untilt (Frob⁻ⁿ y))_n` (`colmezEquiv_symm_seq`).

The ring structure on `ColmezR` is the printed one: addition is the printed limit, multiplication
and powers are componentwise, `0` and `1` are the constant sequences. The operations Colmez does
not print (negation, subtraction, scalar multiples, casts) are carried over from `PreTilt`.
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal

variable (O : Type*) [CommRing O] (p : ℕ)

/-- **Colmez's `R`** (p. 632): "l'ensemble des suites x=(x^{(n)}), n∈ℕ d'éléments de O_{C_p}
vérifiant (x^{(n+1)})^p = x^{(n)}". -/
@[ext]
structure ColmezR where
  /-- The sequence `n ↦ x^{(n)}`. -/
  seq : ℕ → O
  /-- `(x^{(n+1)})^p = x^{(n)}`. -/
  pow_seq_succ : ∀ n, seq (n + 1) ^ p = seq n

variable {O p}

/-- `L` is the `p`-adic limit of `a`: for every `k`, eventually `a m ≡ L` modulo `p^k`. This is
the printed `lim` (for `O = 𝓞_ℂ_[p]` it is the limit in `ℂ_p`, see `Cp.lean`). -/
def IsPAdicLim (p : ℕ) (a : ℕ → O) (L : O) : Prop :=
  ∀ k : ℕ, ∀ᶠ m in Filter.atTop, a m - L ∈ span {(p : O)} ^ k

theorem IsPAdicLim.unique [IsHausdorff (span {(p : O)}) O] {a : ℕ → O} {L L' : O}
    (h : IsPAdicLim p a L) (h' : IsPAdicLim p a L') : L = L' := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  intro k
  obtain ⟨m, hm, hm'⟩ := ((h k).and (h' k)).exists
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have := sub_mem hm' hm
  rwa [sub_sub_sub_cancel_left] at this

namespace ColmezR

theorem pow_seq_add (x : ColmezR O p) (n m : ℕ) : x.seq (n + m) ^ p ^ m = x.seq n := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, pow_succ', pow_mul, x.pow_seq_succ, ih]

/-- The sequence whose limit Colmez prints for `(x+y)^{(n)}`: `m ↦ (x^{(n+m)}+y^{(n+m)})^{p^m}`. -/
def addApprox (x y : ColmezR O p) (n m : ℕ) : O :=
  (x.seq (n + m) + y.seq (n + m)) ^ p ^ m

/-- The shifted sequence `k ↦ x^{(k+m)}`. -/
def shift (x : ColmezR O p) (m : ℕ) : ColmezR O p :=
  ⟨fun n => x.seq (n + m), fun n => by rw [Nat.add_right_comm, x.pow_seq_succ]⟩

section Tilt

variable [Fact p.Prime] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

/-- Reduction modulo `p`: `x ↦ (x^{(n)} mod p)_n ∈ PreTilt O p`. -/
def toPreTilt (x : ColmezR O p) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk _ (x.seq n), fun n => by
    rw [← map_pow, x.pow_seq_succ]⟩

theorem coeff_toPreTilt (x : ColmezR O p) (n : ℕ) :
    PreTilt.coeff n (toPreTilt x) = Ideal.Quotient.mk _ (x.seq n) :=
  rfl

/-- `y ↦ (untilt (Frob⁻ⁿ y))_n`, the map suggested by `PreTilt.untilt` and
`PreTilt.untilt_iterate_frobeniusEquiv_symm_pow`. -/
noncomputable def ofPreTilt (y : PreTilt O p) : ColmezR O p :=
  ⟨fun n => PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) y), fun n => by
    rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]⟩

theorem ofPreTilt_seq (y : PreTilt O p) (n : ℕ) :
    (ofPreTilt y).seq n = PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) y) :=
  rfl

theorem untilt_toPreTilt (x : ColmezR O p) : PreTilt.untilt (toPreTilt x) = x.seq 0 := by
  refine Perfection.teichmuller_spec fun n => ⟨x.seq n, rfl, ?_⟩
  have h := x.pow_seq_add 0 n
  rw [zero_add] at h
  rw [h]

theorem iterate_frobeniusEquiv_symm_toPreTilt (x : ColmezR O p) (m : ℕ) :
    ((frobeniusEquiv (PreTilt O p) p).symm^[m]) (toPreTilt x) = toPreTilt (x.shift m) := by
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [PreTilt.coeff_iterate_frobeniusEquiv_symm]
  rfl

theorem ofPreTilt_toPreTilt (x : ColmezR O p) : ofPreTilt (toPreTilt x) = x := by
  ext n
  rw [ofPreTilt_seq, iterate_frobeniusEquiv_symm_toPreTilt, untilt_toPreTilt]
  change x.seq (0 + n) = x.seq n
  rw [zero_add]

theorem toPreTilt_ofPreTilt (y : PreTilt O p) : toPreTilt (ofPreTilt y) = y := by
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [coeff_toPreTilt, ofPreTilt_seq, PreTilt.mk_untilt_eq_coeff_zero,
    PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem toPreTilt_injective : Function.Injective (toPreTilt (O := O) (p := p)) :=
  Function.LeftInverse.injective ofPreTilt_toPreTilt

/-- The candidate for `(x+y)^{(n)}` coming from `PreTilt`; it is the printed limit. -/
theorem isPAdicLim_addApprox (x y : ColmezR O p) (n : ℕ) :
    IsPAdicLim p (addApprox x y n) ((ofPreTilt (toPreTilt x + toPreTilt y)).seq n) := by
  set s := ofPreTilt (toPreTilt x + toPreTilt y)
  have hmod : ∀ k, (p : O) ∣ s.seq k - (x.seq k + y.seq k) := fun k => by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_add]
    have h := congrArg (PreTilt.coeff k) (toPreTilt_ofPreTilt (toPreTilt x + toPreTilt y))
    rw [map_add, coeff_toPreTilt, coeff_toPreTilt, coeff_toPreTilt] at h
    exact h
  intro k
  refine Filter.eventually_atTop.mpr ⟨k, fun m hm => ?_⟩
  have h := dvd_sub_pow_of_dvd_sub (hmod (n + m)) m
  rw [s.pow_seq_add] at h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, addApprox]
  exact (pow_dvd_pow _ (by omega)).trans (dvd_sub_comm.mp h)

/-- **The printed limit exists** (Colmez, p. 632): for all `x y ∈ R` and `n`,
`lim_{m→∞} (x^{(n+m)}+y^{(n+m)})^{p^m}` exists `p`-adically. -/
theorem exists_isPAdicLim_addApprox (x y : ColmezR O p) (n : ℕ) :
    ∃ L, IsPAdicLim p (addApprox x y n) L :=
  ⟨_, isPAdicLim_addApprox x y n⟩

/-- The printed sum, coordinate by coordinate: the limit. -/
noncomputable def addSeq (x y : ColmezR O p) (n : ℕ) : O :=
  (exists_isPAdicLim_addApprox x y n).choose

theorem addSeq_eq (x y : ColmezR O p) (n : ℕ) :
    addSeq x y n = (ofPreTilt (toPreTilt x + toPreTilt y)).seq n :=
  (exists_isPAdicLim_addApprox x y n).choose_spec.unique (isPAdicLim_addApprox x y n)

/-- Colmez's addition (p. 632): `s^{(n)} = lim_{m→∞} (x^{(n+m)}+y^{(n+m)})^{p^m}`. -/
noncomputable instance : Add (ColmezR O p) where
  add x y := ⟨addSeq x y, fun n => by rw [addSeq_eq, addSeq_eq, ColmezR.pow_seq_succ]⟩

/-- Colmez's multiplication (p. 632): `t^{(n)} = x^{(n)} y^{(n)}`. -/
instance : Mul (ColmezR O p) where
  mul x y := ⟨fun n => x.seq n * y.seq n, fun n => by rw [mul_pow, x.pow_seq_succ, y.pow_seq_succ]⟩

instance : Zero (ColmezR O p) where
  zero := ⟨fun _ => 0, fun _ => zero_pow (Fact.out : p.Prime).ne_zero⟩

instance : One (ColmezR O p) where
  one := ⟨fun _ => 1, fun _ => one_pow _⟩

/-- Powers, componentwise (they follow from the printed multiplication). -/
instance : Pow (ColmezR O p) ℕ where
  pow x k := ⟨fun n => x.seq n ^ k, fun n => by rw [← pow_mul, mul_comm, pow_mul, x.pow_seq_succ]⟩

/-! Operations not printed by Colmez, carried over from `PreTilt`. -/

noncomputable instance : Neg (ColmezR O p) where
  neg x := ofPreTilt (-toPreTilt x)

noncomputable instance : Sub (ColmezR O p) where
  sub x y := ofPreTilt (toPreTilt x - toPreTilt y)

noncomputable instance : SMul ℕ (ColmezR O p) where
  smul k x := ofPreTilt (k • toPreTilt x)

noncomputable instance : SMul ℤ (ColmezR O p) where
  smul k x := ofPreTilt (k • toPreTilt x)

noncomputable instance : NatCast (ColmezR O p) where
  natCast k := ofPreTilt k

noncomputable instance : IntCast (ColmezR O p) where
  intCast k := ofPreTilt k

/-- **Addition is the printed limit** (Colmez, p. 632). -/
theorem add_seq_isPAdicLim (x y : ColmezR O p) (n : ℕ) :
    IsPAdicLim p (fun m => (x.seq (n + m) + y.seq (n + m)) ^ p ^ m) ((x + y).seq n) :=
  (exists_isPAdicLim_addApprox x y n).choose_spec

/-- **Multiplication is componentwise** (Colmez, p. 632). -/
theorem mul_seq (x y : ColmezR O p) (n : ℕ) : (x * y).seq n = x.seq n * y.seq n :=
  rfl

theorem zero_seq (n : ℕ) : (0 : ColmezR O p).seq n = 0 :=
  rfl

theorem one_seq (n : ℕ) : (1 : ColmezR O p).seq n = 1 :=
  rfl

theorem pow_seq (x : ColmezR O p) (k n : ℕ) : (x ^ k).seq n = x.seq n ^ k :=
  rfl

theorem toPreTilt_add (x y : ColmezR O p) : toPreTilt (x + y) = toPreTilt x + toPreTilt y := by
  have h : x + y = ofPreTilt (toPreTilt x + toPreTilt y) := ColmezR.ext (funext (addSeq_eq x y))
  rw [h, toPreTilt_ofPreTilt]

theorem toPreTilt_mul (x y : ColmezR O p) : toPreTilt (x * y) = toPreTilt x * toPreTilt y :=
  Perfection.ext fun n => map_mul (Ideal.Quotient.mk _) (x.seq n) (y.seq n)

theorem toPreTilt_zero : toPreTilt (0 : ColmezR O p) = 0 :=
  Perfection.ext fun _ => map_zero (Ideal.Quotient.mk _)

theorem toPreTilt_one : toPreTilt (1 : ColmezR O p) = 1 :=
  Perfection.ext fun _ => map_one (Ideal.Quotient.mk _)

theorem toPreTilt_pow (x : ColmezR O p) (k : ℕ) : toPreTilt (x ^ k) = toPreTilt x ^ k :=
  Perfection.ext fun n => map_pow (Ideal.Quotient.mk _) (x.seq n) k

/-- `R` is a commutative ring, with the printed addition and multiplication. -/
noncomputable instance : CommRing (ColmezR O p) :=
  Function.Injective.commRing toPreTilt toPreTilt_injective toPreTilt_zero toPreTilt_one
    toPreTilt_add toPreTilt_mul (fun _ => toPreTilt_ofPreTilt _) (fun _ _ => toPreTilt_ofPreTilt _)
    (fun _ _ => toPreTilt_ofPreTilt _) (fun _ _ => toPreTilt_ofPreTilt _) toPreTilt_pow
    (fun _ => toPreTilt_ofPreTilt _) (fun _ => toPreTilt_ofPreTilt _)

end Tilt

end ColmezR

open ColmezR

variable [Fact p.Prime] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

/-- **Colmez's `R` is Mathlib's `PreTilt`**: the ring isomorphism `x ↦ (x^{(n)} mod p)_n`, under
which the printed addition (a limit) and the componentwise multiplication become the operations of
`PreTilt O p`. -/
noncomputable def colmezEquiv : ColmezR O p ≃+* PreTilt O p where
  toFun := toPreTilt
  invFun := ofPreTilt
  left_inv := ofPreTilt_toPreTilt
  right_inv := toPreTilt_ofPreTilt
  map_add' := toPreTilt_add
  map_mul' := toPreTilt_mul

theorem coeff_colmezEquiv (x : ColmezR O p) (n : ℕ) :
    PreTilt.coeff n (colmezEquiv x) = Ideal.Quotient.mk _ (x.seq n) :=
  rfl

/-- The inverse isomorphism: `y ↦ (untilt (Frob⁻ⁿ y))_n`. -/
theorem colmezEquiv_symm_seq (y : PreTilt O p) (n : ℕ) :
    (colmezEquiv.symm y).seq n =
      PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) y) :=
  rfl

/-- `untilt` reads off the coordinate `x^{(0)}`. -/
theorem untilt_colmezEquiv (x : ColmezR O p) : PreTilt.untilt (colmezEquiv x) = x.seq 0 :=
  untilt_toPreTilt x

/-- The printed addition, transported: for `y z ∈ PreTilt O p`, the `n`-th coordinate of `y + z`
is the printed limit of the coordinates of `y` and `z`. -/
theorem isPAdicLim_colmezEquiv_symm_add (y z : PreTilt O p) (n : ℕ) :
    IsPAdicLim p (fun m => ((colmezEquiv.symm y).seq (n + m) + (colmezEquiv.symm z).seq (n + m))
      ^ p ^ m) ((colmezEquiv.symm (y + z)).seq n) := by
  rw [map_add]
  exact add_seq_isPAdicLim _ _ n

end ZInQ.Contrib.ColmezTiltIso
