# fh-printed: Friedberg–Hoffstein Theorem B in printed terms; `hFH` discharged from it

Status: research note (task fh-printed, 2026-11-15). Branch `wip/fh-printed` (base main 43513d87,
leaf-fold25). Lean (new files only):
`ZInQKernel/Contrib/OneProof/FriedbergHoffsteinBFE.lean` (the contributor file: new leaf,
dictionary, equivalence, root-number clause),
`ZInQKernel/Contrib/OneProof/FHPrinted/LocalNorm.lean` (Mathlib only: local components of
quadratic characters, Hensel, descent, the idelic character).
Scratch: `scratch/fh-printed/` (`Discharges.lean` + `Discharges-output.txt`: `#discharges` and the
proposed fold of `frozenTarget`; `autofold.json`; `FE-statement-copy.lean.txt`: verbatim copy of
the statement discharged; `LocalNorm.lean`, `Statement.lean`: development copies; `log.md`).

Marks. **VERIFIED**: compiled, or read in a file named here. **STANDARD**: published, with
reference. **SPECULATIVE**: an assessment. No copy of Friedberg–Hoffstein (or of any other paper
cited here) is on this host and there is no network: **every literature locator is UNVERIFIED**.

---

## 0. Main result

**`hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` is proved from a new leaf that states
Friedberg–Hoffstein Theorem B over its own objects, and the two leaves are proved equivalent.**

```lean
theorem ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
    (h : ZInQ.FHPrinted.FriedbergHoffsteinB_Printed) : ZInQ.GZFH.FriedbergHoffsteinB_FE
theorem ZInQ.FHPrinted.friedbergHoffsteinB_printed_iff_FE :
    ZInQ.FHPrinted.FriedbergHoffsteinB_Printed ↔ ZInQ.GZFH.FriedbergHoffsteinB_FE
theorem ZInQ.FHPrinted.rootNumberTwistEqOne_iff {N : ℕ} [NeZero N] (f : Newform N 2)
    (hχ : f.χ = 1) {D₀ : ℤ} (hD₀ : IsOddFundDisc D₀) (hcop : Nat.Coprime D₀.natAbs N) :
    RootNumberTwistEqOne f D₀ ↔ (jacobiSym (-(N : ℤ)) D₀.natAbs : ℂ) * rootNumber f hχ = 1
```

All compile; every theorem has axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED).
`#discharges` reports (VERIFIED, §4):

```
DISCHARGES [hFH] by ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
  still assumes: [ZInQ.FHPrinted.FriedbergHoffsteinB_Printed]
  axioms: [propext, Classical.choice, Quot.sound]
```

The three dictionary clauses that made `FriedbergHoffsteinB_FE` a consequence (statement
review):

| Clause | In `FriedbergHoffsteinB_FE` | In the new leaf | Status |
| --- | --- | --- | --- |
| (ii) local conditions `χ_v = χ₀,v` | `D/D₀ ∈ (ℚ_p^×)²`, `D D₀ > 0`, `D` odd | equality of the local characters `χ_{d,v}, χ_{D₀,v} : ℚ_v^× → {±1}` (norm-residue symbols, `localChar`), for `d` any squarefree integer `≠ 1` | **proved in Lean**, both directions (Hensel, descent on the norm form, Chevalley–Warning mod `p`); the parity `d ≡ 1 (4)` is derived from the condition at `2` |
| (i) root number `ε(½, π ⊗ χ₀) = 1` | sign `+1` of the functional equation at the conductor `N D₀²` | sign `+1` of the functional equation of the completed L-function for *some* conductor `q` (`RootNumberTwistEqOne`) | the conductor theorem is gone; proved equivalent to the closed form `χ_{D₀}(−N) ε(f) = 1` (`rootNumberTwistEqOne_iff`), i.e. the Atkin–Li value of `ε(½, π_f ⊗ χ₀)`; the identification "global root number = sign of the functional equation" is the definition of the global root number |
| (iii) `L(½, π ⊗ χ) ≠ 0` | `G(1) ≠ 0`, `G` the continuation of `∑ aₙ(f) (n/|D|) n^{−s}` | `G(1) ≠ 0`, `G` the continuation of `∑ aₙ(f) χ_d(n) n^{−s}`, with `χ_d(n)` built from the local components of `χ_d` (`idelicChar`) | the character is now the idele class character itself (proved equal to `(n/|d|)` for `d ≡ 1 (4)`); **the GL(2) side remains a reading**: `L(s, π_f ⊗ χ) = ∑ aₙ(f) χ(n) n^{−s−½}` for `χ` unramified at `p ∣ N` (local newform theory at `p ∣ N`, Hecke–Satake at `p ∤ N`); Mathlib has no automorphic L-functions |

Plus: "infinitely many `χ`" is `Set.Infinite` of the set of `d` (proved equivalent to the
`∀ B, ∃ D, B < |D|` form).

**Rating of the new leaf `FriedbergHoffsteinB_Printed`: printed form for clauses (i), (ii), the
character and "infinitely many"; not printed in one clause, (iii)**, the identification of the
automorphic L-function of `π_f ⊗ χ_d` with the classical twisted series (§5). Since it is
equivalent in Lean to `FriedbergHoffsteinB_FE`, it is not stronger than the leaf it replaces.
GLUE count: if the integrator accepts the classical normalization of the L-function of a newform
(the convention under which the project's other modular L-function leaves are read), the leaf
counts as printed and the fold removes one GLUE (hFH was rated a consequence). If not, the
count is unchanged and (iii) is the one step left.

---

## 1. The new leaf (verbatim from `FriedbergHoffsteinBFE.lean`; docstrings shortened)

```lean
-- FHPrinted/LocalNorm.lean
/-- `x` is a norm from `K(√d)`: `x = y² − d z²` with `y, z ∈ K`. -/
def IsLocalNorm (K : Type*) [Field K] (d : ℤ) (x : K) : Prop :=
  ∃ y z : K, x = y ^ 2 - d * z ^ 2

/-- `χ_d` at a prime `p`: `χ_{d,p}(p)` if `χ_{d,p}` is unramified (trivial on `ℤ_p^×`), else `0`. -/
noncomputable def charAtPrime (d : ℤ) (p : ℕ) : ℤ := by
  classical
  exact if hp : p.Prime then
    haveI := Fact.mk hp
    if (∀ u : ℤ_[p], IsUnit u → IsLocalNorm ℚ_[p] d (u : ℚ_[p])) then
      (if IsLocalNorm ℚ_[p] d (p : ℚ_[p]) then 1 else -1)
    else 0
  else 0

/-- `χ_d(n) = ∏_{p^k ∥ n} χ_d(p)^k`: the coefficients of `L(s, χ_d) = ∏_{p unram} (1 − χ_{d,p}(p) p^{−s})^{−1}`. -/
noncomputable def idelicChar (d : ℤ) (n : ℕ) : ℤ :=
  n.factorization.prod fun p k => charAtPrime d p ^ k

-- FriedbergHoffsteinBFE.lean
/-- The local component `χ_{d,v}`: the norm-residue (Hilbert) symbol `(d, ·)_v`. -/
noncomputable def localChar (K : Type*) [Field K] (d : ℤ) (x : Kˣ) : ℤ := by
  classical
  exact if IsLocalNorm K d (x : K) then 1 else -1

noncomputable def printedTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) (n : ℕ) : ℂ :=
  coeff f n * (idelicChar d n : ℂ)

/-- `ε(½, π_f ⊗ χ_{D₀}) = 1`: the completed L-function satisfies `Λ(2 − s) = Λ(s)` for some
conductor `q ≥ 1`, on the strip. -/
def RootNumberTwistEqOne {N : ℕ} [NeZero N] (f : Newform N 2) (D₀ : ℤ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f D₀) 2 G ∧
    ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL q G (2 - s) = ZInQ.Literature.completedL q G s

/-- `L(½, π_f ⊗ χ_d) ≠ 0`, read classically. -/
def CentralValueNeZero {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f d) 2 G → G 1 ≠ 0

def FriedbergHoffsteinB_Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    RootNumberTwistEqOne f D₀ →
    Set.Infinite {d : ℤ | Squarefree d ∧ d ≠ 1 ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → localChar ℚ_[p] d = localChar ℚ_[p] D₀) ∧
      localChar ℝ d = localChar ℝ D₀ ∧ CentralValueNeZero f d}
```

Objects. `Newform`, `f.χ` (Tau Ceti); `coeff`, `IsEntireCont` (gz-decomp); `IsOddFundDisc`
(gz-fh); `ZInQ.Literature.completedL q G s = q^{s/2}(2π)^{−s}Γ(s)G(s)` (kernel); `ℚ_[p]`,
`ℤ_[p]`, `ℝ`, `Squarefree`, `Set.Infinite`, `Nat.factorization` (Mathlib). New: `IsLocalNorm`,
`localChar`, `charAtPrime`, `idelicChar`, `printedTwistCoeff`, `RootNumberTwistEqOne`,
`CentralValueNeZero`, all definitions of standard objects, none a structure invented for the
purpose:

* `localChar ℚ_v d` is the local component `χ_{d,v}` of the quadratic idele class character of
  `ℚ(√d)`: by local class field theory its kernel is the norm group `N(ℚ_v(√d)^×)`, and
  `χ_{d,v}(x)` is the Hilbert symbol `(d, x)_v` (STANDARD: Serre, *A course in arithmetic*,
  Ch. III §1, Prop. 1; Neukirch, *Algebraic number theory*, Ch. V; numbers UNVERIFIED). For `d`
  a square in `ℚ_v` the algebra `ℚ_v(√d)` is split, every `x` is a norm and the character is
  trivial, which the definition gives.
* `idelicChar d` is the Dirichlet coefficient sequence of `L(s, χ_d)` in Tate's definition: the
  value of `χ_{d,p}` at the uniformizer `p` when `χ_{d,p}` is unramified (trivial on `ℤ_p^×`),
  `0` at the ramified primes, extended completely multiplicatively. Proved: it is the Jacobi
  symbol `(n/|d|)` for `d ≡ 1 (4)` squarefree (`idelicChar_eq_jacobiSym`), and `χ_d(2) = 0` for
  `d ≡ 2, 3 (4)` (`charAtPrime_two_of_ramified`), so it is the Kronecker character of `ℚ(√d)`
  at least for odd discriminants and at `2` for even ones (VERIFIED).
* Quadratic idele class characters of `ℚ` ↔ squarefree `d ≠ 1` (`χ_d` ↔ `ℚ(√d)`, class field
  theory): STANDARD; the leaf quantifies over `d`.

## 2. The printed theorem and the specialization

**Recalled statement (UNVERIFIED in every detail; as in gz-fh §2 and gz-statements §2.2).**
S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic L-functions on GL(2)*,
Ann. of Math. (2) 142 (1995), no. 2, 385–423, Theorem B: `π` a cuspidal automorphic
representation of `GL₂(𝔸_F)` (trivial central character or self-contragredient), `S` a finite set
of places containing the archimedean places, the places above `2` and the places where `π`
ramifies, `χ₀` a quadratic idele class character with `ε(½, π ⊗ χ₀) = 1`; then infinitely many
quadratic idele class characters `χ` have `χ_v = χ₀,v` for all `v ∈ S` and `L(½, π ⊗ χ) ≠ 0`.

**Clause by clause.**

| Lean | Print | Relation |
| --- | --- | --- |
| `f : Newform N 2`, `f.χ = 1` | `π = π_f`, trivial central character | specialization |
| `S ⊇ {p ∣ 2N}`, `∞` via `localChar ℝ` | `S ∋ ∞`, places above 2, ramified places of `π` | specialization; if the print requires more places in `S` (e.g. ramified places of `χ₀`), apply it to the enlarged set: its conclusion implies this one |
| `IsOddFundDisc D₀`, `p ∤ D₀` (`p ∈ S`) | `χ₀` quadratic | specialization: `χ₀ = χ_{D₀}` unramified at the finite places of `S` |
| `RootNumberTwistEqOne f D₀` | `ε(½, π ⊗ χ₀) = 1` | the global root number is the sign of the functional equation `Λ(s) = ε(s) Λ(1 − s)`, `ε(s) = ε(½) q^{½−s}`, here for the self-dual `π_f ⊗ χ₀` in the classical variable; equivalent (proved) to `χ_{D₀}(−N) ε(f) = 1` |
| `Set.Infinite {d | …}` | infinitely many `χ` | `χ = χ_d` |
| `Squarefree d ∧ d ≠ 1` | `χ` quadratic | `χ_d` ↔ `ℚ(√d)` |
| `localChar ℚ_[p] d = localChar ℚ_[p] D₀`, `localChar ℝ d = localChar ℝ D₀` | `χ_v = χ₀,v`, `v ∈ S` | literal (the local components) |
| `CentralValueNeZero f d` | `L(½, π ⊗ χ) ≠ 0` | reading (iii), §5 |

The specialization only narrows the theorem. The leaf inherits gz-statements' open human checks
§6 H1 (label, page, whether dihedral `π` is allowed, the exact form of the hypotheses, full or
partial L-function; for the partial `L^S` the conclusion here follows because the omitted local
factors are reciprocals of polynomials and never vanish).

## 3. The dictionary, proved

### 3.1 Local conditions (`FHPrinted/LocalNorm.lean`, Mathlib only; VERIFIED)

* `isSquare_div_of_localNorm_iff` (`p` odd, `p ∤ D₀`, `D` squarefree): equal norm groups in
  `ℚ_p^×` give `D/D₀ ∈ (ℚ_p^×)²`. If `p ∣ D`, a nonsquare unit `u` is a norm from
  `ℚ_p(√D₀)` (`isLocalNorm_intCast_unit`) but not from `ℚ_p(√D)` (`not_isLocalNorm_of_ramified`).
  If `p ∤ D` and `D D₀` is not a square mod `p`, exactly one of `D, D₀` is a square (Legendre
  symbol), that one is a square in `ℚ_p` (Hensel) so `p` is a norm for it, and `p` is not a norm
  for the other (`not_isLocalNorm_p`). If `D D₀` is a square mod `p`, Hensel.
* `isSquare_div_two_of_localNorm_iff` (`D₀ ≡ 1 (4)`, `D` squarefree): `D ≡ 1 (4)` and
  `D/D₀ ∈ (ℚ_2^×)²`. `D ≡ 2 (4)`: `5` separates (`not_isLocalNorm_five_of_two`,
  `isLocalNorm_two_five`); `D ≡ 3 (4)`: `−1` separates (`not_isLocalNorm_neg_one_of_three`,
  `isLocalNorm_two_neg_one`); `D ≡ 1 (4)`: `2` separates the classes `1, 5 (mod 8)`
  (`not_isLocalNorm_two_of_five`); same class mod 8 gives `D D₀ ≡ 1 (8)`, a square (Hensel at 2).
* `pos_mul_of_real_iff`: `−1` is a norm from `ℝ(√d)` iff `d > 0`.
* Converse (`isLocalNorm_iff_of_isSquare_div`, `real_isSquare_div_of_pos_mul`): equal square
  classes give equal norm groups.

Tools: `not_isLocalNorm_of_descent` (a representation of `p^{2k} x` with `p ∣ Y, Z` descends to
`p^{2k−2} x`; integrality by scaling), with the step conditions checked mod `p` or by `decide`
in `ZMod 8`; Hensel (`isSquare_of_toZMod`, `isSquare_of_toZModPow_three`, from Mathlib's
`hensels_lemma`); units are norms from unramified extensions (`isLocalNorm_unit`: Mathlib's
`FiniteField.exists_root_sum_quadratic` mod `p`, then Hensel; `isLocalNorm_two_unit`: the classes
`1, 5, −1, −5` mod 8 are norms and the norm form is multiplicative).

### 3.2 The character (VERIFIED)

`charAtPrime_eq_jacobiSym`: `χ_d(p) = (p/|d|)` for `d ≡ 1 (4)` squarefree (unramified odd `p`:
`χ_{d,p}(p) = (d/p)` and quadratic reciprocity `jacobiSym_prime_eq_legendreSym`; ramified
`p ∣ d`: a nonsquare unit is not a norm; `p = 2`: `(2/|d|) = χ₈(|d|)` against `d mod 8`).
`idelicChar_eq_jacobiSym` by multiplicativity. Hence `printedTwistCoeff f d n = twistCoeff f d n`
for `n ≠ 0` (`printedTwistCoeff_eq`).

### 3.3 The root number (VERIFIED)

`rootNumberTwistEqOne_iff`. (←) the proved twisted functional equation (gz-fh,
`twistFunctionalEquation`) with sign `χ_{D₀}(−N) ε(f) = 1` at `q = N D₀²`. (→) given the
functional equation with sign `1` at some `q` and the proved one with sign `w` at `Q = N D₀²`,
`sign_eq_one_of_functionalEquations` gives `w = 1`: the entire function
`H(s) = Q^{(2−s)/2} q^{s/2} − w q^{(2−s)/2} Q^{s/2}` satisfies `H(s) E(s) = 0` on the strip, where
`E(s) = (2π)^{−s}Γ(s)G(s)`; `G ≢ 0` (`twist_cont_ne_zero`: `G` is the L-function of Tau Ceti's
twisted cusp form, nonzero since `a₁ = 1`, `CuspForm.L_ne_zero_of_qExpansion_coeff_ne_zero`), so
`E ≠ 0` near some point of the strip (`exists_ne_zero_on_strip`), `H` vanishes there, hence
everywhere (identity theorem), and `H(1) = (qQ)^{1/2}(1 − w) = 0`.

So the root-number clause of the leaf says exactly `χ_{D₀}(−N) ε(f) = 1`, which is
`ε(½, π_f ⊗ χ_{D₀}) = 1` by the twisted root-number formula (Atkin–Li, Invent. Math. 48 (1978);
Iwaniec–Kowalski Prop. 14.20; UNVERIFIED numbers): the leaf's hypothesis is not weaker than the
printed one, whichever of the two descriptions of `ε` one reads.

### 3.4 The equivalence (VERIFIED)

`friedbergHoffsteinB_FE_of_printed` (the deliverable): from `FriedbergHoffsteinB_FE`'s hypothesis
build `RootNumberTwistEqOne` (`q = N D₀²`), take `d` in the infinite set with `|d| > B`
(`exists_natAbs_gt_of_infinite`), and translate the local conditions (§3.1), the character
(§3.2) and the L-value (same series). `friedbergHoffsteinB_printed_of_FE`: the converse, using
`rootNumberTwistEqOne_iff` (→), the converse local lemmas, and `infinite_of_forall_exists_natAbs_gt`.

## 4. `#discharges` and axioms

`scratch/fh-printed/Discharges.lean` against the built `ZInQKernel.OneProof.Main` of this base
(`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE`, 12996 jobs, then `lake env lean`; full output
`scratch/fh-printed/Discharges-output.txt`, VERIFIED). The other seven DISCHARGES lines are the
base's known contributions; the line for this task and the axioms:

```
DISCHARGES [hFH] by ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
  still assumes: [ZInQ.FHPrinted.FriedbergHoffsteinB_Printed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1918 theorems checked, 8 discharge one
'fhprinted_frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.FHPrinted.friedbergHoffsteinB_printed_of_FE' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.FHPrinted.friedbergHoffsteinB_printed_iff_FE' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.FHPrinted.rootNumberTwistEqOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.FHPrinted.idelicChar_eq_jacobiSym' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`fhprinted_frozenTarget` is `ZInQ.OneProof.frozenTarget` with `hFH` replaced by
`friedbergHoffsteinB_FE_of_printed hFHP`, `hFHP : FriedbergHoffsteinB_Printed`: the fold, checked
without editing `Main.lean`. The contributor files contain no code that runs at build time.

**Fold (for the integrator).** `hFH` is a top-level hypothesis of `frozenTarget`, not a bundle
field, so `autofold.py` does not apply as is; `scratch/fh-printed/autofold.json` gives the spec
in the documented format with a `_note` describing the hand fold (as in leaf-fold24): import
`ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE`, replace the binder by
`(hFHP : ZInQ.FHPrinted.FriedbergHoffsteinB_Printed)`, pass
`(ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed hFHP)` where `hFH` was used. kinds.tsv row:
`frozenTarget  hFHP  published  <flag of §5>  LEAF  LEAF  <source>  fh-printed`.

## 5. Rating of the new leaf

**`ZInQ.FHPrinted.FriedbergHoffsteinB_Printed`: printed form, except one clause.**

* Printed: the local conditions (the local components themselves, compared as characters), the
  quadratic characters (`χ_d`, `d` squarefree, with Dirichlet coefficients from the local
  components), "infinitely many", the root-number hypothesis (the sign of the functional equation
  of the completed L-function, no conductor; equivalent, proved, to the Atkin–Li value
  `χ_{D₀}(−N) ε(f)`), the specialization (`F = ℚ`, `π = π_f`, `χ₀ = χ_{D₀}` unramified at `S`).
* Not printed: `L(s, π_f ⊗ χ_d)` (in the conclusion, and inside the completed L-function of the
  hypothesis) is the classical series `∑ aₙ(f) χ_d(n) n^{−s−½}`. For `χ_d` unramified at every
  `p ∣ N` (which the local conditions force at the `d` produced, and which holds for `D₀`) this
  equals the automorphic L-function by local newform theory at `p ∣ N` (Casselman; Atkin–Lehner;
  Li) and the Hecke–Satake dictionary at `p ∤ N`; at `p ∣ d` both local factors are `1`. Mathlib
  has no automorphic representations, so this is the one step not expressible in Lean.

Suggested flag (class `unread`): "unread: Friedberg-Hoffstein 1995 Thm B label, page and
hypotheses recalled from memory (locator UNVERIFIED); one reading left: L(s, pi_f x chi_d) is
taken as the classical series sum a_n(f) chi_d(n) n^(-s-1/2) for chi_d unramified at the primes
dividing N (local newform theory); equivalent in Lean to the previous leaf FriedbergHoffsteinB_FE".

Proposed locators.md row (not added here; locators.md belongs to the integrator):
`| Nonvanishing of central values of quadratic twists | S. Friedberg, J. Hoffstein, Nonvanishing
theorems for automorphic L-functions on GL(2), Ann. of Math. (2) 142 (1995) 385–423 | Thm B
(label, page unread) | UNVERIFIED. Used as ZInQ.FHPrinted.FriedbergHoffsteinB_Printed for F = Q,
pi = pi_f (weight 2, trivial nebentypus), chi_0 unramified at S ⊇ {p | 2N}; checks: dihedral pi
allowed, places required in S, full or partial L, form of the root-number hypothesis |`.

## 6. What remains

* Reading (iii) (§5). Removing it needs either an automorphic L-function in Lean or a
  classically stated source for the same nonvanishing (candidates, SPECULATIVE and unread:
  Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543–618; Iwaniec, Sém. Théor. Nombres
  Bordeaux 2 (1990); Murty–Murty, Ann. of Math. 133 (1991)), whose statements, if they are in
  terms of `∑ aₙ(f) χ_D(n) n^{−s}` with congruence conditions on `D`, would make the leaf printed
  in every clause.
* The human checks of gz-statements §6 H1 against the print (label, page, dihedral `π`, required
  places in `S`, full or partial L).
* The fold (§4), done by the integrator.
