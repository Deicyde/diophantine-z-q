# T21 continuation: exact global Serre different bound

Formal status: **the exact global baseline proposition is proved** by a closed
Lean theorem. Contribution review, parent integration, full-candidate replay,
registration and designated independent acceptance remain separate and pending.
Serving model identities are unknown; this is not an Astra acceptance record.

## Exact declaration and verification

```lean
theorem ZInQ.Contrib.DifferentBound.serreDifferentBound :
    GlueConductor.SerreDifferentBound
```

The stored declaration type is literally the unchanged baseline constant
`GlueConductor.SerreDifferentBound`, and its universe-parameter list is empty.
The baseline expands to:

```lean
∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
  ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)
```

`GlobalAudit.lean` checks the stored type, not only its pretty-printed text; it
requires a theorem declaration and no universe parameters. It rechecks the
actual serialized proof body under a fresh theorem name with
`Kernel.Environment.addDeclCore` at trust level `0`. The renamed proof is
checked, not added as an assumed supplier to prove the original theorem. The
ordinary compiled example also consumes the theorem at the exact baseline type.

The final five-module compile and focused audit exit `0`, without compiler
warnings/errors. Twenty selected axiom reports across those compiles contain
only:

```text
[propext, Classical.choice, Quot.sound]
```

The captured successful checks include:

```text
EXACT STORED TYPE: GlueConductor.SerreDifferentBound; universe parameters: []
KERNEL RECHECK: actual global theorem proof body passed at trust level 0
```

A separate read of the five new compiled modules' raw declaration tables inspected
45 serialized declarations and found zero new axioms, zero unsafe declarations,
and zero partial declarations. This is metadata inspection, not a substitute for
the integrator's full candidate replay or independent source coverage review.

The audit specializes the same theorem at the dyadic prime and at arbitrary
primes over arbitrary nongalois number fields. A specialization is not substituted
for the full universal proof.

## Frozen base and additive scope

Baseline: `a5937595cde3e3db00975b81e5171cdef92c801a`.
`ZInQKernel/HDecomp/Conductor/Breaks.lean:350–354` remains unchanged, SHA-256
`7742365fd985fda83c733324394cb4a59db3f083e246dad63279924ce790306d`.

Lean: `4.35.0`, compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`). No pin, root,
registry, baseline, dependency source or checker is changed.

The initial thirteen `DifferentBound` sources are preserved byte for byte. The
initial note `docs/research/t21-different-bound.md`, SHA-256
`8b8d000e4d9c80d078001e7f35fc68d71e4e1fcfd73e6c18c457d7fc71f24f0d`, is also
preserved byte for byte as the earlier global-open evidence. Its open status was
correct for that earlier snapshot; this additive continuation supersedes that
status, rather than retroactively relabeling it as a closed proof.

The five new owned source modules are:

- `FixedField.lean`: consumes the actual localized fixed-field tower and proves
  the original fixed field's absolute different-exponent bound.
- `Equivalence.lean`: proves literal integer-ring, trace-dual, absolute-different,
  ramification-index and multiplicity transport under the actual rational field
  isomorphism.
- `Presentation.lean`: constructs a finite Galois fixed-field presentation of
  every number field.
- `SerreGlobal.lean`: closes the integral multiplicity bound for every original
  number field and prime, then closes the exact global baseline proposition.
- `GlobalAudit.lean`: the focused stored-type, proof-body kernel and axiom check.

All are under `ZInQKernel/Contrib/DifferentBound/`. No `Contrib/H` registration
alias, commit, push, PR, land or protocol acceptance is supplied. The verifier
and this continuation note are review artifacts, not changes to the audit policy
or manuscript. The initial conditional model reductions remain valid conditional
lemmas, but they are not the final global proof route.

## The actual proof route

### 1. Every original number field has a genuine fixed-field presentation

For any original `L`, `Presentation.ambient L` is the actual normal closure of
`L/ℚ` inside `AlgebraicClosure L`. Mathlib proves its finite dimension. Algebraic
closure is constructed, not assumed of `L`; algebraicity over `ℚ` follows from
`L` being a number field, and characteristic-zero separability and normality
prove the ambient field `M/ℚ` is finite Galois.

The actual normal-closure inclusion embeds `L` in `M`. Its image `K` is the
`fieldRange` of this very embedding. With `H = K.fixingSubgroup`, the finite
Galois correspondence gives `M^H = K`, and `equivFieldRange` followed by the
intermediate-field equality yields the actual `ℚ`-algebra isomorphism
`L ≃ₐ[ℚ] M^H`. No normality of `H`, and hence no Galois assumption on `L`, is used.

### 2. Every input prime is carried and lifted, not restricted to a subfamily

Restrict the actual field isomorphism to
`integersEquiv : 𝓞 L ≃ₐ[ℤ] 𝓞(M^H)`. For each arbitrary nonzero prime `P` of
`𝓞 L`, put `q = P.map integersEquiv`. Its primality and nonzeroness follow from
the actual bijective integer-ring map. Integral lying-over gives a prime `Q` of
`𝓞 M` above `q`. The proof chooses this witness separately for each input prime;
it assumes neither uniqueness nor an unramified property of this original fibre.
The equation `Q.under (𝓞(M^H)) = q` is the literal lying-over conclusion used by
the arithmetic supplier.

### 3. The actual localized F/U/E tower supplies the raw local inequality

For the selected `Q` in the finite Galois ambient field, the shared supplying
proof constructs:

```text
D = the actual decomposition subgroup at Q
I = the actual inertia subgroup at Q
H0 = D ∩ H
F = M^D
E = M^H0
U = M^(I ⊔ H0)
A  = (𝓞 F)_(Q ∩ 𝓞 F)
U0 = (𝓞 U)_(Q ∩ 𝓞 U)
B  = (𝓞 E)_(Q ∩ 𝓞 E)
```

Its three canonical localized algebra maps form the actual scalar tower; all
three rings are DVRs at their proved nonzero primes. Finiteness uses the proved
unique-prime fibres above the decomposition-field prime, not a false finiteness
claim for `B_P/ℤ_(p)` when primes split. The actual `A → U0` is unramified, and

```lean
Function.Surjective ((IsLocalRing.residue B).comp (algebraMap U0 B))
```

is proved for the literal upper inclusion. The actual canonical fraction fields
are finite and separable; faithful and torsion-free maps are supplied/proved.

`fixedFieldLocalDifferentBound` invokes the existing **raw**
`differentIdeal_bound_of_residue_surjective_unramified_tower A U0 B` on those
objects. It does not use a subalgebra-package wrapper or assume its desired
output. Completeness and perfectness are absent from this boundary.

The raw arithmetic proves uniformizer generation via residue digits and
Nakayama, proves the genuine degree equals the actual ramification index, proves
that the actual different is the actual minimal-polynomial derivative, and rules
out derivative-term cancellation through distinct valuation residues modulo `e`.
This gives `D_(B/A) ∣ m_B^(e-1)·(e)`. No Hilbert formula or assumed Serre estimate
is used.

### 4. Actual e and different coefficients return the inequality to M^H

The supplying proofs establish that `F/ℚ` and `E/(M^H)` are unramified at the
selected primes with index one. Global different transitivity, genuine
localization of the different, and normalized ideal multiplicity transport prove
that the local relative different coefficient equals the original absolute
`differentIdeal ℤ (𝓞(M^H))` coefficient. The actual local ramification index is
the original global index, not merely a proportional valuation convention.

`fixedFieldLocal_multiplicity_natCast` also compares every **nonzero** natural
integer's principal-ideal coefficient: the unramified `E/(M^H)` factor has index
one, and the selected prime localization preserves its multiplicity. Applying it
to `n = e` is justified by the proved positive ramification index and
characteristic zero of the actual upper ring. Thus the original fixed field
satisfies

```lean
multiplicity q (differentIdeal ℤ (𝓞(M^H))) ≤
  q.ramificationIdx ℤ - 1 +
    multiplicity q (Ideal.span {(q.ramificationIdx ℤ : 𝓞(M^H))})
```

### 5. Literal integral equivalence transports that bound to the original field

`Equivalence.lean` proves the actual complementary-module comparison from
`Algebra.trace_eq_of_algEquiv` and the preservation of integral elements by the
restricted field isomorphism. Mathlib's actual
`coeSubmodule_differentIdeal` then proves the literal ideal equality

```lean
(differentIdeal ℤ (𝓞 L)).map (integersEquiv e) =
  differentIdeal ℤ (𝓞(M^H))
```

This is over `ℤ`, not a silently substituted `𝓞 ℚ`; it is not equality only after
rational tensoring, equality of an order different, or equality up to a dropped
valuation factor. The same ideal equivalence preserves every principal-ideal
multiplicity. The pinned `ramificationIdx'_map_eq` and
`ramificationIdx'_eq_ramificationIdx` identify the actual length-defined global
ramification indices through that exact map.

The closed integral theorem `numberFieldDifferentMultiplicityBound` consequently
holds for every original number field and every nonzero prime `P`, without
requiring a rational prime argument.

### 6. The exact +1 nondivisibility follows with the original normalization

The global target's `P ≠ ⊥` follows from lying above nonzero `(p)`. The global
ramification index is positive. The initial proved normalization gives, at
`n = e ≠ 0`,

```lean
multiplicity P (Ideal.span {(e : 𝓞 L)}) = e * padicValNat p e
```

The initial proved prime-power/multiplicity equivalence converts the upper bound
into `¬ P^(e-1+e*padicValNat p e+1) ∣ differentIdeal ℤ (𝓞 L)`, exactly as stored in
the unchanged global baseline.

## Source-first nine obligations for this new global transition

These are author-supplied comparisons, not independent acceptance. The earlier
note's unresolved global model obligations are discharged by this **new** route
and its named supplying proofs, not by reusing a historical favorable verdict.

1. **Source hypotheses.** Required: ambient finite Galois `M/ℚ`, a nonzero prime
   `Q`, arbitrary subgroup `H`, and the raw finite faithful/separable DVR tower
   with unramified bottom and residue-surjective top. Constructed: `M` is the
   actual finite normal closure, `H` fixes the actual image, and `Q` is lifted
   from the actual transported input prime. All local inputs come from
   `FixedFieldLocalTower` and `FixedFieldLocalFractionFields`; positivity precedes
   division or finite valuation use. Evidence: `Presentation`, `SerreGlobal`,
   `FixedField`, and the exact shared supplier versions listed below. No such
   property is added as an external hypothesis to global T21.
2. **Constructed objects.** Required: the objects whose conclusions refer back
   to the original `L,P`. Constructed: the actual field image, restricted
   integer-ring isomorphism, literal mapped prime, lifted ambient prime,
   fixed-field `F/U/E` and canonical prime localizations. The shared source's
   definitions and our raw consumer agree, including the original fixed field
   `M^H`. Evidence: `Presentation.equiv`, `integersEquiv`,
   `FixedFieldLocalTower.baseRing/factorRing/extensionRing`, and `SerreGlobal`.
3. **Domain/index coverage.** Required: every original `L`, every natural prime
   `p`, and every prime `P | p`; derivative and ideal comparisons must cover
   their full indices. Constructed: canonical presentation for each `L`, prime
   map/lift for each `P`, and the shared tower for any `H,Q`. No normal-subgroup
   restriction is imposed. The raw derivative uses all `Fin e`, including zero
   coefficients, and the shared different-powers theorem covers all natural
   exponents. Evidence: `SerreGlobal` per-prime construction, `Local`, `Valuation`,
   and `FixedFieldLocalDifferentPowers`. All original primes are covered.
4. **Transition/comparison maps.** Required: actual inclusions and equality of
   integral ideals/coefficients with correct factors. Constructed: normal-closure
   inclusion, field-range isomorphism, integral restriction, canonical localized
   `A → U0 → B` and fraction maps. Trace compatibility proves literal different
   image; actual unramified towers/localization prove coefficient and index
   identities. Evidence: `Equivalence.map_absoluteDifferent_equiv`,
   `ramificationIdx_integersEquiv`, `FixedFieldDifferentTransport`,
   `FixedFieldLocalTower`, and `fixedFieldLocal_multiplicity_natCast`.
5. **Identity of the consumed object.** Required: precisely
   `differentIdeal ℤ (𝓞 L)`. Constructed: the raw local theorem uses the actual
   `differentIdeal A B`; the supplying coefficient theorem returns it to the
   actual original fixed field's absolute different; the trace-dual proof
   returns that literal ideal to `L`. Evidence: `fixedFieldDifferentMultiplicityBound`,
   `map_absoluteDifferent_equiv`, and `SerreGlobal.numberFieldDifferentMultiplicityBound`.
   Neither an order different nor a completion without an identity is consumed.
6. **Coefficient/normalization conventions.** Required: integral ideals, the
   actual length-defined `Ideal.ramificationIdx`, natural subtraction and the
   exact successor exponent. Constructed: the same integral rings and index;
   ideal equivalence and the prime-localization coefficient are exact. The
   integer formula `v_P(e)=e*padicValNat p e` is used only after `e>0`.
   Evidence: `Equivalence`, `FixedField`, initial `Global`, and the literal
   stored-type check in `GlobalAudit`. No residue/degree/valuation scalar is
   dropped.
7. **Local conditions.** Required: finite canonical DVR extensions, unramified
   `A/U0` and literal residue surjectivity. Constructed: the actual unique-prime
   fibres over `F` and their canonical prime localizations; the supplying proofs
   establish all conditions. We do not assert general single-prime localization
   finiteness over `ℤ_(p)`. There is **no completion** in this final global route,
   and no completeness or perfectness assumption is needed at the raw boundary.
   Evidence: `FixedFieldLocalization`, `FixedFieldUnramifiedFactor`,
   `FixedFieldLocalTower`, `FiniteNormalFractionField`, and `FixedField`.
8. **Exceptional cases.** Required: exclude no allowed prime/field and handle
   zero endpoints. Constructed/proved: `P=⊥` is impossible above `(p)` with
   `p.Prime`; lifted `Q≠⊥` follows from lying over the actual nonzero image;
   `e=0` is impossible by positivity; characteristic zero makes its local cast
   nonzero. `e=1` and unramified fields remain in the proof. Zero derivative
   coefficients have infinite valuation, not a fake finite value. `p=2` and all
   small primes are included. Evidence: initial `Global`, `Valuation`, actual
   localization nonzero proofs, `SerreGlobal`, and the dyadic/nongalois examples
   in `GlobalAudit`. Finite `padicValNat p 0` junk is never substituted for the
   valuation of zero.
9. **Downstream consumption.** Required: a closed theorem at the exact baseline
   proposition for the `hS` argument of `GlueConductor.D1_genuine`.
   Constructed: `serreDifferentBound` has precisely that stored type, no outer
   hypotheses or universe parameters; its actual proof passes the focused
   kernel recheck and standard-axiom report. This does not itself close the
   independent `hH`/T20 input, the assembled conductor argument or the height
   theorem. No registration/root consumer is changed; parent integration and
   eligible independent review remain required. Evidence:
   `SerreGlobal.serreDifferentBound`, baseline `Breaks.lean:363–404`, and
   `GlobalAudit`.

## Supplying source versions and exact local-to-global foundations

The fixed-field/localization foundation is the frozen 27-module
`ZInQKernel/Contrib/GlobalDifferentTransport` supplying packet. Its file bytes
were checked against the immutable supplier digest inventory before consumption.
No foundation implementation, wrapper, package, cache or source is copied or
changed in the worktree; compilation uses a read-only build overlay. The current
T21 packet contains a supplier SHA-256 inventory, not a second implementation.

The directly consumed supplier fingerprints are:

```text
ba1c4c8d7cb393f80a0e6209964d91a3d6fec80a69b0383d5f20f2150c5c0b74 FixedFieldLocalTower.lean
d73bf8460b94147a00c34e9db41c183026678c17b099d8c027ae5f6e5fc34b8d FixedFieldLocalFractionFields.lean
810bffa0f4f418d11e0669902fc7a208d2a8e05e3bc3069089475f35ceb9a0bd FixedFieldDifferentTransport.lean
5fc25e167d603c13ce26ea64b59958a7c60557fd469d31649fc7401d7ddc31d9 FixedFieldLocalDifferentPowers.lean
ced22e1c8c8fbacf3f318bc54e25304fb88f77d3ae04129d7190c7b6140d994b FiniteNormalFractionField.lean
cb154a26757d59ba957a2f066ef57ad801b2932cfebffea34453bd18a5913de5 FixedFieldUnramifiedFactor.lean
480473df64678fedc35a295dc1148e846092c8447833b419aef729a6d4ea5dd8 FixedFieldTransport.lean
9ef20878edaf0b72160c92b729439f110e71bef43c0b5ea6f197d8c117113707 NumberFieldLocalRamification.lean
933069e7582c7df2b1df7cb21dc1d9a9c172b097047270d3532802fda171427a NumberFieldPrimeLocalizationDifferent.lean
2194aa841e0f2190bd3bb5311482923c25af33e6b2d2fde189e382105b3e5d1a FixedFieldLocalization.lean
```

The initial Tau Ceti-derived local arithmetic sources and their exact
`a6027b1d24fcb935c53bd5b50d11b40991cda418` attribution are retained in the initial
thirteen source files and frozen note. Their license is included in the packet;
the pins stay Mathlib/Lean 4.35, not Tau Ceti's 4.36 toolchain.

The new presentation/equivalence steps read and consume these pinned Mathlib
sources directly:

- `NumberTheory/NumberField/Basic.lean`: actual integer-ring restriction and
  integral closures, finite number fields and their integer rings.
- `FieldTheory/Normal/Closure.lean`: actual normal closure, canonical inclusion,
  finite dimension and normality.
- `FieldTheory/Galois/Basic.lean`: separable normal closures and the actual finite
  fixed-field/fixing-subgroup correspondence.
- `FieldTheory/IntermediateField/Basic.lean`: actual `fieldRange`,
  `equivFieldRange` and equality-induced intermediate-field isomorphism.
- `FieldTheory/IsAlgClosed/AlgebraicClosure.lean` and `IsAlgClosed/Basic.lean`:
  actual algebraic closure and its normality/algebraicity properties.
- `RingTheory/Ideal/GoingUp.lean`: integral lying-over for every original input
  prime, not an assumed prime or uniqueness witness.
- `RingTheory/Trace/Basic.lean`: exact trace under the rational field isomorphism.
- `RingTheory/DedekindDomain/Different.lean`: actual trace-dual/different
  submodule identity.
- The previously recorded ramification/multiplicity and ideal-isomorphism
  suppliers: their required maps and nonzero hypotheses are proved at use.

The source inventory's baseline PR41 statement extraction remains frozen,
unregistered and unreviewed. It is a statement reference, not a theorem supplier.
Historical book numbering that was previously unverified is not promoted to a
verified citation by this kernel proof. The current kernel proof uses named
published-library proofs and exact linked project proofs, not a literature axiom.

## Reproduction, limits and integration duties

Materialize the eighteen owned contribution modules on the unchanged baseline,
plus the separately frozen `GlobalDifferentTransport` supplier. Do not update
pins, install an entire library or silently overwrite the initial snapshot.
Prepare a read-only import/build overlay by the authorized integration workflow.
The new dependency-safe compile order is:

```text
FixedField, Equivalence, Presentation, SerreGlobal, GlobalAudit
```

The initial thirteen sources retain their earlier dependency-safe compile order.
Use `LEAN_NUM_THREADS=2`, one compiler in this lane, and the authorized resource
gate. The verification log records the repository-relative compiler invocations,
source hashes, exits and selected axiom reports. No full root build or protected
controller acceptance is performed by this contribution.

The stronger integral theorem and the exact global theorem are no longer
conditional on an unproved mathematical model interface. Nevertheless, focused
compilation and one proof-body kernel recheck are not the integrator's complete
candidate raw-dependency replay, an independently reconstructed coverage decision,
an eligible Astra acceptance, a registered-provider decision, or assembled-proof
and manuscript-release acceptance. Those steps must use these exact frozen
sources and their directly consumed supplier versions. Prior scoped local
acceptances or the initial global-open packet are not acceptance of this new
composition.
