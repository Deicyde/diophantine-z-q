# gt-sga3: SGA 3 VI_B 3.10 (identity component of a smooth group scheme is open), reduced

## Verdict

`CToPrinted.SGA3_VIB_3_10` (field `sga3_VIB_3_10` of `HDec.HSyn.OpenResearchLeaves16`; defined at
`ZInQKernel/OneProof/H/TailZ19.lean` L199) is **true as stated and not vacuous**. It is **reduced in Lean** to a
strictly weaker published-form leaf plus a leaf already in the bundle. All the glue is proved. The theorem is

```lean
theorem SGA3IdComp.sga3_VIB_3_10_of_nbhd (hN : SGA3IdComp.SGA3_VIB_3_10_Nbhd)
    (hG : AVGlue.GeomConnOfRationalPoint) : CToPrinted.SGA3_VIB_3_10
```

in `ZInQKernel/Contrib/OneProof/SGA3IdComp.lean`. It has no `sorry` and uses only `propext`,
`Classical.choice` and `Quot.sound` (VERIFIED, `#print axioms` and `#discharges` below).

* **New LEAF `SGA3_VIB_3_10_Nbhd`** (published form): for every smooth group scheme `G → S` and every
  `s ∈ S`, `G⁰ = idCompSet G` contains an open neighbourhood of `e(s)`. It follows from SGA 3 I, Exp. VI_B,
  Thm. 3.10 (and from EGA IV₃ 15.6.5); both numbers are recalled, UNVERIFIED. It is weaker than the printed
  theorem: `G⁰` open implies that it is a neighbourhood of each `e(s)`.
* **`AVGlue.GeomConnOfRationalPoint`** (Stacks 04KV): this is already the open field
  `OpenTextbookLeaves10.geomConnOfRationalPoint`, so the reduction adds no new textbook leaf.

The strict LEAF count is unchanged: one leaf goes out (`sga3_VIB_3_10`) and one strictly weaker leaf comes
in (`SGA3_VIB_3_10_Nbhd`). No GLUE is added.

What the reduction does and does not do. The Lean proof covers the step from the unit section to all of `G⁰`.
That step is the group-theoretic translation argument, together with the field-level facts it needs: smooth
schemes over a field have irreducible connected components, and `G⁰` is closed under the group law over any
base. What remains in the leaf is the behaviour of `G⁰` near the unit section across fibres. That is the
EGA IV₃ §15.6 content, which the literature proves by reducing to noetherian bases (EGA IV₃ §8) and using the
constructibility of the connectedness of fibres (EGA IV₃ §9.7). Mathlib 4.35 has neither (see §3). The new
leaf has the same depth as the original, and this reduction shows the two are equivalent modulo Stacks
04KV. So the leaf to crowdsource is now the neighbourhood statement, or EGA IV₃ 15.6.4/15.6.5 directly.

## 1. Statements

`idCompSet G` (TailZ19 L191; VERIFIED, read): `x ∈ connectedComponentIn (f⁻¹{f x}) (e (f x))`, the union of the
identity components of the fibres. The fibre carries the subspace topology, which is homeomorphic to the
scheme fibre (Mathlib `Scheme.Hom.fiberHomeo`).

```lean
/-- LEAF (SGA 3 VI_B 3.10; EGA IV₃ 15.6.5; UNVERIFIED numbers; a consequence, weaker). -/
def SGA3IdComp.SGA3_VIB_3_10_Nbhd : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (s : S),
    ∃ U : Set G.left, IsOpen U ∧ (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ U ∧ U ⊆ idCompSet G
```

## 2. Proof (all compiled)

Let `U ⊆ G⁰` be open with `e(S) ⊆ U`. Take the union over `s` of the leaf's neighbourhoods.

1. **Irreducible neighbourhoods over a field** (`exists_irred_nbhd`, `exists_irred_nbhd_of_smooth`).
   * A smooth scheme over a field has regular local rings: the vendored CloudW07 result
     `Smooth.isRegularLocalRing_stalk`.
   * Regular local rings are domains: CloudW07 `IsRegularLocalRing.isDomain`.
   * The generizations of a point are the image of `Spec 𝒪_x` (Mathlib `Scheme.range_fromSpecStalk`), so they
     form an irreducible set.
   * In a noetherian affine open, the point therefore lies in exactly one irreducible component. Removing
     the other, finitely many, components leaves an open, compact, irreducible neighbourhood.
   * A chain argument (`exists_irred_of_mem_connectedComponent`) puts any two points of a connected component
     in a common open compact irreducible set. The union of two open irreducible sets that meet is
     irreducible.
2. **`G⁰` is closed under `μ` over any base** (`mul_mem`). This is the c-to-printed glue `IdCompSubgroup`, now
   for any `S` and with no `SGA3_VIB_3_10` hypothesis.
   * Take `z` over `t` with both coordinates in `G⁰`. Put `e(t)` and the two coordinates in one open compact
     irreducible `Q` of the fibre `G_t`.
   * `Q → Spec κ(t)` is geometrically connected (`geomConnOfRationalPoint`, applied to the open subscheme `Q`),
     so `Q ×_{κ(t)} Q` is connected. This uses Mathlib's instance for products, with `UniversallyOpen` over a
     field.
   * Its image in `G ×_S G` contains `z` and `(e(t), e(t))` (`Scheme.Pullback.range_map`, since
     `Spec κ(t) → S` is a monomorphism).
   * So `μ` maps it to a connected subset of the fibre that contains `μ(z)` and `e(t)`.
3. **Translation through `κ(x)`** (`exists_point`).
   * Let `x ∈ G⁰` lie over `t`, with `K = κ(x)` (residue field of the fibre at `x`) and `x̃ : Spec K → G`.
   * In `H = G ×_S Spec K`, which is smooth over `K`, the points `e_K` and `δ = (x̃, id)` lie in the image of
     the connected `Q ×_{κ(t)} Spec K`. They are therefore in one component, hence in a common irreducible
     open `W`.
   * The opens `{h : pr₁ h ∈ U}` (it contains `e_K`) and `{h : x̃·(pr₁ h)⁻¹ ∈ U}` (it contains `δ`, since
     `x̃ x̃⁻¹ = e`) both meet `W`, so they meet each other.
   * This gives `w ∈ G ×_S G` with `w₁ = x`, `w₂ ∈ U` and `w₁ w₂⁻¹ ∈ U`.
4. **Openness.** `M = pr₁(pr₂⁻¹ U ∩ d⁻¹ U)`, where `d(w) = w₁ w₂⁻¹`.
   * `M` is open: `pr₁` is a base change of the smooth `G → S`, hence flat and locally of finite presentation,
     hence universally open (Mathlib `UniversallyOpen.of_flat`).
   * `M` contains `x`.
   * `M ⊆ G⁰`, because `w₁ = (w₁ w₂⁻¹)·w₂` (the identity `lift d pr₂ ≫ μ = pr₁` in the group `Hom(G ⊗ G, G)`)
     and step 2 applies.

## 3. Why the neighbourhood leaf is not proved here

Survey (VERIFIED by reading Mathlib 4.35 and the vendored libraries):
* Mathlib has Chevalley's theorem for rings (`PrimeSpectrum.isConstructible_comap_image`). It has no
  scheme-level constructibility and no constructibility of connected or irreducible fibres (EGA IV₃ 9.7.7).
* CloudW01Spread descends smooth morphisms along cofiltered limits (EGA IV 17.7.8). Nothing descends the
  connected-fibre behaviour of `G⁰`.
* SPECULATIVE: no proof avoiding these inputs is known to me. Pointwise statements about smooth morphisms are
  false without the section: for `Spec ℤ[i][1/2] → Spec ℤ[1/2]`, no open has connected fibres. For a
  non-noetherian `S`, topological closure arguments cannot replace constructibility.

The leaf is used once per point `x` (at `s = f x`), at the same `S` and `G` as the target.

## 4. Checks

* Scratch: `scratch/gt-sga3/Part1.lean` (the same content as the contribution) compiles with
  `lake env lean`. `#print axioms SGA3IdComp.sga3_VIB_3_10_of_nbhd` gives
  `[propext, Classical.choice, Quot.sound]` (VERIFIED).
* `#discharges`: see §5 (`scratch/gt-sga3/Discharges.lean`).

## 5. `#discharges` output

Built with `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.SGA3IdComp` (exit 0; the module built in 80 s). Then
`lake env lean scratch/gt-sga3/Discharges.lean` printed (VERIFIED):

```
DISCHARGES [OpenResearchLeaves16.sga3_VIB_3_10] by SGA3IdComp.sga3_VIB_3_10_of_nbhd
  still assumes: [SGA3IdComp.SGA3_VIB_3_10_Nbhd, AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 528 theorems checked, 1 discharge one
```

Fold spec: remove `sga3_VIB_3_10` and add the leaf `SGA3IdComp.SGA3_VIB_3_10_Nbhd` (kind: published, LEAF,
consequence of SGA 3 VI_B 3.10). `AVGlue.GeomConnOfRationalPoint` is already the field
`geomConnOfRationalPoint`.
