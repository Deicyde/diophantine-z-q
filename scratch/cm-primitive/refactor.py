p='ZInQKernel/Contrib/OneProof/CMPrimitive.lean'
s=open(p).read()
def stmt(k): return open(f'scratch/cm-primitive/stmt_{k}.lean').read()
prim = "    IsPrimitiveType Φ →\n"
def sub(b, new, old_name, new_name):
    assert b.count(prim)==1
    b = b.replace(prim, new)
    assert old_name in b
    return b.replace(old_name, new_name, 1)
quadline = "    Module.finrank ℚ E = 2 →\n"
genline = "    P E g Φ →\n"
MaxQuad = sub(stmt('MaxPrim'), quadline, 'def MainTheoremCMPolMaxPrim', 'def MainTheoremCMPolMaxQuad')
PolQuadSign = sub(stmt('PolSignPrim'), quadline, 'def MainTheoremCMPolPrimSign (ε', 'def MainTheoremCMPolQuadSign (ε')
SignQuad = sub(stmt('SignPrim'), quadline, 'def MainTheoremCMSignPrim (ε', 'def MainTheoremCMSignQuad (ε')
PolOn = sub(stmt('PolSignPrim'), genline, 'def MainTheoremCMPolPrimSign (ε : ℤˣ)', 'def MainTheoremCMPolOn (P : CMTypeClass) (ε : ℤˣ)')
SignOn = sub(stmt('SignPrim'), genline, 'def MainTheoremCMSignPrim (ε : ℤˣ)', 'def MainTheoremCMSignOn (P : CMTypeClass) (ε : ℤˣ)')
quad_block = r'''
/-! ### The imaginary quadratic case (`g = 1`, CM elliptic curves)

Both consumers use the main theorem only for imaginary quadratic fields: hcm-printed's at `(QNeg m, κ)`, and the
reduction `mainTheoremCMEK_of_quad` below at `(K, κ)`. So an even weaker form of the leaf suffices: the main theorem
for `[E : ℚ] = 2` (every such type is primitive, `isPrimitiveType_of_finrank_two`). -/

/-- **LEAF `MainTheoremCMPolMaxQuad` (the main theorem of complex multiplication for CM elliptic curves with
`𝓞_E`-ideal lattices, in Shimura's normalization; printed form).** mtcm-polar's `MainCMPolar.MainTheoremCMPolMax`
with the one added hypothesis `Module.finrank ℚ E = 2` (so `g = 1`: `E` imaginary quadratic, `A` an elliptic curve
with CM by `𝓞_E`).

*Published statement*: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm 5.4
(elliptic curves: `ξ(u)^σ = ξ'(s⁻¹u)` for `σ = [s, K]`, `ξ' : ℂ/s⁻¹𝔞 ≅ E^σ`); S. Lang, *Elliptic functions*, Ch. 10,
Thm 3; J. Silverman, *Advanced topics in the arithmetic of elliptic curves*, Thm II.8.2 (numbers UNVERIFIED). In
dimension `1` the reflex field of `(E, {κ})` is `κ(E)`, the reflex norm is the identity (`reflexNorm_rho1`), every
lattice of the leaf is an `𝓞_E`-ideal and every elliptic curve is polarized, so the leaf is the printed statement
for `𝓞_E`-ideal lattices with the clauses on the type of `(E^σ, θ')` and the uniqueness of `θ'` dropped. Implied by
`MainTheoremCMPolMaxPrim` (`polMaxQuad_of_polMaxPrim`). -/
''' + MaxQuad + r'''
/-- `MainTheoremCMPolMaxQuad` at a sign `ε`. -/
''' + PolQuadSign + r'''
/-- **LEAF `MainTheoremCMPolQuad` (the main theorem of CM for CM elliptic curves with `𝓞_E`-ideal lattices, sign of
the Artin map left open; printed form).** `∃ ε, MainTheoremCMPolQuadSign ε`. Same sources as
`MainTheoremCMPolMaxQuad`; implied by it and by `MainTheoremCMPolPrim` (`polQuad_of_polPrim`). -/
def MainTheoremCMPolQuad : Prop := ∃ ε : ℤˣ, MainTheoremCMPolQuadSign ε

/-- **Glue target** `MainTheoremCMSignQuad ε`: `HcmPrinted.MainTheoremCMSign ε` for imaginary quadratic `E`. -/
''' + SignQuad + r'''
theorem polQuadSign_of_polPrimSign {ε : ℤˣ} (h : MainTheoremCMPolPrimSign ε) : MainTheoremCMPolQuadSign ε := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    hO hζ A' hh hpb hone

/-- The quadratic leaf is implied by the primitive leaf. -/
theorem polMaxQuad_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolMaxQuad := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    hO hζ A' hh hpb hone

/-- The quadratic leaf is implied by the primitive leaf. -/
theorem polQuad_of_polPrim (h : MainTheoremCMPolPrim) : MainTheoremCMPolQuad := by
  obtain ⟨ε, h⟩ := h
  exact ⟨ε, polQuadSign_of_polPrimSign h⟩

theorem polQuadSign_one_of_polMaxQuad (h : MainTheoremCMPolMaxQuad) : MainTheoremCMPolQuadSign 1 := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  simp only [Units.val_one, zpow_one]
  exact h E g Φ hdeg hinj h2 Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

theorem polQuad_of_polMaxQuad (h : MainTheoremCMPolMaxQuad) : MainTheoremCMPolQuad :=
  ⟨1, polQuadSign_one_of_polMaxQuad h⟩

theorem signQuad_of_signPrim {ε : ℤˣ} (h : MainTheoremCMSignPrim ε) : MainTheoremCMSignQuad ε := by
  intro E _ _ _ g Φ hdeg hinj h2 Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone
  obtain rfl : g = 1 := by omega
  exact h E 1 Φ hdeg hinj (isPrimitiveType_of_finrank_two Φ h2 hinj) Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype
    A' hh hpb hone

/-! ### Generic forms (a class of CM types), for the copied proof -/

/-- A class of CM types `(E, Φ)`. -/
abbrev CMTypeClass : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ), (Fin g → E →+* ℂ) → Prop

/-- `MainCMPolar.MainTheoremCMPolSign ε` restricted to a class `P` of CM types. -/
''' + PolOn + r'''
/-- `HcmPrinted.MainTheoremCMSign ε` restricted to a class `P` of CM types. -/
''' + SignOn + r'''
end Leaves
'''
assert s.count('\nend Leaves\n')==1
s = s.replace('\nend Leaves\n', quad_block, 1)
# generic copied proof
old_hdr = "theorem mainTheoremCMSignPrim_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolPrimSign ε)"
assert old_hdr in s
s = s.replace(old_hdr, "theorem mainTheoremCMSignOn_of_polar (P : CMTypeClass) (ε : ℤˣ) (hP : MainTheoremCMPolOn P ε)")
s = s.replace("    MainTheoremCMSignPrim ε := by\n  have hH", "    MainTheoremCMSignOn P ε := by\n  have hH", 1)
old_doc = """/-- **The main theorem of CM for arbitrary lattices and primitive types from the polarized, maximal-order print
for primitive types, at any sign `ε`.** -/
"""
assert old_doc in s
s = s.replace(old_doc, """/-- **The main theorem of CM for arbitrary lattices from the polarized, maximal-order print, on any class `P` of CM
types, at any sign `ε`.** -/
""")
tail_proof = "    ⟨isAnalyticHom_comp (isAnalyticHom_of_unif hθB') muO, hker, hsurj⟩, htors⟩\n"
assert s.count(tail_proof)==1
s = s.replace(tail_proof, tail_proof + r'''
/-- **The main theorem of CM for arbitrary lattices and primitive types** from the primitive print. -/
theorem mainTheoremCMSignPrim_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolPrimSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignPrim ε :=
  mainTheoremCMSignOn_of_polar (fun _ _ _ _ _ Φ => IsPrimitiveType Φ) ε hP hX hUL hG

/-- **The main theorem of CM for arbitrary lattices on CM elliptic curves** from the quadratic print. -/
theorem mainTheoremCMSignQuad_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolQuadSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignQuad ε :=
  mainTheoremCMSignOn_of_polar (fun E _ _ _ _ _ => Module.finrank ℚ E = 2) ε hP hX hUL hG
''')
s = s.replace("""Copy of `MainCMPolar.mainTheoremCMSign_of_polar` (`ZInQKernel/Contrib/OneProof/MainCMPolar.lean`, wip/mtcm-polar
50dcdc48, lines 637-846), with the hypothesis `hprim : IsPrimitiveType Φ` introduced and passed to the leaf; no
other change. -/""", """Copy of `MainCMPolar.mainTheoremCMSign_of_polar` (`ZInQKernel/Contrib/OneProof/MainCMPolar.lean`, wip/mtcm-polar
50dcdc48, lines 637-846), for a class `P` of CM types: the hypothesis `hprim : P E g Φ` is introduced and passed to
the leaf; no other change. -/""")
# EK reduction via quad
old = "theorem mainTheoremCMEK_of_prim (ε : ℤˣ) (hP : MainTheoremCMSignPrim ε) (hX : CMAbVarExists)"
assert old in s
s = s.replace(old, "theorem mainTheoremCMEK_of_quad (ε : ℤˣ) (hP : MainTheoremCMSignQuad ε) (hX : CMAbVarExists)")
old = "hP K 1 Φ0 (by rw [hK]) hinj1 (isPrimitiveType_of_finrank_two Φ0 hK hinj1)"
assert old in s
s = s.replace(old, "hP K 1 Φ0 (by rw [hK]) hinj1 hK")
s = s.replace("""/-- **The reduction from the induced type of `E = K(√2)` to the primitive type `(K, κ)`.** The main theorem of CM
for primitive types (every lattice), Shimura's existence theorem and the textbook leaves give the main theorem for
`(E, PhiE κ)`. -/""", """/-- **The reduction from the induced type of `E = K(√2)` to the primitive type `(K, κ)`.** The main theorem of CM
for imaginary quadratic fields (every lattice), Shimura's existence theorem and the textbook leaves give the main
theorem for `(E, PhiE κ)`. -/""")
anchor = "\n/-- **Sanity check: the induced type of `K(√2)` is not primitive**"
assert anchor in s
s = s.replace(anchor, r'''
/-- **The reduction from the induced type of `E = K(√2)`**, from the main theorem for primitive types. -/
theorem mainTheoremCMEK_of_prim (ε : ℤˣ) (hP : MainTheoremCMSignPrim ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMEK ε :=
  mainTheoremCMEK_of_quad ε (signQuad_of_signPrim hP) hX hUL hG
''' + anchor, 1)
anchor2 = "\nend EK\n"
s = s.replace(anchor2, r'''
/-- **The main theorem of CM at the induced type of `K(√2)`** (existential sign) from the quadratic print. -/
theorem mainTheoremCMEK_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMEK ε := by
  obtain ⟨ε, h⟩ := hP
  exact ⟨ε, mainTheoremCMEK_of_quad ε (mainTheoremCMSignQuad_of_polar ε h hX hUL hG) hX hUL hG⟩
''' + anchor2, 1)
# consumers
old = """theorem qmReciprocityL3_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 := by
  obtain ⟨ε, h⟩ := hP
  exact qmReciprocityL3_of_ek
    ⟨ε, mainTheoremCMEK_of_prim ε (mainTheoremCMSignPrim_of_polar ε h hX hUL hG) hX hUL hG⟩
    (AvSplit.Final.h69 hUL hG)"""
assert old in s
s = s.replace(old, """theorem qmReciprocityL3_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 :=
  qmReciprocityL3_of_ek (mainTheoremCMEK_of_polPrim hP hX hUL hG) (AvSplit.Final.h69 hUL hG)

/-- **`QMReciprocityL3` from the main theorem of CM for CM elliptic curves** (`𝓞_E`-ideal lattices, existential
sign), Shimura's existence theorem and the textbook leaves. -/
theorem qmReciprocityL3_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 :=
  qmReciprocityL3_of_ek (mainTheoremCMEK_of_polQuad hP hX hUL hG) (AvSplit.Final.h69 hUL hG)""")
old = """  rayClassCMAb_of_leaves2 hR (qmReciprocityL3_of_polPrim hP hX hUL hG) hUL hG hMum
"""
assert old in s
s = s.replace(old, old + r'''
/-- **The former field `rayClassCMAb`** from the quadratic print. -/
theorem rayClassCMAb_of_polQuad (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPolQuad)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_leaves2 hR (qmReciprocityL3_of_polQuad hP hX hUL hG) hUL hG hMum
''')
old = "theorem shimuraMainCM_of_arithPrim (hM : MainTheoremCMSignPrim 1)"
assert old in s
s = s.replace(old, "theorem shimuraMainCM_of_arithQuad (hM : MainTheoremCMSignQuad 1)")
old = """type_inj
    (isPrimitiveType_of_finrank_two _ finrank_QNeg type_inj) (QNeg m) (kap m)"""
assert old in s
s = s.replace(old, """type_inj finrank_QNeg
    (QNeg m) (kap m)""")
old = """/-- **`hCM = T5Glue.ShimuraMainCM` from the polarized, maximal-order print for primitive types**"""
assert old in s
s = s.replace(old, r'''/-- `T5Glue.ShimuraMainCM` from the main theorem of CM for primitive types. -/
theorem shimuraMainCM_of_arithPrim (hM : MainTheoremCMSignPrim 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_arithQuad (signQuad_of_signPrim hM) hWU hWP hWA hH

''' + old)
s = s.replace("""  shimuraMainCM_of_arithPrim (mainTheoremCMSignPrim_of_polar 1 (polPrimSign_one_of_polMaxPrim hP) hX hUL hG)
    hWU hWP hWA (AvSplit.Final.h69 hUL hG)
""", """  shimuraMainCM_of_arithPrim (mainTheoremCMSignPrim_of_polar 1 (polPrimSign_one_of_polMaxPrim hP) hX hUL hG)
    hWU hWP hWA (AvSplit.Final.h69 hUL hG)

/-- **`hCM = T5Glue.ShimuraMainCM` from the main theorem of CM for CM elliptic curves** (`𝓞_E`-ideal lattices,
`ε = 1`), Shimura's existence theorem, hcm-printed's Weierstrass leaves and the textbook leaves. -/
theorem shimuraMainCM_of_polMaxQuad (hP : MainTheoremCMPolMaxQuad) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_arithQuad (mainTheoremCMSignQuad_of_polar 1 (polQuadSign_one_of_polMaxQuad hP) hX hUL hG)
    hWU hWP hWA (AvSplit.Final.h69 hUL hG)
""")
open(p,'w').write(s)
print("ok", len(s))
