import re
T19=open('ZInQKernel/OneProof/H/TailZ19.lean').read().split('\n')
NF=open('ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean').read().split('\n')
PD=open('ZInQKernel/Contrib/OneProof/PersistsDVR.lean').read().split('\n')
PR=open('ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean').read().split('\n')
def rng(L,a,b): return '\n'.join(L[a-1:b])
def noh3(s,tag):
    bad=[l for l in s.split('\n') if re.search(r'\bh3\b',l)]
    assert not bad,(tag,bad)
parts=open('scratch/sga3-nbhd/_parts.txt').read()
sub=rng(T19,1344,1451)
inv=sub[sub.index("  · intro x hx\n"):]
subproof='''/-- **The glue `IdCompSubgroup` with no SGA 3 hypothesis**: multiplication by `SGA3IdComp.mul_mem` (any base,
from Stacks 04KV), inversion by the argument of `CToPrinted.idCompSubgroup_of` (which never used openness). -/
theorem idCompSubgroup_proof (hG : AVGlue.GeomConnOfRationalPoint) : IdCompSubgroup := by
  intro S _ G _ _ _
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have he : ∀ s, G.hom (e s) = s := by
    intro s
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  constructor
  · intro z hz1 hz2
    exact SGA3IdComp.mul_mem G hG z hz1 hz2
'''+inv
parts=parts.replace("@@SUBGROUP@@",subproof)
out=[parts]
s=rng(T19,1508,1572)
s=s.replace("theorem identityComponentOLRange_of (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) :\n    IdentityComponentOLRange := by\n  intro K _ A L _ _ _ 𝒢\n  have hO : IsOpen (idCompSet 𝒢.G) := h3 _ 𝒢.G\n  have gc := idCompSubgroup_of h3 hG",
"theorem identityComponentOLRange_at (hG : AVGlue.GeomConnOfRationalPoint) {K : Type} [Field K]\n    {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)\n    (hO : IsOpen (idCompSet 𝒢.G)) :\n    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧\n      IsMonHom i ∧ Set.range i.left = idCompSet 𝒢.G := by\n  have gc := idCompSubgroup_proof hG")
assert "identityComponentOLRange_at" in s
s=s.replace("/-- **`IdentityComponentOLRange`, PROVED** from SGA 3 VI_B 3.10 and the bundle leaf","/-- **`IdentityComponentOLRange` at one `𝒢` whose `𝒢⁰` is open** (the proof of `identityComponentOLRange_of`), from the bundle leaf")
noh3(s,'OLRange'); out.append('\n'+s+'\n')
s=rng(T19,1592,1644)
s=s.replace("theorem identityComponentBaseChangeDVRRange_of (h3 : SGA3_VIB_3_10) (h7 : SGA7_IX_3_3)\n    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRange := by",
"theorem identityComponentBaseChangeDVRRange_proof (h7 : SGA7_IX_3_3)\n    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRange := by")
s=s.replace("  have gb := idCompBaseChangeDVR_of h3 hG\n","")
s=s.replace("have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := h3 _ (bcO hO 𝒩.G)","have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := isOpen_idCompSet_groupModelO (ReductGlue.bcDVR hO 𝒩)")
s=s.replace("have hgb := gb K O K' O' hO 𝒩.G","have hgb := idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G\n      (isOpen_idCompSet_groupModelO 𝒩)")
s=s.replace("/-- **`IdentityComponentBaseChangeDVRRange`, PROVED** from the printed SGA 3 VI_B 3.10, SGA 7 IX 3.3 and the","/-- **`IdentityComponentBaseChangeDVRRange` with no SGA 3 hypothesis** (`G⁰` open over a DVR is proved here), from SGA 7 IX 3.3 and the")
noh3(s,'DVRRange'); out.append('\n'+s+'\n')
s=rng(T19,1646,1752)
s=s.replace("theorem semistableNeronBaseChange_of_printed_full (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)","theorem semistableNeronBaseChange_of_NeronOL (hB : BLR_1_2_4) (hOL : SGA3_VIB_3_10_NeronOL)")
s=s.replace("  have hIC := identityComponentOLRange_of h3 hG\n  have h33 := identityComponentBaseChangeDVRRange_of h3 h7 hG\n","  have h33 := identityComponentBaseChangeDVRRange_proof h7 hG\n")
s=s.replace("obtain ⟨𝒢₀, i, hoi, hmi, hri⟩ := hIC K A L 𝒩","have hO𝒩 : IsOpen (idCompSet 𝒩.G) := hOL K A L 𝒩 h𝒩 hss\n  obtain ⟨𝒢₀, i, hoi, hmi, hri⟩ := identityComponentOLRange_at hG 𝒩 hO𝒩")
s=s.replace("exact CToPrinted.idComp_baseChange h3 hG (gO O) 𝒩.G","exact idComp_baseChange' hG (gO O) 𝒩.G hO𝒩")
s=s.replace("/-- **The field `semistableNeronBaseChange` (SS2) from published-form leaves alone** (compiled): BLR 1.2/4,\nSGA 3 VI_B 3.10,","/-- **The field `semistableNeronBaseChange` (SS2)** (the proof of `semistableNeronBaseChange_of_printed_full`) with\nSGA 3 VI_B 3.10 replaced by its specialization `SGA3_VIB_3_10_NeronOL` (Néron models over `𝓞_L`): BLR 1.2/4,")
noh3(s,'full'); out.append('\n'+s+'\n')
out.append("end SGA3Nbhd\n")
s=rng(NF,263,376)
s=s.replace("theorem body_of_SH","theorem body_of_SH'")
s=s.replace("(hPP' : P'.comap (algebraMap E E') = P) (h3 : SGA3_VIB_3_10)","(hPP' : P'.comap (algebraMap E E') = P)")
s=s.replace("⟨idCompSet Y₁, h3 _ Y₁⟩","⟨idCompSet Y₁, SGA3Nbhd.isOpen_idCompSet_groupModelO (bcDVR hPP' 𝒩₁)⟩")
s=s.replace("idComp_baseChange h3 hG (gD hO) 𝒩.G","SGA3Nbhd.idComp_baseChange' hG (gD hO) 𝒩.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)")
s=s.replace("idComp_baseChange h3 hG (gD hP) 𝒩.G","SGA3Nbhd.idComp_baseChange' hG (gD hP) 𝒩.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)")
s=s.replace("idComp_baseChange h3 hG (gD hPP') 𝒩₁.G","SGA3Nbhd.idComp_baseChange' hG (gD hPP') 𝒩₁.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩₁)")
s=s.replace("idComp_baseChange h3 hG (gD hP') 𝒩'.G","SGA3Nbhd.idComp_baseChange' hG (gD hP') 𝒩'.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩')")
noh3(s,'body')
s2=rng(NF,378,387)
s2=s2.replace("theorem sga7_IX_3_3_of_SH (h7 : SGA7_IX_3_3_SH) (hN : GapSHPair.NeronBaseChangeStrictHenselization)\n    (h3 : SGA3_VIB_3_10) (hG","theorem sga7_IX_3_3_of_SH' (h7 : SGA7_IX_3_3_SH) (hN : GapSHPair.NeronBaseChangeStrictHenselization)\n    (hG")
s2=s2.replace("body_of_SH hO hP hP' hSHP hSHP' hPP' h3 hG","body_of_SH' hO hP hP' hSHP hSHP' hPP' hG")
s2=s2.replace("three leaves already in the bundles: gt-shpair's Néron leaf\n`GapSHPair.NeronBaseChangeStrictHenselization` (BLR 1.2/2), SGA 3 VI_B 3.10 and Stacks 04KV.","two leaves already in the bundles (no SGA 3 VI_B 3.10): gt-shpair's Néron leaf\n`GapSHPair.NeronBaseChangeStrictHenselization` (BLR 1.2/2) and Stacks 04KV.")
noh3(s2,'s2')
out.append('''
namespace SGA3Nbhd.NF

open ReductSplit ReductGlue SGA7PersistsNF

/-- `SGA7PersistsNF.body_of_SH` without `SGA3_VIB_3_10` (all bases are DVRs; `G⁰` open there is proved). -/
'''+s+'\n\n'+s2+'\n\nend SGA3Nbhd.NF\n')
s=rng(PD,203,256)
s=s.replace("theorem semistablePersistsDVR_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7","theorem semistablePersistsDVR_of_printed' (h7")
s=s.replace("have gc := idCompSubgroup_of h3 hG","have gc := SGA3Nbhd.idCompSubgroup_proof hG")
s=s.replace("⟨idCompSet 𝒩.G, h3 _ 𝒩.G⟩","⟨idCompSet 𝒩.G, SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩⟩")
s=s.replace("identityComponentBaseChangeDVRRange_of h3 h7 hG","SGA3Nbhd.identityComponentBaseChangeDVRRange_proof h7 hG")
s=s.replace("exact idCompBaseChangeDVR_of h3 hG K O K' O' hO 𝒩.G","exact SGA3Nbhd.idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G\n      (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)")
s=s.replace("theorem semistablePersistsSHcp_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7","theorem semistablePersistsSHcp_of_printed' (h7")
s=s.replace("semistablePersistsDVR_of_printed h3 h7 hG","semistablePersistsDVR_of_printed' h7 hG")
s=s.replace("theorem semistablePersistsSHcp_of_SH (h3 : CToPrinted.SGA3_VIB_3_10) (h7","theorem semistablePersistsSHcp_of_SH' (h7")
s=s.replace("semistablePersistsSHcp_of_printed h3 (SGA7PersistsNF.sga7_IX_3_3_of_SH h7 hN h3 hG) hG","semistablePersistsSHcp_of_printed' (SGA3Nbhd.NF.sga7_IX_3_3_of_SH' h7 hN hG) hG")
noh3(s,'persists')
out.append('''
namespace SGA3Nbhd.Persists

open ZInQ.HeightSplit GapPersists

'''+s+'\n\nend SGA3Nbhd.Persists\n')
pr='\n'.join(PR)
a=pr.index("/-- The two opens agree"); b=pr.index("/-- Conversely, the field gives")
s=pr[a:b]
s=s.replace("theorem preimage_eq","theorem preimage_eq'")
s=s.replace("(𝒩 : GroupModelO A O) (h3 : SGA3_VIB_3_10) (hG","(𝒩 : GroupModelO A O) (hG")
s=s.replace("idComp_baseChange h3 hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G","SGA3Nbhd.idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G\n    (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)")
s=s.replace("theorem sga7_IX_3_3_SH_of_pre (h : SGA7_IX_3_3_SHpre) (h3 : SGA3_VIB_3_10)\n    (hG","theorem sga7_IX_3_3_SH_of_pre' (h : SGA7_IX_3_3_SHpre)\n    (hG")
s=s.replace("(preimage_eq hO 𝒩 h3 hG)","(preimage_eq' hO 𝒩 hG)")
s=s.replace("from the print's form `SGA7_IX_3_3_SHpre` and the bundle leaves\n`SGA3_VIB_3_10` (research) and `GeomConnOfRationalPoint` (textbook).","from the print's form `SGA7_IX_3_3_SHpre` and `GeomConnOfRationalPoint`\n(no SGA 3 VI_B 3.10: `G⁰` open over a DVR is proved).")
noh3(s,'pre')
out.append('''
namespace SGA3Nbhd.Pre

open ReductSplit ReductGlue DictModels.SGA7Pre

'''+s+'\nend SGA3Nbhd.Pre\n\nend\n')
open('scratch/sga3-nbhd/SGA3NbhdOL.lean','w').write('\n'.join(out))
