from pathlib import Path
import json,hashlib
R=Path('/tmp/quartic214-manuscript-20261112');O=Path(__file__).parent
T=R/'research/quartic214-manuscript-revision2/quartic214.tex';M=R/'research/quartic214-manuscript-revision2/SOURCE_SPANS.json';sp=json.loads(M.read_text())['spans'];tl=T.read_text().splitlines()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
items=[]
def add(id,path,lines,meaning,issue):
 p=R/path;sl=p.read_text().splitlines();rr=[]
 for n in lines:
  ss=[s for s in sp if s.get('source')==path and s['source_lines'][0]<=n<=s['source_lines'][1]]
  assert len(ss)==1,(path,n)
  s=ss[0];a,b=s['tex_lines'];rr.append({'source_line':n,'source_text':sl[n-1],'receiving_lines':[a,b],'receiving_text':'\n'.join(tl[a-1:b])})
 items.append({'id':id,'source':path,'source_sha256':h(p),'occurrences':rr,'required_semantics':meaning,'finding':issue})
p='research/quartic214/'
add('F8a',p+'sources/conductor-sections1-3.md',[105,106],'G_t=G_{ceil(t)}; G^u=G_{phi^{-1}(u)}. Whole evaluated function value is the index.','The function argument and inverse escaped the ramification-group subscript. The received G_phi^{-1}(u) is not the stated upper-numbering definition.')
add('F8b',p+'sources/conductor-sections1-3.md',[135,136,138],"G_{F'} for the absolute Galois group of the quadratic kernel field F'.",'The prime is attached to G_F instead of the field F in its subscript.')
add('F8b-related',p+'proofs/provider-scope-carry.md',[66],"G_{F'} for that same field.",'Same field-prime scope in the provider consumer.')
add('F9a',p+'proofs/height-metric.md',[15],'Indexed forms omega_1,...,omega_g and dz_1 wedge ... wedge dz_g.','ASCII shorthand indices in the source were emitted as baseline factors or text dzg; the target must distinguish the g forms and their wedge.')
add('F9b',p+'proofs/height-metric.md',[21,23,29],'Projective line P^{1}_{t}, fibre points P_1,...,P_d, evaluations at P_j, and tuple indexed by j.','t is incorrectly inside the exponent of P. Pd and Pj are emitted without their intended point indices; the tuple j is also baseline and should be explicit.')
add('F9c',p+'proofs/height-evaluation.md',[18,28,40,48,54,60],'Projective line P^{1} over R,K,kappa(x),T and affine line A^{1}_R, including the entire omega_{P^{1}_R/R} relative-sheaf index.','The local P1 adapter does not match underscore-adjacent shorthand. P1_R etc and A1_R remain baseline 1, inconsistent with the actual schemes in the argument.')
add('F10',p+'proofs/modularity.md',[25],'b(g h g^{-1})=b(h). Only the final g is inverted.','The translator wraps ghg into text{ghg} and attaches the inverse to that entire grouped word.')
add('F9d',p+'proofs/modularity.md',[23],'Local field Q_p, absolute Galois group G_{Q_p}, and multiplicative group Q_p^{*}.','Source shorthand Qp survives as the two-letter subscript Qp / plain Qp*. This should be made explicit in the receiving mathematical notation; no lost literal star is asserted.')
add('F11a',p+'proofs/height-supplier.md',[47],'rho_l(sigma)=b(sigma)^{-1} a_sigma (mu_sigma composed with sigma).','ASCII o was intended as composition; the receiver emits a separate italic variable o. Use circ or explicit composition wording.')
add('F11b',p+'sources/conductor-sections1-3.md',[132],'The identical composition convention for rho_{ell_c}.','Related occurrence of the literal-o composition shorthand.')
report={'schema':'independent-semantic-serialization-findings-v1','reviewer':'/root/d214_geometry_source_closure','frozen_input_commit':'e3626cac202cdbcdfedc2bff1978dcd3ea3fd3ab','receiving_tex':{'path':str(T.relative_to(R)),'sha256':h(T)},'map':{'path':str(M.relative_to(R)),'sha256':h(M)},'exposure':'F1-F7 known before these findings. Initial transformation obligations frozen before author star inventory. These findings are independently found by actual source and receiver comparison.','scope':'All19 converted proof source bodies read,789 nonblank mapped spans content-compared,49 lexical differences individually inspected, all distinct target sub/superscript operands inspected. The content comparator deliberately erases grouping and is not semantic proof; the findings arise from the separate scope/notation read. This finite queue completes that converted-proof pass. IR rows, retained fragments, native body, new operative overlay and final rendering remain separately checked.','decision':'receiving revision not accepted; batch presentation correction required','items':items,'limits':['No mathematical source file or theorem is changed by this reviewer.','F9d/F11 make ASCII conventions explicit; the source arguments remain intelligible and no arithmetic counterexample is alleged.','This is a full converted-proof transformation pass, not a claim to have visually read all703PDFpages or newly audited every published supplier.','No controller eligibility or release acceptance.']}
(O/'FINDINGS_F8_F11.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(h(O/'FINDINGS_F8_F11.json'))
