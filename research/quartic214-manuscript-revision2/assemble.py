#!/usr/bin/env python3
"""Create the complete operative receiving revision from frozen e362 artifacts.

No historical source is edited. No polynomial expansion or PDF build occurs.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,resource
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'research/quartic214-manuscript'
BASE_TEX_SHA='27b189745aa78d2e36927468e554d2d29e8f8be84e2022204124ab897f75ed58'
BASE_MAP_SHA='c98fc0d5860fb1d17a1d1ec7f23e266015f26e37d72443b796a782006c371391'
def sha(b):return hashlib.sha256(b).hexdigest()
def relative(p):return str(p.relative_to(ROOT))
def assemble():
 raw=(BASE/'quartic214.tex').read_bytes();mapping=(BASE/'SOURCE_SPANS.json').read_bytes()
 if sha(raw)!=BASE_TEX_SHA or sha(mapping)!=BASE_MAP_SHA:raise ValueError('frozen receiving base changed')
 old=raw.decode().splitlines();data=json.loads(mapping);overlay=json.loads((HERE/'RECEIVING_OVERLAY.json').read_text())
 source=ROOT/overlay['f6']['source'];original=source.read_text().splitlines()[overlay['f6']['source_line']-1]
 if sha(source.read_bytes())!=overlay['f6']['source_sha256']or original!=overlay['f6']['original_source_line']:raise ValueError('F6 source binding changed')
 spec=importlib.util.spec_from_file_location('frozen_q214_renderer',BASE/'assemble.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
 replacement=a.prose(overlay['f6']['corrected_source_line'],source)
 f6span=next(q for q in data['spans']if q.get('source')==overlay['f6']['source']and q.get('source_lines')==[57,57])
 f6line=f6span['tex_lines'][0]
 if f6line!=2552:raise ValueError('unexpected F6 receiving locus')
 f7=overlay['f7'];f7line=f7['old_tex_line']
 if old[f7line-1]!=f7['old_description']:raise ValueError('unexpected F7 catalogue locus')
 catalogue=a.prose(f7['current_description'],ROOT/f7['sources'][0]['path'])
 extra={}
 legacy=json.loads((BASE/'SOURCE_CORRECTIONS_V1.json').read_text())['corrections']
 for fix in overlay.get('additional_source_lines',[]):
  src=ROOT/fix['source'];ls=src.read_text().splitlines()
  if sha(src.read_bytes())!=fix['source_sha256']or ls[fix['source_line']-1]!=fix['original_source_line']:raise ValueError('stale additional source overlay '+fix['id'])
  span=next(q for q in data['spans']if q.get('source')==fix['source']and 'source_lines'in q and q['source_lines'][0]<=fix['source_line']<=q['source_lines'][1]and q['method']in ['prose-with-math-typesetting','ascii-display-math'])
  left,right=span['tex_lines'];sl,sr=span['source_lines']
  if left not in extra:
   for oldfix in legacy:
    if oldfix['source']==fix['source']:ls[oldfix['source_line']-1]=oldfix['corrected_line']
   extra[left]={'span':span,'records':[],'source_lines':ls,'path':src}
  extra[left]['records'].append(fix);extra[left]['source_lines'][fix['source_line']-1]=fix['corrected_source_line']
 for left,x in extra.items():
  span=x['span'];sl,sr=span['source_lines'];ls=x['source_lines']
  if span['method']=='prose-with-math-typesetting':
   if sl!=sr:raise ValueError('multiline prose overlay unsupported')
   x['text_lines']=[a.prose(ls[sl-1],x['path'])]
  else:
   x['text_lines']=[r'\begin{gather*}']+[a.math(ls[n-1].strip().rstrip('.'))+(r'\\'if n<sr else '')for n in range(sl,sr+1)]+[r'\end{gather*}']
  if len(x['text_lines'])!=span['tex_lines'][1]-left+1:raise ValueError('additional overlay changes line count')
 note=overlay['native_operative_note'].splitlines();needle="Li's old/new decomposition"
 native=next(i for i,l in enumerate(old,1)if l==needle)
 if native!=5769:raise ValueError('unexpected native primitive locus')
 date_old=overlay['date']['original'];date_new=overlay['date']['current']
 if old.count(date_old)!=1:raise ValueError('unexpected edition date')
 edits=[{'id':'F7-CERTIFICATE-CATALOGUE','old_lines':[f7line,f7line],'old_sha256':sha((old[f7line-1]+'\n').encode()),'new_lines':[catalogue],'source_json_pointer':'/f7'},{'id':'F6-M3-LINE57','old_lines':[f6line,f6line],'old_sha256':sha((old[f6line-1]+'\n').encode()),'new_lines':[replacement],'source_json_pointer':'/f6'}, {'id':'CURRENT-NATIVE-PRIMITIVE','insert_before_old_line':native,'new_lines':note,'source_json_pointer':'/native_operative_note'}, {'id':'RECEIVING-EDITION-DATE','old_lines':[old.index(date_old)+1,old.index(date_old)+1],'new_lines':[date_new],'source_json_pointer':'/date'}]
 for n,x in sorted(extra.items()):
  end=x['span']['tex_lines'][1];edits.append({'id':'+'.join(f['id']for f in x['records']),'old_lines':[n,end],'old_sha256':sha(('\n'.join(old[n-1:end])+'\n').encode()),'new_lines':x['text_lines'],'source_json_pointer':'/additional_source_lines'})
 extra_lines={n+i:line for n,x in extra.items()for i,line in enumerate(x['text_lines'])}
 new=[]
 for i,line in enumerate(old,1):
  if i==native:new.extend(note)
  new.append(extra_lines[i]if i in extra_lines else replacement if i==f6line else catalogue if i==f7line else date_new if line==date_old else line)
 output=('\n'.join(new)+'\n').encode()
 def shifted(line):return line+len(note)if line>=native else line
 spans=[]
 for q in data['spans']:
  q=copy.deepcopy(q);left,right=q['tex_lines']
  if left<native<=right:
   if q['method']!='exact-retained-body-LF':raise ValueError('native insertion crosses non-exact span')
   sl,sr=q['source_lines'];cut=sl+(native-left)
   l=copy.deepcopy(q);l['tex_lines']=[left,native-1];l['source_lines']=[sl,cut-1];spans.append(l)
   spans.append({'source':relative(HERE/'RECEIVING_OVERLAY.json'),'source_json_pointer':'/native_operative_note','tex_lines':[native,native+len(note)-1],'method':'operative-current-native-primitive-source-application-note','application':'Q214-CURRENT-NATIVE-PRIMITIVE-EXISTENCE-20261112'})
   q['tex_lines']=[native+len(note),shifted(right)];q['source_lines']=[cut,sr]
  else:q['tex_lines']=[shifted(left),shifted(right)]
  if left==f6line:
   q['method']='current-receiving-F6-source-local-overlay'
   q['source_corrections']=[{'sidecar':relative(HERE/'RECEIVING_OVERLAY.json'),'id':'F6-M3-LINE57','corrected_source_line':overlay['f6']['corrected_source_line'],'finding_ids':['F6'],'prior_source_and_receiving_bytes_preserved':True}]
  if left in extra:
   q['method']='current-receiving-explicit-source-notation-overlay';q['source_corrections']=q.get('source_corrections',[])+[{'sidecar':relative(HERE/'RECEIVING_OVERLAY.json'),'id':fix['id'],'corrected_source_line':fix['corrected_source_line'],'finding_ids':fix['finding_ids'],'prior_source_and_receiving_bytes_preserved':True}for fix in extra[left]['records']]
  if left<=f7line<=right:q['current_purpose_overlay']={'sidecar':relative(HERE/'RECEIVING_OVERLAY.json'),'id':'F7-CERTIFICATE-CATALOGUE','source_json_pointer':'/f7','numeric_certificate_bytes_unchanged':True}
  spans.append(q)
 data['spans']=spans;data['schema']='quartic214-receiving-revision2-source-spans/v1';data['output']=relative(HERE/'quartic214.tex');data['output_sha256']=sha(output)
 data['base_receiving']={'source':relative(BASE/'quartic214.tex'),'sha256':BASE_TEX_SHA,'source_map':relative(BASE/'SOURCE_SPANS.json'),'source_map_sha256':BASE_MAP_SHA,'status':'historical frozen receiving edition; no original bytes altered'}
 data['receiving_revision']={'id':'revision2-F6-and-current-native-primitive','role':'complete operative receiving source, pending new receiving review/PDF','overlay':relative(HERE/'RECEIVING_OVERLAY.json'),'overlay_sha256':sha((HERE/'RECEIVING_OVERLAY.json').read_bytes()),'edits':edits,'source_locus_to_current_map':'Original spans retained; exact foundation span split around the operative inserted note; all later TeX line references shifted by the inserted note length.'}
 p=HERE/'RECEIVING_OVERLAY.json';b=p.read_bytes();data['sources'][relative(p)]={'sha256':sha(b),'bytes':len(b),'line_count':len(b.splitlines())}
 data['presentation_rules']+=['Revision2 protects all M3 line57 unit-group markers from Markdown emphasis, groups R_{>0}, and explicitly chooses the least Dirichlet modulus r=cond(eta).','F7 distinguishes the four quotient-quartic/cross-ratio certificate from the five-form/ten-pair determinant support certificate, with all artifact bytes unchanged.','An operative note at the actual native Li-only existence locator applies the already-written Deligne–Serre primitive extraction to this exact current receiving use; old native source remains historical evidence.']
 return output,(json.dumps(data,indent=2,ensure_ascii=False,sort_keys=True)+'\n').encode()
def main():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024));p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();tex,mapping=assemble()
 for name,b in [('quartic214.tex',tex),('SOURCE_SPANS.json',mapping)]:
  path=HERE/name
  if args.check:
   if not path.exists()or path.read_bytes()!=b:raise SystemExit('stale revision2 generated file: '+name)
  else:path.write_bytes(b)
 print('PASS: complete receiving revision2 deterministic source and map; not mathematical acceptance')
if __name__=='__main__':main()
