"""assemble-port (stretch): parts/z93z_ltlocal.lean = lg-kerwild's KerWild.lean body (minus imports and `#print`) and lt-local's
part_tools, part_g7, part_main, part_rank, part_gp4 (part_copy omitted), with every top-level declaration whose qualified name
this file already declares removed (mk/dedup_part.py against the current AssemblePort.lean; a removed copy is then
resolved to this file's text, e.g. g0-assemble3's fixed `G7Data`, as lt-local's LtLocal4 variant uses); then open_zinq.
Run from scratch/assemble-port after `bash assemble.sh` WITHOUT this part (the reference must not contain it)."""
import subprocess, sys, os
def run(*a): subprocess.run([sys.executable, '-I'] + list(a), check=True)
kw = [l for l in open('../lg-kerwild/KerWild.lean').read().split('\n') if not l.startswith('#print') and not l.startswith('import ')]
open('/tmp/ap_kw_body.lean', 'w').write('\n'.join(kw))
lt = []
for f in ['part_tools', 'part_g7', 'part_main', 'part_rank', 'part_gp4']:
    lt += [l for l in open('../lt-local/%s.lean' % f).read().split('\n') if not l.startswith('#print')] + ['']
import re
# `ι` is a token in this file (a notation of an earlier part); lt-local's part_tools uses it as a bound name -> `ιq`
lt = [re.sub(r'(?<![\w.])ι(?![\wC₀-₉])', 'ιq', l) for l in lt]
open('/tmp/ap_lt_parts.lean', 'w').write('\n'.join(lt))
run('mk/dedup_part.py', '/tmp/ap_kw_body.lean', 'AssemblePort.lean', '/tmp/ap_kw_dedup.lean')
run('mk/dedup_part.py', '/tmp/ap_lt_parts.lean', 'AssemblePort.lean', '/tmp/ap_lt_dedup.lean')
hdr = '/-! ## assemble-port (stretch): lg-kerwild + lt-local, de-duplicated against this file (mk/mk_z93b.py) -/\n\n'
open('parts/z93z_ltlocal.lean', 'w').write(hdr + open('/tmp/ap_kw_dedup.lean').read() + '\n\n' + open('/tmp/ap_lt_dedup.lean').read() + '\n')
run('mk/open_zinq.py', 'parts/z93z_ltlocal.lean')
