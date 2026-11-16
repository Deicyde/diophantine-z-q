"""Audit: every line of each ported file that differs from upstream (~/flt-src) is classified as header,
import, set_option (lakefile options), clash rename (equal to upstream after deleting `_aflt`), or [port]-marked
(the line or a line within 3 above carries `[port]`).  Prints any other difference."""
import difflib,os,re,sys
FLT_SRC=sys.argv[1] if len(sys.argv)>1 else os.environ['FLT_SRC']  # a checkout of upstream FLT at the vendored commit
files=[l.strip() for l in open('scratch/flt-cqj2/new_files.txt') if l.strip()]
cnt={'rename':0,'port':0,'import':0,'setopt':0,'other':0}
for f in files:
    rel=f.split('AnthropicFLT/')[1]
    up=open(os.path.join(FLT_SRC,rel)).read().split('\n')
    loc=open(f).read()
    loc=loc.split('\n-/\n',1)[1].split('\n')  # drop vendoring header
    sm=difflib.SequenceMatcher(None,up,loc,autojunk=False)
    for tag,i1,i2,j1,j2 in sm.get_opcodes():
        if tag=='equal': continue
        for j in range(j1,j2):
            l=loc[j]
            if l.startswith('import '): cnt['import']+=1; continue
            if l.startswith('set_option ') and j<40: cnt['setopt']+=1; continue
            if l.replace('_aflt','') in up[max(0,i1-2):i2+2]: cnt['rename']+=1; continue
            if any('[port]' in loc[k] for k in range(max(0,j-3),min(len(loc),j+4))): cnt['port']+=1; continue
            if l.strip()=='' : continue
            cnt['other']+=1; print('OTHER',rel,j+1,l[:150])
        if tag in('delete','replace') and j2==j1:
            for i in range(i1,i2):
                if up[i].startswith('import '): cnt['import']+=1
                else: cnt['other']+=1; print('DELETED',rel,i+1,up[i][:150])
print(cnt)
