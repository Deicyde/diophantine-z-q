"""Check that the copied definitions in T4.lean occur verbatim in the branch files."""
import subprocess, re, sys
t4 = open('scratch/smooth-regular/T4.lean').read()
def show(ref, path):
    return subprocess.run(['git', 'show', f'{ref}:{path}'], capture_output=True, text=True).stdout
srcs = {
 'hcm': show('origin/wip/hcm-g1', 'ZInQKernel/Contrib/OneProof/ShimuraMainCMPrinted.lean'),
 'mcp': show('origin/wip/cm-primitive', 'ZInQKernel/Contrib/OneProof/MainCMPolar.lean'),
 'qmr': show('origin/wip/cm-primitive', 'ZInQKernel/Contrib/OneProof/QMRecPrinted.lean'),
}
def block(text, head):
    i = text.index(head)
    j = text.find('\n\n', i)
    return text[i:j]
checks = [('hcm', 'def lat1'), ('hcm', 'def WeierstrassAbVar :'), ('qmr', 'def cmVec'), ('qmr', 'def cmLat'),
          ('mcp', 'def IsOLattice'), ('mcp', 'def IsRiemannDatum'), ('mcp', 'def CMAbVarExists :')]
ok = True
for k, h in checks:
    b = block(srcs[k], h)
    r = b in t4
    ok &= r
    print(('VERBATIM ' if r else 'DIFFERS  ') + h)
sys.exit(0 if ok else 1)
