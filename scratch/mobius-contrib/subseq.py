"""Check: the nonblank body lines of each Contrib/Mobius module (after its header docstring) form
an in-order subsequence of the nonblank lines of scratch/image-plane/ImagePlaneFinal.lean."""
src = [l for l in open('scratch/image-plane/ImagePlaneFinal.lean').read().split('\n') if l.strip()]
for mod in ['InfraDim', 'Glue', 'CurveFacts', 'ImagePlane']:
    ls = open(f'ZInQKernel/Contrib/Mobius/{mod}.lean').read().split('\n')
    body = [l for l in ls[ls.index('-/') + 1:] if l.strip()]
    j, ok = 0, True
    for l in body:
        while j < len(src) and src[j] != l: j += 1
        if j == len(src): ok = False; print(mod, 'NOT FOUND:', l[:80]); break
        j += 1
    print(mod, 'subsequence of source:', ok, len(body), 'nonblank lines')
