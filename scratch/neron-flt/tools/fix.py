"""Apply mechanical Mathlib-v4.35 renames to ported files; each changed line gets a `-- [port]` comment above it.
(adapted from flt-cqj2's fix.py) usage: python3 -I fix.py FILE..."""
import sys, re
M = 'Mathlib v4.35: the monoidal structure on presheaves of modules over CommRingCat moved to `PresheafOfModulesOfCommRing`'
RULES = [
  (r'Ideal\.isMaximal_of_isIntegral_of_isMaximal_comap \(R := ', 'Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ',
   'Mathlib v4.35: the algebra form of `isMaximal_of_isIntegral_of_isMaximal_comap` is `..._under`'),
  (r'PresheafOfModules\.Monoidal\.tensorHom_app', 'PresheafOfModulesOfCommRing.tensorHom_app', M),
  (r'PresheafOfModules\.Monoidal\.', 'PresheafOfModulesOfCommRing.Monoidal.', M),
  (r'PresheafOfModules\.(tensorHom_app|whiskerRight_app|whiskerLeft_app|leftUnitor_hom_app|leftUnitor_inv_app|rightUnitor_hom_app|rightUnitor_inv_app|associator_hom_app|associator_inv_app|tensorObj_obj|braiding_hom_app|braiding_inv_app)\b',
   r'PresheafOfModulesOfCommRing.\1', M),
  (r'PresheafOfModules\.DifferentialsConstruction\.', 'PresheafOfModulesOfCommRing.DifferentialsConstruction.',
   'Mathlib v4.35: relative differentials of presheaves of CommRingCat moved to `PresheafOfModulesOfCommRing`'),
  (r'ULift\.ext _ _ ', 'ULift.ext ', 'Mathlib v4.35: `ULift.ext` takes its two points implicitly'),
  (r'Ideal\.bot_prime\b', 'Ideal.isPrime_bot', 'Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`'),
  (r'Ideal\.isMaximal_of_isIntegral_of_isMaximal_comap _ ', 'Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _ ',
   'Mathlib v4.35: the algebra form of `isMaximal_of_isIntegral_of_isMaximal_comap` is `..._under`'),
]
for p in sys.argv[1:]:
    lines = open(p, encoding='utf-8').read().split('\n'); out = []; n = 0
    for l in lines:
        new = l; why = []
        if l.lstrip().startswith('--'): out.append(l); continue
        for pat, rep, msg in RULES:
            if re.search(pat, new): new = re.sub(pat, rep, new); why.append(msg)
        if new != l:
            ind = re.match(r'\s*', l).group(0); out.append(ind + '-- [port] ' + '; '.join(sorted(set(why)))); n += 1
        out.append(new)
    if n:
        open(p, 'w', encoding='utf-8').write('\n'.join(out)); print(p.split('/')[-1], n)
