import re, json, sys
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
kinds = {'theorem':'Theorem','proposition':'Proposition','lemma':'Lemma','corollary':'Corollary','definition':'Definition','remark':'Remark'}
sec = 0; appendix = False; app = 0; ctr = 0; items = []; cur = None; sec_title = ''
for i, line in enumerate(src, 1):
    if line.startswith('\\appendix'):
        appendix = True; continue
    m = re.match(r'\\section\{(.*)', line)
    if m:
        if appendix: app += 1
        else: sec += 1
        ctr = 0
        sec_title = re.sub(r'\}\\label.*|\}\s*$', '', m.group(1))
        continue
    m = re.match(r'\\begin\{(theorem|proposition|lemma|corollary|definition|remark)\}(\[(.*?)\])?(.*)', line)
    if m:
        ctr += 1
        secno = chr(64 + app) if appendix else str(sec)
        lab = re.search(r'\\label\{([^}]*)\}', line)
        title = m.group(3)
        if title is None:
            t = re.match(r'\\begin\{\w+\}\[(.*)', line)
            title = t.group(1) if t else None
        cur = {'kind': m.group(1), 'number': f'{secno}.{ctr}', 'name': f'{kinds[m.group(1)]} {secno}.{ctr}',
               'title': title, 'label': lab.group(1) if lab else None, 'start': i, 'section': sec_title}
        continue
    if cur and cur['label'] is None:
        lab = re.search(r'\\label\{([^}]*)\}', line)
        if lab and i <= cur['start'] + 3: cur['label'] = lab.group(1)
    m = re.match(r'\\end\{(theorem|proposition|lemma|corollary|definition|remark)\}', line)
    if m and cur:
        cur['end'] = i; items.append(cur); cur = None
json.dump(items, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(len(items), 'items;', sum(1 for x in items if x['label']), 'labelled')
for x in items: print(x['name'].ljust(18), str(x['start']).rjust(6), (x['label'] or '-').ljust(26), (x['title'] or '')[:60])
