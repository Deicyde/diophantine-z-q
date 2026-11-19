"""Parse the actual Version21 TeX equations and all normalization entries."""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import lcm
import json
import re
import verify229 as v

HERE=Path(__file__).resolve().parent
TEX=HERE.parents[2]/'manuscripts/quartic_v21.tex'

def parse_polynomial(text,variable):
    result={}
    compact=re.sub(r'\s+','',text.replace('\\\\','').replace('&{}',''))
    v.require(compact and not any(c in compact for c in '&%='),'unexpected TeX polynomial syntax')
    position=0
    while position<len(compact):
        match=re.match(r'([+-]?)(\d*)(C(?:\^\{[1-9][0-9]*\})?)?',compact[position:])
        v.require(match is not None,'term prefix')
        sign,digits,param=match.groups();start=position;position+=match.end()
        v.require(start==0 or sign in ['+','-'],'missing term sign')
        v.require(not digits or re.fullmatch(r'[1-9][0-9]*',digits),'coefficient format')
        coefficient=int(digits or 1)*(-1 if sign=='-' else 1)
        exponent=0 if not param else 1 if param=='C' else int(param[3:-1])
        monomial=[]
        while True:
            item=re.match(re.escape(variable)+r'_\{([1-9][0-9]*)\}(?:\^\{([1-9][0-9]*)\})?',compact[position:])
            if item is None:break
            i,n=int(item[1]),int(item[2] or 1)
            v.require(1<=i<=229 and n<=2,'coordinate or power outside quadratic domain')
            monomial.extend([i]*n);position+=item.end()
        v.require(position>start and (digits or param or monomial),'empty term')
        v.require(monomial==sorted(monomial) and len(monomial)<=2,'monomial order or degree')
        v.require(position==len(compact) or compact[position] in '+-','unparsed TeX tail')
        key=exponent,tuple(monomial)
        v.require(key not in result,'duplicate TeX monomial')
        result[key]=coefficient
    return result

def read_rows(text,kind,variable,symbol):
    pattern=r'% V21-'+kind+r'-ROW-START ([0-9]+)\s*\\begin\{align\*\}\s*'+symbol+r'_\{([0-9]+)\}&=(.*?)\\end\{align\*\}\s*% V21-'+kind+r'-ROW-END ([0-9]+)'
    matches=list(re.finditer(pattern,text,re.S))
    v.require(len(matches)==207,'missing or extra printed '+kind+' row')
    v.require(text.count('% V21-'+kind+'-ROW-START ')==207 and text.count('% V21-'+kind+'-ROW-END ')==207,'unparsed row markers')
    output=[]
    for i,m in enumerate(matches,1):
        v.require([int(m[j]) for j in [1,2,4]]==[i]*3,'printed row numbering')
        tags=re.findall(r'\\tag\{V21\.'+symbol+r'([0-9]+)\}',m[3]);v.require(tags==[str(i)],'row tag')
        body=re.sub(r'\\tag\{V21\.'+symbol+r'[0-9]+\}','',m[3])
        output.append(parse_polynomial(body,variable))
    return output

def read_exponents(text,kind,count):
    pattern=r'% V21-'+kind+r'-EXPONENTS ([0-9]+) ([0-9]+)\s*\$([0-9]+)--([0-9]+)\$\s*&\s*\$([-0-9,]+)\$\\\\'
    matches=list(re.finditer(pattern,text));out=[]
    v.require(len(matches)==text.count('% V21-'+kind+'-EXPONENTS '),'unparsed exponent block')
    for m in matches:
        a,b,c,d=map(int,m.group(1,2,3,4));block=list(map(int,m[5].split(',')))
        v.require((a,b)==(c,d) and a==len(out)+1 and b==a+len(block)-1,'exponent index mismatch')
        out+=block
    v.require(len(out)==count,'incomplete exponent inventory')
    return out

def check_copy_maps(text):
    expected={'COORDINATES':list(zip([7,8,9,10,*range(86,100),*range(134,150)],range(196,230))),
              'ROWS':list(zip([*range(34,47),*range(83,101)],range(176,207)))}
    for kind,pairs in expected.items():
        matches=re.findall(r'% V21-COPY-'+kind+r'-START(.*?)% V21-COPY-'+kind+r'-END',text,re.S)
        v.require(len(matches)==1,'missing or duplicate copy map')
        values=list(map(int,re.findall(r'\$([0-9]+)\$',matches[0])))
        v.require(len(values)==2*len(pairs),'copy map length')
        v.require(list(zip(values[::2],values[1::2]))==pairs,'printed copy map differs')


def read_field_pair(text):
    text=re.sub(r'\s+','',text)
    power=0
    if text.startswith('C(') and text.endswith(')'):
        power=1;text=text[2:-1]
    m=re.fullmatch(r'x_\{([0-9]+)\}([+-])x_\{([0-9]+)\}\\rho',text)
    v.require(m is not None,'unparsed physical field expression')
    real,imag=int(m[1]),int(m[3])
    v.require(1<=real<=229 and 1<=imag<=229,'physical coordinate range')
    return v.x(real,power),v.scale(v.x(imag,power),1 if m[2]=='+' else -1)


def check_physical_table(text,source):
    sections=re.findall(r'The stored field expressions are(.*?)Their physical meanings are',text,re.S)
    v.require(len(sections)==1,'missing or duplicated physical table')
    section=sections[0]
    arrays=re.findall(r'\\begin\{array\}\{c\|ccc\}(.*?)\\end\{array\}',section,re.S)
    v.require(len(arrays)==1,'physical array shape')
    body=re.sub(r'\s+','',arrays[0]);prefix=r'i&f_i&g_i&s_i\\\hline'
    v.require(body.startswith(prefix),'physical table columns')
    rows=body[len(prefix):].split('\\\\');v.require(len(rows)==3,'physical table row count')
    fields={}
    for expected,row in zip([1,3,4],rows):
        parts=row.split('&');v.require(len(parts)==4 and parts[0]==str(expected),'physical table indices')
        fields[expected]=tuple(read_field_pair(item) for item in parts[1:])
    matches=re.findall(r'\\qquad\s+p=(.*?)\.',section,re.S)
    v.require(len(matches)==1,'physical scalar field missing')
    scalar=read_field_pair(matches[0]);v.require(scalar==v.pair(192),'physical scalar components')
    Q=(v.x(77),{});D=(v.const(11),v.const(-6));total=({},{})
    for i,start,k,l in [(1,111,154,158),(3,127,164,168),(4,143,174,178)]:
        f,g,s=fields[i]
        secant=v.field_add(v.field_mul(v.field_add(g,tuple(v.scale(c,-1) for c in f)),s),v.field_mul((v.x(77,1),{}),v.field_add(v.pair(k),v.pair(l))))
        v.require(source[start-1:start+1]==list(secant),'printed physical secant mismatch')
        total=v.field_add(total,v.field_mul(s,s),v.field_mul(v.field_mul(Q,D),v.field_add(f,g)))
    total=v.field_add(total,v.field_mul(Q,scalar))
    expected0=v.add(total[0],v.scale(v.mul(v.x(77),v.add(v.x(2),v.scale(v.x(86),-1))),2),v.scale(v.power(v.x(77),2),26))
    expected1=v.add(total[1],v.scale(v.mul(v.x(77),v.add(v.x(2),v.scale(v.x(86),-2),v.x(200))),2),v.scale(v.power(v.x(77),2),-8))
    v.require(source[174]==expected0 and source[206]==expected1,'printed aggregate field components mismatch')
    recovery=re.findall(r'\\label\{v21:point-recovery\}(.*?)\\end\{equation\}',text,re.S)
    v.require(len(recovery)==1,'missing point recovery')
    v.require(re.sub(r'\s+','',recovery[0])==r'x(Q_i)=s_i^2/q^2+D(f_i+g_i)/q\quad(i=1,3,4),\qquadx(Q_2)=p/q.','physical denominator or identity differs')



def check_contact_tables(text):
    sections=re.findall(r'\\label\{v21:contacts\}(.*?)\\section\{Arithmetic of the fixed parameter\}',text,re.S)
    v.require(len(sections)==1,'missing or duplicated contact section')
    section=sections[0]
    theta_match=re.findall(r'\\Theta=\\\{([^}]+)\\\}',section)
    v.require(len(theta_match)==1,'contact set declaration')
    theta=[Fraction(x.strip()) for x in theta_match[0].split(',')]
    v.require(theta==[Fraction(0),Fraction(-1,2),Fraction(-1),Fraction(1,2399),Fraction(-32,407)],'contact set differs')
    alpha=[(22*x-3)**2 for x in theta];es=[Fraction(1)]
    for a in alpha:es=[es[0]]+[es[j]+a*es[j-1] for j in range(1,len(es))]+[a*es[-1]]
    L=lcm(*(a.denominator for a in es))
    printedL=re.findall(r'With \$L=([0-9]+)\$',section);v.require(printedL==[str(L)],'contact denominator')
    arrays=re.findall(r'\\begin\{array\}\{c\|r\}(.*?)\\end\{array\}',section,re.S)
    v.require(len(arrays)==1,'contact coefficient table')
    body=re.sub(r'\s+','',arrays[0]);prefix=r'k&Le_k\\\hline';v.require(body.startswith(prefix),'contact coefficient header')
    rows=body[len(prefix):].rstrip('.').split('\\\\')
    v.require(len(rows)==5,'contact coefficient row count')
    for k,row in enumerate(rows,1):
        pieces=row.split('&');v.require(pieces==[str(k),str(int(L*es[k]))],'printed elementary coefficient differs')
    # This is the complete stored substitution map, not the source generator.
    arrays=re.findall(r'\\begin\{array\}\{c\|ccccc\}(.*?)\\end\{array\}',section,re.S)
    v.require(len(arrays)==1,'contact stored map missing')
    body=re.sub(r'\s+','',arrays[0]);prefix=r'j&t_j&r_j&s_j&v_j&w_j\\\hline';v.require(body.startswith(prefix),'contact map columns')
    rows=body[len(prefix):].rstrip('.').split('\\\\')
    expected=[r'0&x_2/q&x_{74}/q&x_{75}/q&Cx_{76}/(Lq)&1/q',
              r'1&x_{86}/q&x_{87}/q&x_{88}/q&x_{89}/(Lq)&x_{91}/q',
              r'2&x_{200}/q&x_{201}/q&x_{202}/q&x_{203}/(Lq)&x_{205}/q']
    v.require(rows==expected,'printed stored contact substitution differs')


def check(text):
    check_copy_maps(text)
    check_contact_tables(text)
    source=read_rows(text,'SOURCE','x','Q')
    normalized=read_rows(text,'NORMALIZED','y','R')
    check_physical_table(text,source)
    transform=v.load('transformation.json')
    v.require(read_exponents(text,'COORDINATE',229)==transform['coordinate_powers'],'printed coordinate exponents differ')
    v.require(read_exponents(text,'EQUATION',207)==transform['row_powers'],'printed row exponents differ')
    v.require(source==v.rows(v.load('source/quadratic229-v62.json'),229,207,True),'printed source rows differ')
    v.require(normalized==v.rows(v.load('quadratic.json'),229,207,False),'printed normalized rows differ')
    v.require(v.specialize(source,transform)==normalized,'printed diagonal substitution differs')
    return {'source_rows':207,'normalized_rows':207,'coordinate_exponents':229,'row_exponents':207,'physical_field_expressions':10,'contact_elementary_coefficients':5,'contact_substitution_entries':15}

def main():
    v.authenticate();text=TEX.read_text(encoding='utf-8');result=check(text)
    # Mutate displayed mathematics, not the generator or metadata, and require refusal.
    bad=[text.replace('Q_{1}&=','Q_{1}&=2+',1),
         text.replace('% V21-SOURCE-ROW-START 207','% V21-SOURCE-ROW-START 208',1),
         text.replace('R_{207}&=','R_{207}&=1+',1),
         text.replace('$1--16$ & $0,','$1--16$ & $1,',1),
         text.replace('$7$ & $196$','$7$ & $197$',1),
         text.replace(r'1&x_{152}+x_{153}\rho&',r'1&C(x_{152}+x_{153}\rho)&',1),
         text.replace(r'x_{160}+x_{161}\rho\\',r'x_{160}-x_{161}\rho\\',1),
         text.replace(r'p=x_{192}+x_{193}\rho.',r'p=x_{192}-x_{193}\rho.',1),
         text.replace('1&6786192246520','1&6786192246521',1),
         text.replace('Cx_{76}/(Lq)','x_{76}/(Lq)',1)]
    for i,probe in enumerate(bad,1):
        v.require(probe!=text,'inactive negative control')
        try:check(probe)
        except ValueError:pass
        else:raise ValueError('accepted corrupted displayed table '+str(i))
    result['rejected_corruptions']=len(bad)
    result['scope']='Actual printed equations, exponents, copy maps and physical-coordinate expressions; arithmetic proof acceptance is separate.'
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
