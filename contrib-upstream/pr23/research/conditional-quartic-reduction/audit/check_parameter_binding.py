"""Adversarial tests of the actual Python/JavaScript fixed-parameter readers.

This test invokes both implementations and compares their outputs against
separately calculated expectations. It does not certify global arithmetic.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys


def main():
    sys.set_int_max_str_digits(0)
    ap = argparse.ArgumentParser()
    ap.add_argument('tools', type=Path)
    ap.add_argument('--report', type=Path)
    args = ap.parse_args()
    folder = args.tools.resolve()
    spec = importlib.util.spec_from_file_location('tested_compiler', folder/'compile_ir.py')
    compiler = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(compiler)
    probes = [3071, 3072, 4096, 8192, 1048576]
    declarations = [('3^3072', 3072), ('3^4096', 4096), ('3^7168', 7168),
                    ('3^(2^13)', 8192), ('3^(2^26)', 2**26)]
    malformed = ['3^0', '3^-1', '3^03072', '3^1073741825', '3^(3072)',
                 '3^3.072e3', '3^(2^31)', '3^(2^-1)', '2^3072', '3^3072+1']
    javascript = r'''
const c=require(process.argv[2]),value=process.argv[3],probes=JSON.parse(process.argv[4]);
const bad=JSON.parse(process.argv[5]);
const ir=v=>({fixedParameter:{name:'S',value:v,coordinate:false},
coordinates:[{id:0,name:'input',kind:'input'}],residuals:[]});
c.readIR(ir(value));
const dominance=[];
for(const exponent of probes){
 let accepted=false;
 try{c.scalarSign(new Map([[1,new c.Q(1n)],[0,new c.Q(-(1n<<BigInt(exponent)))]]));accepted=true;}
 catch(e){if(!/dominance bound/.test(e.message))throw e;}
 dominance.push(accepted);
}
const p=new c.Poly().put([0,0,0,0],1,new c.Q(1n))
 .put([0,0,0,0],0,new c.Q(-9n)).put([],0,new c.Q(19n));
const content=c.coefficientStats(p).primitiveContent;
const invalid=[];
for(const declaration of bad){
 let rejected=false;
 try{c.readIR(ir(declaration));}
 catch(e){if(!/unsupported fixed S declaration/.test(e.message))throw e;rejected=true;}
 invalid.push(rejected);
}
let mixedRejected=false;
try{c.readIR(ir(value==='3^4096'?'3^(2^12)':'3^4096'));}
catch(e){if(!/parameter changes/.test(e.message))throw e;mixedRejected=true;}
process.stdout.write(JSON.stringify({value,dominanceAccepted:dominance,content,mixedRejected,invalid}));
'''
    for declaration in malformed:
        try:
            compiler.fixed_parameter({'fixedParameter': {'name': 'S', 'value': declaration, 'coordinate': False}})
        except ValueError as error:
            assert 'Unsupported' in str(error)
        else:
            raise AssertionError(('malformed declaration accepted', declaration))
    cases = []
    for value, exponent in declarations:
        meta = {'fixedParameter': {'name': 'S', 'value': value, 'coordinate': False}}
        assert compiler.fixed_parameter(meta)[2] == exponent
        accepted = []
        for n in probes:
            polynomial = {(1, ()): Fraction(1), (0, ()): Fraction(-(1 << n))}
            passed = True
            try:
                compiler.specialization_analysis(polynomial, meta)
            except ValueError as error:
                assert 'exceeds available' in str(error)
                passed = False
            accepted.append(passed)
        assert accepted == [n < exponent for n in probes]
        result = subprocess.run(['node', '-', str(folder/'checker.cjs'), value,
                                 json.dumps(probes), json.dumps(malformed)],
                                input=javascript, text=True, capture_output=True, check=True)
        js = json.loads(result.stdout)
        assert js['dominanceAccepted'] == accepted
        assert js['content'] == ('19' if pow(3, exponent, 19) == 9 else '1')
        assert js['mixedRejected'] is True and all(js['invalid'])
        cases.append({'value': value, 'exactExponent': exponent,
                      'pythonDominanceAccepted': accepted, **js})
    report = {'status': 'PASS', 'probeConstantBinaryExponents': probes,
              'malformedDeclarationsRejected': malformed, 'cases': cases,
              'compilerSha256': hashlib.sha256((folder/'compile_ir.py').read_bytes()).hexdigest(),
              'javascriptCheckerSha256': hashlib.sha256((folder/'checker.cjs').read_bytes()).hexdigest(),
              'scope': 'The declared exponent controls both sign certificates and exact modular content; malformed and mixed declarations are rejected. No arithmetic characterization is asserted.'}
    output = json.dumps(report, indent=2)+'\n'
    if args.report:
        args.report.write_text(output)
    print(output)


if __name__ == '__main__':
    main()
