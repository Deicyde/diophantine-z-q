'use strict';
// Transformed residual IR has historical source gates, not current circuit gates.
// Check the final SOS, compaction and specialization using the exported verifier
// routines. Source gates are checked separately in independent-gate-check.json.
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const C=require('./tools/checker.cjs');
const root=__dirname,dir=path.join(root,'final/polynomial');
const read=n=>JSON.parse(fs.readFileSync(path.join(dir,n),'utf8'));
const ir=C.readIR(read('compiled-ir.json'));
const map=C.checkCoordinateMap(ir,read('coordinate-map.json'));
const p=C.checkQuartic(ir,read('polynomial.json'),map);
const statistics=C.coefficientStats(p);
const sha=n=>crypto.createHash('sha256').update(fs.readFileSync(path.join(dir,n))).digest('hex');
const report={status:'passed_final_SOS_and_fixed_parameter_checks',scope:'Transformed-system full sum of squares, exact coordinate compaction, specialized support, integer coefficients, primitive content and maximum coefficient. Source gates and arithmetic are not newly certified here.',statistics,sha256:{compiledIR:sha('compiled-ir.json'),polynomial:sha('polynomial.json'),coordinateMap:sha('coordinate-map.json')}};
fs.writeFileSync(path.join(root,'independent-final-symbolic-check.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({status:report.status,degree:statistics.degree,monomials:statistics.monomials,content:statistics.primitiveContent,maximum:statistics.maximumAbsoluteCoefficient}));
