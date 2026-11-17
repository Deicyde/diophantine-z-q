import json,sys
from measure import measure
from orders import BASE
def drop(groups1, drop_pu=(2,3,4), drop_pv=()):
    s=BASE
    old="const tests=[...PU.map((p,i)=>({value:p.point.g,order:i===0?45:i===1?12:1})),...PV.map(p=>({value:fconj(p.f),order:1}))];"
    assert old in s
    new="const tests=[...PU.map((p,i)=>({value:p.point.g,order:i===0?45:i===1?12:1,i})).filter(t=>!%s.includes(t.i)),...PV.map((p,i)=>({value:fconj(p.f),order:1,i})).filter(t=>!%s.includes(t.i))];"%(json.dumps(list(drop_pu)),json.dumps(list(drop_pv)))
    s=s.replace(old,new)
    s=s.replace("sizes=m===1?[4,4]:[3,3]","sizes=m===1?%s:[3,3]"%json.dumps(groups1))
    return s
if 0:
 for name,args in {'drop3U_32':([3,2],),'drop3U_5':([5],),'drop3U_23':([2,3],)}.items():
    print(name, measure(name, drop(*args)),flush=True)
if __name__=='__main__':
 for name,args in {'drop1U':([3,4],(4,)),'drop2U':([2,4],(3,4))}.items():
    print(name, measure(name, drop(*args)),flush=True)
