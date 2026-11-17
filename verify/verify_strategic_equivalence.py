"""Exact checks on a family equivalent in unilateral deviation gains."""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

signs=(-1,1)
policies=list(product(signs,repeat=3))
discount=Q(9,10)
c=Q(1,10)

def rewards(x,z,f,g,transfer,delay):
    return (c*x*z+(1-delay)*transfer*z, -c*x*z,
            c*f*g+delay*transfer*z/discount, f*(z-c*g))

def returns(a,b,transfer,delay):
    x,z=a[0],b[0]
    state=1 if z==1 else 2
    r,s,u,v=rewards(x,z,a[state],b[state],transfer,delay)
    return r+discount*u,s+discount*v

def field(transfer,delay):
    total=[[Q(0) for _ in range(3)] for _ in range(2)]
    for x,z,f,g in product(signs,repeat=4):
        r,s,u,v=rewards(x,z,f,g,transfer,delay)
        terminal_mean=delay*transfer*z/discount
        past=(r+discount*terminal_mean,s)
        current=(u-terminal_mean,v)
        state=1 if z==1 else 2
        for i,(first,last) in enumerate(((x,f),(z,g))):
            total[i][0]+=past[i]*first/32
            total[i][state]+=(discount*current[i]+discount**3*past[i]*current[1-i])*last/32
    return total

results=[]
for t in map(Q,[-2,-1,0,1,2]):
    for delay in (0,1):
        for a,b in product(policies,repeat=2):
            base=returns(a,b,0,0)
            alt=returns(a,b,t,delay)
            assert alt==(base[0]+t*b[0],base[1])
        actual=field(t,delay)
        v=t*discount**3/4
        assert actual==[[0,v,v],[0,0,0]]
        results.append(dict(transfer=str(t),delay=delay,field=[[str(x) for x in row] for row in actual]))
out=Path(__file__).with_name("strategic_equivalence.json")
out.write_text(json.dumps(results,indent=2))
print("Verified 640 pure Markov profiles/settings and 10 exact fields.")
