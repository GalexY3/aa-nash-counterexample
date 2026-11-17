"""Checks the discounted state aggregation of the exact AA-8 term."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import numpy as np

def two_stage(eta):
    field = {s:F(0) for s in (-1,1)}
    weight = {s:F(0) for s in field}
    for x,z,s,f,g in product((-1,1), repeat=5):
        prob=(1+eta*s*z)/32
        past=z*(1+F(1,10)*x)
        current=f*(s-F(1,10)*g)
        field[s]+=prob*past*current*f/2
        weight[s]+=prob*past
    assert all(v==eta/4 for v in field.values())
    assert all(weight[s]==s*eta/2 for s in weight)
    return [str(v) for v in field.values()]

def compare(seed):
    rng=np.random.default_rng(seed)
    n=4
    def norm(x):
        return x/x.sum(axis=-1, keepdims=True)
    pi=norm(rng.random((n,2)))
    opp=norm(rng.random((n,2)))
    joint=pi[:,:,None]*opp[:,None,:]
    transitions=norm(rng.random((n,2,2,n)))
    kernel=np.einsum('sab,sabj->sj',joint,transitions)
    g=.8
    rewards=rng.normal(size=(2,n,2,2))
    values=np.linalg.solve(np.eye(n)-g*kernel,np.einsum('sab,isab->si',joint,rewards))
    adv=rewards+g*np.einsum('sabj,ji->isab',transitions,values)-values.T[:,:,None,None]
    score=np.array([0,1])[None,:]-pi[:,1,None]
    covariance=np.einsum('sab,sab,sa->s',joint,adv[1],score)
    source=np.einsum('sab,sab,sabj->sj',joint,adv[0],transitions)
    initial=np.ones(n)/n
    visits=np.linalg.solve((np.eye(n)-g*kernel).T,initial)
    weighted=np.linalg.solve((np.eye(n)-g*g*kernel).T,g*g*(visits@source))
    predicted=g*weighted*covariance
    # Forward unroll, accumulating raw joint-action contributions on every transition.
    state=initial
    trace=np.zeros(n)
    actual=np.zeros(n)
    for t in range(180):
        actual+=g**(t+1)*trace*covariance
        trace=g*np.einsum('sabj,sab,sab->j',transitions,joint,
                          trace[:,None,None]+state[:,None,None]*adv[0])
        state=state@kernel
    err=float(np.max(np.abs(actual-predicted)))
    assert err<1e-11
    return err

if __name__=='__main__':
    cases={str(v):two_stage(v) for v in map(F,('-1','-1/2','0','1/2','1'))}
    result=dict(scaled_two_stage_field=cases,max_numeric_error=max(map(compare,range(100))))
    print(result)
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2))
