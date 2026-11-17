"""C07: run the authors' unmodified AA helper bodies (loaded and hash-checked by the V205 harness)
on the lambda family of the V205 game. Only the game module differs (c07_lambda_game, lam=1 is V205)."""
import sys, json, itertools, hashlib, time
from pathlib import Path
from types import SimpleNamespace
import numpy as np
import torch
H = Path(__file__).resolve().parent
sys.path.insert(0, str(H))
from v205_author_helpers import helpers, Config, EXPECTED
from c07_lambda_game import trajectories, state_values, sigmoid, best_responses_p

def lambda_probe(lam,coupling,loss_mode,proximal,normalize,lmbda,dtype_name):
    namespace,digests=helpers()
    dtype=torch.float64 if dtype_name=='float64' else torch.float32
    torch.set_default_dtype(dtype)
    gamma=.9;beta=.3;alpha=.1
    theta=torch.zeros((2,3),dtype=dtype,requires_grad=True)
    paths=list(trajectories(np.full((2,3),.5),gamma,coupling=coupling,lam=lam))
    rewards=[];actions=[];states=[];players=[]
    for path in paths:
        for i in range(2):
            rewards.append([*path['rewards'][i],0.])
            actions.append([*path['actions'][i],0])
            states.append(path['states']);players.append(i)
    rewards=torch.tensor(rewards,dtype=dtype);actions=torch.tensor(actions,dtype=torch.long)
    actor=SimpleNamespace(batch_size=16,num_agents=2,sum_rewards=False,
        train_cfg=Config(num_on_policy_agents=2,actor_loss_mode=loss_mode,gamma=gamma,lmbda=lmbda,
            proximal=proximal,clip_range=.2,center_rewards=False,normalize_advantages=normalize,aa_weight=beta),
        main_cfg=Config(use_full_maps=False,run_single_agent=False),
        agents=[SimpleNamespace(train=lambda:None),SimpleNamespace(train=lambda:None)])
    actor.aa_terms=lambda a:namespace['aa_terms'](actor,a)
    actor.aa_loss=lambda a,l,o:namespace['aa_loss'](actor,a,l,o)
    def get_values(*args):
        p=sigmoid(theta.detach().numpy());v=state_values(p,gamma,coupling,lam)
        out=torch.tensor([[v[i,h[0]],v[i,h[1]],0.] for i,h in zip(players,states)],dtype=dtype)
        return out,out
    def get_logs(*args):
        p=torch.sigmoid(theta);logs=[];entropy=[]
        for row,(i,hs) in enumerate(zip(players,states)):
            xx=[];ee=[]
            for t,h in enumerate(hs):
                pp=p[i,h];a=actions[row,t]
                xx.append(torch.log(pp) if a else torch.log(1-pp))
                ee.append(-pp*torch.log(pp)-(1-pp)*torch.log(1-pp))
            logs.append(torch.stack([*xx,theta.new_zeros(())]))
            entropy.append(torch.stack([*ee,theta.new_zeros(())]))
        return torch.stack(logs),torch.stack(entropy)
    actor.get_trajectory_values=get_values;actor.get_trajectory_log_ps=get_logs
    fixture=SimpleNamespace(data=dict(obs=torch.zeros((32,3,1),dtype=dtype),rewards=rewards,actions=actions))
    loss=namespace['actor_losses'](actor,fixture,None)
    gradient=torch.autograd.grad(-loss['losses'].sum(),theta)[0].detach().numpy().astype(float)
    after=best_responses_p(sigmoid(alpha*gradient),gamma,coupling,lam)
    torch.set_default_dtype(torch.float64)
    return dict(lam=lam,coupling=coupling,loss_mode=loss_mode,proximal=proximal,normalize_advantages=normalize,
        lmbda=lmbda,dtype=dtype_name,gradient=gradient.tolist(),after_step=after,
        field_changes_player1_terminal=bool(np.min(gradient[0,1:])>1e-6),
        post_step_exploitable=bool(after['max_gain']>1e-8),
        source_bodies_unmodified=True,source_functions=digests,
        upstream_commit='2065e43c0c36694965cf4476dc692512e3892dcc',
        source_file_sha256=EXPECTED,fixture='All 16 equiprobable action paths; independent tabular policies; exact critic')


def main():
    rows = []; t0 = time.time()
    for lam, loss_mode, proximal, normalize, lmbda, dt in itertools.product(
            [-1., 0., .5, 1., 2.], ['integrated_aa', 'separated_aa'], [False, True], [False, True], [0., .95, 1.], ['float32', 'float64']):
        r = lambda_probe(lam, .1, loss_mode, proximal, normalize, lmbda, dt)
        g = np.array(r['gradient'])
        rows.append(dict(lam=lam, loss_mode=loss_mode, proximal=proximal, normalize=normalize, lmbda=lmbda, dtype=dt,
                         terminal=g[0, 1:].tolist(), player2=g[1].tolist(), max_gain=r['after_step']['max_gain']))
    pre = [x for x in rows if x['lmbda'] == 0.]
    tol = lambda x: 1e-12 if x['dtype'] == 'float64' else 1e-6
    P1 = [x for x in pre if x['lam'] == 0.]
    P1_ok = all(max(abs(v) for v in x['terminal']) <= tol(x) and x['max_gain'] <= 1e-8 for x in P1)
    P2 = [x for x in pre if x['lam'] != 0.]
    P2_ok = all(min(abs(v) for v in x['terminal']) > 1e-6 and all(np.sign(v) == np.sign(x['lam']) for v in x['terminal'])
                and x['max_gain'] > 1e-8 for x in P2)
    fails = [x for x in P1 if not (max(abs(v) for v in x['terminal']) <= tol(x) and x['max_gain'] <= 1e-8)] +             [x for x in P2 if not (min(abs(v) for v in x['terminal']) > 1e-6 and all(np.sign(v) == np.sign(x['lam']) for v in x['terminal']) and x['max_gain'] > 1e-8)]
    ns, digests = helpers()
    out = dict(status='PREREGISTERED_C07', P1_lambda0_no_movement=P1_ok, P2_lambda_nonzero_moves=P2_ok,
               n_configs=len(rows), n_preregistered=len(pre), failures=fails, rows=rows,
               upstream_commit='2065e43c0c36694965cf4476dc692512e3892dcc', upstream_source_sha256=EXPECTED,
               upstream_function_segments=digests, seconds=time.time() - t0,
               scope='Unmodified upstream loss/advantage helper bodies on a tabular exact-critic fixture; not the authors networks or benchmarks')
    pass
    (H / 'author_code_lambda_probe.json').write_text(json.dumps(out, indent=1), encoding='utf-8', newline=chr(10))
    print(json.dumps({k: v for k, v in out.items() if k not in ('rows', 'upstream_function_segments')}, indent=1)[:2500])
    for lam in [-1., 0., .5, 1., 2.]:
        sel = [x for x in pre if x['lam'] == lam and x['dtype'] == 'float64' and not x['normalize']]
        print('lam', lam, 'terminal grads (lmbda0,float64,no-norm):', sorted({tuple(round(v, 8) for v in x['terminal']) for x in sel}), 'max_gain', max(x['max_gain'] for x in sel))


if __name__ == '__main__':
    main()
