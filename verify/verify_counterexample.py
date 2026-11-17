"""Exact enumeration reproducing every number in the preprint (no dependencies beyond NumPy).

Checks: values and joint advantages at the uniform profile; the Eq. 8 field
(0, beta*gamma^3/4, beta*gamma^3/4) and 0; the post-step deviation gain
gamma*(1+c)*tanh(alpha*beta*gamma^3/8); exhaustive deterministic deviations at the uniform
profile; the repaired (past-weight marginalized) alignment term at the uniform profile and on
random profiles. Run: python verify_counterexample.py
"""
import itertools
import numpy as np

B = [True, False]
sg = lambda b: 1.0 if b else -1.0
sig = lambda t: 1.0/(1.0 + np.exp(-t))
pr = lambda th, b: sig(th) if b else 1 - sig(th)
sc = lambda th, b: (1 - sig(th)) if b else -sig(th)
st = lambda z: 1 if z else 2


def game(c):
    return (lambda x, z: sg(z)*(1 + c*sg(x)), lambda x, z: -c*sg(x)*sg(z),
            lambda f, g: c*sg(f)*sg(g), lambda z, f, g: sg(f)*(sg(z) - c*sg(g)))


def field(th1, th2, gam, c, beta, repair=False):
    r10, r20, r11, r21 = game(c)
    V11 = {z: sum(pr(th1[st(z)], f)*pr(th2[st(z)], g)*r11(f, g) for f in B for g in B) for z in B}
    V21 = {z: sum(pr(th1[st(z)], f)*pr(th2[st(z)], g)*r21(z, f, g) for f in B for g in B) for z in B}
    V10 = sum(pr(th1[0], x)*pr(th2[0], z)*(r10(x, z) + gam*V11[z]) for x in B for z in B)
    V20 = sum(pr(th1[0], x)*pr(th2[0], z)*(r20(x, z) + gam*V21[z]) for x in B for z in B)
    A10 = lambda x, z: r10(x, z) + gam*V11[z] - V10; A20 = lambda x, z: r20(x, z) + gam*V21[z] - V20
    A11 = lambda z, f, g: r11(f, g) - V11[z]; A21 = lambda z, f, g: r21(z, f, g) - V21[z]
    A1b = lambda x: sum(pr(th2[0], z)*A10(x, z) for z in B); A2b = lambda z: sum(pr(th1[0], x)*A20(x, z) for x in B)
    F1 = np.zeros(3); F2 = np.zeros(3); S1 = np.zeros(3); S2 = np.zeros(3)
    for x, z, f, g in itertools.product(B, B, B, B):
        P = pr(th1[0], x)*pr(th2[0], z)*pr(th1[st(z)], f)*pr(th2[st(z)], g)
        w1 = A1b(x) if repair else A10(x, z); w2 = A2b(z) if repair else A20(x, z)
        F1[0] += P*A10(x, z)*sc(th1[0], x); F1[st(z)] += P*gam*A11(z, f, g)*sc(th1[st(z)], f)
        F2[0] += P*A20(x, z)*sc(th2[0], z); F2[st(z)] += P*gam*A21(z, f, g)*sc(th2[st(z)], g)
        S1[st(z)] += P*beta*gam**2*(gam*w1)*A21(z, f, g)*sc(th1[st(z)], f)
        S2[st(z)] += P*beta*gam**2*(gam*w2)*A11(z, f, g)*sc(th2[st(z)], g)
    return F1 + S1, F2 + S2, S1, S2


def best_dev_p2(th1, gam, c):
    r10, r20, r11, r21 = game(c); best = -np.inf
    for z0 in B:
        for gtab in itertools.product(B, repeat=2):           # g as a function of x (z0 fixed)
            g = dict(zip(B, gtab))
            R = sum(pr(th1[0], x)*pr(th1[st(z0)], f)*(r20(x, z0) + gam*r21(z0, f, g[x])) for x in B for f in B)
            best = max(best, R)
    return best


def main():
    gam, c, beta, alpha = 0.9, 0.1, 0.3, 0.1
    z = [0.0, 0.0, 0.0]
    F1, F2, _, _ = field(z, z, gam, c, beta)
    assert np.allclose(F1, [0, beta*gam**3/4, beta*gam**3/4], atol=1e-15) and np.allclose(F2, 0, atol=1e-15)
    print('F1 at uniform =', F1, ' F2 =', F2)
    assert abs(best_dev_p2(z, gam, c)) < 1e-15
    th1 = list(alpha*F1)
    gain = best_dev_p2(th1, gam, c)
    expected = gam*(1 + c)*np.tanh(alpha*beta*gam**3/8)
    print('post-step best deviation of player 2 =', gain, ' formula =', expected)
    assert abs(gain - expected) < 1e-15
    _, _, R1, R2 = field(z, z, gam, c, beta, repair=True)
    assert np.allclose(R1, 0) and np.allclose(R2, 0)
    rng = np.random.default_rng(5); m1 = m2 = 0.0
    for _ in range(2000):
        a, b = rng.normal(0, 2, 3), rng.normal(0, 2, 3)
        _, _, R1, R2 = field(a, b, gam, c, beta, repair=True); m1 = max(m1, abs(R1).max()); m2 = max(m2, abs(R2).max())
    print('repaired alignment term, max |player 1| =', m1, ' max |player 2| =', m2)
    assert m1 < 1e-15 < m2
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
