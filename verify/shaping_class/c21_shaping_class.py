"""C21: numerical checks P1-P3 of PREREG_C21_CLASE_SHAPING_NASH.md (frozen in cdf4949).

Stage game, two players, softmax policies. All terms are for player 1 and live in R^A
(gradient with respect to player 1's logits). Writes formal/C21_RESULTS/c21_results.json.
"""
import json
import os

import numpy as np

rng = np.random.default_rng(20261121)
OUT = os.path.join(os.path.dirname(__file__), "C21_RESULTS")
os.makedirs(OUT, exist_ok=True)


def J(p):
    return np.diag(p) - np.outer(p, p)


def simplex(n):
    x = rng.dirichlet(np.ones(n) * 2.0)
    return 0.8 * x + 0.2 / n  # keep away from the boundary


def anova(u, p, q):
    k = p @ u @ q
    row = u @ q - k          # main effect of a (n2 for u2, r1 for u1)
    col = p @ u - k          # main effect of b (s2 for u2, t1 for u1)
    inter = u - k - row[:, None] - col[None, :]
    return k, row, col, inter


def nash_game(p, q, A, B):
    """Random (u1, u2) with an interior Nash equilibrium at (p, q): r1 = 0 and s2 = 0."""
    u1 = rng.normal(size=(A, B))
    u2 = rng.normal(size=(A, B))
    _, r1, _, _ = anova(u1, p, q)
    u1 = u1 - r1[:, None]
    _, _, s2, _ = anova(u2, p, q)
    u2 = u2 - s2[None, :]
    return u1, u2


def terms(u1, u2, p, q, past):
    a0, b0 = past
    k1 = p @ u1 @ q
    v2 = J(p) @ (u2 @ q)                                  # J_p mu2
    W_joint = u1[a0, b0] - k1                             # joint past advantage of player 1
    W_marg = (u1 @ q)[a0] - k1                            # past weight marginalized over b (r1(a0))
    g = J(q) @ (p @ u1)                                   # grad_theta2 V1
    lola = J(p) @ u2 @ J(q) @ g                           # first-order LOLA shaping term
    grad2_V2 = J(q) @ (p @ u2)                            # = J_q s2
    lookahead = J(p) @ u1 @ J(q) @ grad2_V2               # LookAhead (LOLA without chi)
    return {
        "AA": W_joint * v2,
        "AA_past_marginal": W_marg * v2,
        "LOLA": lola,
        "LookAhead": lookahead,
    }


def p1(n_games=2000):
    res = {}
    for A, B in [(2, 2), (3, 3), (3, 4)]:
        mx = {k: 0.0 for k in ["AA", "AA_past_marginal", "LOLA", "LookAhead"]}
        nonzero = {k: 0 for k in mx}
        for _ in range(n_games):
            p, q = simplex(A), simplex(B)
            u1, u2 = nash_game(p, q, A, B)
            past = (rng.integers(A), rng.integers(B))
            for k, v in terms(u1, u2, p, q, past).items():
                m = float(np.max(np.abs(v)))
                mx[k] = max(mx[k], m)
                nonzero[k] += m > 1e-6
        res[f"{A}x{B}"] = {"max_abs": mx, "share_nonzero_gt_1e-6": {k: v / n_games for k, v in nonzero.items()}}
    return res


def p2(n_forms=200, A=2, B=3):
    """Random bilinear maps T: R^N x R^N -> R^A. Vanishing on G1 x G2 <=> gated factorization."""
    N = A * B
    p, q = simplex(A), simplex(B)

    def basis_G(which):
        # orthonormal basis of G1 (r1 = 0) or G2 (s2 = 0), as flattened matrices
        cons = []
        for i in range(A if which == 1 else B):
            e = np.zeros((A, B))
            if which == 1:   # row main effect r1(a) for a = i (linear functional of u1)
                for b in range(B):
                    e[i, b] += q[b]
                e -= np.outer(np.ones(A), q) * p[i]
            else:            # column main effect s2(b) for b = i
                for a in range(A):
                    e[a, i] += p[a]
                e -= np.outer(p, np.ones(B)) * q[i]
            cons.append(e.ravel())
        C = np.array(cons)
        _, s, vt = np.linalg.svd(C)
        rank = int((s > 1e-10).sum())
        return vt[rank:].T, C  # columns span the null space

    G1, C1 = basis_G(1)
    G2, C2 = basis_G(2)
    agree = 0
    for t in range(n_forms):
        if t % 2 == 0:  # build a gated form B1(r1,u2) + B2(u1,s2)
            M1 = rng.normal(size=(A, C1.shape[0], N))
            M2 = rng.normal(size=(A, N, C2.shape[0]))
            T = np.einsum("aij,ik->akj", M1, C1) + np.einsum("aij,jk->aik", M2, C2)
            gated = True
        else:           # generic random form
            T = rng.normal(size=(A, N, N))
            gated = False
        restricted = np.einsum("aij,ik,jl->akl", T, G1, G2)
        vanishes = bool(np.max(np.abs(restricted)) < 1e-9)
        agree += vanishes == gated
    dims = {"N": N, "dimG1": G1.shape[1], "dimG2": G2.shape[1]}
    return {"agreement": agree / n_forms, "dims": dims}


def solve_fixed_point(u1, u2, p0, q0, beta, past, iters=60):
    """Newton on reduced logits for F1 = J_p u1 q + beta*T_AA, F2 = J_q u2^T p."""
    A, B = u1.shape
    x = np.concatenate([np.log(p0[1:] / p0[0]), np.log(q0[1:] / q0[0])])

    def unpack(x):
        lp = np.concatenate([[0.0], x[: A - 1]])
        lq = np.concatenate([[0.0], x[A - 1:]])
        p = np.exp(lp - lp.max()); p /= p.sum()
        q = np.exp(lq - lq.max()); q /= q.sum()
        return p, q

    def F(x):
        p, q = unpack(x)
        f1 = J(p) @ u1 @ q + beta * terms(u1, u2, p, q, past)["AA"]
        f2 = J(q) @ (p @ u2)
        return np.concatenate([f1[1:], f2[1:]])

    for _ in range(iters):
        f = F(x)
        h = 1e-7
        Jm = np.array([(F(x + h * e) - f) / h for e in np.eye(len(x))]).T
        try:
            x = x - np.linalg.solve(Jm, f)
        except np.linalg.LinAlgError:
            return None
    if np.max(np.abs(F(x))) > 1e-9:
        return None
    return unpack(x)


def p3(n_games=500, beta=1e-3, A=2, B=2):
    """As frozen: sign of player 1's first displacement component vs sign of first component of W J_p n2.
    Exploratory (post hoc, not frozen): the same for player 2's displacement."""
    frozen_hits = frozen_n = 0
    post_hits = post_n = 0
    disp1, disp2, solved = [], [], 0
    for _ in range(n_games):
        p, q = simplex(A), simplex(B)
        u1, u2 = nash_game(p, q, A, B)
        past = (rng.integers(A), rng.integers(B))
        T = terms(u1, u2, p, q, past)["AA"]
        if abs(T[0]) <= 1e-3:
            continue
        fp = solve_fixed_point(u1, u2, p, q, beta, past)
        if fp is None:
            continue
        solved += 1
        p1_, q1_ = fp
        dp, dq = p1_ - p, q1_ - q
        disp1.append(float(np.max(np.abs(dp))))
        disp2.append(float(np.max(np.abs(dq))))
        frozen_n += 1
        frozen_hits += np.sign(dp[0]) == np.sign(T[0])
        # post hoc: in 2x2 at an interior Nash the own block of the naive field is zero, so the
        # shift falls on the rival: dq solves H12 dq = -beta T with H12 = d(J_p u1 q)/dq.
        H12 = J(p) @ u1 @ J(q)
        pred_dq = np.linalg.lstsq(H12[1:, :][:, 1:] if A > 1 else H12, -beta * T[1:], rcond=None)[0]
        post_n += 1
        post_hits += np.sign(dq[1]) == np.sign(pred_dq[0]) if abs(pred_dq[0]) > 1e-9 else 0
    return {
        "solved": solved,
        "frozen_P3_sign_agreement_player1": frozen_hits / max(frozen_n, 1),
        "median_abs_displacement_player1": float(np.median(disp1)) if disp1 else None,
        "median_abs_displacement_player2": float(np.median(disp2)) if disp2 else None,
        "posthoc_rival_shift_sign_agreement": post_hits / max(post_n, 1),
        "beta": beta,
    }


if __name__ == "__main__":
    out = {"P1": p1(), "P2": p2(), "P3": p3()}
    with open(os.path.join(OUT, "c21_results.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, default=float)
    print(json.dumps(out, indent=2, default=float))
