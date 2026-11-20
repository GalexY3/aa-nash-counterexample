"""C21b: checks H1-H3 of PREREG_C21B_DESPLAZAMIENTO_DEL_RIVAL.md (frozen in 819151f).

Displacements are measured in reduced logit coordinates (first logit of each player fixed at 0).
Writes formal/C21_RESULTS/c21b_results.json.
"""
import json
import os

import numpy as np

rng = np.random.default_rng(20261122)
OUT = os.path.join(os.path.dirname(__file__), "C21_RESULTS")
os.makedirs(OUT, exist_ok=True)


def J(p):
    return np.diag(p) - np.outer(p, p)


def simplex(n):
    x = rng.dirichlet(np.ones(n) * 2.0)
    return 0.8 * x + 0.2 / n


def nash_game(p, q, A, B):
    u1 = rng.normal(size=(A, B))
    u2 = rng.normal(size=(A, B))
    u1 = u1 - (u1 @ q - p @ u1 @ q)[:, None]      # r1 = 0
    u2 = u2 - (p @ u2 - p @ u2 @ q)[None, :]      # s2 = 0
    return u1, u2


def shaping(kind, u1, u2, p, q, past):
    if kind == "AA":
        a0, b0 = past
        return (u1[a0, b0] - p @ u1 @ q) * (J(p) @ (u2 @ q))
    if kind == "LOLA":
        g = J(q) @ (p @ u1)
        return J(p) @ u2 @ J(q) @ g
    raise ValueError(kind)


def to_pol(x, A):
    lp = np.concatenate([[0.0], x[: A - 1]])
    lq = np.concatenate([[0.0], x[A - 1:]])
    p = np.exp(lp - lp.max()); p /= p.sum()
    q = np.exp(lq - lq.max()); q /= q.sum()
    return p, q


def to_logits(p, q):
    return np.concatenate([np.log(p[1:] / p[0]), np.log(q[1:] / q[0])])


def field(x, u1, u2, beta, kind, past):
    A = u1.shape[0]
    p, q = to_pol(x, A)
    f1 = J(p) @ u1 @ q + beta * shaping(kind, u1, u2, p, q, past)
    f2 = J(q) @ (p @ u2)
    return np.concatenate([f1[1:], f2[1:]])


def solve(x0, u1, u2, beta, kind, past, iters=80, h=1e-6):
    x = x0.copy()
    for _ in range(iters):
        f = field(x, u1, u2, beta, kind, past)
        if np.max(np.abs(f)) < 1e-13:
            break
        Jm = np.array([(field(x + h * e, u1, u2, beta, kind, past)
                        - field(x - h * e, u1, u2, beta, kind, past)) / (2 * h)
                       for e in np.eye(len(x))]).T
        x = x - np.linalg.pinv(Jm, rcond=1e-12) @ f   # minimum-norm Gauss-Newton step
        if np.max(np.abs(x - x0)) > 5:
            return None
    if np.max(np.abs(field(x, u1, u2, beta, kind, past))) > 1e-10:
        return None
    return x


def run(A, B, kind, n=500, betas=(1e-3, 5e-4)):
    rec = {"n": n, "excluded_cond": 0, "excluded_noconv": 0, "ratio": [], "pred_err": [],
           "half_d2": [], "half_d1": []}
    for _ in range(n):
        p, q = simplex(A), simplex(B)
        u1, u2 = nash_game(p, q, A, B)
        past = (rng.integers(A), rng.integers(B))
        x0 = to_logits(p, q)
        H12 = (J(p) @ u1 @ J(q))[1:, 1:]
        if A == B and np.linalg.cond(H12) > 1e6:
            rec["excluded_cond"] += 1
            continue
        T = shaping(kind, u1, u2, p, q, past)[1:]
        sols = [solve(x0, u1, u2, b, kind, past) for b in betas]
        if any(s is None for s in sols):
            rec["excluded_noconv"] += 1
            continue
        d = [s - x0 for s in sols]
        d1 = [np.linalg.norm(di[: A - 1]) for di in d]
        d2 = [np.linalg.norm(di[A - 1:]) for di in d]
        if d2[0] == 0:
            rec["excluded_noconv"] += 1
            continue
        rec["ratio"].append(d1[0] / d2[0])
        pred = np.linalg.lstsq(H12, -betas[0] * T, rcond=None)[0]
        rec["pred_err"].append(np.linalg.norm(d[0][A - 1:] - pred) / d2[0])
        rec["half_d2"].append(d2[0] / d2[1] if d2[1] > 0 else np.nan)
        rec["half_d1"].append(d1[0] / d1[1] if d1[1] > 1e-15 else np.inf)
    r = np.array(rec["ratio"]); e = np.array(rec["pred_err"])
    h2 = np.array(rec["half_d2"]); h1 = np.array(rec["half_d1"])
    used = len(r)
    excluded = rec["excluded_cond"] + rec["excluded_noconv"]
    return {
        "used": used,
        "excluded_cond": rec["excluded_cond"],
        "excluded_noconv": rec["excluded_noconv"],
        "excluded_share": excluded / n,
        "share_ratio_lt_1e-2": float(np.mean(r < 1e-2)) if used else None,
        "median_ratio": float(np.median(r)) if used else None,
        "share_pred_err_lt_5e-2": float(np.mean(e < 5e-2)) if used else None,
        "median_pred_err": float(np.median(e)) if used else None,
        "share_half_ok": float(np.mean((h2 > 1.8) & (h2 < 2.2) & (h1 >= 3))) if used else None,
        "median_d2_halving": float(np.nanmedian(h2)) if used else None,
        "median_d1_halving": float(np.median(h1[np.isfinite(h1)])) if np.isfinite(h1).any() else "d1 below 1e-15",
    }


if __name__ == "__main__":
    out = {}
    for label, sizes in [("H1", [(2, 2), (3, 3), (4, 4)]), ("H2", [(2, 3), (3, 4)]),
                         ("H3_exploratory", [(3, 2), (4, 3)])]:
        out[label] = {}
        for A, B in sizes:
            for kind in ["AA", "LOLA"]:
                out[label][f"{A}x{B}_{kind}"] = run(A, B, kind)
    with open(os.path.join(OUT, "c21b_results.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, default=float)
    print(json.dumps(out, indent=1, default=float))
