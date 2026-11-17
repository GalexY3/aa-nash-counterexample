# Advantage Alignment does not preserve mixed Nash equilibria

A machine-checked counterexample to Theorem 3 of *Advantage Alignment Algorithms*
(Duque et al., ICLR 2025, arXiv:2406.14662), plus an exact covariance characterization of
the alignment term. Author: GalexY3. Preprint source: `paper/main.tex`.

**Results.**
- **Counterexample.** In a two-player, two-stage game, the uniform profile is an isolated mixed
  Markov-perfect equilibrium. The Eq. 8 field is (0, βγ³/4, βγ³/4) for player 1. After one
  ascent step, player 2 gains γ(1+c)·tanh(αβγ³/8) > 0 by deviating.
- **Characterization.** At any state, the alignment term equals W · Cov(own score, the effect of
  one's own action on the opponent's expected advantage). It vanishes at an interior
  equilibrium iff that externality covariance is zero. It always vanishes at pure profiles.
- **Repairs.** Marginalizing the opponent's current advantage removes the term for every policy.
  The authors' suggested repair (issue #12) preserves mixed Markov-perfect equilibria, but can
  suppress the alignment signal.

**Verification.**
- `lean/` (Lean 4.36 + Mathlib): `lake exe cache get && lake build && lake env lean AaNash/Axioms.lean`.
  No `sorry`; the axioms used are only propext, Classical.choice and Quot.sound
  (`lean/AXIOMS_AUDIT.txt`).
- `verify/verify_counterexample.py` (NumPy) reproduces every number; expected output `ALL CHECKS PASSED`.
- `preregistration/`: the formal statements, fixed before any proof was written (in Spanish).

**Credit.** Advantage Alignment, Eq. 8 and Theorem 3 are the work of Duque, Aghajohari,
Cooijmans, Ciuca, Zhang, Gidel and Courville. J. A. Duque publicly confirmed the scope issue
and proposed the repair analysed here in
https://github.com/jduquevan/advantage-alignment/issues/12. The idea is the author's. AI tools
assisted with programming, the Lean proofs and drafting, under the author's direction.

**License.** Code: MIT. Text: CC BY 4.0.
