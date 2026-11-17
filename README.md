# Advantage Alignment does not preserve mixed Nash equilibria

A machine-checked counterexample to Theorem 3 of *Advantage Alignment Algorithms*
(Duque et al., ICLR 2025, arXiv:2406.14662), plus an exact covariance characterization of
the alignment term.

Author: **Alejandro Panera Pascual (GalexY)**, Universidad de Salamanca.
Preprint: [`paper/main.pdf`](paper/main.pdf) (source `paper/main.tex`).

**Results.**
- **Counterexample.** In a two-player, two-stage game, the uniform profile is an isolated mixed
  Markov-perfect equilibrium. The Eq. 8 field is (0, βγ³/4, βγ³/4) for player 1. After one
  ascent step, player 2 gains γ(1+c)·tanh(αβγ³/8) > 0 by deviating.
- **Characterization.** At any state, the alignment term equals W · Cov(own score, the effect of
  one's own action on the opponent's expected advantage). It vanishes at an interior
  equilibrium iff that externality covariance is zero. It always vanishes at pure profiles.
- **Not invariant to strategic equivalence.** Adding to player 1's reward a term λz that depends only on
  the opponent's action leaves every unilateral deviation gain and the equilibrium unchanged, but the
  equilibrium update becomes (0, βγ³λ/4, βγ³λ/4). The counterexample (λ = 1) is driven entirely by this
  component. How past experience reaches the current state (memory η) can also cancel or reverse the update.
- **Repairs.** Marginalizing the opponent's current advantage removes the term for every policy.
  The authors' suggested repair (issue #12) preserves mixed Markov-perfect equilibria, but can
  suppress the alignment signal.

**Verification.**
- `lean/` (Lean 4.36 + Mathlib): `lake exe cache get && lake build && lake env lean AaNash/Axioms.lean`.
  No `sorry`; the axioms used are only propext, Classical.choice and Quot.sound
  (`lean/AXIOMS_AUDIT.txt`).
- `verify/verify_counterexample.py` (NumPy) reproduces the counterexample (`ALL CHECKS PASSED`);
  `verify_aggregation.py` checks the history aggregation and the memory control with exact fractions;
  `verify_strategic_equivalence.py` checks the λ control (640 pure Markov profiles, 10 exact fields).
- `preregistration/`: the formal statements, fixed before any proof was written (in Spanish).

**Credit.** Advantage Alignment, Eq. 8 and Theorem 3 are the work of Duque, Aghajohari,
Cooijmans, Ciuca, Zhang, Gidel and Courville. J. A. Duque publicly confirmed the scope issue
and proposed the repair analysed here in
https://github.com/jduquevan/advantage-alignment/issues/12. The idea is the author's and AI tools
assisted with programming, the Lean proofs and drafting, under the author's direction.

**License.** Code: MIT. Text: CC BY 4.0.
