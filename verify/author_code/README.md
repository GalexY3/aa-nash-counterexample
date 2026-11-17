# Confirmation with the authors' original code (lambda family)

1. `python fetch_v205_upstream.py` downloads `train.py` and `utils.py` of
   jduquevan/advantage-alignment at commit 2065e43 into `upstream/` and checks their SHA-256
   (the third-party code is not redistributed here).
2. `python c07_author_probe.py` loads the unmodified functions `compute_gae_advantages`,
   `aa_terms`, `aa_loss` and `actor_losses` and runs them on the lambda family of the two-stage
   game (240 configurations). Expected: `P1_lambda0_no_movement: true` and
   `P2_lambda_nonzero_moves: true`. Reference output: `author_code_lambda_probe.json`.

Requires NumPy and PyTorch. This audits the loss functions on an exact tabular fixture; it does
not reproduce the authors' networks or benchmarks.
