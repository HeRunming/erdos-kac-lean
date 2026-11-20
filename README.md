# Erdős–Kac theorem in Lean 4

A complete, sorry-free formalisation of the Erdős–Kac theorem in Lean 4 with
Mathlib, packaged for the [Palomar](https://palomar-registry.org/) registry of
Lean-verified mathematics.

## The theorem

Let ω(n) be the number of distinct prime factors of n. For all real a < b,

$$
\lim_{N\to\infty} \frac{1}{N}\,\\#\Bigl\\{\,1 \le n \le N :
a \le \frac{\omega(n) - \log\log N}{\sqrt{\log\log N}} \le b \Bigr\\}
= \frac{1}{\sqrt{2\pi}} \int_a^b e^{-t^2/2}\,dt .
$$

P. Erdős and M. Kac, *The Gaussian law of errors in the theory of additive
number theoretic functions*, Amer. J. Math. **62** (1940), 738–742.

The Lean statement is `ErdosKac.erdos_kac` in [`Challenge.lean`](Challenge.lean),
with ω given by Mathlib's `ArithmeticFunction.cardDistinctFactors`.

## Layout

| File | Role |
|---|---|
| `Challenge.lean` | The advertised statement (35 lines, deliberately `sorry`). This is the file to audit. |
| `Solution.lean` | The same statement, proved by the development below. |
| `ErdosKac/Proof.lean` | The proof development (about 2,000 lines). |
| `comparator.json` | Tells Comparator to check `ErdosKac.erdos_kac` against the three standard axioms. |
| `formalization.yaml` | Metadata: sources, scope, automation and review status. |

## Proof outline

The proof follows the sieve-and-characteristic-function route of
Granville and Soundararajan ([arXiv:math/0606039](https://arxiv.org/abs/math/0606039)),
not the original argument of Erdős and Kac.

1. **Mertens' second theorem** (`ms_*`): Chebyshev's bound on θ, Legendre's
   formula for n!, and Abel summation give Σ_{p ≤ n} 1/p = log log n + O(1).
2. **Truncation** (`ek_trunc*`, `ek_center`): primes above
   x = exp(log N / log log log N) change ω(n) by a negligible amount.
3. **Sieve against model** (`ek_mc_*`, `ek_moment_compare`): the first 2K−1
   moments of the truncated count agree with those of a sum of independent
   Bernoulli variables.
4. **Characteristic functions** (`ek_cf_aux_taylor`, `ek_cf_moment_compare`):
   truncating exp(iτs) at order 2K bounds the difference of the sieve and model
   characteristic functions by the first 2K−1 moment differences plus a
   remainder controlled by the 2K-th moments. This is the step that carries
   moment information over to characteristic functions; moment comparison alone
   does not give convergence.
5. **Uniform moment bound** (`ek_model_moment_bound`, `ek_sieve_model`): a
   uniform even-moment bound for the model lets K be fixed first, which makes
   the remainder as small as required, after which the finitely many moment
   differences tend to zero.
6. **Model limit** (`ek_ml_*`, `ek_model_limit`): the model's characteristic
   function tends to exp(−t²/2).
7. **Lévy continuity** (`levy_continuity_Icc`, `levy_counting`): convergence of
   characteristic functions gives convergence on intervals.

## How this was produced

The Lean proof was written by the multi-agent proving system FolioCert Prove,
using the model `claude-opus-5.5`. No human wrote any of the Lean. Runming He
chose the target and supplied the reference proof texts. The port from Lean
v4.28.0 to v4.35.0-rc2 and the packaging for Palomar were done by Claude Code,
using the same model, at the author's direction. The port only renamed five
deprecated Mathlib lemmas. No human has reviewed the proof development; it is
machine-checked. Full details are in [`formalization.yaml`](formalization.yaml).

## Verification

```sh
lake exe cache get
lake build
scripts/verify-comparator.sh
```

The last command runs `lake comparator` the way Palomar does. It replays the
proof through Lean's kernel and the independent NanoDa and con-ron kernels, and
checks that `ErdosKac.erdos_kac` depends only on `propext`,
`Classical.choice` and `Quot.sound`. You need Linux, `bwrap` and the toolchain
in `lean-toolchain` (Lean v4.35.0-rc2, Mathlib pinned in `lake-manifest.json`).

## Submitting to Palomar

Push this repository to a public GitHub repository, copy the full 40-character
commit SHA, and
[open the submission form](https://submit.palomar-registry.org/).

## Licence

Apache-2.0, copyright 2026 Runming He. See [`LICENSE`](LICENSE).
