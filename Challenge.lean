module

public import Mathlib

public section

/-!
# Erdős–Kac theorem

`ω(n)`, the number of distinct prime factors of `n`, is asymptotically normally
distributed: after centring by `log log N` and scaling by `sqrt(log log N)`, the
proportion of `n ≤ N` whose normalised value lies in `[a, b]` tends to the
Gaussian mass `1/sqrt(2π) ∫_a^b exp(-t²/2) dt`.

This module is the small trusted statement surface; the proof is in
`ErdosKac/Proof.lean` and the checked solution is `Solution.lean`.
-/

open Real Filter Topology

namespace ErdosKac

/-- Erdős–Kac theorem: `ω(n)` is asymptotically normal with mean and variance `log log N`. -/
theorem erdos_kac (a b : ℝ) (hab : a < b) :
    Tendsto
      (fun N : ℕ =>
        ((((Finset.Icc 1 N).filter (fun n : ℕ =>
            a ≤ ((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
                  Real.sqrt (Real.log (Real.log N)) ∧
            ((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
                  Real.sqrt (Real.log (Real.log N)) ≤ b)).card : ℝ) / (N : ℝ)))
      atTop
      (𝓝 ((1 / Real.sqrt (2 * π)) * ∫ t in a..b, Real.exp (-t ^ 2 / 2))) := by sorry

end ErdosKac
