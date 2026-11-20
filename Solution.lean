module

public import ErdosKac

public section

/-!
# Proved solution

Repeats the advertised statement of `Challenge.lean`, proved by the development
in `ErdosKac/Proof.lean`. Comparator checks that the two statements agree and
that the proof uses only the permitted axioms.
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
      (𝓝 ((1 / Real.sqrt (2 * π)) * ∫ t in a..b, Real.exp (-t ^ 2 / 2))) := by
  exact erdos_kac_aux a b hab

end ErdosKac
