module

public import Mathlib

public section

/-!
# Erdős–Kac theorem — proof development

Supporting lemmas and the proof of the Erdős–Kac theorem, culminating in
`ErdosKac.erdos_kac_aux`. The advertised statement that is checked by Comparator
lives in `Challenge.lean` / `Solution.lean`.
-/

namespace ErdosKac

open Real Filter Topology

/-- Erdős–Kac theorem: `ω(n)` is asymptotically normal with mean and variance `log log N`. -/
theorem ms_theta_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤ Real.log 4 * n := by
  have h1 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ)
      = Real.log ((primorial n : ℕ) : ℝ) := by
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.1 hp).2.pos
    exact_mod_cast this.ne'
  rw [h1]
  have h2 : ((primorial n : ℕ) : ℝ) ≤ (4:ℝ) ^ n := by exact_mod_cast primorial_le_4_pow n
  have h3 : (0:ℝ) < (primorial n : ℕ) := by exact_mod_cast primorial_pos n
  calc Real.log ((primorial n : ℕ) : ℝ) ≤ Real.log ((4:ℝ)^n) := Real.log_le_log h3 h2
    _ = Real.log 4 * n := by rw [Real.log_pow]; ring

theorem ms_log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      Real.log (p : ℝ) * ((n.factorial.factorization p : ℕ) : ℝ) := by
  have hm : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hsub : n.factorial.factorization.support ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ((Nat.Prime.dvd_factorial hp.1).mp hp.2.1), hp.1⟩
  have h1 := Nat.factorization_prod_pow_eq_self hm
  rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _)] at h1
  have h2 : (n.factorial : ℝ) = ((∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      p ^ (n.factorial.factorization p) : ℕ) : ℝ) := by
    rw [h1]
  rw [h2, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
    ring
  · intro p hp
    have := (Finset.mem_filter.1 hp).2.pos
    exact_mod_cast (pow_pos this _).ne'

theorem ms_legendre_bounds (n p : ℕ) (hp : p.Prime) :
    (n : ℝ) / p - 1 ≤ ((n.factorial.factorization p : ℕ) : ℝ) ∧
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / p + (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · have hv1 : n / p ≤ n.factorial.factorization p := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [Nat.factorization_factorial hp (b := n + 1)
          (Nat.lt_succ_of_lt (Nat.log_lt_self p hn.ne'))]
        have h1 : (1:ℕ) ∈ Finset.Ico 1 (n + 1) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
        have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
        simpa only [pow_one] using this
    have hv1' : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      exact_mod_cast hv1
    have h2 : n < n / p * p + p := Nat.lt_div_mul_add hp.pos
    have h2' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h2
    have h3 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]
      linarith [show (((n / p : ℕ) : ℝ) + 1) * p = ((n / p : ℕ) : ℝ) * p + p by ring]
    linarith
  · have hu := Nat.factorization_factorial_le_div_pred hp n
    have hv : ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast hu
    have hc : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hsub] at hc
    have hpp : (0:ℝ) < (p:ℝ) * ((p:ℝ) - 1) := mul_pos hp0 hp1
    have heq : (n : ℝ) / ((p : ℝ) - 1) = (n : ℝ) / p + (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      first
        | (rw [eq_comm, div_add_div _ _ hp0.ne' hpp.ne',
            div_eq_div_iff (mul_pos hp0 hpp).ne' hp1.ne']; ring)
        | (field_simp; ring)
        | field_simp
    linarith

theorem ms_log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  constructor
  · have h := Real.pow_div_factorial_le_exp (n:ℝ) hnpos.le n
    rw [div_le_iff₀ hf] at h
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
    linarith
  · have h : ((n.factorial : ℕ) : ℝ) ≤ (n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 := Real.log_le_log hf h
    rw [Real.log_pow] at h2
    exact h2

theorem ms_tail_const : ∃ D : ℝ, ∀ n : ℕ,
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ D := by
  have hs : Summable (fun m : ℕ => 4 * (m:ℝ) ^ (-(3/2:ℝ))) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left 4
  refine ⟨∑' m : ℕ, 4 * (m:ℝ) ^ (-(3/2:ℝ)), fun n => ?_⟩
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun m _ _ => by positivity)).trans (hs.sum_le_tsum _ (fun m _ => by positivity)))
  have hpp := (Finset.mem_filter.1 hp).2
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hlog : Real.log p ≤ (p:ℝ) ^ (1/2:ℝ) / (1/2) := Real.log_le_rpow_div hpos.le (by norm_num)
  have hsq : (p:ℝ) ^ (1/2:ℝ) * (p:ℝ) ^ (1/2:ℝ) = p := by
    rw [← Real.rpow_add hpos]; norm_num
  have hr : (p:ℝ) ^ (-(3/2:ℝ)) * (p:ℝ) ^ (1/2:ℝ) * p = 1 := by
    rw [← Real.rpow_add hpos, ← Real.rpow_add_one hpos.ne']; norm_num
  set s := (p:ℝ) ^ (1/2:ℝ) with hsdef
  set q := (p:ℝ) ^ (-(3/2:ℝ)) with hqdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hpos _
  have hq0 : 0 < q := Real.rpow_pos_of_pos hpos _
  have e1 : q * p * p = s := by
    apply mul_right_cancel₀ hs0.ne'
    nlinarith [hr, hsq]
  have e2 : 2 * (q * p) ≤ s := by nlinarith [mul_pos hq0 hpos]
  rw [div_le_iff₀ (by nlinarith)]
  have e3 : 4 * q * (p * (p - 1)) = 4 * (q * p * p) - 4 * (q * p) := by ring
  rw [e3]
  linarith

theorem ms_mertens_first_nat : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    |(∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / p) - Real.log n| ≤ C := by
  obtain ⟨D, hD⟩ := ms_tail_const
  refine ⟨Real.log 4 + 1 + |D|, fun n hn => ?_⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlf := ms_log_factorial_eq n
  have hb := ms_log_factorial_bounds n (by omega)
  have hθ := ms_theta_le n
  have hT := hD n
  have hlow : (n:ℝ) * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / p)
      - ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ)
      ≤ Real.log (n.factorial : ℝ) := by
    rw [hlf, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2
    have h1 := (ms_legendre_bounds n p hpp).1
    have hlp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    calc (n:ℝ) * (Real.log p / p) - Real.log p = Real.log p * ((n:ℝ) / p - 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hlp
  have hup : Real.log (n.factorial : ℝ) ≤
      (n:ℝ) * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / p) +
      (n:ℝ) * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hlf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2
    have h2 := (ms_legendre_bounds n p hpp).2
    have hlp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    calc Real.log (p:ℝ) * ((n.factorial.factorization p : ℕ) : ℝ)
        ≤ Real.log p * ((n : ℝ) / p + (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left h2 hlp
      _ = _ := by ring
  set A := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / p with hA
  set T := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) with hTdef
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hU : A - Real.log n - Real.log 4 ≤ 0 := by
    by_contra h
    push_neg at h
    have := mul_pos hnpos h
    have e : (n:ℝ) * (A - Real.log n - Real.log 4) = n * A - n * Real.log n - Real.log 4 * n := by
      ring
    linarith [hb.1, hb.2]
  have hL : 0 ≤ A + T - Real.log n + 1 := by
    by_contra h
    push_neg at h
    have := mul_neg_of_pos_of_neg hnpos h
    have e : (n:ℝ) * (A + T - Real.log n + 1) = n * A + n * T - n * Real.log n + n := by ring
    linarith [hb.1, hb.2]
  rw [abs_le]
  constructor <;> linarith [le_abs_self D, abs_nonneg D]

theorem ms_abel_identity (f : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Icc 2 n, f m =
      (∑ k ∈ Finset.Icc 2 n, f k * Real.log k) / Real.log n +
      ∑ m ∈ Finset.Ico 2 n, (∑ k ∈ Finset.Icc 2 m, f k * Real.log k) *
        (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
    simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty,
      add_zero, Nat.cast_ofNat]
    field_simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1),
      Finset.sum_Ico_succ_top hn, ih]
    generalize hT : (∑ m ∈ Finset.Ico 2 n, (∑ k ∈ Finset.Icc 2 m, f k * Real.log k) *
        (1 / Real.log m - 1 / Real.log (m + 1))) = T
    generalize hS : (∑ k ∈ Finset.Icc 2 n, f k * Real.log k) = S
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : Real.log (n:ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hn1 : Real.log ((n:ℝ) + 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
    push_cast
    field_simp
    ring

theorem ms_loglog_step (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ (Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log m)) -
        (1 - Real.log m / Real.log ((m : ℝ) + 1)) ∧
    (Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log m)) -
        (1 - Real.log m / Real.log ((m : ℝ) + 1)) ≤
      1 / (Real.log 2) ^ 2 * (1 / ((m : ℝ) - 1) - 1 / m) := by
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha2 : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
  have hab : Real.log m < Real.log ((m:ℝ) + 1) := Real.log_lt_log hmpos (by linarith)
  have hd : Real.log ((m:ℝ) + 1) - Real.log m ≤ 1 / (m:ℝ) := by
    have h1 : Real.log ((m:ℝ) + 1) - Real.log m = Real.log (((m:ℝ) + 1) / m) := by
      rw [Real.log_div (by linarith) hmpos.ne']
    have h2 := Real.log_le_sub_one_of_pos (show 0 < ((m:ℝ) + 1) / m by positivity)
    have h3 : ((m:ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  set a := Real.log (m:ℝ) with ha_def
  set b := Real.log ((m:ℝ) + 1) with hb_def
  have ha : 0 < a := lt_of_lt_of_le hl2 ha2
  have hb : 0 < b := by linarith
  have hdiv : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hu : 0 < b / a := div_pos hb ha
  have hinv : (b / a)⁻¹ = a / b := inv_div b a
  have hd0 : 0 ≤ b - a := by linarith
  rw [hdiv]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hu
    rw [hinv] at this
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hu
    have h2 : b / a - 1 - (1 - a / b) = (b - a) ^ 2 / (a * b) := by
      rw [div_sub_one ha.ne', one_sub_div hb.ne', div_sub_div _ _ ha.ne' hb.ne']
      ring
    have h3 : (b - a) ^ 2 / (a * b) ≤ (1 / (m:ℝ)) ^ 2 / (Real.log 2) ^ 2 := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hd0 hd 2) (by positivity)
      nlinarith
    have hm1 : (0:ℝ) < (m:ℝ) - 1 := by linarith
    have h4 : (1 / (m:ℝ)) ^ 2 ≤ 1 / ((m:ℝ) - 1) - 1 / m := by
      rw [div_sub_div _ _ hm1.ne' hmpos.ne', div_pow, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have h5 : (1 / (m:ℝ)) ^ 2 / (Real.log 2) ^ 2 = 1 / (Real.log 2) ^ 2 * (1 / (m:ℝ)) ^ 2 := by
      ring
    have h6 : 1 / (Real.log 2) ^ 2 * (1 / (m:ℝ)) ^ 2 ≤
        1 / (Real.log 2) ^ 2 * (1 / ((m:ℝ) - 1) - 1 / m) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith

theorem ms_prime_sum_Icc (g : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, g p =
      ∑ m ∈ Finset.Icc 2 n, (if m.Prime then g m else 0) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.two_le, by omega⟩, h2⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨by omega, h3⟩

theorem ms_telescope_Ico (g : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Ico 2 n, (g (m + 1) - g m) = g n - g 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

theorem ms_weight_telescope (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Ico 2 n, (1 / Real.log m - 1 / Real.log ((m : ℝ) + 1)) =
      1 / Real.log 2 - 1 / Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n), ih]
    push_cast
    ring

theorem ms_loglog_telescope (n : ℕ) (hn : 2 ≤ n) :
    |1 + ∑ m ∈ Finset.Ico 2 n, (1 - Real.log m / Real.log ((m : ℝ) + 1)) - Real.log (Real.log n)| ≤
      1 + |Real.log (Real.log 2)| + 1 / (Real.log 2) ^ 2 := by
  have key : ∀ k : ℕ, 2 ≤ k →
      0 ≤ (Real.log (Real.log k) - Real.log (Real.log 2)) -
        ∑ m ∈ Finset.Ico 2 k, (1 - Real.log m / Real.log ((m : ℝ) + 1)) ∧
      (Real.log (Real.log k) - Real.log (Real.log 2)) -
        ∑ m ∈ Finset.Ico 2 k, (1 - Real.log m / Real.log ((m : ℝ) + 1)) ≤
        1 / (Real.log 2) ^ 2 * (1 - 1 / ((k : ℝ) - 1)) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk]
      have hs := ms_loglog_step k hk
      have hk1 : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
      rw [hk1]
      push_cast
      have e : 1 / (Real.log 2) ^ 2 * (1 - 1 / (k : ℝ)) =
          1 / (Real.log 2) ^ 2 * (1 - 1 / ((k : ℝ) - 1)) +
          1 / (Real.log 2) ^ 2 * (1 / ((k : ℝ) - 1) - 1 / k) := by ring
      rw [e]
      constructor <;> linarith [ih.1, ih.2, hs.1, hs.2]
  obtain ⟨h1, h2⟩ := key n hn
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have h3 : 0 ≤ 1 / (Real.log 2) ^ 2 * (1 / ((n:ℝ) - 1)) :=
    mul_nonneg (by positivity) (div_nonneg zero_le_one (by linarith))
  have e : 1 / (Real.log 2) ^ 2 * (1 - 1 / ((n:ℝ) - 1)) =
      1 / (Real.log 2) ^ 2 - 1 / (Real.log 2) ^ 2 * (1 / ((n:ℝ) - 1)) := by ring
  have h4 : 0 ≤ 1 / (Real.log 2) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Real.log 2)),
    neg_abs_le (Real.log (Real.log 2))]

theorem ms_reciprocal_nat : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    |(∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 / (p : ℝ))) - Real.log (Real.log n)| ≤ C := by
  obtain ⟨C0, hC0⟩ := ms_mertens_first_nat
  refine ⟨1 + |Real.log (Real.log 2)| + 1 / (Real.log 2) ^ 2 + |C0| / Real.log 2 +
    |C0| / Real.log 2, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun m => if m.Prime then 1 / (m:ℝ) else 0 := ⟨_, rfl⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : ∀ m : ℕ, 2 ≤ m → Real.log 2 ≤ Real.log m := fun m hm =>
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hlogn : 0 < Real.log n := lt_of_lt_of_le hl2 (hlogpos n hn)
  have h1 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 / (p : ℝ)) =
      ∑ m ∈ Finset.Icc 2 n, f m := by
    rw [ms_prime_sum_Icc, hf]
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, ∀ m, ∑ k ∈ Finset.Icc 2 m, f k * Real.log k = A m :=
    ⟨_, fun m => rfl⟩
  have hR : ∀ m, 2 ≤ m → |A m - Real.log m| ≤ C0 := by
    intro m hm
    rw [← hAdef m]
    have : ∑ k ∈ Finset.Icc 2 m, f k * Real.log k =
        ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, Real.log (p : ℝ) / p := by
      rw [ms_prime_sum_Icc (fun p => Real.log (p:ℝ) / p) m]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hf]
      dsimp only
      split_ifs <;> ring
    rw [this]
    exact hC0 m hm
  have hsplit : ∀ m ∈ Finset.Ico 2 n, A m * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1)) =
      (1 - Real.log m / Real.log ((m:ℝ) + 1)) +
        (A m - Real.log m) * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1)) := by
    intro m hm
    have hm2 := (Finset.mem_Ico.1 hm).1
    have ha : Real.log m ≠ 0 := (lt_of_lt_of_le hl2 (hlogpos m hm2)).ne'
    have key : Real.log m * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1)) =
        1 - Real.log m / Real.log ((m:ℝ) + 1) := by
      rw [mul_sub, mul_one_div_cancel ha, mul_one_div]
    linear_combination key
  have hw0 : ∀ m ∈ Finset.Ico 2 n, 0 ≤ 1 / Real.log m - 1 / Real.log ((m:ℝ) + 1) := by
    intro m hm
    have hm2 := (Finset.mem_Ico.1 hm).1
    have ha := lt_of_lt_of_le hl2 (hlogpos m hm2)
    have hm2' : (2:ℝ) ≤ m := by exact_mod_cast hm2
    have hb : Real.log m ≤ Real.log ((m:ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le ha hb
  rw [h1, ms_abel_identity f n hn]
  simp only [hAdef]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hAn : A n / Real.log n = 1 + (A n - Real.log n) / Real.log n := by
    rw [sub_div, div_self hlogn.ne']
    ring
  rw [hAn]
  have hE1 : |(A n - Real.log n) / Real.log n| ≤ |C0| / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogn]
    exact div_le_div₀ (abs_nonneg _) ((hR n hn).trans (le_abs_self _)) hl2 (hlogpos n hn)
  have hE2 : |∑ m ∈ Finset.Ico 2 n,
      (A m - Real.log m) * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1))| ≤ |C0| / Real.log 2 := by
    calc _ ≤ ∑ m ∈ Finset.Ico 2 n,
          |(A m - Real.log m) * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ico 2 n, |C0| * (1 / Real.log m - 1 / Real.log ((m:ℝ) + 1)) :=
          Finset.sum_le_sum fun m hm => by
            rw [abs_mul, abs_of_nonneg (hw0 m hm)]
            exact mul_le_mul_of_nonneg_right
              ((hR m (Finset.mem_Ico.1 hm).1).trans (le_abs_self _)) (hw0 m hm)
      _ = |C0| * (1 / Real.log 2 - 1 / Real.log n) := by
          rw [← Finset.mul_sum, ms_weight_telescope n hn]
      _ ≤ |C0| / Real.log 2 := by
          rw [mul_sub, mul_one_div, mul_one_div]
          have := div_nonneg (abs_nonneg C0) hlogn.le
          linarith
  have hT := ms_loglog_telescope n hn
  rw [abs_le] at hE1 hE2 hT ⊢
  constructor <;> linarith [hE1.1, hE1.2, hE2.1, hE2.2, hT.1, hT.2]

theorem ms_loglog_floor (x : ℝ) (hx : 2 ≤ x) :
    |Real.log (Real.log x) - Real.log (Real.log (⌊x⌋₊ : ℝ))| ≤ Real.log 2 := by
  have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hn : (2:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn2
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx2 : x < 2 * (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hln : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hle : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlx : Real.log x ≤ 2 * Real.log (⌊x⌋₊ : ℝ) := by
    have h := Real.log_le_log (by linarith) hx2.le
    rw [Real.log_mul (by norm_num) (by linarith)] at h
    have hl2 : Real.log 2 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_le_log (by norm_num) hn
    linarith
  have h1 : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) := Real.log_le_log hln hle
  have h2 : Real.log (Real.log x) ≤ Real.log 2 + Real.log (Real.log (⌊x⌋₊ : ℝ)) := by
    have h := Real.log_le_log (by linarith) hlx
    rw [Real.log_mul (by norm_num) hln.ne'] at h
    exact h
  rw [abs_le]
  constructor <;> linarith

theorem mertens_second : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 / (p : ℝ))) - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC⟩ := ms_reciprocal_nat
  refine ⟨C + Real.log 2, fun x hx => ?_⟩
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1 := hC ⌊x⌋₊ hn
  have h2 := ms_loglog_floor x hx
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

noncomputable def ekL (N : ℕ) : ℝ := Real.log (Real.log N)

noncomputable def ekX (N : ℕ) : ℝ := Real.exp (Real.log N / Real.log (Real.log (Real.log N)))

noncomputable def ekP (x : ℝ) : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

noncomputable def ekMu (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1 / (p : ℝ))

noncomputable def ekS (P : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ P, ((if p ∣ n then (1 : ℝ) else 0) - 1 / (p : ℝ))

noncomputable def ekSA (P A : Finset ℕ) : ℝ := ∑ p ∈ P, ((if p ∈ A then (1 : ℝ) else 0) - 1 / (p : ℝ))

noncomputable def ekW (P A : Finset ℕ) : ℝ := (∏ p ∈ A, (1 / (p : ℝ))) * ∏ p ∈ P \ A, (1 - 1 / (p : ℝ))

noncomputable def sieveMoment (P : Finset ℕ) (N k : ℕ) : ℝ := (1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ekS P n ^ k

noncomputable def modelMoment (P : Finset ℕ) (k : ℕ) : ℝ := ∑ A ∈ P.powerset, ekW P A * ekSA P A ^ k

noncomputable def sieveCF (P : Finset ℕ) (N : ℕ) (τ : ℝ) : ℂ := (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ))

noncomputable def modelCF (P : Finset ℕ) (τ : ℝ) : ℂ := ∑ A ∈ P.powerset, ((ekW P A : ℝ) : ℂ) * Complex.exp (Complex.I * (τ : ℂ) * ((ekSA P A : ℝ) : ℂ))

theorem ek_taylor_R_deriv (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)) -
      ∑ j ∈ Finset.range (m + 1), (Complex.I * (s : ℂ)) ^ j / (j.factorial : ℂ))
      (Complex.I * (Complex.exp (Complex.I * (t : ℂ)) -
      ∑ j ∈ Finset.range m, (Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I t := by
    have := ((hasDerivAt_id t).ofReal_comp).const_mul Complex.I
    simpa using this
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)))
      (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) t := h1.cexp
  have hterm : ∀ k : ℕ, HasDerivAt (fun s : ℝ => (Complex.I * (s : ℂ)) ^ (k + 1) /
      ((k + 1).factorial : ℂ)) (Complex.I * ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ))) t := by
    intro k
    have := (h1.pow (k + 1)).div_const ((k + 1).factorial : ℂ)
    convert this using 1
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
  have hfun : (fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)) -
      ∑ j ∈ Finset.range (m + 1), (Complex.I * (s : ℂ)) ^ j / (j.factorial : ℂ)) =
      fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)) -
      (∑ k ∈ Finset.range m, (Complex.I * (s : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ) + 1) := by
    funext s
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [hfun]
  have hs := HasDerivAt.fun_sum (u := Finset.range m)
    (A := fun k (s : ℝ) => (Complex.I * (s : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ))
    (A' := fun k => Complex.I * ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)))
    (fun k _ => hterm k)
  have := hexp.sub (hs.add_const 1)
  convert this using 1
  rw [mul_sub, Finset.mul_sum]
  ring

theorem ek_taylor_nonneg (m : ℕ) : ∀ x : ℝ, 0 ≤ x →
    ‖Complex.exp (Complex.I * (x : ℂ)) -
      ∑ j ∈ Finset.range m, (Complex.I * (x : ℂ)) ^ j / (j.factorial : ℂ)‖ ≤
      x ^ m / (m.factorial : ℝ) := by
  induction m with
  | zero =>
    intro x _
    simp [Complex.norm_exp_I_mul_ofReal]
  | succ m ih =>
    intro x hx
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)) -
        ∑ j ∈ Finset.range (m + 1), (Complex.I * (s : ℂ)) ^ j / (j.factorial : ℂ))
      (f' := fun t : ℝ => Complex.I * (Complex.exp (Complex.I * (t : ℂ)) -
        ∑ j ∈ Finset.range m, (Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ)))
      (a := 0) (b := x)
      (B := fun t : ℝ => t ^ (m + 1) / ((m + 1).factorial : ℝ))
      (B' := fun t : ℝ => t ^ m / (m.factorial : ℝ))
      (fun t _ => (ek_taylor_R_deriv m t).continuousAt.continuousWithinAt)
      (fun t _ => (ek_taylor_R_deriv m t).hasDerivWithinAt)
      (by simp [Finset.sum_range_succ'])
      (by
        intro t
        have := (hasDerivAt_pow (m + 1) t).div_const ((m + 1).factorial : ℝ)
        convert this using 1
        have hk : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        have hk1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        rw [Nat.factorial_succ, Nat.add_sub_cancel]
        push_cast
        field_simp)
      (by
        intro t ht
        rw [norm_mul, Complex.norm_I, one_mul]
        exact ih t ht.1)
    exact key ⟨hx, le_rfl⟩

theorem ek_exp_taylor (x : ℝ) (m : ℕ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) -
      ∑ j ∈ Finset.range m, (Complex.I * (x : ℂ)) ^ j / (j.factorial : ℂ)‖ ≤
      |x| ^ m / (m.factorial : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact ek_taylor_nonneg m x hx
  · rw [abs_of_neg hx]
    have h := ek_taylor_nonneg m (-x) (by linarith)
    rw [← Complex.norm_conj]
    convert h using 2
    simp [map_sub, map_sum, map_div₀, map_pow, map_mul, Complex.conj_I,
      Complex.conj_ofReal, map_natCast, ← Complex.exp_conj]

theorem ek_avg_close (N : ℕ) (f g : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ n ∈ Finset.Icc 1 N, |f n - g n| ≤ ε) :
    ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * ((f n : ℝ) : ℂ)) -
      (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * ((g n : ℝ) : ℂ))‖ ≤ ε := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hε]
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  have hpt : ∀ n ∈ Finset.Icc 1 N, ‖Complex.exp (Complex.I * ((f n : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((g n : ℝ) : ℂ))‖ ≤ ε := by
    intro n hn
    have e : Complex.exp (Complex.I * ((f n : ℝ) : ℂ)) - Complex.exp (Complex.I * ((g n : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((g n : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * (((f n - g n : ℝ)) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
    have h1 : ‖Complex.exp (Complex.I * ((g n : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [e, norm_mul, h1, one_mul]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
    rw [Real.norm_eq_abs]; exact h n hn
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hpt)
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by simp
  rw [hn]
  calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (N * ε) := by gcongr
    _ = ε := by field_simp

theorem ek_trunc (x : ℝ) (hx : 1 < x) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (ArithmeticFunction.cardDistinctFactors n : ℝ) -
        ∑ p ∈ ekP x, (if p ∣ n then (1:ℝ) else 0) ∧
    (ArithmeticFunction.cardDistinctFactors n : ℝ) -
        ∑ p ∈ ekP x, (if p ∣ n then (1:ℝ) else 0) ≤ Real.log n / Real.log x := by
  classical
  have hn0 : n ≠ 0 := by omega
  set L := n.primeFactors.filter (fun p => p ∉ ekP x) with hL
  have hω : (ArithmeticFunction.cardDistinctFactors n : ℝ) = (n.primeFactors.card : ℝ) := by
    congr 1
    try (rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]; rfl)
  have hsum : ∑ p ∈ ekP x, (if p ∣ n then (1:ℝ) else 0) =
      ((n.primeFactors.filter (fun p => p ∈ ekP x)).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 2
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ekP, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3, hn0⟩, h1, h2⟩
    · rintro ⟨⟨h2, h3, _⟩, h1, _⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have hcard : (n.primeFactors.card : ℝ) =
      ((n.primeFactors.filter (fun p => p ∈ ekP x)).card : ℝ) + (L.card : ℝ) := by
    rw [← Finset.card_filter_add_card_filter_not (fun p => p ∈ ekP x)]
    push_cast
    try rfl
  rw [hω, hsum, hcard, add_sub_cancel_left]
  refine ⟨by positivity, ?_⟩
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hbig : ∀ p ∈ L, x ≤ (p:ℝ) := by
    intro p hp
    rw [hL, Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, _, _⟩, hnot⟩ := hp
    simp only [ekP, Finset.mem_filter, Finset.mem_range, not_and] at hnot
    have : ¬ p < ⌊x⌋₊ + 1 := fun h => hnot h hpp
    have h2 : ⌊x⌋₊ + 1 ≤ p := by omega
    have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h4 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h2
    push_cast at h4
    linarith
  have hprod : x ^ L.card ≤ (n:ℝ) := by
    calc x ^ L.card = ∏ p ∈ L, x := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ L, (p:ℝ) := Finset.prod_le_prod₀ (fun _ _ => hx0.le) hbig
      _ ≤ n := by
        have hd : (∏ p ∈ L, p) ∣ n :=
          (Finset.prod_dvd_prod_of_subset L n.primeFactors (fun p => p)
            (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
        have := Nat.le_of_dvd (by omega) hd
        rw [← Nat.cast_prod]
        exact_mod_cast this
  rw [le_div_iff₀ hlogx]
  have := Real.log_le_log (pow_pos hx0 _) hprod
  rw [Real.log_pow] at this
  linarith

theorem ek_L_tendsto : Tendsto ekL atTop atTop := by
  unfold ekL
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem ek_X_eventually : ∀ᶠ N : ℕ in atTop, 2 ≤ ekX N ∧ ekX N ≤ N := by
  have h0 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp h0
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  filter_upwards [h0.eventually_ge_atTop 1, h1.eventually_ge_atTop 1,
    h2.eventually_ge_atTop 1, eventually_ge_atTop 1] with N ha hb hc hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold ekX
  set a := Real.log (N : ℝ) with ha_def
  have hlb : Real.log (Real.log a) ≤ Real.log a - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hla : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hL3pos : 0 < Real.log (Real.log a) := by linarith
  constructor
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    refine le_trans he (Real.exp_le_exp.2 ?_)
    rw [le_div_iff₀ hL3pos]; linarith
  · calc Real.exp (a / Real.log (Real.log a)) ≤ Real.exp a :=
          Real.exp_le_exp.2 (div_le_self (by linarith) hc)
      _ = N := Real.exp_log hNpos

theorem ek_trunc_small :
    Tendsto (fun N : ℕ => Real.log N / Real.log (ekX N) / Real.sqrt (ekL N)) atTop (𝓝 0) := by
  have hL : Tendsto ekL atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1/2:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have h2 := h1.comp hL
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N:ℝ) ≠ 0 := by
    have : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact (Real.log_pos this).ne'
  simp only [Function.comp, ekX, ekL, Real.log_exp, Real.sqrt_eq_rpow]
  rw [div_div_cancel₀ hlog]

theorem ek_center :
    Tendsto (fun N : ℕ => (ekL N - ekMu (ekP (ekX N))) / Real.sqrt (ekL N)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := mertens_second
  have hs : Tendsto (fun N => Real.sqrt (ekL N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ek_L_tendsto
  have hf : Tendsto (fun s : ℝ => 2 * (Real.log s / s) + |C| * s⁻¹) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at h1
    simpa using (h1.const_mul 2).add (tendsto_inv_atTop_zero.const_mul |C|)
  have hg := hf.comp hs
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [ek_X_eventually, ek_L_tendsto.eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 2] with N hX hL hN
  simp only [Function.comp, Real.norm_eq_abs]
  have hLpos : 0 < ekL N := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hlogL : 1 ≤ Real.log (ekL N) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL
  have hN1 : (1:ℝ) < N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < Real.log N := Real.log_pos hN1
  have hXlog : Real.log (ekX N) = Real.log N / Real.log (ekL N) := by
    simp only [ekX, Real.log_exp]; rfl
  have hloglog : Real.log (Real.log (ekX N)) = ekL N - Real.log (Real.log (ekL N)) := by
    rw [hXlog, Real.log_div hNpos.ne' (by linarith : Real.log (ekL N) ≠ 0)]; rfl
  have hM := hC (ekX N) hX.1
  have hM' : |ekMu (ekP (ekX N)) - (ekL N - Real.log (Real.log (ekL N)))| ≤ C := by
    rw [← hloglog]; exact hM
  have hll0 : 0 ≤ Real.log (Real.log (ekL N)) := Real.log_nonneg hlogL
  have hll : Real.log (Real.log (ekL N)) ≤ Real.log (ekL N) :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hsq : 0 < Real.sqrt (ekL N) := Real.sqrt_pos.2 hLpos
  rw [abs_div, abs_of_pos hsq, Real.log_sqrt hLpos.le, div_le_iff₀ hsq]
  have key : |ekL N - ekMu (ekP (ekX N))| ≤ Real.log (ekL N) + |C| := by
    rw [abs_le] at hM' ⊢
    constructor <;> linarith [le_abs_self C]
  calc |ekL N - ekMu (ekP (ekX N))| ≤ Real.log (ekL N) + |C| := key
    _ = (2 * (Real.log (ekL N) / 2 / √(ekL N)) + |C| * (√(ekL N))⁻¹) * √(ekL N) := by
      field_simp

theorem ek_mu_ratio : Tendsto (fun N : ℕ => ekMu (ekP (ekX N)) / ekL N) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := mertens_second
  have hL := ek_L_tendsto
  have hlim : Tendsto (fun x : ℝ => (Real.log x + C) / x) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun x : ℝ => C / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr ?_
    intro x
    simp only [pow_one, one_mul, add_zero, add_div]
  have hlim2 := hlim.comp hL
  have hsq : Tendsto (fun N : ℕ => ekMu (ekP (ekX N)) / ekL N - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim2
    filter_upwards [ek_X_eventually, hL.eventually (eventually_ge_atTop (Real.exp 1)),
      eventually_ge_atTop 2] with N hX hLe hN
    have hLpos : 0 < ekL N := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hlogL : 1 ≤ Real.log (ekL N) := by
      have := Real.log_le_log (Real.exp_pos 1) hLe
      rwa [Real.log_exp] at this
    have hlogN : 0 < Real.log (N : ℝ) := by
      apply Real.log_pos
      have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    have hlogX : Real.log (ekX N) = Real.log N / Real.log (ekL N) := by
      unfold ekX ekL
      rw [Real.log_exp]
    have hll : Real.log (Real.log (ekX N)) = ekL N - Real.log (Real.log (ekL N)) := by
      rw [hlogX, Real.log_div hlogN.ne' (by linarith)]
      rfl
    have hm := hC (ekX N) hX.1
    have hm' : |ekMu (ekP (ekX N)) - Real.log (Real.log (ekX N))| ≤ C := hm
    rw [hll] at hm'
    have h0 : 0 ≤ Real.log (Real.log (ekL N)) := Real.log_nonneg hlogL
    have h1 : Real.log (Real.log (ekL N)) ≤ Real.log (ekL N) := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (ekL N))
      linarith
    rw [Real.norm_eq_abs, div_sub_one hLpos.ne', abs_div, abs_of_pos hLpos]
    show _ ≤ (Real.log (ekL N) + C) / ekL N
    gcongr
    rw [abs_le] at hm' ⊢
    constructor <;> linarith [hm'.1, hm'.2]
  have := hsq.add_const 1
  simpa using this

theorem ek_card_small (j : ℕ) :
    Tendsto (fun N : ℕ => (2 * ((ekP (ekX N)).card : ℝ)) ^ j / N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL3 : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N:ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hlog)
  have hup : Tendsto (fun N : ℕ => (4:ℝ)^j * Real.exp (-(Real.log (N:ℝ) / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -(Real.log (N:ℝ) / 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hlog.atTop_div_const (by norm_num))
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul ((4:ℝ)^j)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [hL3.eventually_ge_atTop (2 * ((j:ℝ) + 1)), eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 (by omega)
    have hx : ekX N = Real.exp (Real.log (N:ℝ) / Real.log (Real.log (Real.log (N:ℝ)))) := rfl
    set a := Real.log (N:ℝ) with ha_def
    have ha : 0 ≤ a := Real.log_nonneg (by exact_mod_cast hN1)
    have hjpos : (0:ℝ) < 2 * ((j:ℝ)+1) := by positivity
    have hL3pos : 0 < Real.log (Real.log a) := lt_of_lt_of_le hjpos hN
    have hq : a / Real.log (Real.log a) ≤ a / (2*((j:ℝ)+1)) :=
      div_le_div_of_nonneg_left ha hjpos hN
    have hq0 : 0 ≤ a / Real.log (Real.log a) := div_nonneg ha hL3pos.le
    have hx1 : 1 ≤ ekX N := by rw [hx]; exact Real.one_le_exp hq0
    have hcard : (((ekP (ekX N)).card : ℕ) : ℝ) ≤ ekX N + 1 := by
      have h1 : (ekP (ekX N)).card ≤ ⌊ekX N⌋₊ + 1 := by
        unfold ekP; exact (Finset.card_filter_le _ _).trans (by simp)
      have h2 : ((⌊ekX N⌋₊ : ℕ) : ℝ) ≤ ekX N := Nat.floor_le (by linarith)
      have h3 : (((ekP (ekX N)).card : ℕ) : ℝ) ≤ ((⌊ekX N⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h3; linarith
    have hpow : (2 * ((ekP (ekX N)).card : ℝ)) ^ j ≤ (4:ℝ)^j * Real.exp (a/2) := by
      have hb : 2 * ((ekP (ekX N)).card : ℝ) ≤ 4 * ekX N := by linarith
      calc (2 * ((ekP (ekX N)).card : ℝ)) ^ j ≤ (4 * ekX N)^j :=
            pow_le_pow_left₀ (by positivity) hb j
        _ = (4:ℝ)^j * Real.exp ((j:ℝ) * (a / Real.log (Real.log a))) := by
            rw [mul_pow, hx, Real.exp_nat_mul]
        _ ≤ (4:ℝ)^j * Real.exp (a/2) := by
          gcongr
          have e : (j:ℝ) * (a/(2*((j:ℝ)+1))) = a/2 - a/(2*((j:ℝ)+1)) := by
            field_simp; ring
          have h0 : 0 ≤ a/(2*((j:ℝ)+1)) := div_nonneg ha hjpos.le
          have h4 : (j:ℝ) * (a / Real.log (Real.log a)) ≤ (j:ℝ) * (a/(2*((j:ℝ)+1))) :=
            mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg j)
          linarith
    have hNe : (N:ℝ) = Real.exp (a/2) * Real.exp (a/2) := by
      rw [← Real.exp_add, add_halves, ha_def, Real.exp_log hNpos]
    have hE := Real.exp_pos (a/2)
    calc (2 * ((ekP (ekX N)).card : ℝ)) ^ j / N ≤ (4:ℝ)^j * Real.exp (a/2) / N :=
          div_le_div_of_nonneg_right hpow hNpos.le
      _ = (4:ℝ)^j * Real.exp (-(a/2)) := by
          rw [hNe, Real.exp_neg]; field_simp

theorem ek_mc_arith (N d : ℕ) (hN : 1 ≤ N) (hd : 0 < d) :
    |(1 / (N : ℝ)) * ((N / d : ℕ) : ℝ) - 1 / (d : ℝ)| ≤ 1 / (N : ℝ) := by
  have h1 : N / d * d ≤ N := Nat.div_mul_le_self N d
  have h2 : N < N / d * d + d := Nat.lt_div_mul_add hd
  have r1 : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast h1
  have r2 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast h2
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [abs_sub_le_iff]
  constructor
  · have : (1 / (N : ℝ)) * ((N / d : ℕ) : ℝ) ≤ 1 / d := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ hNp hdp]; nlinarith
    have : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith
  · have : 1 / (d : ℝ) ≤ (((N / d : ℕ) : ℝ) + 1) / N := by
      rw [div_le_div_iff₀ hdp hNp]; nlinarith
    have e : (((N / d : ℕ) : ℝ) + 1) / N = 1 / N * ((N / d : ℕ) : ℝ) + 1 / N := by ring
    linarith

theorem ek_mc_sieve (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 / (N : ℝ)) * (if ∀ p ∈ D, p ∣ n then (1 : ℝ) else 0) =
      (1 / (N : ℝ)) * ((N / ∏ p ∈ D, p : ℕ) : ℝ) := by
  have hiff : ∀ n : ℕ, (∀ p ∈ D, p ∣ n) ↔ (∏ p ∈ D, p) ∣ n := fun n =>
    ⟨fun h => Finset.prod_primes_dvd n (fun p hp => (hD p hp).prime) h,
     fun h p hp => (Finset.dvd_prod_of_mem _ hp).trans h⟩
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
  simp only [hiff]
  rw [← Finset.mul_sum, Finset.sum_boole, hI, Nat.Ioc_filter_dvd_card_eq_div]

theorem ek_mc_model (P D : Finset ℕ) (hD : D ⊆ P) :
    ∑ A ∈ P.powerset, ekW P A * (if D ⊆ A then (1 : ℝ) else 0) = ∏ p ∈ D, (1 / (p : ℝ)) := by
  classical
  have hprod := Finset.prod_add (fun p : ℕ => 1 / (p : ℝ))
    (fun p : ℕ => if p ∈ D then (0 : ℝ) else 1 - 1 / (p : ℝ)) P
  calc ∑ A ∈ P.powerset, ekW P A * (if D ⊆ A then (1 : ℝ) else 0)
      = ∑ t ∈ P.powerset, (∏ p ∈ t, (1 / (p : ℝ))) *
          ∏ p ∈ P \ t, (if p ∈ D then (0 : ℝ) else 1 - 1 / (p : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases h : D ⊆ t
        · rw [if_pos h, mul_one]
          unfold ekW
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          rw [if_neg]
          intro hpD
          exact (Finset.mem_sdiff.1 hp).2 (h hpD)
        · rw [if_neg h, mul_zero]
          obtain ⟨p, hpD, hpt⟩ := Finset.not_subset.1 h
          symm
          apply mul_eq_zero_of_right
          apply Finset.prod_eq_zero (i := p) (Finset.mem_sdiff.2 ⟨hD hpD, hpt⟩)
          simp [hpD]
    _ = ∏ p ∈ P, (1 / (p : ℝ) + (if p ∈ D then (0 : ℝ) else 1 - 1 / (p : ℝ))) := hprod.symm
    _ = ∏ p ∈ P, (if p ∈ D then 1 / (p : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro p _
        split_ifs <;> ring
    _ = ∏ p ∈ P ∩ D, (1 / (p : ℝ)) := Finset.prod_ite_mem _ _ _
    _ = ∏ p ∈ D, (1 / (p : ℝ)) := by rw [Finset.inter_eq_right.2 hD]

theorem ek_mc_term {ι : Type*} [DecidableEq ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (hN : 1 ≤ N) (T : Finset ι) (x : ι → ℕ) (hx : ∀ i ∈ T, x i ∈ P) :
    |∑ n ∈ Finset.Icc 1 N, (1 / (N : ℝ)) * (if ∀ i ∈ T, x i ∣ n then (1 : ℝ) else 0) -
      ∑ A ∈ P.powerset, ekW P A * (if ∀ i ∈ T, x i ∈ A then (1 : ℝ) else 0)| ≤ 1 / (N : ℝ) := by
  have hDP : T.image x ⊆ P := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact hx i hi
  have h1 : ∀ n : ℕ, (∀ i ∈ T, x i ∣ n) ↔ ∀ p ∈ T.image x, p ∣ n := fun n => by
    constructor
    · intro h p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact h i hi
    · intro h i hi
      exact h _ (Finset.mem_image_of_mem x hi)
  have h2 : ∀ A : Finset ℕ, (∀ i ∈ T, x i ∈ A) ↔ T.image x ⊆ A := fun A => by
    constructor
    · intro h p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact h i hi
    · intro h i hi
      exact h (Finset.mem_image_of_mem x hi)
  simp only [h1, h2]
  rw [ek_mc_sieve (T.image x) (fun p hp => hP p (hDP hp)) N, ek_mc_model P (T.image x) hDP]
  have hd : ∏ p ∈ T.image x, (1 / (p : ℝ)) = 1 / (((∏ p ∈ T.image x, p : ℕ)) : ℝ) := by
    rw [Nat.cast_prod]
    simp only [one_div, Finset.prod_inv_distrib]
  rw [hd]
  exact ek_mc_arith N _ hN (Finset.prod_pos fun p hp => (hP p (hDP hp)).pos)

theorem ek_mc_expand {β : Type*} (P : Finset ℕ) (k : ℕ) (S : Finset β) (μ : β → ℝ)
    (I : ℕ → β → Prop) [∀ p b, Decidable (I p b)] :
    ∑ b ∈ S, μ b * (∑ p ∈ P, ((if I p b then (1 : ℝ) else 0) - 1 / (p : ℝ))) ^ k =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          (∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))) *
            ∑ b ∈ S, μ b * (if ∀ i ∈ T, I (x i) b then (1 : ℝ) else 0) := by
  have hexp : ∀ b, (∑ p ∈ P, ((if I p b then (1 : ℝ) else 0) - 1 / (p : ℝ))) ^ k =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          (if ∀ i ∈ T, I (x i) b then (1 : ℝ) else 0) *
            ∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ))) := by
    intro b
    rw [← Fin.prod_const, Finset.prod_univ_sum (fun _ : Fin k => P)
      (fun _ p => (if I p b then (1 : ℝ) else 0) - 1 / (p : ℝ))]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.prod_boole]
    congr
  calc _ = ∑ b ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          μ b * ((if ∀ i ∈ T, I (x i) b then (1 : ℝ) else 0) *
            ∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hexp b, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset, ∑ b ∈ S,
          μ b * ((if ∀ i ∈ T, I (x i) b then (1 : ℝ) else 0) *
            ∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro T _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring

theorem ek_moment_compare (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N k : ℕ) (hN : 1 ≤ N) :
    |sieveMoment P N k - modelMoment P k| ≤ (2 * (P.card : ℝ)) ^ k / N := by
  have hS : sieveMoment P N k = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          (∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))) *
            ∑ n ∈ Finset.Icc 1 N, (1 / (N : ℝ)) * (if ∀ i ∈ T, x i ∣ n then (1 : ℝ) else 0) := by
    unfold sieveMoment ekS
    rw [Finset.mul_sum]
    exact ek_mc_expand P k (Finset.Icc 1 N) (fun _ => 1 / (N : ℝ)) (fun p n => p ∣ n)
  have hM : modelMoment P k = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          (∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))) *
            ∑ A ∈ P.powerset, ekW P A * (if ∀ i ∈ T, x i ∈ A then (1 : ℝ) else 0) := by
    unfold modelMoment ekSA
    exact ek_mc_expand P k P.powerset (fun A => ekW P A) (fun p A => p ∈ A)
  rw [hS, hM]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset, (1 / (N : ℝ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T _ => ?_)
        rw [abs_mul]
        have hxP : ∀ i, x i ∈ P := Fintype.mem_piFinset.1 hx
        have hc : |∏ i ∈ Finset.univ \ T, (-(1 / (x i : ℝ)))| ≤ 1 := by
          rw [Finset.abs_prod]
          apply Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
          intro i _
          have hp1 : (1 : ℝ) < x i := by exact_mod_cast (hP _ (hxP i)).one_lt
          rw [abs_neg, abs_of_nonneg (by positivity), div_le_one (by linarith)]
          exact hp1.le
        have ht := ek_mc_term P hP N hN T x (fun i _ => hxP i)
        have hm := mul_le_mul hc ht (abs_nonneg _) zero_le_one
        rw [one_mul] at hm
        convert hm
    _ = (2 * (P.card : ℝ)) ^ k / N := by
        simp only [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
          Fintype.card_piFinset, Finset.prod_const, nsmul_eq_mul]
        push_cast
        ring

theorem ek_mb_prod (P : Finset ℕ) (l : ℝ) :
    ∑ A ∈ P.powerset, ekW P A * Real.exp (l * ekSA P A) =
      ∏ p ∈ P, ((1 / (p:ℝ)) * Real.exp (l * (1 - 1 / (p:ℝ))) +
        (1 - 1 / (p:ℝ)) * Real.exp (l * (0 - 1 / (p:ℝ)))) := by
  classical
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mem_powerset] at hA
  unfold ekW ekSA
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_sdiff hA]
  have e1 : ∏ p ∈ A, Real.exp (l * ((if p ∈ A then (1:ℝ) else 0) - 1 / (p:ℝ))) =
      ∏ p ∈ A, Real.exp (l * (1 - 1 / (p:ℝ))) :=
    Finset.prod_congr rfl fun p hp => by rw [if_pos hp]
  have e2 : ∏ p ∈ P \ A, Real.exp (l * ((if p ∈ A then (1:ℝ) else 0) - 1 / (p:ℝ))) =
      ∏ p ∈ P \ A, Real.exp (l * (0 - 1 / (p:ℝ))) :=
    Finset.prod_congr rfl fun p hp => by rw [if_neg (Finset.mem_sdiff.1 hp).2]
  rw [e1, e2, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem ek_mb_factor (q l : ℝ) :
    q * Real.exp (l * (1 - q)) + (1 - q) * Real.exp (l * (0 - q)) ≤
      Real.exp (q * (Real.exp l - 1 - l)) := by
  have h1 : Real.exp (l * (1 - q)) = Real.exp l * Real.exp (-(l*q)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (l * (0 - q)) = Real.exp (-(l*q)) := by congr 1; ring
  have h3 : Real.exp (q * (Real.exp l - 1 - l)) =
      Real.exp (q * (Real.exp l - 1)) * Real.exp (-(l*q)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2, h3]
  have h4 := Real.add_one_le_exp (q * (Real.exp l - 1))
  have h5 := Real.exp_pos (-(l*q))
  nlinarith [mul_le_mul_of_nonneg_right h4 h5.le]

theorem ek_mb_expsum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (l : ℝ) :
    ∑ A ∈ P.powerset, ekW P A * Real.exp (l * ekSA P A) ≤
      Real.exp (ekMu P * (Real.exp l - 1 - l)) := by
  rw [ek_mb_prod]
  calc _ ≤ ∏ p ∈ P, Real.exp (1 / (p:ℝ) * (Real.exp l - 1 - l)) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
          have h0 : 0 ≤ 1 / (p:ℝ) := by positivity
          have h1 : 1 / (p:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
          have e1 := Real.exp_pos (l * (1 - 1 / (p:ℝ)))
          have e2 := Real.exp_pos (l * (0 - 1 / (p:ℝ)))
          have h2 : 0 ≤ 1 - 1 / (p:ℝ) := by linarith
          exact add_nonneg (mul_nonneg h0 e1.le) (mul_nonneg h2 e2.le)
        · intro p _
          exact ek_mb_factor (1 / (p:ℝ)) l
    _ = Real.exp (ekMu P * (Real.exp l - 1 - l)) := by
        rw [← Real.exp_sum, ekMu, Finset.sum_mul]

theorem ek_mb_g (y : ℝ) (hy : 0 ≤ y) :
    Real.exp y - 1 - y ≤ y ^ 2 * Real.exp y ∧
      Real.exp (-y) - 1 - (-y) ≤ y ^ 2 * Real.exp y := by
  have hEF : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have H1 := Real.add_one_le_exp (-y)
  have H2 := Real.add_one_le_exp y
  have hE := Real.exp_pos y
  have hF := Real.exp_pos (-y)
  have hE1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have A : Real.exp y - 1 ≤ y * Real.exp y := by
    nlinarith [mul_le_mul_of_nonneg_left H1 hE.le]
  have B : Real.exp (-y) + y * Real.exp (-y) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left H2 hF.le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left A hy]
  · nlinarith [mul_le_mul_of_nonneg_left H1 hy, mul_le_mul_of_nonneg_left hE1 (sq_nonneg y)]

theorem ek_mb_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (K : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    modelMoment P (2 * K) ≤ ((2 * K).factorial : ℝ) *
      (2 * Real.exp (a ^ 2 * Real.exp a) / a ^ (2 * K)) * (max 1 (ekMu P)) ^ K := by
  obtain ⟨M, hM⟩ : ∃ M, M = max 1 (ekMu P) := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := hM ▸ le_max_left _ _
  have hμM : ekMu P ≤ M := hM ▸ le_max_right _ _
  have hμ0 : 0 ≤ ekMu P := by
    unfold ekMu; exact Finset.sum_nonneg fun p _ => by positivity
  have hsM : 1 ≤ Real.sqrt M := Real.one_le_sqrt.2 hM1
  obtain ⟨l, hl⟩ : ∃ l, l = a / Real.sqrt M := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; exact div_pos (by linarith) (by linarith)
  have hla : l ≤ a := by rw [hl]; exact div_le_self (by linarith) hsM
  have hl2 : l ^ 2 * M = a ^ 2 := by
    rw [hl, div_pow, Real.sq_sqrt (by linarith)]
    have : M ≠ 0 := by positivity
    field_simp
  have hw : ∀ A ∈ P.powerset, 0 ≤ ekW P A := by
    intro A _
    unfold ekW
    apply mul_nonneg
    · apply Finset.prod_nonneg; intro p _; positivity
    · apply Finset.prod_nonneg; intro p hp
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (hP p (Finset.mem_sdiff.1 hp).1).one_lt.le
      have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith
  have hel : Real.exp l ≤ Real.exp a := Real.exp_le_exp.2 hla
  have hc1 := (ek_mb_g l hl0.le).1
  have hc2 := (ek_mb_g l hl0.le).2
  have hB : ekMu P * (l ^ 2 * Real.exp l) ≤ a ^ 2 * Real.exp a := by
    calc ekMu P * (l ^ 2 * Real.exp l) ≤ M * (l ^ 2 * Real.exp l) :=
          mul_le_mul_of_nonneg_right hμM (by positivity)
      _ = a ^ 2 * Real.exp l := by rw [← hl2]; ring
      _ ≤ a ^ 2 * Real.exp a := mul_le_mul_of_nonneg_left hel (by positivity)
  have hg1 := (mul_le_mul_of_nonneg_left hc1 hμ0).trans hB
  have hg2 := (mul_le_mul_of_nonneg_left hc2 hμ0).trans hB
  have hE1 := (ek_mb_expsum P hP l).trans (Real.exp_le_exp.2 hg1)
  have hE2 := (ek_mb_expsum P hP (-l)).trans (Real.exp_le_exp.2 hg2)
  have hf : (0:ℝ) < ((2*K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpt : ∀ A, ekSA P A ^ (2*K) * l ^ (2*K) ≤ ((2*K).factorial : ℝ) *
      (Real.exp (l * ekSA P A) + Real.exp ((-l) * ekSA P A)) := by
    intro A
    have h := Real.pow_div_factorial_le_exp (|l * ekSA P A|) (abs_nonneg _) (2*K)
    rw [div_le_iff₀ hf, (even_two_mul K).pow_abs, mul_pow] at h
    have h2 : Real.exp |l * ekSA P A| ≤ Real.exp (l * ekSA P A) + Real.exp ((-l) * ekSA P A) := by
      rcases abs_cases (l * ekSA P A) with ⟨h3, _⟩ | ⟨h3, _⟩
      · rw [h3]; have := Real.exp_pos ((-l) * ekSA P A); linarith
      · rw [h3, show -(l * ekSA P A) = (-l) * ekSA P A by ring]
        have := Real.exp_pos (l * ekSA P A); linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hf.le
    nlinarith [h4]
  have hlpos : 0 < l ^ (2*K) := pow_pos hl0 _
  have hsum : modelMoment P (2*K) * l ^ (2*K) ≤
      ((2*K).factorial : ℝ) * (2 * Real.exp (a ^ 2 * Real.exp a)) := by
    unfold modelMoment
    rw [Finset.sum_mul]
    calc _ ≤ ∑ A ∈ P.powerset, ekW P A * (((2*K).factorial : ℝ) *
          (Real.exp (l * ekSA P A) + Real.exp ((-l) * ekSA P A))) := by
          refine Finset.sum_le_sum fun A hA => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hpt A) (hw A hA)
      _ = ((2*K).factorial : ℝ) * (∑ A ∈ P.powerset, ekW P A * Real.exp (l * ekSA P A) +
          ∑ A ∈ P.powerset, ekW P A * Real.exp ((-l) * ekSA P A)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun A _ => by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hf.le
          linarith
  have hkey : l ^ (2*K) * M ^ K = a ^ (2*K) := by
    rw [pow_mul, pow_mul, ← mul_pow, hl2]
  rw [← hkey]
  have hMK : 0 < M ^ K := pow_pos (by linarith) _
  have e : ((2*K).factorial : ℝ) * (2 * Real.exp (a ^ 2 * Real.exp a) / (l ^ (2*K) * M ^ K)) * M ^ K
      = ((2*K).factorial : ℝ) * (2 * Real.exp (a ^ 2 * Real.exp a)) / l ^ (2*K) := by
    field_simp
  rw [e, le_div_iff₀ hlpos]
  exact hsum

noncomputable def ekMbI (m : ℕ) : ℝ := ⨅ a : {a : ℝ // 1 ≤ a}, 2 * Real.exp (a.1 ^ 2 * Real.exp a.1) / a.1 ^ m

theorem ek_model_moment_bound : ∃ C : ℕ → ℝ,
    (∀ s : ℝ, Tendsto (fun m : ℕ => s ^ m * C m / (m.factorial : ℝ)) atTop (𝓝 0)) ∧
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ K : ℕ,
      modelMoment P (2 * K) ≤ C (2 * K) * (max 1 (ekMu P)) ^ K := by
  haveI : Nonempty {a : ℝ // 1 ≤ a} := ⟨⟨1, le_rfl⟩⟩
  have hlow : ∀ m, 0 ≤ ekMbI m := fun m => le_ciInf fun a =>
    div_nonneg (by positivity) (pow_nonneg (by linarith [a.2]) _)
  have hbdd : ∀ m, BddBelow (Set.range fun a : {a : ℝ // 1 ≤ a} =>
      2 * Real.exp (a.1 ^ 2 * Real.exp a.1) / a.1 ^ m) := fun m =>
    ⟨0, by
      rintro _ ⟨a, rfl⟩
      exact div_nonneg (by positivity) (pow_nonneg (by linarith [a.2]) _)⟩
  refine ⟨fun m => (m.factorial : ℝ) * ekMbI m, ?_, ?_⟩
  · intro s
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * |s| + 1 := ⟨_, rfl⟩
    have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg s]
    have hApos : 0 < A := by linarith
    have hup : ∀ m, ekMbI m ≤ 2 * Real.exp (A ^ 2 * Real.exp A) / A ^ m := fun m =>
      ciInf_le (hbdd m) ⟨A, hA1⟩
    have hr0 : 0 ≤ |s| / A := div_nonneg (abs_nonneg _) hApos.le
    have hr1 : |s| / A < 1 := by rw [div_lt_one hApos, hA]; linarith [abs_nonneg s]
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (2 * Real.exp (A ^ 2 * Real.exp A))
    rw [mul_zero] at hlim
    refine squeeze_zero_norm (fun m => ?_) hlim
    have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    rw [show s ^ m * ((m.factorial : ℝ) * ekMbI m) / (m.factorial : ℝ) = s ^ m * ekMbI m by
      field_simp]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hlow m), div_pow]
    calc |s| ^ m * ekMbI m ≤ |s| ^ m * (2 * Real.exp (A ^ 2 * Real.exp A) / A ^ m) :=
          mul_le_mul_of_nonneg_left (hup m) (by positivity)
      _ = 2 * Real.exp (A ^ 2 * Real.exp A) * (|s| ^ m / A ^ m) := by ring
  · intro P hP K
    have hMK : 0 < (max 1 (ekMu P)) ^ K :=
      pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _
    have hf : (0:ℝ) < ((2*K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h : modelMoment P (2*K) / (((2*K).factorial : ℝ) * (max 1 (ekMu P)) ^ K) ≤
        ekMbI (2*K) := by
      apply le_ciInf
      intro a
      rw [div_le_iff₀ (mul_pos hf hMK)]
      have := ek_mb_bound P hP K a.1 a.2
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [div_le_iff₀ (mul_pos hf hMK)] at h
    dsimp only
    calc _ ≤ _ := h
      _ = _ := by ring

theorem ek_cf_aux_taylor (τ s : ℝ) (K : ℕ) :
    ‖Complex.exp (Complex.I * (τ : ℂ) * (s : ℂ)) -
      ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * (s : ℂ) ^ j‖ ≤
      |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) * s ^ (2 * K) := by
  have h := ek_exp_taylor (τ * s) (2 * K)
  have e1 : Complex.I * ((τ * s : ℝ) : ℂ) = Complex.I * (τ : ℂ) * (s : ℂ) := by push_cast; ring
  have e2 : ∀ j ∈ Finset.range (2 * K), (Complex.I * ((τ * s : ℝ) : ℂ)) ^ j / (j.factorial : ℂ)
      = (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * (s : ℂ) ^ j := by
    intro j _; push_cast; ring
  rw [Finset.sum_congr rfl e2, e1] at h
  refine h.trans (le_of_eq ?_)
  rw [abs_mul, mul_pow, (even_two_mul K).pow_abs s]
  ring

theorem ek_cf_moment_compare (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (hN : 1 ≤ N)
    (τ : ℝ) (K : ℕ) :
    ‖sieveCF P N τ - modelCF P τ‖ ≤
      ∑ j ∈ Finset.range (2 * K), |τ| ^ j / (j.factorial : ℝ) *
          |sieveMoment P N j - modelMoment P j| +
        |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (sieveMoment P N (2 * K) + modelMoment P (2 * K)) := by
  have hw : ∀ A ∈ P.powerset, 0 ≤ ekW P A := by
    intro A _
    unfold ekW
    apply mul_nonneg
    · apply Finset.prod_nonneg; intro p _; positivity
    · apply Finset.prod_nonneg; intro p hp
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (hP p (Finset.mem_sdiff.1 hp).1).one_lt.le
      have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith
  have hs : sieveCF P N τ = ∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((sieveMoment P N j : ℝ) : ℂ) +
      (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekS P n : ℝ) : ℂ) ^ j) := by
    unfold sieveCF sieveMoment
    have : ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
        (((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ekS P n ^ j : ℝ) : ℂ)
        = (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (2 * K),
          (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((ekS P n : ℝ) : ℂ) ^ j := by
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hm : modelCF P τ = ∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((modelMoment P j : ℝ) : ℂ) +
      ∑ A ∈ P.powerset, ((ekW P A : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekSA P A : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekSA P A : ℝ) : ℂ) ^ j) := by
    unfold modelCF modelMoment
    have : ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
        ((∑ A ∈ P.powerset, ekW P A * ekSA P A ^ j : ℝ) : ℂ)
        = ∑ A ∈ P.powerset, ((ekW P A : ℝ) : ℂ) * ∑ j ∈ Finset.range (2 * K),
          (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((ekSA P A : ℝ) : ℂ) ^ j := by
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hs, hm]
  set c : ℝ := |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) with hc
  have hX : ‖∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((sieveMoment P N j : ℝ) : ℂ) -
      ∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((modelMoment P j : ℝ) : ℂ)‖ ≤
      ∑ j ∈ Finset.range (2 * K), |τ| ^ j / (j.factorial : ℝ) *
          |sieveMoment P N j - modelMoment P j| := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      Complex.norm_natCast]
  have hB : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekS P n : ℝ) : ℂ) ^ j)‖ ≤ c * sieveMoment P N (2 * K) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc 1 / (N : ℝ) * ‖∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekS P n : ℝ) : ℂ) ^ j)‖
        ≤ 1 / (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, c * ekS P n ^ (2 * K) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun n _ => ek_cf_aux_taylor _ _ K)) (by positivity)
      _ = c * sieveMoment P N (2 * K) := by
          unfold sieveMoment; rw [← Finset.mul_sum]; ring
  have hB' : ‖∑ A ∈ P.powerset, ((ekW P A : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekSA P A : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekSA P A : ℝ) : ℂ) ^ j)‖ ≤ c * modelMoment P (2 * K) := by
    calc _ ≤ ∑ A ∈ P.powerset, ekW P A * (c * ekSA P A ^ (2 * K)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A hA => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw A hA)]
          exact mul_le_mul_of_nonneg_left (ek_cf_aux_taylor _ _ K) (hw A hA)
      _ = c * modelMoment P (2 * K) := by
          unfold modelMoment; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun A _ => by ring
  have h0 := norm_sub_le
    ((∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((sieveMoment P N j : ℝ) : ℂ) -
      ∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((modelMoment P j : ℝ) : ℂ)) +
      (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekS P n : ℝ) : ℂ) ^ j))
    (∑ A ∈ P.powerset, ((ekW P A : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekSA P A : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekSA P A : ℝ) : ℂ) ^ j))
  have h1 := norm_add_le
    (∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((sieveMoment P N j : ℝ) : ℂ) -
      ∑ j ∈ Finset.range (2 * K),
      (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) * ((modelMoment P j : ℝ) : ℂ))
    ((1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (Complex.I * (τ : ℂ) * ((ekS P n : ℝ) : ℂ)) -
          ∑ j ∈ Finset.range (2 * K), (Complex.I * (τ : ℂ)) ^ j / (j.factorial : ℂ) *
            ((ekS P n : ℝ) : ℂ) ^ j))
  have heq : ∀ X Y B B' : ℂ, X + B - (Y + B') = (X - Y) + B - B' := fun _ _ _ _ => by ring
  rw [heq]
  nlinarith [h0, h1, hX, hB, hB']

theorem ek_sieve_model (t : ℝ) :
    Tendsto (fun N : ℕ => sieveCF (ekP (ekX N)) N (t / Real.sqrt (ekL N)) -
      modelCF (ekP (ekX N)) (t / Real.sqrt (ekL N))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCb⟩ := ek_model_moment_bound
  rw [Metric.tendsto_nhds]
  intro ε hε
  set s : ℝ := Real.sqrt 2 * |t| with hs
  have hs2 : s ^ 2 = 2 * t ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => by show K ≤ 2 * K; omega) tendsto_id
  have hK1 : Tendsto (fun K : ℕ => s ^ (2 * K) * C (2 * K) / ((2 * K).factorial : ℝ))
      atTop (𝓝 0) := (hC s).comp h2K
  obtain ⟨K, hK, hKpos⟩ :=
    ((hK1.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by positivity))).and
      (eventually_ge_atTop 1)).exists
  have h0 : modelMoment ∅ (2 * K) = 0 := by
    simp only [modelMoment, Finset.powerset_empty, Finset.sum_singleton, ekSA, Finset.sum_empty]
    rw [zero_pow (by omega)]
    ring
  have hCnn : 0 ≤ C (2 * K) := by
    have h := hCb ∅ (by simp) K
    have hmax : max 1 (ekMu ∅) = 1 := by simp [ekMu]
    rw [h0, hmax, one_pow, mul_one] at h
    exact h
  have hg : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (2 * K + 1),
      |t| ^ j / (j.factorial : ℝ) * ((2 * ((ekP (ekX N)).card : ℝ)) ^ j / N)) atTop (𝓝 0) := by
    rw [show (0:ℝ) = ∑ j ∈ Finset.range (2 * K + 1), |t| ^ j / (j.factorial : ℝ) * 0 by simp]
    exact tendsto_finset_sum _ fun j _ => (ek_card_small j).const_mul _
  filter_upwards [ek_L_tendsto.eventually_ge_atTop 1,
    ek_mu_ratio.eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num)),
    eventually_ge_atTop 1, hg.eventually (gt_mem_nhds (show (0:ℝ) < ε / 2 by positivity))]
    with N hL hμ hN hgN
  rw [dist_zero_right]
  set P := ekP (ekX N) with hPdef
  set L := ekL N with hLdef
  set τ := t / Real.sqrt L with hτdef
  have hL0 : 0 < L := by linarith
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    rw [hPdef] at hp
    unfold ekP at hp
    exact (Finset.mem_filter.1 hp).2
  have hμ' : ekMu P < 2 * L := (div_lt_iff₀ hL0).1 hμ
  have hmain := ek_cf_moment_compare P hP N hN τ K
  have hE : ∀ j, |sieveMoment P N j - modelMoment P j| ≤ (2 * (P.card : ℝ)) ^ j / N :=
    fun j => ek_moment_compare P hP N j hN
  have hτ : |τ| ≤ |t| := by
    rw [hτdef, abs_div, abs_of_pos (Real.sqrt_pos.2 hL0)]
    exact div_le_self (abs_nonneg t) (Real.one_le_sqrt.2 hL)
  have hτsq : τ ^ 2 * (2 * L) = s ^ 2 := by
    rw [hτdef, div_pow, Real.sq_sqrt hL0.le, hs2]
    field_simp
  have hkey : |τ| ^ (2 * K) * (2 * L) ^ K = s ^ (2 * K) := by
    rw [pow_mul, pow_mul, sq_abs, ← mul_pow, hτsq]
  have hmax : max 1 (ekMu P) ≤ 2 * L := max_le (by linarith) hμ'.le
  have hpow : (max 1 (ekMu P)) ^ K ≤ (2 * L) ^ K :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax K
  have hmm : modelMoment P (2 * K) ≤ C (2 * K) * (2 * L) ^ K :=
    le_trans (hCb P hP K) (mul_le_mul_of_nonneg_left hpow hCnn)
  have ha_nn : 0 ≤ |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) := by positivity
  have hstep1 : ∑ j ∈ Finset.range (2 * K), |τ| ^ j / (j.factorial : ℝ) *
        |sieveMoment P N j - modelMoment P j|
      ≤ ∑ j ∈ Finset.range (2 * K), |t| ^ j / (j.factorial : ℝ) *
        ((2 * (P.card : ℝ)) ^ j / N) := by
    apply Finset.sum_le_sum
    intro j _
    have hEj := hE j
    gcongr
  have hsm := (abs_le.1 (hE (2 * K))).2
  have hstep2 : |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) *
        (sieveMoment P N (2 * K) + modelMoment P (2 * K))
      ≤ |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) *
        (2 * (C (2 * K) * (2 * L) ^ K) + (2 * (P.card : ℝ)) ^ (2 * K) / N) := by
    apply mul_le_mul_of_nonneg_left _ ha_nn
    linarith
  have hstep3 : |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) * (2 * (C (2 * K) * (2 * L) ^ K)) =
      2 * (s ^ (2 * K) * C (2 * K) / ((2 * K).factorial : ℝ)) := by
    rw [← hkey]; ring
  have hstep4 : |τ| ^ (2 * K) / ((2 * K).factorial : ℝ) * ((2 * (P.card : ℝ)) ^ (2 * K) / N)
      ≤ |t| ^ (2 * K) / ((2 * K).factorial : ℝ) * ((2 * (P.card : ℝ)) ^ (2 * K) / N) := by
    gcongr
  have hgN' := hgN
  rw [Finset.sum_range_succ] at hgN'
  refine lt_of_le_of_lt hmain ?_
  refine lt_of_le_of_lt (add_le_add hstep1 hstep2) ?_
  rw [mul_add, hstep3]
  linarith [hstep4, hK]

theorem ek_modelCF_prod (P : Finset ℕ) (τ : ℝ) :
    modelCF P τ = ∏ p ∈ P, (1 + (Complex.exp (Complex.I * (τ : ℂ)) - 1) / (p : ℂ)) *
      Complex.exp (-(Complex.I * (τ : ℂ)) / (p : ℂ)) := by
  classical
  have key : ∀ p : ℕ, (1 + (Complex.exp (Complex.I * (τ : ℂ)) - 1) / (p : ℂ)) *
      Complex.exp (-(Complex.I * (τ : ℂ)) / (p : ℂ)) =
      (1 / (p : ℂ)) * Complex.exp (Complex.I * (τ : ℂ) * ((1 : ℂ) - 1 / (p : ℂ))) +
      (1 - 1 / (p : ℂ)) * Complex.exp (Complex.I * (τ : ℂ) * ((0 : ℂ) - 1 / (p : ℂ))) := by
    intro p
    have h1 : Complex.exp (Complex.I * (τ : ℂ) * ((1 : ℂ) - 1 / (p : ℂ))) =
        Complex.exp (Complex.I * (τ : ℂ)) * Complex.exp (-(Complex.I * (τ : ℂ)) / (p : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : Complex.exp (Complex.I * (τ : ℂ) * ((0 : ℂ) - 1 / (p : ℂ))) =
        Complex.exp (-(Complex.I * (τ : ℂ)) / (p : ℂ)) := by
      congr 1; ring
    rw [h1, h2]; ring
  rw [Finset.prod_congr rfl (fun p _ => key p), Finset.prod_add]
  unfold modelCF
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mem_powerset] at hA
  unfold ekW ekSA
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_sdiff hA,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have e1 : ∏ p ∈ A, Complex.exp (Complex.I * (τ : ℂ) *
      (((if p ∈ A then (1 : ℝ) else 0 : ℝ) : ℂ) - 1 / (p : ℂ))) =
      ∏ p ∈ A, Complex.exp (Complex.I * (τ : ℂ) * ((1 : ℂ) - 1 / (p : ℂ))) :=
    Finset.prod_congr rfl fun p hp => by rw [if_pos hp, Complex.ofReal_one]
  have e2 : ∏ p ∈ P \ A, Complex.exp (Complex.I * (τ : ℂ) *
      (((if p ∈ A then (1 : ℝ) else 0 : ℝ) : ℂ) - 1 / (p : ℂ))) =
      ∏ p ∈ P \ A, Complex.exp (Complex.I * (τ : ℂ) * ((0 : ℂ) - 1 / (p : ℂ))) :=
    Finset.prod_congr rfl fun p hp => by rw [if_neg (Finset.mem_sdiff.1 hp).2, Complex.ofReal_zero]
  rw [e1, e2]
  ring

theorem ek_ml_prod_diff (s : Finset ℕ) (a b : ℕ → ℂ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have haj : ‖a j‖ ≤ 1 := ha j (Finset.mem_insert_self j s)
    have hbs : ‖∏ i ∈ s, b i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) hb'
    have hrec := ih ha' hb'
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have h1 : ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
      rw [norm_mul]
      calc ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ 1 * ∑ i ∈ s, ‖a i - b i‖ :=
            mul_le_mul haj hrec (norm_nonneg _) zero_le_one
        _ = ∑ i ∈ s, ‖a i - b i‖ := one_mul _
    have h2 : ‖(a j - b j) * ∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ := by
      rw [norm_mul]
      calc ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ * 1 :=
            mul_le_mul_of_nonneg_left hbs (norm_nonneg _)
        _ = ‖a j - b j‖ := mul_one _
    have h3 := norm_add_le (a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)) ((a j - b j) * ∏ i ∈ s, b i)
    linarith

theorem ek_ml_factor_norm (τ : ℝ) (p : ℕ) (hp : p.Prime) :
    ‖(1 + (Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ)) *
      Complex.exp (-(Complex.I * (τ:ℂ)) / (p:ℂ))‖ ≤ 1 ∧
    ‖Complex.exp ((Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ))‖ ≤ 1 := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : 0 ≤ 1 / (p:ℝ) := by positivity
  have hq1 : 1 / (p:ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1
  have hE : ‖Complex.exp (Complex.I * (τ:ℂ))‖ = 1 := Complex.norm_exp_I_mul_ofReal τ
  constructor
  · rw [norm_mul]
    have h1 : ‖Complex.exp (-(Complex.I * (τ:ℂ)) / (p:ℂ))‖ = 1 := by
      have : -(Complex.I * (τ:ℂ)) / (p:ℂ) = Complex.I * ((-τ / p : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.norm_exp_I_mul_ofReal]
    have h2 : 1 + (Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ) =
        ((1 - 1 / (p:ℝ) : ℝ) : ℂ) + ((1 / (p:ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (τ:ℂ)) := by
      push_cast; ring
    rw [h1, mul_one, h2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, hE, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg hq0]
    linarith
  · rw [Complex.norm_exp, Real.exp_le_one_iff]
    have h3 : (Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ) =
        ((1 / (p:ℝ) : ℝ) : ℂ) * (Complex.exp ((τ:ℂ) * Complex.I) - 1 - Complex.I * (τ:ℂ)) := by
      rw [mul_comm (τ:ℂ) Complex.I]; push_cast; ring
    rw [h3, Complex.re_ofReal_mul, Complex.sub_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re]
    have : (Complex.I * (τ:ℂ)).re = 0 := by simp
    rw [this, Complex.one_re]
    have := Real.cos_le_one τ
    nlinarith

theorem ek_ml_factor (τ : ℝ) (p : ℕ) (hp : p.Prime) (hτ : |τ| ≤ 1) :
    ‖(1 + (Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ)) *
      Complex.exp (-(Complex.I * (τ:ℂ)) / (p:ℂ)) -
      Complex.exp ((Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ))‖ ≤
      τ ^ 2 / (p:ℝ) ^ 2 := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  
  have hsplit : (Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ) =
      (Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ) + -(Complex.I * (τ:ℂ)) / (p:ℂ) := by ring
  
  have hu : -(Complex.I * (τ:ℂ)) / (p:ℂ) = Complex.I * ((-τ / p : ℝ) : ℂ) := by
    push_cast; ring
  have hun : ‖Complex.exp (-(Complex.I * (τ:ℂ)) / (p:ℂ))‖ = 1 := by
    rw [hu]
    generalize (-τ / p : ℝ) = x
    rw [Complex.norm_exp]
    simp
  
  have hz : ‖Complex.exp (Complex.I * (τ:ℂ)) - 1‖ ≤ |τ| := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := τ)
    rwa [Real.norm_eq_abs] at h
  have hwn : ‖(Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ)‖ ≤ |τ| / p := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hz hp0.le
  have hw1 : ‖(Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ)‖ ≤ 1 :=
    hwn.trans (by rw [div_le_one hp0]; linarith)
  set w : ℂ := (Complex.exp (Complex.I * (τ:ℂ)) - 1) / (p:ℂ) with hw
  
  have hkey : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le hw1
  rw [hsplit, Complex.exp_add, ← sub_mul, norm_mul, hun, mul_one]
  rw [show (1 + w) - Complex.exp w = -(Complex.exp w - 1 - w) by ring, norm_neg]
  calc ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := hkey
    _ ≤ (|τ| / p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
    _ = τ ^ 2 / (p:ℝ) ^ 2 := by rw [div_pow, sq_abs]

theorem ek_ml_inv_sq_aux (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / ((m:ℝ) + 1) ^ 2 ≤ 2 - 2 / ((n:ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h : 1 / ((k:ℝ) + 1) ^ 2 ≤ 2 / ((k:ℝ) + 1) - 2 / ((k:ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem ek_ml_inv_sq (x : ℝ) : ∑ p ∈ ekP x, 1 / (p:ℝ) ^ 2 ≤ 2 := by
  unfold ekP
  calc ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, 1 / (p:ℝ) ^ 2
      ≤ ∑ m ∈ Finset.range (⌊x⌋₊ + 1), 1 / (m:ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun m _ _ => by positivity)
    _ = ∑ m ∈ Finset.range ⌊x⌋₊, 1 / ((m:ℝ) + 1) ^ 2 := by
        rw [Finset.sum_range_succ']
        simp
    _ ≤ 2 - 2 / ((⌊x⌋₊ : ℝ) + 1) := ek_ml_inv_sq_aux _
    _ ≤ 2 := by
        have : (0:ℝ) ≤ 2 / ((⌊x⌋₊ : ℝ) + 1) := by positivity
        linarith

theorem ek_ml_mu_sq (t : ℝ) :
    Tendsto (fun N : ℕ => ekMu (ekP (ekX N)) * (t / Real.sqrt (ekL N)) ^ 2) atTop (𝓝 (t ^ 2)) := by
  have h := ek_mu_ratio.const_mul (t ^ 2)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [ek_L_tendsto.eventually_ge_atTop 1] with N hN
  have hL : (0:ℝ) < ekL N := lt_of_lt_of_le one_pos hN
  rw [div_pow, Real.sq_sqrt hL.le]
  ring

theorem ek_ml_mu_cube (t : ℝ) :
    Tendsto (fun N : ℕ => ekMu (ekP (ekX N)) * |t / Real.sqrt (ekL N)| ^ 3) atTop (𝓝 0) := by
  have h1 := ek_mu_ratio
  have h2 : Tendsto (fun N : ℕ => |t| ^ 3 / Real.sqrt (ekL N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp ek_L_tendsto)
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [ek_L_tendsto.eventually_gt_atTop 0] with N hN
  show ekMu (ekP (ekX N)) / ekL N * (|t| ^ 3 / Real.sqrt (ekL N)) =
    ekMu (ekP (ekX N)) * |t / Real.sqrt (ekL N)| ^ 3
  have hs0 : 0 < Real.sqrt (ekL N) := Real.sqrt_pos.2 hN
  have hsq : Real.sqrt (ekL N) ^ 2 = ekL N := Real.sq_sqrt hN.le
  set s := Real.sqrt (ekL N) with hsdef
  rw [abs_div, abs_of_pos hs0, div_pow, ← hsq]
  have hs : s ≠ 0 := hs0.ne'
  first
    | ring
    | (field_simp; ring)

theorem ek_ml_exponent (t : ℝ) :
    Tendsto (fun N : ℕ => ((ekMu (ekP (ekX N)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)) - 1 -
        Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ))) atTop (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
  have hA : Tendsto (fun N : ℕ => (((ekMu (ekP (ekX N)) * (t / Real.sqrt (ekL N)) ^ 2 : ℝ)) : ℂ))
      atTop (𝓝 ((t ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (ek_ml_mu_sq t)
  have hB : Tendsto (fun N : ℕ => ((ekMu (ekP (ekX N)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)) -
        ∑ j ∈ Finset.range 3, (Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)) ^ j /
          (j.factorial : ℂ))) atTop (𝓝 0) := by
    have hc := (ek_ml_mu_cube t).const_mul (1/6 : ℝ)
    rw [mul_zero] at hc
    refine squeeze_zero_norm (fun N => ?_) hc
    have hmu : 0 ≤ ekMu (ekP (ekX N)) := by
      unfold ekMu; exact Finset.sum_nonneg fun p _ => by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu]
    have h := ek_exp_taylor (t / Real.sqrt (ekL N)) 3
    have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h3] at h
    calc _ ≤ ekMu (ekP (ekX N)) * (|t / Real.sqrt (ekL N)| ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left h hmu
      _ = 1/6 * (ekMu (ekP (ekX N)) * |t / Real.sqrt (ekL N)| ^ 3) := by ring
  have hC := (hA.const_mul (-1/2 : ℂ)).add hB
  have hlim : (-1/2 : ℂ) * ((t ^ 2 : ℝ) : ℂ) + 0 = -(t : ℂ) ^ 2 / 2 := by push_cast; ring
  rw [hlim] at hC
  refine hC.congr fun N => ?_
  try simp only [Function.comp_apply]
  generalize t / Real.sqrt (ekL N) = x
  generalize ekMu (ekP (ekX N)) = m
  have hsum : ∑ j ∈ Finset.range 3, (Complex.I * (x : ℂ)) ^ j / (j.factorial : ℂ) =
      1 + Complex.I * (x : ℂ) - (x : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    try linear_combination ((x : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [hsum]
  push_cast
  ring

theorem ek_model_limit (t : ℝ) :
    Tendsto (fun N : ℕ => modelCF (ekP (ekX N)) (t / Real.sqrt (ekL N))) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hE : Tendsto (fun N : ℕ => Complex.exp (((ekMu (ekP (ekX N)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)) - 1 -
        Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)))) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
    (Complex.continuous_exp.tendsto _).comp (ek_ml_exponent t)
  have hB : Tendsto (fun N : ℕ => 2 * t ^ 2 * (ekL N)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp ek_L_tendsto).const_mul (2 * t ^ 2)
    rw [mul_zero] at this
    exact this
  have hD : Tendsto (fun N : ℕ => modelCF (ekP (ekX N)) (t / Real.sqrt (ekL N)) -
      Complex.exp (((ekMu (ekP (ekX N)) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)) - 1 -
        Complex.I * ((t / Real.sqrt (ekL N) : ℝ) : ℂ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [ek_L_tendsto.eventually_ge_atTop (max 1 (t ^ 2))] with N hN
    set P := ekP (ekX N) with hPdef
    set L := ekL N with hLdef
    set τ : ℝ := t / Real.sqrt L with hτdef
    have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hN
    have hL0 : 0 < L := by linarith
    have hP : ∀ p ∈ P, p.Prime := by
      intro p hp
      rw [hPdef] at hp
      unfold ekP at hp
      exact (Finset.mem_filter.1 hp).2
    have hsq : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
    have hτ : |τ| ≤ 1 := by
      rw [hτdef, abs_div, abs_of_pos hsq, div_le_one hsq]
      exact Real.abs_le_sqrt (le_trans (le_max_right _ _) hN)
    have hprod : Complex.exp (((ekMu P : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (τ : ℂ)) - 1 - Complex.I * (τ : ℂ))) =
        ∏ p ∈ P, Complex.exp ((Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ)) := by
      have hs : ((ekMu P : ℝ) : ℂ) * (Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) =
          ∑ p ∈ P, (Complex.exp (Complex.I * (τ:ℂ)) - 1 - Complex.I * (τ:ℂ)) / (p:ℂ) := by
        unfold ekMu
        simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_natCast]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [hs, Complex.exp_sum]
    rw [ek_modelCF_prod, hprod]
    refine (ek_ml_prod_diff P _ _ (fun p hp => (ek_ml_factor_norm τ p (hP p hp)).1)
      (fun p hp => (ek_ml_factor_norm τ p (hP p hp)).2)).trans ?_
    calc _ ≤ ∑ p ∈ P, τ ^ 2 / (p:ℝ) ^ 2 :=
          Finset.sum_le_sum fun p hp => ek_ml_factor τ p (hP p hp) hτ
      _ = τ ^ 2 * ∑ p ∈ P, 1 / (p:ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ τ ^ 2 * 2 := mul_le_mul_of_nonneg_left (ek_ml_inv_sq (ekX N)) (sq_nonneg τ)
      _ = 2 * t ^ 2 * L⁻¹ := by
          rw [hτdef, div_pow, Real.sq_sqrt hL0.le]
          ring
  have := hD.add hE
  rw [zero_add] at this
  refine this.congr fun N => ?_
  exact sub_add_cancel _ _

theorem ek_step_trunc (t : ℝ) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
      Complex.exp (Complex.I * (t : ℂ) *
        ((((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
          Real.sqrt (Real.log (Real.log N)) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) * (ekMu (ekP (ekX N)) - ekL N) : ℝ) : ℂ)) *
        sieveCF (ekP (ekX N)) N (t / Real.sqrt (ekL N))) atTop (𝓝 0) := by
  have hε0 : Tendsto (fun N : ℕ => |t| * (Real.log N / Real.log (ekX N) / Real.sqrt (ekL N)))
      atTop (𝓝 0) := by
    simpa using ek_trunc_small.const_mul |t|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hε0
  filter_upwards [ek_X_eventually, eventually_ge_atTop 1] with N hN hN1
  obtain ⟨hX2, hXN⟩ := hN
  have hlogX : 0 < Real.log (ekX N) := Real.log_pos (by linarith)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1'
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun n => ∑ p ∈ ekP (ekX N), (if p ∣ n then (1:ℝ) else 0) :=
    ⟨_, rfl⟩
  have hTn : ∀ n, T n = ∑ p ∈ ekP (ekX N), (if p ∣ n then (1:ℝ) else 0) := by
    intro n; rw [hT]
  have hS : ∀ n, ekS (ekP (ekX N)) n = T n - ekMu (ekP (ekX N)) := by
    intro n; rw [hTn]; unfold ekS ekMu; rw [Finset.sum_sub_distrib]
  have h1 : (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (t : ℂ) *
        ((((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
          Real.sqrt (Real.log (Real.log N)) : ℝ) : ℂ))
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I *
          (((t / Real.sqrt (ekL N) *
            ((ArithmeticFunction.cardDistinctFactors n : ℝ) - ekL N)) : ℝ) : ℂ)) := by
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    simp only [ekL]
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) * (ekMu (ekP (ekX N)) - ekL N) : ℝ) : ℂ)) *
        sieveCF (ekP (ekX N)) N (t / Real.sqrt (ekL N))
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I *
          (((t / Real.sqrt (ekL N) * (T n - ekL N)) : ℝ) : ℂ)) := by
    unfold sieveCF
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_add, hS n]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  refine ek_avg_close N _ _ _ (mul_nonneg (abs_nonneg _)
    (div_nonneg (div_nonneg hlogN hlogX.le) (Real.sqrt_nonneg _))) ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
  obtain ⟨ha, hb⟩ := ek_trunc (ekX N) (by linarith) n hn1
  rw [← hTn n] at ha hb
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlogn : Real.log n ≤ Real.log N :=
    Real.log_le_log hnpos (by exact_mod_cast hnN)
  have hq : (ArithmeticFunction.cardDistinctFactors n : ℝ) - T n ≤
      Real.log N / Real.log (ekX N) := by
    refine hb.trans ?_
    gcongr
  have hsq := Real.sqrt_nonneg (ekL N)
  rw [show t / Real.sqrt (ekL N) * ((ArithmeticFunction.cardDistinctFactors n : ℝ) - ekL N) -
      t / Real.sqrt (ekL N) * (T n - ekL N) =
      t / Real.sqrt (ekL N) * ((ArithmeticFunction.cardDistinctFactors n : ℝ) - T n) by ring,
    abs_mul, abs_div, abs_of_nonneg hsq, abs_of_nonneg ha]
  calc |t| / Real.sqrt (ekL N) * ((ArithmeticFunction.cardDistinctFactors n : ℝ) - T n)
      ≤ |t| / Real.sqrt (ekL N) * (Real.log N / Real.log (ekX N)) :=
        mul_le_mul_of_nonneg_left hq (div_nonneg (abs_nonneg _) hsq)
    _ = |t| * (Real.log N / Real.log (ekX N) / Real.sqrt (ekL N)) := by ring

theorem ek_phase (t : ℝ) :
    Tendsto (fun N : ℕ =>
      Complex.exp (Complex.I * ((t / Real.sqrt (ekL N) * (ekMu (ekP (ekX N)) - ekL N) : ℝ) : ℂ)))
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ => t / Real.sqrt (ekL N) * (ekMu (ekP (ekX N)) - ekL N))
      atTop (𝓝 0) := by
    have := ek_center.const_mul (-t)
    simp only [mul_zero] at this
    refine this.congr (fun N => ?_)
    ring
  have hc : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by fun_prop
  have h1 := (hc.tendsto 0).comp h0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1
  exact h1

theorem erdos_kac_charfun (t : ℝ) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
      Complex.exp (Complex.I * (t : ℂ) *
        ((((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
          Real.sqrt (Real.log (Real.log N)) : ℝ) : ℂ)))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have h1 := ek_step_trunc t
  have h2 := ek_phase t
  have h5 := (ek_sieve_model t).add (ek_model_limit t)
  simp only [sub_add_cancel, zero_add] at h5
  have h6 := h2.mul h5
  rw [one_mul] at h6
  have h7 := h1.add h6
  simp only [sub_add_cancel, zero_add] at h7
  exact h7

theorem gaussian_measureReal_Icc (a b : ℝ) (hab : a ≤ b) :
    (ProbabilityTheory.gaussianReal 0 1).real (Set.Icc a b) =
      (1 / Real.sqrt (2 * π)) * ∫ t in a..b, Real.exp (-t ^ 2 / 2) := by
  rw [MeasureTheory.measureReal_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg
      (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)),
    intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  simp [ProbabilityTheory.gaussianPDFReal_def]

theorem levy_continuity_Icc (μ : ℕ → MeasureTheory.Measure ℝ)
    (hμ : ∀ N, MeasureTheory.IsProbabilityMeasure (μ N))
    (h : ∀ t : ℝ, Tendsto (fun N => MeasureTheory.charFun (μ N) t) atTop
      (𝓝 (MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t)))
    (a b : ℝ) :
    Tendsto (fun N => (μ N).real (Set.Icc a b)) atTop
      (𝓝 ((ProbabilityTheory.gaussianReal 0 1).real (Set.Icc a b))) := by
  classical
  haveI : ∀ N, MeasureTheory.IsProbabilityMeasure (μ N) := hμ
  have hf : ∀ t : ℝ, MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t
      = Complex.exp (-((t:ℂ)^2) / 2) := by
    intro t; rw [ProbabilityTheory.charFun_gaussianReal]; congr 1; push_cast; ring
  have hfc : Continuous (fun t : ℝ => MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t) := by
    simp_rw [hf]; fun_prop
  have hf0 : MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) 0 = 1 := by simp [hf]
  have hmain : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ N, (μ N).real {x | R < |x|} ≤ e := by
    intro e he
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (hfc.continuousAt (x := 0)) (e/4) (by positivity)
    set r : ℝ := 4 / δ with hr_def
    have hr : 0 < r := by positivity
    have hrinv : 0 < r⁻¹ := inv_pos.2 hr
    have hbound : ∀ t ∈ Set.uIoc (-2 * r⁻¹) (2 * r⁻¹),
        ‖1 - MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t‖ ≤ e/4 := by
      intro t ht
      have h2 : 2 * r⁻¹ = δ / 2 := by rw [hr_def]; field_simp; ring
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| < δ := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
      have := hδf (x := t) (by simpa [Real.dist_eq] using habs)
      rw [dist_eq_norm, hf0, norm_sub_rev] at this
      exact this.le
    have hIf : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 - MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t)‖ ≤ e / r := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
      have hab : |2 * r⁻¹ - -2 * r⁻¹| = 4 * r⁻¹ := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [hab] at this
      calc _ ≤ e / 4 * (4 * r⁻¹) := this
        _ = e / r := by ring
    have hconv : Tendsto (fun N => ∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 - MeasureTheory.charFun (μ N) t))
        atTop (𝓝 (∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
          (1 - MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun N =>
          (MeasureTheory.stronglyMeasurable_const.sub
            MeasureTheory.stronglyMeasurable_charFun).aestronglyMeasurable
      · exact Eventually.of_forall fun N =>
          MeasureTheory.ae_of_all _ fun t _ => MeasureTheory.norm_one_sub_charFun_le_two
      · exact intervalIntegrable_const
      · exact MeasureTheory.ae_of_all _ fun t _ => tendsto_const_nhds.sub (h t)
    have hlt' : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 - MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t)‖ < e / r + e / r := by
      have : 0 < e / r := by positivity
      linarith
    have hev : ∀ᶠ N in atTop, ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 - MeasureTheory.charFun (μ N) t)‖
        < e / r + e / r :=
      hconv.norm.eventually (gt_mem_nhds hlt')
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    have hlarge : ∀ N ≥ N0, (μ N).real {x | r < |x|} ≤ e := by
      intro N hN
      calc (μ N).real {x | r < |x|}
          ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 - MeasureTheory.charFun (μ N) t)‖ :=
            MeasureTheory.measureReal_abs_gt_le_integral_charFun hr
        _ ≤ 2⁻¹ * r * (e / r + e / r) := by gcongr; exact (hN0 N hN).le
        _ = e * (r * r⁻¹) := by ring
        _ = e := by rw [mul_inv_cancel₀ hr.ne', mul_one]
    have hper : ∀ N, ∃ R : ℝ, (μ N).real {x | R < |x|} ≤ e := by
      intro N
      have hanti : Antitone (fun n : ℕ => {x : ℝ | (n:ℝ) < |x|}) := by
        intro m n hmn x hx
        simp only [Set.mem_setOf_eq] at *
        exact lt_of_le_of_lt (by exact_mod_cast hmn) hx
      have hmeas : ∀ n : ℕ, MeasurableSet {x : ℝ | (n:ℝ) < |x|} := fun n =>
        measurableSet_lt measurable_const continuous_abs.measurable
      have hinter : (⋂ n : ℕ, {x : ℝ | (n:ℝ) < |x|}) = ∅ := by
        ext x
        simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_forall, not_lt]
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        exact ⟨n, hn⟩
      have ht := MeasureTheory.tendsto_measure_iInter_atTop (μ := μ N)
        (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, MeasureTheory.measure_ne_top _ _⟩
      rw [hinter, MeasureTheory.measure_empty] at ht
      obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 he))).exists
      refine ⟨n, ?_⟩
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal he.le hn.le
    choose Rf hRf using hper
    refine ⟨|r| + ∑ N ∈ Finset.range N0, |Rf N|, fun N => ?_⟩
    have hsub : ∀ s : ℝ, s ≤ |r| + ∑ N ∈ Finset.range N0, |Rf N| →
        {x : ℝ | |r| + ∑ N ∈ Finset.range N0, |Rf N| < |x|} ⊆ {x | s < |x|} :=
      fun s hs x hx => lt_of_le_of_lt hs hx
    have hsum_nonneg : 0 ≤ ∑ N ∈ Finset.range N0, |Rf N| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases hN : N0 ≤ N
    · refine le_trans (MeasureTheory.measureReal_mono (hsub r ?_)) (hlarge N hN)
      linarith [le_abs_self r]
    · push_neg at hN
      refine le_trans (MeasureTheory.measureReal_mono (hsub (Rf N) ?_)) (hRf N)
      have := Finset.single_le_sum (f := fun N => |Rf N|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hN)
      linarith [le_abs_self (Rf N), abs_nonneg r]
  have htight : MeasureTheory.IsTightMeasureSet (Set.range μ) := by
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨e, -, hpos, hlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have he : 0 < e := ENNReal.ofReal_pos.1 hpos
    obtain ⟨R, hR⟩ := hmain e he
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    rintro _ ⟨N, rfl⟩
    have hc : (Metric.closedBall (0:ℝ) R)ᶜ = {x | R < |x|} := by
      ext x; simp [not_le]
    rw [hc]
    calc (μ N) {x | R < |x|} = ENNReal.ofReal ((μ N).real {x | R < |x|}) :=
          (MeasureTheory.ofReal_measureReal (MeasureTheory.measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (hR N)
      _ ≤ ε := hlt.le
  let ν : ℕ → MeasureTheory.ProbabilityMeasure ℝ := fun N => ⟨μ N, hμ N⟩
  let ν₀ : MeasureTheory.ProbabilityMeasure ℝ :=
    ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  have hcpt : IsCompact (closure (Set.range ν)) := by
    apply isCompact_closure_of_isTightMeasureSet
    refine htight.subset ?_
    rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
    exact ⟨N, rfl⟩
  have hcont : ∀ t : ℝ, Continuous (fun ρ : MeasureTheory.ProbabilityMeasure ℝ =>
      MeasureTheory.charFun (ρ : MeasureTheory.Measure ℝ) t) := by
    intro t
    have : (fun ρ : MeasureTheory.ProbabilityMeasure ℝ =>
        MeasureTheory.charFun (ρ : MeasureTheory.Measure ℝ) t) =
          fun ρ : MeasureTheory.ProbabilityMeasure ℝ =>
          ∫ x, (BoundedContinuousFunction.innerProbChar t) x ∂(ρ : MeasureTheory.Measure ℝ) := by
      funext ρ; exact MeasureTheory.charFun_eq_integral_innerProbChar
    rw [this, continuous_iff_continuousAt]
    intro ρ
    exact (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
      tendsto_id _
  have hlim : Tendsto ν atTop (𝓝 ν₀) := by
    refine hcpt.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun N => subset_closure ⟨N, rfl⟩) ?_
    intro x _ hx
    haveI : MeasureTheory.IsProbabilityMeasure x.1 := x.2
    haveI : MeasureTheory.IsProbabilityMeasure ν₀.1 := ν₀.2
    apply Subtype.ext
    apply MeasureTheory.Measure.ext_of_charFun
    funext t
    have h1 := MapClusterPt.continuousAt_comp (hcont t).continuousAt hx
    have h2 : ClusterPt (MeasureTheory.charFun (x : MeasureTheory.Measure ℝ) t)
        (𝓝 (MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t)) :=
      ClusterPt.mono h1 (h t)
    exact eq_of_nhds_neBot h2
  have hsub : frontier (Set.Icc a b) ⊆ {a, b} := by
    intro x hx
    rw [frontier, isClosed_Icc.closure_eq, interior_Icc] at hx
    simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with ⟨⟨h1, h2⟩, h3 | h3⟩
    · left; linarith
    · right; linarith
  have hnull : (ProbabilityTheory.gaussianReal 0 1) (frontier (Set.Icc a b)) = 0 := by
    apply MeasureTheory.measure_mono_null hsub
    apply ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero
    exact (Set.toFinite _).measure_zero _
  have hnull' : ν₀ (frontier (Set.Icc a b)) = 0 := by
    simp [ν₀, hnull]
  have key := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hlim hnull'
  have key2 : Tendsto (fun N => ((ν N (Set.Icc a b) : NNReal) : ℝ)) atTop
      (𝓝 ((ν₀ (Set.Icc a b) : NNReal) : ℝ)) := (NNReal.continuous_coe.tendsto _).comp key
  exact key2

theorem levy_counting (X : ℕ → ℕ → ℝ)
    (hX : ∀ t : ℝ, Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
      Complex.exp (Complex.I * (t : ℂ) * ((X N n : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))))
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
      (fun n : ℕ => a ≤ X N n ∧ X N n ≤ b)).card : ℝ) / (N : ℝ)) atTop
      (𝓝 ((1 / Real.sqrt (2 * π)) * ∫ t in a..b, Real.exp (-t ^ 2 / 2))) := by
  classical
  let μ : ℕ → MeasureTheory.Measure ℝ := fun N =>
    if N = 0 then MeasureTheory.Measure.dirac 0
    else ((N : ENNReal)⁻¹) • ∑ n ∈ Finset.Icc 1 N, MeasureTheory.Measure.dirac (X N n)
  have hμ_apply : ∀ N, N ≠ 0 → ∀ s : Set ℝ, MeasurableSet s →
      μ N s = (N : ENNReal)⁻¹ * (((Finset.Icc 1 N).filter (fun n => X N n ∈ s)).card : ENNReal) := by
    intro N hN s hs
    simp only [μ, if_neg hN, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.coe_finset_sum, Finset.sum_apply,
      MeasureTheory.Measure.dirac_apply' _ hs, smul_eq_mul]
    congr 1
    rw [Finset.card_filter]
    push_cast
    simp [Set.indicator_apply]
  have hprob : ∀ N, MeasureTheory.IsProbabilityMeasure (μ N) := by
    intro N
    by_cases hN : N = 0
    · simp only [μ, if_pos hN]; infer_instance
    · constructor
      rw [hμ_apply N hN _ MeasurableSet.univ]
      simp only [Set.mem_univ, Finset.filter_true, Nat.card_Icc, Nat.add_sub_cancel]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hN) (by simp)
  have hchar : ∀ t : ℝ, Tendsto (fun N => MeasureTheory.charFun (μ N) t) atTop
      (𝓝 (MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t)) := by
    intro t
    have hg : MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t
        = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      congr 1
      push_cast
      ring
    rw [hg]
    refine (hX t).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    rw [MeasureTheory.charFun_apply_real]
    simp only [μ, if_neg hN0]
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_finset_sum_measure]
    · simp only [MeasureTheory.integral_dirac]
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
      push_cast
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun n _ => ?_
        congr 1
        ring
    · intro n _
      exact MeasureTheory.integrable_dirac (by simp)
  have hmain := levy_continuity_Icc μ hprob hchar a b
  rw [gaussian_measureReal_Icc a b hab.le] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : N ≠ 0 := by omega
  rw [MeasureTheory.measureReal_def, hμ_apply N hN0 _ measurableSet_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_inv_mul]
  simp [Set.mem_Icc]

theorem erdos_kac_aux (a b : ℝ) (hab : a < b) :
    Tendsto
      (fun N : ℕ =>
        ((((Finset.Icc 1 N).filter (fun n : ℕ =>
            a ≤ ((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
                  Real.sqrt (Real.log (Real.log N)) ∧
            ((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
                  Real.sqrt (Real.log (Real.log N)) ≤ b)).card : ℝ) / (N : ℝ)))
      atTop
      (𝓝 ((1 / Real.sqrt (2 * π)) * ∫ t in a..b, Real.exp (-t ^ 2 / 2))) := levy_counting
    (fun N n => ((ArithmeticFunction.cardDistinctFactors n : ℝ) - Real.log (Real.log N)) /
      Real.sqrt (Real.log (Real.log N)))
    erdos_kac_charfun a b hab

end ErdosKac
