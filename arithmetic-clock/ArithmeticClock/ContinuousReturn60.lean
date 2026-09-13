import ArithmeticClock.RealClock60

set_option autoImplicit false
open scoped BigOperators

namespace ArithmeticClock.RealClock60

noncomputable section

def flowOrbit (t : ℝ) := flow t * realCarrier * (flow t).transpose

theorem orbit_crossblock (p q : Fin 6) (t : ℝ) :
    (fun x y : Fin 2 => flowOrbit t (p, x) (q, y)) =
      DenseCarrier.rotateBlock (Real.cos (angle p t)) (Real.sin (angle p t))
        (Real.cos (angle q t)) (Real.sin (angle q t))
        (fun x y => realCarrier (p, x) (q, y)) := by
  ext x y
  simp [flowOrbit, flow, Matrix.mul_apply, Fintype.sum_prod_type,
    DenseCarrier.rotateBlock, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    apply_ite, ite_mul, mul_ite]

theorem carrier_crossblock : (fun x y : Fin 2 => realCarrier (0, x) (1, y)) =
    DenseCarrier.crossBlock (1, 60) (2, 30) := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    rfl

theorem flowOrbit_return_frequencies (t : ℝ) (h : flowOrbit t = realCarrier) :
    Real.cos (angle 0 t - angle 1 t) = 1 ∧
      Real.cos (angle 0 t + angle 1 t) = 1 := by
  have hc := congrArg (fun A : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℝ =>
    fun x y : Fin 2 => A (0, x) (1, y)) h
  dsimp only at hc
  rw [orbit_crossblock, carrier_crossblock] at hc
  exact (DenseCarrier.crossBlock_1_60_2_30_stabilizer _ _).mp hc

theorem flowOrbit_return_lattice (t : ℝ) (h : flowOrbit t = realCarrier) :
    ∃ k : ℤ, t = 60 * (k : ℝ) := by
  obtain ⟨hd, hs⟩ := flowOrbit_return_frequencies t h
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp hd
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hs
  have hdelta0 : delta 0 = 59 := by decide
  have hdelta1 : delta 1 = 28 := by decide
  simp only [angle, hdelta0, hdelta1] at hm hn
  refine ⟨5 * n - 14 * m, ?_⟩
  push_cast
  have hp := Real.pi_pos
  nlinarith [hm, hn]

theorem flow_integer_period (k : ℤ) : flow (60 * (k : ℝ)) = 1 := by
  have ha (p : Fin 6) : angle p (60 * (k : ℝ)) =
      ((delta p : ℤ) * k : ℤ) * (2 * Real.pi) := by
    push_cast
    unfold angle
    ring
  have hc (p : Fin 6) : Real.cos (angle p (60 * (k : ℝ))) = 1 := by
    rw [ha]
    exact (Real.cos_eq_one_iff _).mpr ⟨(delta p : ℤ) * k, rfl⟩
  have hs (p : Fin 6) : Real.sin (angle p (60 * (k : ℝ))) = 0 := by
    have hh := Real.sin_sq_add_cos_sq (angle p (60 * (k : ℝ)))
    rw [hc] at hh
    nlinarith [sq_nonneg (Real.sin (angle p (60 * (k : ℝ))))]
  ext i j
  rcases i with ⟨p, x⟩
  rcases j with ⟨q, y⟩
  by_cases hpq : p = q
  · subst q
    fin_cases x <;> fin_cases y <;>
      simp [flow, DenseCarrier.rotation, hc, hs]
  · simp [flow, hpq, Matrix.one_apply, Prod.ext_iff]

theorem flowOrbit_return_iff (t : ℝ) :
    flowOrbit t = realCarrier ↔ ∃ k : ℤ, t = 60 * (k : ℝ) := by
  constructor
  · exact flowOrbit_return_lattice t
  · rintro ⟨k, rfl⟩
    simp [flowOrbit, flow_integer_period]

theorem flow_periodic : Function.Periodic flow 60 := by
  intro t
  have h60 : flow 60 = 1 := by simpa using flow_integer_period 1
  rw [flow_add, h60, Matrix.mul_one]

theorem flowOrbit_periodic : Function.Periodic flowOrbit 60 := by
  intro t
  simp only [flowOrbit, flow_periodic t]

theorem flowOrbit_no_return_between (t : ℝ) (ht : 0 < t) (h60 : t < 60) :
    flowOrbit t ≠ realCarrier := by
  intro h
  obtain ⟨k, hk⟩ := (flowOrbit_return_iff t).mp h
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1 : (k : ℝ) < 1 := by linarith
  have hi0 : (0 : ℤ) < k := by exact_mod_cast hk0
  have hi1 : k < (1 : ℤ) := by exact_mod_cast hk1
  omega

end

end ArithmeticClock.RealClock60
