import Mathlib.Tactic

example (a b : ℝ) : (a - b)^2 = 0 ↔ a = b := by
  constructor
  -- (a - b)^2 = 0 → a = b
  · intro h
    have h1 : a - b = 0 := by
      apply pow_eq_zero h
    exact eq_of_sub_eq_zero h1
  -- a = b → (a - b)^2 = 0
  · intro h
    rw [h]
    ring

