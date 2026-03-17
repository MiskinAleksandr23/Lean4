import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith


-- https://artofproblemsolving.com/wiki/index.php?title=2023_USAMO_Problems
-- Usamo 2023 problem 2

theorem usamo2023p2left: ∀f : (NNReal -> NNReal),
                        (∀ x, f (x) = x + 1) ->
                        ∀x, ∀y, (f (x * y + f (x)) = x * f (y) + 2) := by
  intro f condition x y
  simp [condition]
  grind

theorem usamo2023p2right : ∀f : (NNReal -> NNReal), (∀x, ∀y, (f (x * y + f (x)) = x * f (y) + 2)) →
  ∀ x, (f (x) = x + 1) := by
    intro f condition

    have condition₁ : ∀ x, f (x + f x) = x * f 1 + 2 := by
      intro x
      have := condition x 1
      grind
    have condition₂ : ∀ x, f (x + f x + f 1) = f (x + f (x)) + 2 := by
      intro x
      have := condition 1 (x + f x)
      grind

    have condition₃ : ∀ x: NNReal, (x > 0) -> f (x + f (x) + f (1)) = x * f (1 + (f 1) / x) + 2 := by
      intro x pos
      have cx := condition x (1 + (f 1) / x)
      have : x * (1 + (f 1) / x) = x + f (1) := by
        rw [mul_one_add]
        rw [mul_div_left_comm]
        simp
        rw [mul_right_eq_self₀]
        left
        rw [div_self_eq_one₀]
        grind
      simp at cx
      rw [this] at cx
      suffices x + f 1 + f x = x + f x + f 1 by
        grind
      grind
    -- NNReal is just too bad
    have condition₄ : ∀ x, (x > 0) -> f (1 + (f 1) / x) = f 1 + 2 / x := by
      intro x pos

      have : ∀ x, f (x + f x + f 1) = x * (f 1) + 4 := by grind
      have : ∀ x, (x > 0) -> x * (f 1) + 4 = x * f (1 + (f 1) / x) + 2 := by grind
      specialize this x pos
      simp at this
      have : x * f 1 + 2 = x * f (1 + f 1 / x) := by grind
      have : (x * f 1 + 2) / x = (x * f (1 + f 1 / x)) / x := by grind
      have c₁ : (x * f 1 + 2) / x = f 1 + 2 / x := by
        have : (x * f 1 + 2) / x = (x * f 1) / x + 2 / x := by
          rw [add_div]
        have : x * f 1 / x + 2 / x = f 1 + 2 / x := by
          have : x * f 1 / x = f 1 := by
            rw [mul_div_right_comm]
            have : x / x = 1 := by
              rw [div_self_eq_one₀]
              grind
            grind
          grind
        grind
      have : x * f (1 + f 1 / x) / x = f (1 + f 1 / x) := by
        rw [mul_div_right_comm]
        rw [mul_left_eq_self₀]
        left
        have : x / x = 1 := by
          rw [div_self_eq_one₀]
          grind
        grind
      grind
    have condition₅ : ∀ x, (x > 0) -> f (1 + x) = f 1 + 2 / (f 1 / x) := by
      intro x pos
      specialize condition₄ (f 1 / x) (by sorry)
      sorry
    sorry
theorem usamo2023p2 : ∀f : (NNReal -> NNReal), (∀x, ∀y, (f (x * y + f (x)) = x * f (y) + 2)) ↔
  ∀ x, (f (x) = x + 1) := fun f => ⟨usamo2023p2right f, usamo2023p2left f⟩
