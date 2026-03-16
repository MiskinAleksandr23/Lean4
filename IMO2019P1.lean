
import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas

theorem IMO2019P1 :
    ∀ (f : ℤ → ℤ),
      (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) →
      (∀ x, f x = 0) ∨ (∃ c : ℤ, ∀ x, f x = 2 * x + c) := by
  intro f condition_a_b

  let condition_0_b := condition_a_b
  let condition_1_b := condition_a_b
  specialize (condition_0_b 0)
  specialize (condition_1_b 1)
  simp at condition_0_b
  simp at condition_1_b


  have arith : ∀ b, (f 2) + 2 * (f b) == (f 0) + 2 * f (b + 1) := by grind
  have diff : ∀ b, 2 * (f (b + 1) - f (b)) == (f 2) - (f 0) := by grind

  let c := f 2 - f 0
  match h : c with
  | 0 =>
    have all_equal : ∀b, f (b + 1) - f b == 0 := by
      grind
    simp at all_equal
    have all_equal' : ∀m, ∀n, f n == f m := by
      have all_equal'' : ∀m : ℤ, ∀ xd : ℕ, f (m + xd) == f m := by
        intro m xd
        induction xd with
          | zero => grind
          | succ m =>
            grind
      intro n m
      if n >= m then
        let add' := n - m
        have positive : add' >= 0 := by grind
        let add'' := add'.toNat_of_nonneg positive
        specialize all_equal'' m add'.toNat
        grind
      else
        let add' := m - n
        have positive : add' >= 0 := by grind
        let add'' := add'.toNat_of_nonneg positive
        specialize all_equal'' n add'.toNat
        grind
    have f0 : f 0 == 0 := by
      let value := f 0
      have all_equal_value : ∀n, f n = value := by grind
      have eq := condition_a_b 0 0
      simp at eq
      simp [all_equal_value] at eq
      grind
    specialize all_equal' 0
    simp at all_equal'
    simp at f0
    grind
  | a =>
    let f0 := f 0
    have induct_on_positive : ∀ n : ℕ, 2 * (f n - f 0) == n * c := by
      intro n
      induction n with
      | zero =>
        simp
      | succ m ih =>
        simp
        calc
          2 * (f (↑m + 1) - f 0) = 2 * (f ↑m - f 0) + 2 * (f (↑m + 1) - f ↑m) := by grind
          _ = ↑m * c + c := by grind
        grind
    have induct_on_negative : ∀ n : ℕ, 2 * (f (-n : ℤ) - f 0) == -(n : ℤ) * c := by
      intro n
      induction n with
      | zero =>
        simp
      | succ m ih =>
        simp
        calc
          2 * (f (-1 + -↑m) - f 0) = 2 * (f (-↑m) - f 0) + 2 * (f (-1 + -↑m) - f (-↑m)) := by grind
          _ = _ := by grind


    have final : ∀ z, 2 * (f z - f 0) == z * c := by
      intro z
      if hh : z >= 0 then
        let a'''' := z.toNat_of_nonneg hh
        grind
      else
        simp at hh
        let a'''' := (-z).toNat_of_nonneg
        grind
    have f20 : c % 2 == 0 := by
      simp at c
      have f2 : 2 * (f 2 - f 0) == ↑2 * c := by grind
      have f2' : f 2 - f 0 == c := by grind
      grind
    have differ : ∀z, f (z + 1) - f z == c / 2 := by grind
    have final' : ∀ z, f z == z * (c / 2) + f0 := by grind
    simp at final'
    rw [final'] at condition_0_b
    specialize condition_0_b 1
    simp at condition_0_b
    let h : f 1 == c / 2 + f0 := by grind
    have smp : f0 + 2 * (c / 2 + f0) == f ( (c / 2 + f0) ) := by grind
    have smp': f0 + 2 * (c / 2 + f0) == (c / 2 + f0) * (c / 2) + f0 := by grind

    simp at smp'
    have smp'' : 2 * (c / 2 + f0) = (c / 2 + f0) * (c / 2) := by grind
    have smp''' : ((c / 2 + f0)) * (c / 2 - 2) == 0 := by grind

    simp at smp'''
    cases h : smp'''
    have q₁ : f 1 - f 0 == c / 2 := by grind
    have q₂ : f 2 + f 0  == 0 := by grind
    have q₃ : f 2 - f 1 == c / 2 := by grind

    have q₄ : f 2 == c / 2 := by grind
    have q₅ : f 0 == -c / 2 := by grind
    have q₆ : f 1 == 0 := by grind


    specialize condition_a_b 1 1
    simp at condition_a_b
    simp at q₄ q₅ q₆
    rw [q₄, q₆] at condition_a_b
    simp at condition_a_b

    have pls : c / 2 == (c / 2) * (c / 2) + (-c / 2) := by grind
    have pls' : c == (c / 2) ^ 2 := by grind
    have pls'' : 4 * c == c ^ 2 := by grind
    have pls''' : c * (4 - c) == 0 := by grind

    simp at pls'''
    cases pls'''
    . grind
    .
      have rrr : ∀z, f z = z * 2 + f0 := by grind
      right
      use f0
      grind

    have tle : c == 4 := by grind
    have rrr : ∀z, f z = z * 2 + f0 := by grind
    right
    use f0
    grind

-- #min_imports
