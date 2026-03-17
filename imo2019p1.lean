import Mathlib.Analysis.Normed.Ring.Lemmas


-- imo 2019 P1
-- https://artofproblemsolving.com/wiki/index.php/2019_IMO_Problems?srsltid=AfmBOorb3My9yNkaUrUncV3hQo0xhMC2Fkde4ZRX_GQJJ97FBWc6MdBe

-- Let ℤ be the set of integers. Determine all functions f : ℤ -> ℤ such that, for all integers a and b, f(2a)+2f(b)=f(f(a+b))

theorem ArithProgressionDifference :
  ∀ (f : ℤ -> ℤ), ∀ c : ℤ,
  (∀b : ℤ, f (b + 1) - f b = c)
  ->
  ∀m, ∀n, f n - f m = (n - m) * c := by
    intro f c equal_consequent
    have difference_lemma : ∀m : ℤ, ∀ xd : ℕ, f (m + xd) == f m + c * xd := by
        intro m xd
        induction xd with
          | _ => grind
    intro n m
    if n >= m then
      specialize difference_lemma m (n - m).toNat
      grind
    else
      specialize difference_lemma n (m - n).toNat
      grind

theorem imo2019p1left :
    ∀ (f : ℤ → ℤ),
      (∀ x, f x = 0) ∨ (∃ c : ℤ, ∀ x, f x = 2 * x + c) →
      (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) := by
      rintro f (hf | ⟨c, hc⟩)
      . simp [hf]
      . simp [hc]
        lia

theorem imo2019p1right :
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
  if c == 0 then
    have equal_consequent : ∀b, f (b + 1) - f b = 0 := by
      grind
    simp at equal_consequent

    have all_equal := ArithProgressionDifference f 0 equal_consequent

    have: f 0 == 0 := by
      have all_equal_value : ∀n, f n = f 0 := by grind
      have eq := condition_a_b 0 0
      simp [all_equal_value] at eq
      grind
    grind
  else
    have equal_difference : ∀b, f (b + 1) - f b = (c / 2) := by
      grind
    have equlity : ∀n, (f n - f 0) == n * (c / 2) := by
      simp
      have := ArithProgressionDifference f (c / 2) equal_difference 0
      grind

    have condition : ((c / 2 + f 0)) * (c / 2 - 2) == 0 := by grind

    simp at condition
    cases condition with
    | inl _ =>
      have q₁ : f 2 == c / 2 := by grind
      have q₂ : f 0 == -c / 2 := by grind
      have q₃ : f 1 == 0 := by grind

      simp at q₁ q₂ q₃

      specialize condition_a_b 1 1
      simp at condition_a_b
      rw [q₁, q₃] at condition_a_b
      simp at condition_a_b

      have condition_on_c : c * (4 - c) == 0 := by grind

      simp at condition_on_c
      cases condition_on_c with
      | inl _ =>
        left
        grind
      | inr _ =>
        right
        use f 0
        grind
    | _ =>
        right
        use f 0
        grind

theorem imo2019p1:
    ∀ (f : ℤ → ℤ),
      (∀ x, f x = 0) ∨ (∃ c : ℤ, ∀ x, f x = 2 * x + c) ↔
      (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) := fun f => ⟨imo2019p1left f, imo2019p1right f⟩
-- #min_imports
