import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- ohad: these 2 don't work!
-- #check max_ge_left
-- #check left_le_max

-- here's the real max one:
-- intuitive explanation -
-- we can't start with "max" as it doesn't
-- correspond to how we read the statement,
-- we don't have a left to max yet.
#search "a is less than or equal to max a b."
#check le_max_left

#check max_le

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  -- prove max a b ≤ max b a, then repeat it
  repeat
    apply max_le -- a ≤ max b a, b ≤ max b a
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  -- shamelessely copying from previous solutions
  have h_le : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  have h_eq : ∀ x y : ℝ, min x y = min y x := by
    intro x y
    apply le_antisymm
    repeat apply h_le

  -- the L≤R direction
  have h_L_R : ∀ x y z : ℝ, min (min x y) z ≤  min x (min y z) := by
    intro x y z
    apply le_min -- need: LHS ≤ x, LHS ≤ min y z
    -- LHS ≤ x
    · calc
      min (min x y) z ≤ min x y := by apply min_le_left
      _ ≤ x := by apply min_le_left

    -- LHS ≤ min y z, reduces to: LHS ≤ y, LHS ≤ z
    apply le_min
    · calc
        min (min x y) z ≤ min x y := by apply min_le_left
        _ ≤ y := by apply min_le_right
    apply min_le_right

  apply le_antisymm
  · apply h_L_R
  rw [h_eq a (min b c)]
  rw [h_eq b c]
  rw [h_eq (min a b) c]
  rw [h_eq a b]
  apply h_L_R

-- the book proof is shorter but less conceptual


#check add_neg_cancel_right

-- ohad: even though aux is not defined with universal quantifiers,
-- they're implicit in defining a,b,c as variables,
-- so we can call aux with whatever expressions we want
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h_a : min a b ≤ a := by apply min_le_left
  have h_b : min a b ≤ b := by apply min_le_right
  apply le_min
  repeat linarith

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) + (-c) ≤ min (a + c + (-c)) (b + c + (-c)) := by
    apply aux
  repeat rw [add_neg_cancel_right] at h
  linarith


#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check sub_add_cancel

-- book proof is the same,
-- only with "have h := abs_add_le (a - b) b" directly
example : |a| - |b| ≤ |a - b| := by
  have h : |a-b+b| ≤ |a-b| + |b| := by apply abs_add_le
  rw [sub_add_cancel] at h
  linarith

end

section
variable (w x y z : ℕ)

-- standard bar: |, div: ∣
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  -- dvd_sum doesn't exist, let's search...
  --#search "if a|b and a|c then a|b+c."
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  -- need: x|w^2
  have h_w : w ∣ w ^ 2 := by apply dvd_mul_left
  apply dvd_trans h h_w

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check dvd_antisymm
#check dvd_gcd
#check Nat.dvd_gcd
example : Nat.gcd m n = Nat.gcd n m := by
  let h : ∀ a b : ℕ, Nat.gcd a b ∣ Nat.gcd b a := by
    intro a b
    apply dvd_gcd
    · apply gcd_dvd_right
    apply gcd_dvd_left
  apply dvd_antisymm
  repeat apply h
end
