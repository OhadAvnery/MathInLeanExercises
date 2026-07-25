import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

-- unlike rcases, "have" leaves h in context
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  · exact h.left
  · intro h'
    exact h.right (dvd_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  have ⟨h0, h1⟩ := h
  constructor
  · exact h0
  · contrapose! h1
    exact dvd_antisymm h0 h1

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  ⟨h.left, fun h' ↦ h.right (dvd_antisymm h.left h')⟩


example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  -- intro + rcases - no need for special statement to introduce
  -- the assumption h!
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  --exact ⟨by norm_num, by norm_num⟩
  constructor <;> norm_num

-- there exist two primes m<n in the open interval (4,10)
example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  -- one-line: use 5,7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  -- automatically answers the first part of the constructor?
  -- like how on ∃x P x, "use a" provides a
  -- and then we have to solve P a
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, by contrapose! h1; rw [h1]⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, by contrapose! h1; exact le_antisymm h0 h1⟩

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  --#check pow_two_nonneg y
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg y, pow_two_nonneg x]
  eq_zero_of_pow_eq_zero h'

-- book proof:
-- first direction - same as me only more verbose (with internal constructor)
-- second direction - a bit simpler, use rintro ⟨rfl,rfl⟩
-- (added below in comment)
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    -- x=0 is straight by aux. for y=0, we need
    -- to reverse the roles, so first do add_comm
    exact ⟨aux h, by rw [add_comm] at h; exact aux h⟩
  · rintro ⟨h1,h2⟩
    rw [h1, h2]
    --rintro ⟨rfl, rfl⟩
    norm_num

section
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  -- this extends out the definition of Montone, using the iff def of Monotone
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  --rw [Monotone]
  dsimp only [Monotone]
  push Not
  use 1, 2
  norm_num

-- alt proof
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 1,2
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  -- push Not doesn't work as it's not R
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    · contrapose! h1
      rw [h1]
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    · contrapose! h1
      exact le_antisymm h0 h1


end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  rintro ⟨h1, h2⟩
  exact h2 h1

-- note: this doesn't assume reflexivity and anti-symmetry!
example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  --rintro ⟨h1, h2⟩
  --rintro ⟨h3, h4⟩
  -- book proof: can be a one-liner
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩
  constructor
  · exact le_trans h1 h3
  contrapose! h4
  exact le_trans h4 h1


end
