import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- ohad - these both work, so the variable name doesn't matter
#check (le_rfl : a ≤ a)
#check (le_rfl : b ≤ b)


-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  -- step 1: apply lt_of_le_of_lt on h₀ and goal, new goal is b<e
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

  -- with intermediate claims:
  --let hh₁ : a < c := by apply lt_of_le_of_lt h₀ h₁
  --let hh₂ : a < d := by apply lt_of_lt_of_le hh₁ h₂
  --apply lt_trans hh₂ h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

-- OHAD: continue from here
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_right -- need: exp(...)≤exp(...)
  apply exp_le_exp.mpr

  -- apply add_le_add_right h₀ -- option 1

  -- option 2, more verbose
  apply add_le_add_right
  exact h₀


example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos -- need: 0<1, 0<exp a
    · norm_num
    · apply exp_pos
  -- have h₁ : 1 + exp a ≤ 1 + exp b := by -- if we want forward directed proof
  apply log_le_log h₀
  apply add_le_add_right
  apply exp_le_exp.mpr h


example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a


example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h' : exp a ≤ exp b := exp_le_exp.mpr h
  -- apply? -- suggested: exact tsub_le_tsub_left h' c
  apply tsub_le_tsub_left h'
  -- also: linarith

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    -- ohad - to see the explicit kernel terms:
    -- a^2 - 2*a*b + b^2 = (a - b)^2 := by show_term ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

-- ohad: third method by gpt
example : 2*a*b ≤ a^2 + b^2 := by nlinarith [sq_nonneg (a-b)]

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h : (a*b ≤ (a^2 + b^2)/2) ∧ (-(a*b) ≤ (a^2 + b^2)/2) := by
    constructor
    · have h₁ : 0 ≤ a^2 - 2*a*b + b^2
      calc
        a^2 - 2*a*b + b^2 = (a-b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
      linarith
    · have h₂ : 0 ≤ a^2 + 2*a*b + b^2
      calc
          a^2 + 2*a*b + b^2 = (a+b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
      linarith
  -- note: for this to work, I needed -(a*b), -a*b is not good enough
  exact abs_le'.mpr h

#check abs_le'.mpr

-- ohad: try 2
example : |a*b| ≤ (a^2 + b^2)/2 := by
  apply abs_le'.mpr
  constructor
  · have h₁ : 0 ≤ a^2 - 2*a*b + b^2
    calc
        a^2 - 2*a*b + b^2 = (a-b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith
  · have h₂ : 0 ≤ a^2 + 2*a*b + b^2
    calc
          a^2 + 2*a*b + b^2 = (a+b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith


-- ...........................
-- ohad: BONUSES
-- ...........................

-- ohad: example of LLM plugin
-- note: can only use a,b,c,d,e as they were declared above
example (h : a > 0) : log (2*a) > log (a) := by
  -- #search "log(x*y)=log(x)+log(y) for positive x,y."
  -- #check log_mul
  have h₁ : a≠0 := by
    -- need to match the goal!
    --#search "prove that a≠0 assuming a>0, for real a."
    #search "prove that a≠b assuming a>b, for real a,b."
    --apply ne_iff_gt_or_lt.mpr h
    -- apply ne_of_lt h -- need to reverse...
    sorry
  sorry
  --rw [log_mul h]

-- ohad: try #2 -
-- selected the example, ctrl+shift+p "add to codex thread",
-- wrote the proof outline, asked it to fill in
example (h : a > 0) : log (2*a) > log (a) := by
  have ha : a ≠ 0 := ne_of_gt h
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) ha]
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  linarith
