import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

-- ohad: works even without the ",h1, h2" at the end
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

-- ⟨ = \<, ⟩ = \>
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  -- todo: find t with FnLb (f+g) t
  -- unpack the assumptions
  rcases lbf with ⟨a, lbf_a⟩
  rcases lbg with ⟨b, lbg_b⟩
  -- these are unnecessary but make the goal+assumptions easier to read
  -- dsimp [FnLb] at lbf_a
  -- dsimp [FnLb] at lbg_b
  -- dsimp [FnHasLb, FnLb]
  use a + b
  intro x
  linarith [lbf_a x, lbg_b x]

#search "for real a,b,c, if c>0 and a≤b then c*a≤c*b."

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a,f_ub_a⟩ -- have: f≤a
  use c*a -- need to show: c*f≤c*a
  intro x -- goal is now (after dsimp): c*f(x)≤c*a
  -- theorem name: the left factor is nonneg
  apply mul_le_mul_of_nonneg_left (f_ub_a x) h
  -- no need for actual dsimp because apply is smart enough

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- ohad: explicit expansion. The above is nicer,
-- does two instructions (introduce the assumption + unpack)
-- at once, with no need for a tepmorary variable ubf for the "exists"
-- assumption
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  intro ubf; rcases ubf with ⟨a, ubfa⟩
  intro ubg; rcases ubg with ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

end

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  -- rfl: automatically rewrite x in the goal as a²+b²
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

-- todo: continue from here

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

-- v2
example : a ∣ b → b ∣ c →  a ∣ c := by
  --intro div_a_b, div_b+c
  rintro ⟨d, h_ab⟩ ⟨e, h_bc⟩
  use d*e
  rw [h_bc, h_ab]
  ring -- or just associativity
  --exact ⟨d*e, by ring⟩ -- doesn't work
  -- as ring only does exact equalities

-- v3: one-liner to prove the equality
-- Grobner is always computable, might have double-exponential runtime
-- but in practice is often efficient
example : a ∣ b → b ∣ c →  a ∣ c :=
  fun ⟨d,_⟩ ⟨e,_⟩ ↦ ⟨d*e, by grobner⟩

-- if I want it to be a one-liner, can use match or divac.elim
-- but it seems messier.
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨x, _⟩ := divab
  obtain ⟨y, _⟩ := divac
  exact ⟨x+y, by grobner⟩

-- book solution: just use rfl in obtaining stuff
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨x, rfl⟩ := divab
  obtain ⟨y, rfl⟩ := divac
  exact ⟨x+y, by ring⟩

end

section

open Function

#print Function.Surjective
-- ∀ (b : β), ∃ a, f a = b
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro y
  use y - c
  dsimp; ring

#print mul_div_cancel₀
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro y
  use y / c
  dsimp
  exact mul_div_cancel₀ _ h

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp
  -- the example was given with h explicitly, but turns out it can just deduce it itself?
  --field_simp [h]
  ring

-- trying the previous problem with this new tactic
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro y
  use y / c
  field_simp

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  --rcases h 2 with ⟨x, hx⟩
  obtain ⟨x, hx⟩ := h 2
  use x
  rw [hx]
  norm_num

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  obtain ⟨y, rfl⟩ := surjg z
  obtain ⟨x, rfl⟩ := surjf y
  use x

end
