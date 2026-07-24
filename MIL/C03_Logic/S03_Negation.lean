import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

-- ohad: example section
-- for proving stuff
-- about pure negation.
-- using: ¬P = P→False

section
variable (P Q : Prop)

example: (P→Q)→(¬Q→¬P) := by
  intro P_Q nQ P
  exact nQ (P_Q P)

example: (P→Q)→(¬Q→¬P) := fun p_q nq p ↦ nq (p_q p)

example : P→(¬¬P) :=
  fun p np ↦ (np p)

end

section
variable (a b : ℝ)

-- logic behind it:
-- P = a<b, Q=b<a.
-- we prove P→¬Q by P,Q → R:=a<a
-- and use the axiom ¬R, then apply
-- nr r = False.
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

-- note: we can have multiple anonymous "have"s,
-- but the only one that gets "this" is the last one.


-- test
example (h : a < b) : ¬b < a :=
  fun h' ↦ lt_irrefl a (lt_trans h h')

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  -- note: at this point,
  -- the original a defined at the section start is overshadowed
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  -- uses the latest anonymous have
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro h'
  rcases h' with ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  linarith [ha x]

example : ¬FnHasUb fun x ↦ x := by
  intro h
  rcases h with ⟨a,ha⟩
  -- we have x≤a for all x.
  -- choose x=a+1 for contradiction
  linarith [ha (a+1)]

example : ¬FnHasUb fun x ↦ x :=
  fun ⟨a, ha⟩ ↦ by linarith [ha (a+1)]

-- "of" means "from". first is: "not le" from "gt"
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

-- Monotone f: (a≤b)→(f a ≤ f b)
-- book proof doesn't use let,
-- and instead starts with lt_of_not_ge
-- to reduce the problem to ¬a≥b.
-- also use "absurd h":
--if we have h and need to prove False,
-- reduce to proving ¬h.
example (h : Monotone f) (h' : f a < f b) : a < b := by
  let : ¬(a ≥ b) := by
    intro h_a_b
    linarith [h h_a_b]
  apply lt_of_not_ge this

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro mon
  linarith [mon h]

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := fun a b a_le_b ↦ le_refl 0
  have h' : f 1 ≤ f 0 := le_refl 0
  -- need 1:ℝ explicitly because it can't deduce the type
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith
  -- alternative: turn the assumption to a contradiction.
  -- just "norm_num [this]" doesn't work - tries to simplify the goal, which is already as simple as it gets (False).
  --norm_num at this


example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  -- lt_irrefl gets two params: x and (proof of x<x), and retuns False
  -- second param: h, which takes param x, and proof that x>0, returns a proof of type x<x.
  -- x can be implicit: (h _ h')
  exact lt_irrefl x (h x h')
  --linarith [h x h']

-- TODO: continue from here
end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
