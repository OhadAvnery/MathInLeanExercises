import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry


-- note: there's a problem with the lean server occasionally,
-- and then the process gets stuck on #search, should comment them out in this case
-- #search "if a<b then a≤b." -- le_of_lt
--#search "x≤x for all x." -- le_refl

-- the book solution uses "by apply", and a lot of linarith, so they make it a bit simpler -
-- no need for all the specific results I used (like a<b≤c -> a<c)
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := mul_le_mul (le_refl |x|) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    _ < 1 * ε := mul_lt_mul_of_pos_right (lt_of_lt_of_le xlt ele1) epos
    _ = ε := one_mul ε

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  --have hf : (f x ≥ a) := by apply hfa
  --have hg : (g x ≥ b) := by apply hgb
  --linarith
  -- alternative option: give hfa, hgb as explicit arguments to linarith
  linarith [hfa x, hgb x]

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  --apply mul_nonneg
  --apply nnf; apply nng
  apply mul_nonneg (nnf x) (nng x)

-- f≤a, 0≤g≤b, a≥0 → fg≤ab
example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  repeat linarith [hfa x, hgb x, nng x] -- a bit overkill but whatever

end

section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb -- three params to monotone f: a, b, and the statement a≤b
  apply add_le_add
  apply mf aleb
  apply mg aleb

-- ohad - random thought: if we include ∀x:α P(x), that's the same as building a function that
-- for each x∈α constructs a proof of P(α). That matches the term notation, as x itself is a proof
-- of x∈α.


example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun _a _b aleb ↦ add_le_add (mf aleb) (mg aleb)


#search "if a≤b and c>0 then ca≤cb."
#check mul_le_mul_of_nonneg_left
-- ↦ = \maps
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  --fun a b aleb ↦ mul_le_mul (by linarith) (mf aleb) sorry nnc
  -- _a,_b start with underline because they're not used, otherwise it'll cause a warning
  fun _a _b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun _a _b aleb ↦ mf (mg aleb)

-- alternative proof
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  exact aleb

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

-- the first step (simplifying the lambda) is necessary
-- because otherwise rw wouldn't recognize
-- the fx, gx terms
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]

example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp
  calc
    f x * g x = (-f (-x)) * (-g (-x)) := by rw [of, og]
    _ = f (-x) * g (-x) := by ring

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  calc
    f x * g x = (f (-x)) * (-g (-x)) := by rw [ef, og]
    _ = -(f (-x) * g (-x)) := by ring

-- dsimp: simp (simplifies the goal), but only for trivial identities
example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  calc
    f (g (x)) = f (-g (-x)) := by rw [og]
    _ = f (- - g (-x)) := by rw [ef]
    _ = f (g (-x)) := by ring_nf

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs -- we introduce x:α and the assumption xs: x∈s
  exact xs

theorem Subset.refl : s ⊆ s := fun _x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rs st _x xr
  exact st (rs xr)

example : r ⊆ s → s ⊆ t → r ⊆ t := fun rs st _x xr ↦ st (rs xr)

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- ohad: this is the explicit version, where we write out
-- the types both of the statement (Prop) and of x (α).
-- Not necessary because the compiler infered them.
-- writing x∈s implies x must have type α, otherwise it won't compile
-- (if x has a different type it's not just that it won't have a proof,
-- it's simply undefined)
example (s : Set α) (a : α) : Prop :=
  ∀ x : α , x ∈ s → x ≤ a

-- same proof as the book :)
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

end

section

open Function

-- ohad: we could have done "dsimp at h' " to replace h' with a simpler expression.
-- But it's not necessary as exact knows how to expand up to
-- definitional equality, and rw doesn't (it checks for syntatic occurrences)
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

#check mul_right_inj
#check mul_right_inj'
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x y fx_eq_fy
  --dsimp at fx_eq_fy -- not needed
  --#check (mul_right_inj' h)
  -- the above has type  c * ?m.24 = c * ?m.25 ↔ ?m.24 = ?m.25
  exact (mul_right_inj' h).mp fx_eq_fy

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- book sol is the same, but diff var names and the last is apply and not exact
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x y func_x_eq_func_y
  apply injf
  apply injg
  exact func_x_eq_func_y
end
