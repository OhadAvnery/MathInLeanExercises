import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  -- rfl is useful here, because it allows us to remove y
  -- and replace it with "f x"
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hs
    simp
    apply h
    use x
  · rintro h y hy
    rcases hy with ⟨x,xs,rfl⟩
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

-- if f is injective, then ⋂_i f[A i] ⊆ f[⋂_i A i]
-- we're also given a specific i to make sure the intersection is non-empty,
-- else it's not true!
example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y h
  -- h i says: y∈ f[A i]
  simp at h
  rcases h i with ⟨x, xs, rfl⟩
  -- at this point, h has no use of y, and refers to ∃x1: f(x)=f(x1)
  use x
  simp
  intro j
  rcases h j with ⟨x', xs', h'⟩
  -- rewrite the goal, replace x with x', by f x = f x'
  rw [←injf h']
  assumption



example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  rintro x xnonneg y ynonneg eq
  calc
  -- the claim is (sqrt x)^2 = x, so we can't use it directly,
  -- so I use rw instead
    x = (sqrt x)^2 := by rw [sq_sqrt xnonneg]
    _ = (sqrt y)^2 := by rw [eq]
    _ = y := by rw [sq_sqrt ynonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  rintro x xnonneg y ynonneg eq
  simp at eq -- removethe function description
  calc
    x = sqrt (x^2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y^2) := by rw [eq]
    _ = y := by rw [sqrt_sq ynonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  simp
  constructor
  · rintro ⟨a,h1,rfl⟩ -- rintro h; rcases h with ⟨a,h1,h2⟩
    --rw [←h2]
    apply sqrt_nonneg
  · rintro h
    use (x^2)
    exact ⟨sq_nonneg x, sqrt_sq h⟩


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  simp
  constructor
  · rintro ⟨y, rfl⟩
    apply sq_nonneg
  · rintro h
    use (sqrt x)
    apply sq_sqrt h

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

-- Classical.choose: an operator that maps "∃x, P x" to an element a:α satisfying P. (That is, such that we have a proof for P a.)
-- Classical.choose_spec: matches h to that proof (that is, a term of type P a, with a= Classical.choose h).
-- Note that the existence of h on itself means that we have a proof that ∃x, P x!
example : P (Classical.choose h) :=
  Classical.choose_spec h

-- ohad - tests
example: ∃x, P x :=
  h

-- theorem test1: ∃x, P x :=
--    h
theorem test2: P (Classical.choose h) :=
  Classical.choose_spec h
#check test2

-- trying to turn choose into a more standard global choice function
-- example (s : Set α) (h1 : ∃x, x∈s) : s :=
--   Classical.choose h1
-- UPDATE: never mind, won't work,
-- s is not a type :(\
noncomputable example (s : Set α) (h1 : ∃x, x∈s) : α :=
   Classical.choose h1

-- ohad: using the fact that all proofs of a statement are considered equal
example (h₁ h₂ : ∃ x, P x) :
    Classical.choose h₁ = Classical.choose h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  rw [hh]

noncomputable section

open Classical

-- can replace with just "choose" as we already opened Classical
def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

-- →: (inverse f)(f x) = x for all x:α.
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  -- case 1
  intro injf
  intro x
  let y : β := f x
  let x' : α := (inverse f) y
  show x' = x
  apply injf
  show f x' = f x
  apply inverse_spec y _
  use x

  -- case 2
  intro hleft a b aeqb
  calc
    a = (inverse f) (f a) := by rw [hleft]
    _ = (inverse f) (f b) := by rw [aeqb]
    _ = b := by rw [hleft]

-- shorter version
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf x
    let y : β := f x
    apply injf
    apply inverse_spec y (by use x)
  intro hleft a b aeqb
  rw [←hleft a, ←hleft b, aeqb]

-- oneliner!
-- the rw and use x are kind of cheating though
example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun injf x ↦ injf (inverse_spec (f x) (by use x)),
  fun hleft a b aeqb ↦ by rw [←hleft a, ←hleft b, aeqb]⟩

-- →:f((inverse f) y) = y for all y: β.
example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf y
    let h : ∃x:α, f x = y := surjf y
    exact inverse_spec y h
  intro rightinv y
  use (inverse f y)
  exact rightinv y

-- one-liner
example : Surjective f ↔ RightInverse (inverse f) f :=
 ⟨fun surjf y ↦ inverse_spec y (surjf y), fun rightinv y ↦ ⟨inverse f y, rightinv y⟩ ⟩
end

section
variable {α : Type*}
open Function

-- TODO: continue here

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
