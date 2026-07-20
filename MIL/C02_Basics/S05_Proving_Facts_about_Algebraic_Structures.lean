import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- ohad - character shortcuts:
--
-- α β χ ↓ ε ‹ γ ❰ ∩ ⊔ κ ← μ \n ∘ Π ∎ → σ ▸ \u ∨ ℘ × \y ζ
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)


-- ohad - can we check contradictions?
-- yes, it won't let us create any proof terms for it
-- but the type itself still exists!
-- it's a term of type Prop
#check (x < y) ∧ ¬(x < y)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- ohad: ⊔ = join, ⊓ = meet
-- ∪ = cap = union, ∩ = cap = intersection

-- ohad: this is a universal property -
-- x ⊓ y is the biggest element smaller than x,y.
-- shows that it's the unique property satisfying that
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

-- universal property: x⊔y = smallest element bigger than both x,y
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have h : ∀ a b : α, a ⊓ b ≤ b ⊓ a := by
    intro a b
    apply le_inf
    · apply inf_le_right
    apply inf_le_left
  apply le_antisymm
  repeat apply h

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm

  -- x⊓y⊓z ≤ x⊓(y⊓z)
  apply le_inf

  --x⊓y⊓z ≤ x
  trans x⊓y -- introduce a=x⊓y with x⊓y⊓z≤a≤x
  repeat apply inf_le_left

  --(x⊓y)⊓z≤y⊓z
  apply le_inf
  trans x⊓y
  apply inf_le_left
  apply inf_le_right
  apply inf_le_right

  -- x⊓(y⊓z) ≤ (x⊓y)⊓z
  apply le_inf

  -- x⊓(y⊓z) ≤ (x⊓y)
  apply le_inf
  apply inf_le_left
  trans y⊓z
  apply inf_le_right
  apply inf_le_left

  --x⊓(y⊓z) ≤ z
  trans y⊓z
  repeat apply inf_le_right

-- copying the ⊓ proof and changing names
example : x ⊔ y = y ⊔ x := by
  have h : ∀ a b : α, a ⊔ b ≤ b ⊔ a := by
    intro a b
    apply sup_le
    · apply le_sup_right
    · apply le_sup_left
  apply le_antisymm
  repeat apply h

-- the book solution is exactly the same,
-- but without the "repeat" trick, so 2 more lines
-- (and with the correctly indented bullets)
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  trans y⊔z
  apply le_sup_left
  apply le_sup_right
  trans y⊔z
  repeat apply le_sup_right
  apply sup_le
  trans x⊔y
  repeat apply le_sup_left
  apply sup_le
  trans x⊔y
  apply le_sup_right
  apply le_sup_left
  apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  rfl -- or: apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left


end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

-- ohad: from this point,
-- I'll use comm and assoc because I proved them

-- EXERCISE: build a non-distributive lattice
-- ANSWER: by brute force, the smallest example has 5 elements: 0<a,b,c<1, where each pair of a,b,c has
-- a join of 1 and a meet of 0.
-- TODO: construct this example in Lean explicitly. Prove that it's a lattice
-- and that ¬distributive holds.

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- TODO: finish
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  --#search "for real X,Y, if X=Y then Y=X."
  let h' : (a ⊔ b) ⊓ (a ⊔ c) =  a ⊔ b ⊓ c := by calc
    (a⊔b)⊓(a⊔c) = ((a⊔b)⊓a) ⊔ ((a⊔b)⊓c) := by apply h
    _ = a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm (a⊔b) a, absorb1 a b]
    _ = a ⊔ (c ⊓ (a ⊔ b)) := by rw [inf_comm]
    _ = a ⊔ ((c ⊓ a) ⊔ (c ⊓ b)) := by rw [h]
    _ = (a ⊔ (c ⊓ a)) ⊔ (c ⊓ b) := by rw [← sup_assoc]
    _ = a ⊔ b ⊓ c := by rw [inf_comm c a, absorb2, inf_comm]
  rw [h']

  -- apply le_antisymm
  -- -- ≤ is always true, even without h
  -- · apply sup_le
  --   · apply le_inf
  --     repeat apply le_sup_left
  --   · apply le_inf
  --     · trans b
  --       · apply inf_le_left
  --       · apply le_sup_right
  --     · trans c
  --       · apply inf_le_right
  --       · apply le_sup_right


example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a⊓b) a]
  rw [sup_comm (a⊓b) c]
  rw [absorb2]
  rw [h c]
  rw [← inf_assoc, sup_comm c a, absorb1, sup_comm c b]


end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

-- TODO: return to this after chapter 3
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

#search "a - a = 0 for all a." --sub_self
#search "a - b = a + (-b)." --sub_eq_add_neg
example (h : a ≤ b) : 0 ≤ b - a := by
  -- let ha : a - a = 0 := by apply sub_self
  rw [← sub_self a]
  repeat rw [sub_eq_add_neg, add_comm _ (-a)]
  apply add_le_add_right
  exact h

#search "-a + a = 0."
example (h: 0 ≤ b - a) : a ≤ b := by
  calc
    a = a + 0 := by abel
    _ ≤ a + (b - a) := by apply add_le_add_right h
    _ = b := by abel
  -- a = a + 0 := by exact (add_zero a).symm -- revser a+0=a
  -- _ = 0 + a := by exact add_comm a 0
  -- _ ≤ (b - a) + a := by group
  -- _  = a + (-a + a) := by rw [neg_add_cancel]
  -- _ = a - a + a := by rw [←add_assoc, sub_eq_add_neg]

#search "(x-y)*z=x*z-y*z." -- didn't work
#search "-(x*y) = (-x)*y."
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ b - a := by -- copying previous solution
    rw [← sub_self a]
    repeat rw [sub_eq_add_neg, add_comm _ (-a)]
    apply add_le_add_right
    exact h
  have h2 : 0≤(b-a)*c := by apply mul_nonneg h1 h'
  calc
    b * c = b * c + -(a * c) + a * c := by abel
    _ = b * c + ((-a) * c) + a * c := by rw [neg_mul]
    _ = (b - a) * c + a * c := by rw [← add_mul, sub_eq_add_neg]
    _ = a * c + (b - a) * c := by abel
    _ ≥ a * c + 0 := by apply add_le_add_right h2
    _ = a * c := by abel

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ (dist x y) * 2 := by
    calc
      0 = dist x x := by exact (dist_self x).symm
      _ ≤ dist x y + dist y x := by apply dist_triangle
      _ = dist x y + dist x y := by rw [dist_comm]
      _ = (dist x y) * 2 := by ring
  linarith

end
