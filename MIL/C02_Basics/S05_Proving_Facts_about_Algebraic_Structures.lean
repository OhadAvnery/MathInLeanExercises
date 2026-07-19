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

-- TODO - EXERCISE: build in Lean an explicit example of a non-distributive lattice!

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
    _ = a ⊔ (a ⊔ b) ⊓ c := by sorry -- rw [sup_comm a b, absorb1]
  sorry

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
  sorry

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
