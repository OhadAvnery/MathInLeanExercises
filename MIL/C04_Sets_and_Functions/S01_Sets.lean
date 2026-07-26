import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t -- unnecessary line, but it makes it more clear I guess
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · exact ⟨xs, by left; exact xt⟩
  · exact ⟨xs, by right; exact xu⟩

-- note: the above | syntax only works for rintro+rcases, and doesn't work in non-tactic world


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

-- found out a new tactic - tauto: opposite of contradiction
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · constructor
    · exact xs
    · contrapose xntu; left; tauto
  · contrapose xntu; right; tauto


example : s ∩ t = t ∩ s := by
  ext x -- simplification of doing constructor + intro x twice, I think?
  simp only [mem_inter_iff] -- not required
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (fun _x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · rintro ⟨xs, _⟩; exact xs
  · rintro xs
    constructor
    · exact xs
    · left; exact xs

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

--note: contrapose is classical - P->Q implies ¬Q->¬P
--Explanation: ¬P = P→False, so this is just Hom(_, False), which is a contravariant functor!
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      · left; exact xs
      · contrapose! xnt; exact xnt.2
    · constructor
      · right; exact xt
      · contrapose! xns; exact xns.1 -- need contrapose! and not just contrapose, to do Neg pushing
  · rintro ⟨xs | xt, xnst⟩
    · left
      constructor
      · exact xs
      · contrapose! xnst; exact ⟨xs, xnst⟩
    · right
      constructor
      · exact xt
      · contrapose! xnst; exact ⟨xnst, xt⟩


def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  -- telling simp to NOT turn "not even" to odd.
  -- otherwise it'll use a built-in predicate Odd which we don't want
  simp [-Nat.not_even_iff_odd]
  -- n∈A ↔ n∈univ is just simplified to "A n"
  apply Classical.em

-- since ∅={x|P x} with P x=False, ∅ is exactly the function: fun _ ↦ False
-- and "x∈∅" is ∅ x, or False.
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

-- univ = {x | P x}, P x = True → univ is fun _ ↦ True,
-- so x∈univ is equivalent to True.
-- "trivial" is the canonical term of type "True", I guess!
example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

#check Nat.Prime.eq_two_or_odd
#check Nat.odd_iff
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro np ngt2
  rcases (Nat.Prime.eq_two_or_odd np) with neq2 | nodd
  · linarith -- in fact, shows a contradiction
  · exact Nat.odd_iff.2 nodd

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

-- rwa [...] is a shortcut for "rw [...]; assumption"
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

-- test - like I suspected, the other case needs a reverse use of prime_iff
example (n : ℕ) (h : Nat.Prime n) : Prime n := by
  rwa [← Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

-- we define an external variable s⊆t.
-- this means that all examples below in the section
-- have an additional param, ssubt.
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  --include ssubt
  have xt : x∈t := ssubt xs
  --constructor <;> assumption [h0 x xt, h1 x xt]
  constructor
  · exact h₀ x xt
  · exact h₁ x xt

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, ⟨xe, xp⟩⟩
  -- doesn't work
  -- use x, ⟨ssubt xs, xp⟩
  use x
  exact ⟨ssubt xs, xp⟩
  -- other option:
  -- exact ⟨x, ssubt xs, xp⟩


end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end

-- test
section
variable (s : ℕ)
variable (h : False)

example : False := h

include h
theorem lol : False := by
  apply h

#print axioms lol
end
