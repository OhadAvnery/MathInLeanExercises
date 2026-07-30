import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    exact ⟨by tauto, by assumption⟩
  have : ∃ y, g y = x := by
    --simpa [this]
    simp at this
    assumption
  exact invFun_eq this

-- true even if g is not injective!
-- but requires choice in that case (to define g's inverse)
theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def -- A_def defines a proof for simplifying A
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    -- seems to show: if x₁∉A, then we can reduce to the case x₁∈A by symmetry
    -- kind of involved
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      -- to prove x₂∈A we're adding x₂∉A as an assumption. Funny stuff!
      -- could also prove by contradiction I think, though then it's non-constructive?
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        --have : x₂ = g (f x₂) := by sorry
        rw [hxeq]
        --symm -- to write the goal like the conclusion of invFun_eq
        --apply invFun_eq
        symm
        apply sb_right_inv f g
        exact x₂nA
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
  push Not at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  -- need: x1=x2. Reduce it to: g (g_inv x1) = g (g_inv x2).
  have : x₁ ∉ sbSet f g := by rw [←A_def]; exact xA.1
  rw [←sb_right_inv f g this]
  have : x₂ ∉ sbSet f g := by rw [←A_def]; exact xA.2
  rw [←sb_right_inv f g this]
  rw [hxeq]

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n -- splits natural numbers to cases 0 and n+1
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]
    apply hg hx

  -- assuming g y ∉ A, need to show y∈h'' A
  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg

end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
#print axioms schroeder_bernstein -- [propext, choice, Quot.sound]

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
