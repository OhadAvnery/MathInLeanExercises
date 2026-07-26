import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06


def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

-- note: won't work for |a-b|=|b-a|
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

#check le_of_max_le_left
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  -- two ways to prove the max inequality
  have hns : n ≥ Ns := by linarith [le_max_left Ns Nt]
  have hnt : n ≥ Nt := by apply le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add_le
    _ < ε := by linarith [hs n hns, ht n hnt]

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  -- |c(s n - a)| < ε iff |s n - a| < ε / |c|
  have εcpos : ε / |c| > 0 := div_pos εpos acpos;
  rcases cs (ε / |c|) εcpos with ⟨N, hN⟩
  use N
  intro n hn
  calc
    |c * s n - c * a| = |c * (s n - a)| := by congr; ring
    _ = |c| * |s n - a| := by apply abs_mul
    _ < |c| * (ε / |c|) := by apply (mul_lt_mul_iff_right₀ acpos).2 _; exact hN n hn
    _ = ε := by apply mul_div_cancel₀ _; linarith -- X*(Y/X)=Y, then show X≠0

-- notes:
-- statements that include a ₀ subscript - on groups with zero,
-- have to prove that stuff are non-zero or >0 to use them



theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hnN
  calc
    |s n| = |(s n - a) + a| := by congr; abel
    _ ≤ |s n - a| + |a| := by apply abs_add_le
    _ < |a| + 1 := by linarith [h n hnN]

--#search "for real A,B,C,D≥0, if A<B and C<D then A*C<B*D."
#check mul_lt_mul
#check mul_lt_mul'
#check mul_lt_mul''
-- these are three different theorems!
-- I used the third one, because it's the useful one for me - the first two terms
-- can be zero

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩ -- the placeholder has to be ε/B, the compiler deduces it from the use of pos₀
  use max N₀ N₁
  intro n hnmax
  calc
    |s n * t n - 0| = |s n * t n| := by congr; abel
    _ = |s n| * |t n| := abs_mul _ _
    _ < B * (ε/B) := by
        apply mul_lt_mul'' _ _ _ _;
        · apply h₀ n _; apply le_of_max_le_left hnmax;
        · convert h₁ n (le_of_max_le_right hnmax); abel
        · apply abs_nonneg
        · apply abs_nonneg
    _ = ε := by apply mul_div_cancel₀ _; linarith


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1 -- one-layer depth in proving equalities
  · ext; ring
  ring

-- already proved it in S06_alt without the skeleton :)
-- now trying again with the skeleton
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply abs_pos.2 _; contrapose! abne; linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa N _; apply le_max_left
  have absb : |s N - b| < ε := by apply hNb N _; apply le_max_right
  have : |a - b| < |a - b| := by calc
    |a - b| = |(a - s N) + (s N - b)| := by congr; abel
    _ ≤ |a - s N| + |s N - b| := by apply abs_add_le
    _ = |s N - a| + |s N - b| := by rw [abs_sub_comm]
    _ < ε + ε := by linarith
    _ = |a - b| := by ring --change (|a-b|/2 + |a-b|/2 = |a-b|); ring
  exact lt_irrefl _ this
section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
