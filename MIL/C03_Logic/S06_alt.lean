import MIL.Common
import Mathlib.Data.Real.Basic

-- trying to reconstruct stuff about limits before reading the chapter


-- working with functions s:ℕ→ℝ
def eventuallyIn (s : ℕ → ℝ) (L : ℝ) (ε : ℝ) :=
  ∃N : ℕ, ∀n : ℕ, n>N → |s n - L| < ε

#check eventuallyIn

def converges (s : ℕ → ℝ) (L : ℝ) :=
  ∀ε : ℝ, ε > 0 → eventuallyIn s L ε

example : converges (fun _n ↦ 5) (5) := by
  dsimp only [converges, eventuallyIn]
  rintro ε h_eps
  use 0 -- any natural number will work
  intro n _ -- assumption n>0 isn't needed
  norm_num -- simplify |5-5| to 0
  exact h_eps

-- #search "get the ceiling of a real number."
--#search "for real a,b, if a,b>0 then a/b>0."
--#search "for all real x, ceil(x) ≥ x."
--#search "for natural numbers n>m, n>m as real numbers."
--#search "for real a,b, if a>b>0 then 1/a<1/b."
--#search "for real a, 1/(1/a)=a."
--#search "for natural N, (N:ℝ)≥0."
--#search "natural numbers are non-negative."
example : converges (fun n ↦ 1/(n:ℝ)) (0) := by
  rintro ε h_eps
  let N : ℕ := Nat.ceil (1/ε)
  use N
  rintro n h_n_N
  dsimp
  --#search "n-0=n."
  rw [tsub_zero]

  have h1 : (n:ℝ) > 0 := by
    have : (n:ℝ) > (N:ℝ) := by exact_mod_cast h_n_N
    have : 0 ≤ (N:ℝ) := by exact_mod_cast (Nat.zero_le N)
    linarith
  have h2 : 1/(n:ℝ) > 0 := div_pos (by norm_num) h1

  --#search "if a>0 then a≥0."
  --have h3 : 1/(n:ℝ) ≥ 0 := by linarith
  rw [abs_of_nonneg (by linarith)]

  have h3 : (N:ℝ) ≥ 1/ε := Nat.le_ceil (1/ε)
  have h4 : (n:ℝ) > (N:ℝ) := by exact_mod_cast h_n_N
  have h5 : (n:ℝ) > 1/ε := by linarith
  -- woo boy
  have h6 : 1/(n:ℝ) < 1/(1/ε) := (one_div_lt_one_div h1 (div_pos (by norm_num) h_eps)).mpr h5
  rw [one_div_one_div] at h6
  exact h6

-- done with the example above :)
--I mostly used #search. There are two instances that I couldn't get with it,
--and had to use chatgpt explicitly:
-- If n>m as natural numbers, then n:R>m:R - tactic is exact_mod_cast.
-- If n is natural then n>=0 - Nat.zero_le.


#search "for real a,b,c, |a-c|≤|a-b|+|b-c|."
#search "for real a,b, |a-b|=|b-a|."
#search "max(a,b)≥a and max(a,b)≥b."
#search "n+1>n for all natural n."
#check ENat.natCast_lt_succ
#check lt_add_one
#search "for all real a,b,c, if a>b≥c then a>c."
theorem uniqueLimits {f : ℕ → ℝ} {L1 L2 : ℝ} (hL1 : converges f L1) (hL2 : converges f L2) : L1=L2 := by
  have aux {f : ℕ → ℝ} {L1 L2 : ℝ} (hL1 : converges f L1) (hL2 : converges f L2): L1≤L2 := by
    by_contra h
    push Not at h
    let ε : ℝ := (L1-L2)/2
    have h_eps : ε>0 := by dsimp [ε]; linarith

    have h_L1_eps : eventuallyIn f L1 ε := hL1 ε h_eps
    rcases h_L1_eps with ⟨N1, hN1⟩
    have h_L2_eps : eventuallyIn f L2 ε := hL2 ε h_eps
    rcases h_L2_eps with ⟨N2, hN2⟩

    --#check le_max_left N1 N2
    let n : ℕ := max N1 N2 + 1
    have h_n_1 : n > max N1 N2 := by apply lt_add_one

    -- earlier attempt with calc didn't work, so made a simpler strategy
    -- n>max N1 N2 is used for both steps, and with anonymous constructors
    -- for both "max a b ≥ a" and "max a b ≥ b"
    have h_n_N1 : n > N1 := by linarith [le_max_left N1 N2]
    have h_n_L1 : |f n - L1| < ε := hN1 n h_n_N1

    have h_n_N2 : n > N2 := by linarith [le_max_right N1 N2]
    have h_n_L2 : |f n - L2| < ε := hN2 n h_n_N2

    have h_L1_L2 : L1 - L2 < L1 - L2 := by calc
      L1 - L2 = |L1 - L2| := by rw [abs_of_nonneg (by linarith)]
      _ = |(L1 - f n) + (f n - L2)| := by abel_nf
      _ ≤ |L1 - f n| + |f n - L2| := by apply abs_add_le
      _ = |f n - L1| + |f n - L2| := by rw [abs_sub_comm]
      _ < ε + ε := by linarith
      _ = L1 - L2 := by dsimp [ε]; linarith

    -- L1-L2<L1-L2 is a contradiction
    exact lt_irrefl (L1 - L2) h_L1_L2

  have : L1≤L2 := aux hL1 hL2
  have : L2≤L1 := aux hL2 hL1
  linarith

-- help I got from gpt:
--1. have ε : ℝ := (L1-L2)/2, and tried ε>0 by linarith.
-- didn't work, it suggested to use "let" to remember the value, then use dsimp [ε] to simplify it.
-- 2. I realized n-1 in natural numbers is truncated subraction, so "n>n-1" doesn't always hold!
-- instead I could have used "omega" for natural number arithmetic
