/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

def example_221 (x : ℚ) (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

-- positive example of 221
def a₁: ℚ := (2/3)
def a₁_eq : 3 * a₁ = 2 := by rfl
#check (example_221 a₁ a₁_eq)

def example_221_decidable (x : ℚ) (hx : 3 * x = 2) : Bool :=
  x ≠ 1

---- negative example of 221
-- def a₂: ℚ := (7/3)
-- def a₂_eq : 3 * a₂ = 2 := by rfl
-- #check a₂_eq
-- #check (example_221 a₂ a₂_eq)
-- #eval example_221_decidable a₂ a₂_eq

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    0 ≤ y ^ 2 := by exact sq_nonneg y
    _ < y ^ 2 + 1 := by extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


-- /-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h1 := calc
    4 = -1 + (5) := by rfl
    _ = -1 + (m + 1) := by rw [hm]
    _ = m := by ring
  calc
    6 < 3 * 4 := by numbers
    _ = 3 * m := by rw [h1]




example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = (1 / 3) * (3 * s) := by ring
    _ ≤ (1 / 3) * -6 := by rel [h1]
    _ = -2 := by ring
  calc
    -2 = (1/2) * -4  := by ring
    _ ≤ (1/2) * (2 * s) := by rel [h2]
    _ = s := by ring
