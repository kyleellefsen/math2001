/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  use -3
  ring


example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


-- 3.2.4
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  rw [hj, hk]
  use k^2 * j
  ring

-- 3.2.5
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨t, ht⟩ := h
  use y * t
  rw [ht]
  ring

-- 3.2.6
example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`

-- 3.2.7
theorem t1 {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]

-- We're going to show that if we set b=14, and a∣b, then a ≤ 14
theorem a_divisor_of_14_is_less_than_14 {a:ℕ} (hab: a∣(14:ℕ)) : a ≤ 14 := by
  let hb : 0 < 14 := by norm_num
  apply t1 hb hab

#check a_divisor_of_14_is_less_than_14



--3.2.8
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  dsimp [(· ∣ ·)] at hab
  obtain ⟨k, hk⟩ := hab
  have h1 := calc
    0 < b := hb
    _ = a * k := by rw [hk]
  cancel k at h1

/-! # Exercises (3.2.9) -/


example (t : ℤ) : t ∣ 0 := by
  let k : ℤ := 0
  let hk : 0 = t * k := by calc
    0 = t * 0 := by ring
    _ = t * k := by rw [←Eq.refl k]
  dsimp [(·∣·)]
  use k
  exact hk


example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  . conv in (3 * -4) => rw [show (3 * -4 : ℤ) = -12 by rfl]
    norm_num
  . numbers


example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  dsimp [·∣·]
  conv in (3 * (x * k) - 4 * (x * k) ^ 2) =>
    rw [show 3 * (x * k) - 4 * (x * k) ^ 2 = x * 3 * k - x ^ 2 * 4 * k^2 by ring]
    rw [show x * 3 * k - x ^ 2 * 4 * k^2 = x * (3 * k - x * 4 * k^2) by ring]
  use 3 * k - x * 4 * k^2
  rfl


-- I can't use calc mode inside conv mode, even though it would be very convenient.
-- It simplifies the proof above a lot
example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  dsimp [·∣·]
  conv in (3 * (x * k) - 4 * (x * k) ^ 2) =>
    calc
      3 * (x * k) - 4 * (x * k) ^ 2
        = x * 3 * k - x ^ 2 * 4 * k^2 := by ring
      _ = x * (3 * k - x * 4 * k^2) := by ring
  use 3 * k - x * 4 * k^2
  rfl

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  sorry

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  sorry

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  sorry

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  sorry

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  sorry
