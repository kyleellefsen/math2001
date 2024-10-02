/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Real.Sqrt
import Library.Basic


math2001_init

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  have b2pos : b ^ 2 ≥ 0 := by exact sq_nonneg b
  have b2pos1 : b ^ 2 + 1 > 0 := by addarith[b2pos]
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := b2pos1



example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt': 0 < -x * t:= by addarith [hxt]
    have htx' := by
      calc
        0 < -x * t := hxt'
        _ = -t * x  := by ring
    cancel x at htx'
    apply ne_of_lt
    exact by addarith [htx']



def example253 : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  ring

#check example253


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1)
  use a
  ring


example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  · calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/



def ℚofFloat (f: Float) : ℚ :=
  let parts : ℤ × ℤ :=  Option.getD
                          (Float.toRatParts f)
                          ⟨0, 0⟩
  parts.fst * (2 ^ parts.snd)

def Floatofℚ (q: ℚ) : Float :=
  (Float.ofInt q.num) / (Float.ofInt q.den)

def roundTo (f: Float) (decimals: Nat) : Float :=
  let factor := (10: Nat) ^ decimals
  let factorfloat := Float.ofNat factor
  (f * factorfloat).round / factorfloat

#eval (ℚofFloat (Float.sqrt 1.69))
#eval Floatofℚ (ℚofFloat (Float.sqrt 1.69))

def veryclose := (ℚofFloat (Float.sqrt 1.69)) - (13 / 10)

#eval veryclose - (1 / 22517998136852480)

#eval ((Nat.sqrt 169) : ℚ) / (10 : ℚ)

example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 13/10
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6
  use 7

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.1
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4
  use 3
  ring

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := le_or_gt x 0
  obtain h | h := h
  · use 1
    calc
      1 ^ 2 = 1 := by ring
      _ > (0: ℚ) := by numbers
      _ ≥ x := by rel [h]
  · have h2 := lt_or_ge x 1
    obtain h2 | h2 := h2
    · use 1
      calc
        1 ^ 2 = 1 := by ring
        _ > x := h2
    · have h3 := gt_or_eq_of_le h2
      obtain h3 | h3 := h3
      · use x
        calc
          x ^ 2 = x * x := by ring
          _ > 1 * x := by rel [h3]
          _ = x := by ring
      · use 2
        calc
          2 ^ 2 = 4 := by ring
          _ > (1 : ℚ) := by numbers
          _ = x := Eq.symm h3


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
