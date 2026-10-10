/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

import Batteries.Tactic.Init

@[expose] public section

/-!
# Big-endian digits

Conversions between natural numbers and big-endian lists of digits in a given base. The digits are
represented as elements of `Fin base`.

The definitions are simple specifications. They are replaced at runtime, using `csimp`, by
divide-and-conquer implementations, which are subquadratic when combined with the subquadratic
multiplication and division of `Nat`.
-/

namespace Nat

/--
Construct a natural number from a big-endian list of digits in the given base:
```
ofDigitsBE (base := 10) [2,3,4] = 234 -- 2*10^2 + 3*10^1 + 4*10^0
ofDigitsBE (base := 2) [0,1,0,0] = 4 -- 0*2^3 + 1*2^2 + 0*2^1 + 0*2^0
ofDigitsBE (base := b) [] = 0 -- any base, including "base 0" and "base 1"
```
There are no valid inputs other than `[]` in "base 0". In "base 1", the only valid digit is `0`
and therefore `ofDigitsBE (base := 1) l = 0`.
-/
def ofDigitsBE (l : List (Fin base)) : Nat :=
  l.foldl (fun n d => n * base + d.val) 0

/--
The `prec` least significant digits of `n` in the given `base`, listed in big-endian order.

Only "base 0" is invalid, this is ensured by a `NeZero base` instance. In "base 1" the result is
always a list of `0`s with length `prec`.
```
toDigitsUpToBE 123 10 3 = ([1,2,3] : List (Fin 10))
toDigitsUpToBE 123 10 2 = ([2,3] : List (Fin 10))
toDigitsUpToBE 4 2 4 = ([0,1,0,0] : List (Fin 2))
toDigitsUpToBE 12345 1 5 = ([0,0,0,0,0] : List (Fin 1))
```
-/
def toDigitsUpToBE (n base prec : Nat) [NeZero base] : List (Fin base) :=
  match prec with
  | 0 => []
  | prec+1 => toDigitsUpToBE (n / base) base prec ++ [Fin.ofNat base n]

/--
Big-endian list of digits of a natural number `n` in a given `base`. The base must be at least 2,
a tactic attempts to infer this fact from the context but it may need to be provided as a third
argument when the tactic fails.

When `n` is zero, the result is the empty list. Otherwise, the most significant digit is nonzero.
```
toDigitsBE 123 10 = ([1,2,3] : List (Fin 10))
toDigitsBE 4 2 = ([1,0,0] : List (Fin 2))
toDigitsBE 0 12345 = ([] : List (Fin 12345))
```
-/
def toDigitsBE (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  have : NeZero base := ⟨by omega⟩
  if n = 0 then [] else toDigitsBE (n / base) base ++ [Fin.ofNat base n]
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ### Lemmas -/

@[simp] theorem ofDigitsBE_nil : ofDigitsBE (base := base) [] = 0 := rfl

theorem ofDigitsBE_append {l₁ l₂ : List (Fin base)} :
    ofDigitsBE (l₁ ++ l₂) = ofDigitsBE l₁ * base ^ l₂.length + ofDigitsBE l₂ := by
  suffices ∀ n, l₂.foldl (fun n d => n * base + d.val) n
      = n * base ^ l₂.length + l₂.foldl (fun n d => n * base + d.val) 0 by
    rw [ofDigitsBE, List.foldl_append, this]; rfl
  induction l₂ with
  | nil => simp
  | cons d l ih =>
    intro n
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih, ih d, Nat.pow_succ', Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

@[simp] theorem ofDigitsBE_cons {l : List (Fin base)} :
    ofDigitsBE (d :: l) = d * base ^ l.length + ofDigitsBE l := by
  rw [← List.singleton_append, ofDigitsBE_append]; simp [ofDigitsBE]

@[simp] theorem toDigitsUpToBE_zero [NeZero base] : toDigitsUpToBE n base 0 = [] := rfl

@[simp] theorem toDigitsUpToBE_succ [NeZero base] :
    toDigitsUpToBE n base (prec+1) = toDigitsUpToBE (n / base) base prec ++ [Fin.ofNat base n] :=
  rfl

@[simp] theorem length_toDigitsUpToBE [NeZero base] :
    (toDigitsUpToBE n base prec).length = prec := by
  induction prec generalizing n with simp [*]

@[simp] theorem ofDigitsBE_toDigitsUpToBE [NeZero base] :
    ofDigitsBE (toDigitsUpToBE n base prec) = n % base ^ prec := by
  induction prec generalizing n with
  | zero => simp [Nat.mod_one, ofDigitsBE]
  | succ prec ih =>
    simp only [toDigitsUpToBE_succ, ofDigitsBE_append, ih, List.length_singleton,
      ofDigitsBE_cons, List.length_nil, Nat.pow_zero, Nat.mul_one, ofDigitsBE_nil, Nat.add_zero,
      Fin.val_ofNat, Nat.pow_succ']
    rw [Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

theorem toDigitsUpToBE_add [NeZero base] : toDigitsUpToBE n base (prec + k) =
    toDigitsUpToBE (n / base ^ k) base prec ++ toDigitsUpToBE (n % base ^ k) base k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [← Nat.add_assoc, toDigitsUpToBE_succ, ih, toDigitsUpToBE_succ, List.append_assoc,
      Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mod_mul_right_div_self]
    congr 3
    ext; simp [Nat.mod_mul_right_mod]

theorem toDigitsBE_zero (h : 2 ≤ base) : toDigitsBE 0 base = [] := by
  rw [toDigitsBE, ite_eq_left rfl]

theorem toDigitsBE_of_ne_zero (h : 2 ≤ base) [NeZero base] (hn : n ≠ 0) :
    toDigitsBE n base = toDigitsBE (n / base) base ++ [Fin.ofNat base n] := by
  rw [toDigitsBE, ite_eq_right hn]

@[simp] theorem ofDigitsBE_toDigitsBE (h : 2 ≤ base) : ofDigitsBE (toDigitsBE n base) = n := by
  have : NeZero base := ⟨by omega⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if hn : n = 0 then
      rw [hn, toDigitsBE_zero, ofDigitsBE_nil]
    else
      rw [toDigitsBE_of_ne_zero h hn, ofDigitsBE_append, ih _ (Nat.div_lt_self (by omega) h)]
      simp [Nat.div_add_mod']

theorem toDigitsBE_eq_append (h : 2 ≤ base) [NeZero base] (hk : base ^ k ≤ n) :
    toDigitsBE n base = toDigitsBE (n / base ^ k) base ++ toDigitsUpToBE (n % base ^ k) base k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hn : n ≠ 0 := Nat.ne_of_gt <| Nat.lt_of_lt_of_le (Nat.pow_pos (by omega)) hk
    have hk : base ^ k ≤ n / base := by
      rw [Nat.le_div_iff_mul_le (by omega), ← Nat.pow_succ]; exact hk
    rw [toDigitsBE_of_ne_zero h hn, ih hk, toDigitsUpToBE_succ, List.append_assoc,
      Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mod_mul_right_div_self]
    congr 3
    ext; simp [Nat.mod_mul_right_mod]

/-! ### Subquadratic implementations -/

/-- Divide-and-conquer implementation of `ofDigitsBE`. -/
def ofDigitsBEImpl (l : List (Fin base)) : Nat :=
  if l.length ≤ 16 then ofDigitsBE l else
    let k := l.length / 2
    ofDigitsBEImpl (l.take k) * base ^ (l.length - k) + ofDigitsBEImpl (l.drop k)
termination_by l.length

@[csimp] theorem ofDigitsBE_eq_ofDigitsBEImpl : @ofDigitsBE = @ofDigitsBEImpl := by
  funext base l
  fun_induction ofDigitsBEImpl l with
  | case1 => rfl
  | case2 l _ k ih₁ ih₂ =>
    rw [← ih₁, ← ih₂, ← List.length_drop, ← ofDigitsBE_append, List.take_append_drop]

/-- Divide-and-conquer implementation of `toDigitsUpToBE`. -/
def toDigitsUpToBEImpl (n base prec : Nat) [NeZero base] : List (Fin base) :=
  go n prec []
where
  /-- Prepends `toDigitsUpToBE n base prec` to `acc`. -/
  go (n prec : Nat) (acc : List (Fin base)) : List (Fin base) :=
    if prec ≤ 16 then loop n prec acc else
      let k := prec / 2
      go (n / base ^ k) (prec - k) (go (n % base ^ k) k acc)
  termination_by prec
  /-- Prepends `toDigitsUpToBE n base prec` to `acc`, one digit at a time. -/
  loop (n : Nat) : Nat → List (Fin base) → List (Fin base)
    | 0, acc => acc
    | prec+1, acc => loop (n / base) prec (Fin.ofNat base n :: acc)

theorem toDigitsUpToBEImpl.loop_eq [NeZero base] {acc : List (Fin base)} :
    loop base n prec acc = toDigitsUpToBE n base prec ++ acc := by
  induction prec generalizing n acc with
  | zero => rfl
  | succ prec ih => simp [loop, ih]

theorem toDigitsUpToBEImpl.go_eq [NeZero base] {acc : List (Fin base)} :
    go base n prec acc = toDigitsUpToBE n base prec ++ acc := by
  fun_induction go base n prec acc with
  | case1 => exact loop_eq
  | case2 n prec acc _ k ih₁ _ ih₂ =>
    rw [ih₂, ih₁, ← List.append_assoc, ← toDigitsUpToBE_add,
      Nat.sub_add_cancel (Nat.div_le_self ..)]

@[csimp] theorem toDigitsUpToBE_eq_toDigitsUpToBEImpl :
    @toDigitsUpToBE = @toDigitsUpToBEImpl := by
  funext n base prec _
  rw [toDigitsUpToBEImpl, toDigitsUpToBEImpl.go_eq, List.append_nil]

/-- Divide-and-conquer implementation of `toDigitsBE`. -/
def toDigitsBEImpl (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  go n []
where
  /-- Prepends `toDigitsBE n base` to `acc`. -/
  go (n : Nat) (acc : List (Fin base)) : List (Fin base) :=
    have : NeZero base := ⟨by omega⟩
    -- `k` is about half the number of digits, and `base ^ k ≤ n` whenever `0 < k`
    let k := n.log2 / (2 * base.log2 + 2)
    if h : 8 ≤ k ∧ base ^ k ≤ n then
      have : 1 < base ^ k := Nat.lt_of_lt_of_le hbase (Nat.le_self_pow (by omega) _)
      have : n / base ^ k < n := Nat.div_lt_self (by omega) this
      go (n / base ^ k) (toDigitsUpToBE (n % base ^ k) base k ++ acc)
    else
      loop n acc
  termination_by n
  /-- Prepends `toDigitsBE n base` to `acc`, one digit at a time. -/
  loop (n : Nat) (acc : List (Fin base)) : List (Fin base) :=
    have : NeZero base := ⟨by omega⟩
    if n = 0 then acc else loop (n / base) (Fin.ofNat base n :: acc)
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem toDigitsBEImpl.loop_eq (hbase : 2 ≤ base) {acc : List (Fin base)} :
    loop base hbase n acc = toDigitsBE n base ++ acc := by
  have : NeZero base := ⟨by omega⟩
  fun_induction loop base hbase n acc with
  | case1 => rw [toDigitsBE_zero, List.nil_append]
  | case2 n acc _ hn ih => rw [ih, toDigitsBE_of_ne_zero hbase hn, List.append_assoc]; rfl

theorem toDigitsBEImpl.go_eq (hbase : 2 ≤ base) {acc : List (Fin base)} :
    go base hbase n acc = toDigitsBE n base ++ acc := by
  have : NeZero base := ⟨by omega⟩
  fun_induction go base hbase n acc with
  | case1 n acc _ k hk _ _ ih => rw [ih, toDigitsBE_eq_append hbase hk.2, List.append_assoc]
  | case2 => exact loop_eq hbase

@[csimp] theorem toDigitsBE_eq_toDigitsBEImpl : @toDigitsBE = @toDigitsBEImpl := by
  funext n base hbase
  rw [toDigitsBEImpl, toDigitsBEImpl.go_eq, List.append_nil]
