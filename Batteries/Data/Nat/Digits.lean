/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

import Batteries.Tactic.Init

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
ofFinDigits (base := 10) [2,3,4] = 234 -- 2*10^2 + 3*10^1 + 4*10^0
ofFinDigits (base := 2) [0,1,0,0] = 4 -- 0*2^3 + 1*2^2 + 0*2^1 + 0*2^0
ofFinDigits (base := b) [] = 0 -- any base, including "base 0" and "base 1"
```
There are no valid inputs other than `[]` in "base 0". In "base 1", the only valid digit is `0`
and therefore `ofFinDigits (base := 1) l = 0`.
-/
@[expose] public def ofFinDigits (l : List (Fin base)) : Nat :=
  l.foldl (fun n d => n * base + d.val) 0

/--
The `prec` least significant digits of `n` in the given `base`, listed in big-endian order.

Only "base 0" is invalid, this is ensured by a `NeZero base` instance. In "base 1" the result is
always a list of `0`s with length `prec`.
```
toFinDigitsUpTo 123 10 3 = ([1,2,3] : List (Fin 10))
toFinDigitsUpTo 123 10 2 = ([2,3] : List (Fin 10))
toFinDigitsUpTo 4 2 4 = ([0,1,0,0] : List (Fin 2))
toFinDigitsUpTo 12345 1 5 = ([0,0,0,0,0] : List (Fin 1))
```
-/
@[expose] public def toFinDigitsUpTo (n base prec : Nat) [NeZero base] : List (Fin base) :=
  match prec with
  | 0 => []
  | prec+1 => toFinDigitsUpTo (n / base) base prec ++ [Fin.ofNat base n]

/--
Big-endian list of digits of a natural number `n` in a given `base`. The base must be at least 2,
a tactic attempts to infer this fact from the context but it may need to be provided as a third
argument when the tactic fails.

When `n` is zero, the result is the empty list. Otherwise, the most significant digit is nonzero.
```
toFinDigits 123 10 = ([1,2,3] : List (Fin 10))
toFinDigits 4 2 = ([1,0,0] : List (Fin 2))
toFinDigits 0 12345 = ([] : List (Fin 12345))
```
-/
public def toFinDigits (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  have : NeZero base := ⟨by omega⟩
  if n = 0 then [] else toFinDigits (n / base) base ++ [Fin.ofNat base n]
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ### Lemmas -/

@[simp] public theorem ofFinDigits_nil : ofFinDigits (base := base) [] = 0 := rfl

public theorem ofFinDigits_append {l₁ l₂ : List (Fin base)} :
    ofFinDigits (l₁ ++ l₂) = ofFinDigits l₁ * base ^ l₂.length + ofFinDigits l₂ := by
  suffices ∀ n, l₂.foldl (fun n d => n * base + d.val) n
      = n * base ^ l₂.length + l₂.foldl (fun n d => n * base + d.val) 0 by
    rw [ofFinDigits, List.foldl_append, this]; rfl
  induction l₂ with
  | nil => simp
  | cons d l ih =>
    intro n
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih, ih d, Nat.pow_succ', Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

@[simp] public theorem ofFinDigits_cons {l : List (Fin base)} :
    ofFinDigits (d :: l) = d * base ^ l.length + ofFinDigits l := by
  rw [← List.singleton_append, ofFinDigits_append]; simp [ofFinDigits]

@[simp] public theorem toFinDigitsUpTo_zero [NeZero base] : toFinDigitsUpTo n base 0 = [] := rfl

@[simp] public theorem toFinDigitsUpTo_succ [NeZero base] :
    toFinDigitsUpTo n base (prec+1) = toFinDigitsUpTo (n / base) base prec ++ [Fin.ofNat base n] :=
  rfl

@[simp] public theorem length_toFinDigitsUpTo [NeZero base] :
    (toFinDigitsUpTo n base prec).length = prec := by
  induction prec generalizing n with simp [*]

@[simp] public theorem ofFinDigits_toFinDigitsUpTo [NeZero base] :
    ofFinDigits (toFinDigitsUpTo n base prec) = n % base ^ prec := by
  induction prec generalizing n with
  | zero => simp [Nat.mod_one, ofFinDigits]
  | succ prec ih =>
    simp only [toFinDigitsUpTo_succ, ofFinDigits_append, ih, List.length_singleton,
      ofFinDigits_cons, List.length_nil, Nat.pow_zero, Nat.mul_one, ofFinDigits_nil, Nat.add_zero,
      Fin.val_ofNat, Nat.pow_succ']
    rw [Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

public theorem toFinDigitsUpTo_add [NeZero base] : toFinDigitsUpTo n base (prec + k) =
    toFinDigitsUpTo (n / base ^ k) base prec ++ toFinDigitsUpTo (n % base ^ k) base k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [← Nat.add_assoc, toFinDigitsUpTo_succ, ih, toFinDigitsUpTo_succ, List.append_assoc,
      Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mod_mul_right_div_self]
    congr 3
    ext; simp [Nat.mod_mul_right_mod]

public theorem toFinDigits_zero (h : 2 ≤ base) : toFinDigits 0 base = [] := by
  rw [toFinDigits, ite_eq_left rfl]

public theorem toFinDigits_of_ne_zero (h : 2 ≤ base) [NeZero base] (hn : n ≠ 0) :
    toFinDigits n base = toFinDigits (n / base) base ++ [Fin.ofNat base n] := by
  rw [toFinDigits, ite_eq_right hn]

@[simp] public theorem ofFinDigits_toFinDigits (h : 2 ≤ base) :
    ofFinDigits (toFinDigits n base) = n := by
  have : NeZero base := ⟨by omega⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if hn : n = 0 then
      rw [hn, toFinDigits_zero, ofFinDigits_nil]
    else
      rw [toFinDigits_of_ne_zero h hn, ofFinDigits_append, ih _ (Nat.div_lt_self (by omega) h)]
      simp [Nat.div_add_mod']

public theorem toFinDigits_eq_append (h : 2 ≤ base) [NeZero base] (hk : base ^ k ≤ n) :
    toFinDigits n base =
      toFinDigits (n / base ^ k) base ++ toFinDigitsUpTo (n % base ^ k) base k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hn : n ≠ 0 := Nat.ne_of_gt <| Nat.lt_of_lt_of_le (Nat.pow_pos (by omega)) hk
    have hk : base ^ k ≤ n / base := by
      rw [Nat.le_div_iff_mul_le (by omega), ← Nat.pow_succ]; exact hk
    rw [toFinDigits_of_ne_zero h hn, ih hk, toFinDigitsUpTo_succ, List.append_assoc,
      Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mod_mul_right_div_self]
    congr 3
    ext; simp [Nat.mod_mul_right_mod]

/-! ### Subquadratic implementations -/

/-- Divide-and-conquer implementation of `ofFinDigits`. -/
public def ofFinDigitsImpl (l : List (Fin base)) : Nat :=
  if l.length ≤ 16 then ofFinDigits l else
    let k := l.length / 2
    ofFinDigitsImpl (l.take k) * base ^ (l.length - k) + ofFinDigitsImpl (l.drop k)
termination_by l.length

@[csimp] public theorem ofFinDigits_eq_ofFinDigitsImpl : @ofFinDigits = @ofFinDigitsImpl := by
  funext base l
  fun_induction ofFinDigitsImpl l with
  | case1 => rfl
  | case2 l _ k ih₁ ih₂ =>
    rw [← ih₁, ← ih₂, ← List.length_drop, ← ofFinDigits_append, List.take_append_drop]

/-- Divide-and-conquer implementation of `toFinDigitsUpTo`. -/
public def toFinDigitsUpToImpl (n base prec : Nat) [NeZero base] : List (Fin base) :=
  loopSplit n prec []
where
  /-- Prepends `toFinDigitsUpTo n base prec` to `acc`. -/
  loopSplit (n prec : Nat) (acc : List (Fin base)) : List (Fin base) :=
    if prec ≤ 16 then loopDigit n prec acc else
      let k := prec / 2
      loopSplit (n / base ^ k) (prec - k) (loopSplit (n % base ^ k) k acc)
  termination_by prec
  /-- Prepends `toFinDigitsUpTo n base prec` to `acc`, one digit at a time. -/
  loopDigit (n : Nat) : Nat → List (Fin base) → List (Fin base)
    | 0, acc => acc
    | prec+1, acc => loopDigit (n / base) prec (Fin.ofNat base n :: acc)

private theorem toFinDigitsUpToImpl.loopDigit_eq [NeZero base] {acc : List (Fin base)} :
    loopDigit base n prec acc = toFinDigitsUpTo n base prec ++ acc := by
  induction prec generalizing n acc with
  | zero => rfl
  | succ prec ih => simp [loopDigit, ih]

private theorem toFinDigitsUpToImpl.loopSplit_eq [NeZero base] {acc : List (Fin base)} :
    loopSplit base n prec acc = toFinDigitsUpTo n base prec ++ acc := by
  fun_induction loopSplit base n prec acc with
  | case1 => exact loopDigit_eq
  | case2 n prec acc _ k ih₁ _ ih₂ =>
    rw [ih₂, ih₁, ← List.append_assoc, ← toFinDigitsUpTo_add,
      Nat.sub_add_cancel (Nat.div_le_self ..)]

@[csimp] public theorem toFinDigitsUpTo_eq_toFinDigitsUpToImpl :
    @toFinDigitsUpTo = @toFinDigitsUpToImpl := by
  funext n base prec _
  rw [toFinDigitsUpToImpl, toFinDigitsUpToImpl.loopSplit_eq, List.append_nil]

/-- Divide-and-conquer implementation of `toFinDigits`. -/
public def toFinDigitsImpl (n base : Nat) (hbase : 2 ≤ base := by omega) : List (Fin base) :=
  loopSplit n []
where
  /-- Prepends `toFinDigits n base` to `acc`. -/
  loopSplit (n : Nat) (acc : List (Fin base)) : List (Fin base) :=
    have : NeZero base := ⟨by omega⟩
    -- `k` is about half the number of digits, and `base ^ k ≤ n` whenever `0 < k`
    let k := n.log2 / (2 * base.log2 + 2)
    if h : 8 ≤ k ∧ base ^ k ≤ n then
      have : 1 < base ^ k := Nat.lt_of_lt_of_le hbase (Nat.le_self_pow (by omega) _)
      have : n / base ^ k < n := Nat.div_lt_self (by omega) this
      loopSplit (n / base ^ k) (toFinDigitsUpTo (n % base ^ k) base k ++ acc)
    else
      loopDigit n acc
  termination_by n
  /-- Prepends `toFinDigits n base` to `acc`, one digit at a time. -/
  loopDigit (n : Nat) (acc : List (Fin base)) : List (Fin base) :=
    have : NeZero base := ⟨by omega⟩
    if n = 0 then acc else loopDigit (n / base) (Fin.ofNat base n :: acc)
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

private theorem toFinDigitsImpl.loopDigit_eq (hbase : 2 ≤ base) {acc : List (Fin base)} :
    loopDigit base hbase n acc = toFinDigits n base ++ acc := by
  have : NeZero base := ⟨by omega⟩
  fun_induction loopDigit base hbase n acc with
  | case1 => rw [toFinDigits_zero, List.nil_append]
  | case2 n acc _ hn ih => rw [ih, toFinDigits_of_ne_zero hbase hn, List.append_assoc]; rfl

private theorem toFinDigitsImpl.loopSplit_eq (hbase : 2 ≤ base) {acc : List (Fin base)} :
    loopSplit base hbase n acc = toFinDigits n base ++ acc := by
  have : NeZero base := ⟨by omega⟩
  fun_induction loopSplit base hbase n acc with
  | case1 n acc _ k hk _ _ ih => rw [ih, toFinDigits_eq_append hbase hk.2, List.append_assoc]
  | case2 => exact loopDigit_eq hbase

@[csimp] public theorem toFinDigits_eq_toFinDigitsImpl : @toFinDigits = @toFinDigitsImpl := by
  funext n base hbase
  rw [toFinDigitsImpl, toFinDigitsImpl.loopSplit_eq, List.append_nil]
