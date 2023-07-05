/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Std.Classes.Dvd

namespace Nat

#print Nat.recOn

/--
  Recursor identical to `Nat.rec` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def recAux {motive : Nat → Sort _} (zero : motive 0) (succ : ∀ n, motive n → motive (n+1)) :
    (t : Nat) → motive t
  | 0 => zero
  | _+1 => succ _ (Nat.recAux zero succ _)

/--
  Recursor identical to `Nat.recOn` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def recAuxOn {motive : Nat → Sort _} (t : Nat) (zero : motive 0)
  (succ : ∀ n, motive n → motive (n+1)) : motive t := Nat.recAux zero succ t

/--
  Recursor identical to `Nat.casesOn` but uses notations `0` for `Nat.zero` and `·+1` for `Nat.succ`
-/
@[elab_as_elim]
protected def casesAuxOn {motive : Nat → Sort _} (t : Nat) (zero : motive 0)
  (succ : ∀ n, motive (n+1)) : motive t := Nat.recAux zero (fun n _ => succ n) t

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def recDiag {motive : Nat → Nat → Sort _}
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 n → motive 0 (n+1))
  (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    (m n : Nat) → motive m n
  | 0, _ => right _
  | _, 0 => left _
  | _+1, _+1 => succ_succ _ _ (Nat.recDiag zero_zero zero_succ succ_zero succ_succ _ _)
where
  /-- Right leg for `Nat.recDiag` -/
  right : ∀ n, motive 0 n
  | 0 => zero_zero
  | _+1 => zero_succ _ (right _)
  /-- Left leg for `Nat.recDiag` -/
  left : ∀ m, motive m 0
  | 0 => zero_zero
  | _+1 => succ_zero _ (left _)

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def recDiagOn {motive : Nat → Nat → Sort _} (m n : Nat)
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 n → motive 0 (n+1))
  (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1)) :
    motive m n := Nat.recDiag zero_zero zero_succ succ_zero succ_succ m n

/--
  Diagonal recursor for `Nat`
-/
@[elab_as_elim]
protected def casesDiagOn {motive : Nat → Nat → Sort _} (m n : Nat)
  (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 (n+1))
  (succ_zero : ∀ m, motive (m+1) 0)
  (succ_succ : ∀ m n, motive (m+1) (n+1)) :
    motive m n :=
  Nat.recDiag zero_zero (fun _ _ => zero_succ _) (fun _ _ => succ_zero _)
    (fun _ _ _ => succ_succ _ _) m n

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat := ⟨fun a b => ∃ c, b = a * c⟩

/-- Sum of a list of natural numbers. -/
protected def sum (l : List Nat) : Nat := l.foldr (·+·) 0

/--
Integer square root function. Implemented via Newton's method.
-/
def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
termination_by iter guess => guess
