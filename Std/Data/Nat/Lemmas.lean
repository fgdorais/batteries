/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro, F. G. Dorais
-/
import Std.Logic
import Std.Tactic.Basic
import Std.Data.Nat.Init.Lemmas
import Std.Data.Nat.Basic

namespace Nat

/-! ### rec/cases -/

section recAux
variable {motive : Nat → Sort _} (zero : motive 0) (succ : ∀ n, motive n → motive (n+1))

@[simp] theorem recAux_zero : Nat.recAux zero succ 0 = zero := rfl

theorem recAux_succ (n) : Nat.recAux zero succ (n+1) = succ n (Nat.recAux zero succ n) := rfl

@[simp] theorem recAuxOn_zero : Nat.recAuxOn 0 zero succ = zero := rfl

theorem recAuxOn_succ (n) : Nat.recAuxOn (n+1) zero succ = succ n (Nat.recAuxOn n zero succ) := rfl

variable (succ : ∀ n, motive (n+1))

@[simp] theorem casesAuxOn_zero : Nat.casesAuxOn 0 zero succ = zero := rfl

@[simp] theorem casesAuxOn_succ (n) : Nat.casesAuxOn (n+1) zero succ = succ n := rfl

end recAux

section recDiagAux
variable {motive : Nat → Nat → Sort _}
  (zero_left : ∀ n, motive 0 n) (zero_right : ∀ m, motive m 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1))

@[simp] theorem recDiagAux_zero_left (n) :
  Nat.recDiagAux zero_left zero_right succ_succ 0 n = zero_left n := by cases n <;> rfl

@[simp] theorem recDiagAux_zero_right (m)
  (h : zero_left 0 = zero_right 0 := by first | assumption | trivial) :
  Nat.recDiagAux zero_left zero_right succ_succ m 0 = zero_right m := by cases m; exact h; rfl

theorem recDiagAux_succ_succ (m n) :
  Nat.recDiagAux zero_left zero_right succ_succ (m+1) (n+1)
    = succ_succ m n (Nat.recDiagAux zero_left zero_right succ_succ m n) := rfl

end recDiagAux

section recDiag
variable {motive : Nat → Nat → Sort _} (zero_zero : motive 0 0)
  (zero_succ : ∀ n, motive 0 n → motive 0 (n+1)) (succ_zero : ∀ m, motive m 0 → motive (m+1) 0)
  (succ_succ : ∀ m n, motive m n → motive (m+1) (n+1))

@[simp] theorem recDiag_zero_zero :
  Nat.recDiag (motive:=motive) zero_zero zero_succ succ_zero succ_succ 0 0 = zero_zero := rfl

theorem recDiag_zero_succ (n) :
  Nat.recDiag zero_zero zero_succ succ_zero succ_succ 0 (n+1)
    = zero_succ n (Nat.recDiag zero_zero zero_succ succ_zero succ_succ 0 n) := by
  simp [Nat.recDiag]; rfl

theorem recDiag_succ_zero (m) :
  Nat.recDiag zero_zero zero_succ succ_zero succ_succ (m+1) 0
    = succ_zero m (Nat.recDiag zero_zero zero_succ succ_zero succ_succ m 0) := by
  simp [Nat.recDiag]; cases m <;> rfl

theorem recDiag_succ_succ (m n) :
  Nat.recDiag zero_zero zero_succ succ_zero succ_succ (m+1) (n+1)
    = succ_succ m n (Nat.recDiag zero_zero zero_succ succ_zero succ_succ m n) := rfl

@[simp] theorem recDiagOn_zero_zero :
  Nat.recDiagOn 0 0 (motive:=motive) zero_zero zero_succ succ_zero succ_succ = zero_zero := rfl

theorem recDiagOn_zero_succ (n) :
  Nat.recDiagOn 0 (n+1) zero_zero zero_succ succ_zero succ_succ
    = zero_succ n (Nat.recDiagOn 0 n zero_zero zero_succ succ_zero succ_succ) :=
  Nat.recDiag_zero_succ ..

theorem recDiagOn_succ_zero (m) :
  Nat.recDiagOn (m+1) 0 zero_zero zero_succ succ_zero succ_succ
    = succ_zero m (Nat.recDiagOn m 0 zero_zero zero_succ succ_zero succ_succ) :=
  Nat.recDiag_succ_zero ..

theorem recDiagOn_succ_succ (m n) :
  Nat.recDiagOn (m+1) (n+1) zero_zero zero_succ succ_zero succ_succ
    = succ_succ m n (Nat.recDiagOn m n zero_zero zero_succ succ_zero succ_succ) := rfl

variable (zero_succ : ∀ n, motive 0 (n+1)) (succ_zero : ∀ m, motive (m+1) 0)
  (succ_succ : ∀ m n, motive (m+1) (n+1))

@[simp] theorem casesDiagOn_zero_zero :
  Nat.casesDiagOn 0 0 (motive:=motive) zero_zero zero_succ succ_zero succ_succ = zero_zero := rfl

@[simp] theorem casesDiagOn_zero_succ (n) :
  Nat.casesDiagOn 0 (n+1) zero_zero zero_succ succ_zero succ_succ = zero_succ n := rfl

@[simp] theorem casesDiagOn_succ_zero (m) :
  Nat.casesDiagOn (m+1) 0 zero_zero zero_succ succ_zero succ_succ = succ_zero m := rfl

@[simp] theorem casesDiagOn_succ_succ (m n) :
  Nat.casesDiagOn (m+1) (n+1) zero_zero zero_succ succ_zero succ_succ = succ_succ m n := rfl

end recDiag

/-! ### le/lt -/

theorem ne_of_gt {a b : Nat} (h : b < a) : a ≠ b := (ne_of_lt h).symm

protected theorem le_of_not_le {a b : Nat} : ¬ a ≤ b → b ≤ a := (Nat.le_total a b).resolve_left

protected theorem lt_iff_le_not_le {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun h => Nat.gt_of_not_le h.2⟩

protected theorem lt_iff_le_and_ne {m n : Nat} : m < n ↔ m ≤ n ∧ m ≠ n :=
  Nat.lt_iff_le_not_le.trans (and_congr_right fun h =>
    not_congr ⟨Nat.le_antisymm h, fun e => e ▸ Nat.le_refl _⟩)

@[simp] protected theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
  ⟨Nat.gt_of_not_le, Nat.not_le_of_gt⟩

@[simp] protected theorem not_lt {a b : Nat} : ¬ a < b ↔ b ≤ a :=
  ⟨Nat.ge_of_not_lt, flip Nat.not_le_of_gt⟩

theorem le_lt_antisymm {n m : Nat} (h₁ : n ≤ m) (h₂ : m < n) : False :=
  Nat.lt_irrefl n (Nat.lt_of_le_of_lt h₁ h₂)

theorem lt_le_antisymm {n m : Nat} (h₁ : n < m) (h₂ : m ≤ n) : False :=
  le_lt_antisymm h₂ h₁

protected theorem lt_asymm {n m : Nat} (h₁ : n < m) : ¬ m < n :=
  le_lt_antisymm (Nat.le_of_lt h₁)

/-- Strong case analysis on `a < b ∨ b ≤ a` -/
protected def lt_sum_ge (a b : Nat) : a < b ⊕' b ≤ a :=
  if h : a < b then .inl h else .inr (Nat.not_lt.1 h)

/-- Strong case analysis on `a < b ∨ a = b ∨ b < a` -/
protected def sum_trichotomy (a b : Nat) : a < b ⊕' a = b ⊕' b < a :=
  match a.lt_sum_ge b with
  | .inl h => .inl h
  | .inr h₂ => match b.lt_sum_ge a with
    | .inl h => .inr <| .inr h
    | .inr h₁ => .inr <| .inl <| Nat.le_antisymm h₁ h₂

protected theorem lt_trichotomy (a b : Nat) : a < b ∨ a = b ∨ b < a :=
  match a.sum_trichotomy b with
  | .inl h => .inl h
  | .inr (.inl h) => .inr (.inl h)
  | .inr (.inr h) => .inr (.inr h)

protected theorem eq_or_lt_of_not_lt {a b : Nat} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  (Nat.lt_trichotomy a b).resolve_left hnlt

protected theorem not_lt_of_le {n m : Nat} (h₁ : m ≤ n) : ¬ n < m := (Nat.not_le_of_gt · h₁)

protected theorem not_le_of_lt {n m : Nat} : m < n → ¬ n ≤ m := Nat.not_le_of_gt

protected theorem lt_of_not_le {a b : Nat} : ¬ a ≤ b → b < a := (Nat.lt_or_ge b a).resolve_right

protected theorem le_of_not_lt {a b : Nat} : ¬ a < b → b ≤ a := (Nat.lt_or_ge a b).resolve_left

protected theorem le_or_le (a b : Nat) : a ≤ b ∨ b ≤ a := (Nat.lt_or_ge _ _).imp_left Nat.le_of_lt

protected theorem lt_or_eq_of_le {n m : Nat} (h : n ≤ m) : n < m ∨ n = m :=
  (Nat.lt_or_ge _ _).imp_right (Nat.le_antisymm h)

protected theorem le_iff_lt_or_eq {n m : Nat} : n ≤ m ↔ n < m ∨ n = m :=
  ⟨Nat.lt_or_eq_of_le, (·.elim Nat.le_of_lt Nat.le_of_eq)⟩

protected theorem le_antisymm_iff {n m : Nat} : n = m ↔ n ≤ m ∧ m ≤ n :=
  ⟨fun h => ⟨Nat.le_of_eq h, Nat.le_of_eq h.symm⟩, fun ⟨h₁, h₂⟩ => Nat.le_antisymm h₁ h₂⟩

/-! ### zero/one -/

protected theorem pos_iff_ne_zero : 0 < n ↔ n ≠ 0 :=
  ⟨ne_of_gt, Nat.pos_of_ne_zero⟩

theorem le_zero : i ≤ 0 ↔ i = 0 :=
  ⟨Nat.eq_zero_of_le_zero, fun | rfl => Nat.le_refl _⟩

theorem one_pos : 0 < 1 := Nat.zero_lt_one

theorem add_one_ne_zero (n) : n + 1 ≠ 0 := succ_ne_zero _

protected theorem eq_zero_of_nonpos : ∀ n, ¬0 < n → n = 0
  | 0 => fun _ => rfl
  | _+1 => absurd (Nat.zero_lt_succ _)

/-! ### succ/pred -/

attribute [simp] succ_ne_zero lt_succ_self Nat.pred_zero Nat.pred_succ

theorem succ_le : succ n ≤ m ↔ n < m := .rfl

theorem lt_succ : m < succ n ↔ m ≤ n :=
  ⟨le_of_lt_succ, lt_succ_of_le⟩

theorem lt_succ_of_lt : m < n → m < succ n := le_succ_of_le

theorem succ_ne_self : ∀ n, succ n ≠ n
  | _+1, h => succ_ne_self _ (succ.inj h)

theorem succ_pred_eq_of_pos : ∀ {n}, 0 < n → succ (pred n) = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_succ_pred : ∀ n, n = 0 ∨ n = succ (pred n)
  | 0 => .inl rfl
  | _+1 => .inr rfl

theorem exists_eq_succ_of_ne_zero : ∀ {n}, n ≠ 0 → ∃ k, n = succ k
  | _+1, _ => ⟨_, rfl⟩

theorem succ_eq_one_add (n) : succ n = 1 + n := Nat.add_comm _ 1

theorem succ_inj : succ n = succ m → n = m := succ.inj

theorem succ_inj' : succ n = succ m ↔ n = m :=
  ⟨succ.inj, congrArg _⟩

theorem pred_inj : ∀ {n m}, 0 < n → 0 < m → pred n = pred m → n = m
  | _+1, _+1, _, _ => congrArg _

theorem pred_inj' (hn : 0 < n) (hm : 0 < m) : pred n = pred m ↔ n = m :=
  ⟨pred_inj hn hm, congrArg _⟩

theorem pred_lt_pred : ∀ {n m}, n ≠ 0 → n < m → pred n < pred m
  | _+1, _+1, _, h => lt_of_succ_lt_succ h

theorem succ_le_succ_iff : succ m ≤ succ n ↔ m ≤ n :=
  ⟨le_of_succ_le_succ, succ_le_succ⟩

theorem succ_lt_succ_iff : succ m < succ n ↔ m < n :=
  ⟨lt_of_succ_lt_succ, succ_lt_succ⟩

theorem le_succ_of_pred_le : ∀ {n m}, pred n ≤ m → n ≤ succ m
  | 0, _, _ => Nat.zero_le ..
  | _+1, _, h => Nat.succ_le_succ h

theorem pred_le_of_le_succ : ∀ {n m}, n ≤ succ m → pred n ≤ m
  | 0, _, _ => Nat.zero_le _
  | _+1, _, h => Nat.le_of_succ_le_succ h

theorem pred_le_iff_le_succ : pred n ≤ m ↔ n ≤ succ m :=
  ⟨le_succ_of_pred_le, pred_le_of_le_succ⟩

theorem le_pred_of_lt : ∀ {m n}, m < n → m ≤ pred n
  | _, _+1, h => Nat.le_of_lt_succ h

/-! ### add -/

protected theorem add_add_add_comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem succ_add_eq_add_succ (n m) : succ n + m = n + succ m := Nat.succ_add ..

theorem one_add (n) : 1 + n = succ n := Nat.add_comm ..

protected theorem eq_zero_of_add_eq_zero_right : ∀ {n m}, n + m = 0 → n = 0
  | _, 0, h => h

protected theorem eq_zero_of_add_eq_zero_left : ∀ {n m}, n + m = 0 → m = 0
  | _, 0, _ => rfl

theorem eq_zero_of_add_eq_zero (H : n + m = 0) : n = 0 ∧ m = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero_right H, Nat.eq_zero_of_add_eq_zero_left H⟩

protected theorem add_left_cancel_iff {n m k : Nat} : n + m = n + k ↔ m = k :=
  ⟨Nat.add_left_cancel, fun | rfl => rfl⟩

protected theorem add_right_cancel_iff {n m k : Nat} : n + m = k + m ↔ n = k :=
  ⟨Nat.add_right_cancel, fun | rfl => rfl⟩

protected theorem add_le_add_iff_left (k n m : Nat) : k + n ≤ k + m ↔ n ≤ m :=
  ⟨Nat.le_of_add_le_add_left, fun h => Nat.add_le_add_left h _⟩

protected theorem add_le_add_iff_right (k n m : Nat) : n + k ≤ m + k ↔ n ≤ m :=
  ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

protected theorem lt_of_add_lt_add_right : ∀ {m : Nat}, k + m < n + m → k < n
  | 0, h => h
  | _+1, h => Nat.lt_of_add_lt_add_right (Nat.lt_of_succ_lt_succ h)

protected theorem lt_of_add_lt_add_left {k n m : Nat} : k + n < k + m → n < m := by
  repeat rw [Nat.add_comm k]
  exact Nat.lt_of_add_lt_add_right

protected theorem add_lt_add_iff_left (k n m : Nat) : k + n < k + m ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_left, fun h => Nat.add_lt_add_left h _⟩

protected theorem add_lt_add_iff_right (k n m : Nat) : n + k < m + k ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h _⟩

protected theorem lt_add_right (k : Nat) (h : n < m) : n < m + k :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem lt_add_of_pos_right (h : 0 < k) : n < n + k :=
  Nat.add_lt_add_left h n

protected theorem lt_add_of_pos_left : 0 < k → n < k + n := by
  rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right

protected theorem pos_of_lt_add_right (h : n < n + k) : 0 < k :=
  Nat.lt_of_add_lt_add_left h

protected theorem pos_of_lt_add_left : n < k + n → 0 < k := by
  rw [Nat.add_comm]; exact Nat.pos_of_lt_add_right

protected theorem lt_add_right_iff_pos : n < n + k ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_right, Nat.lt_add_of_pos_right⟩

protected theorem lt_add_left_iff_pos : n < k + n ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_left, Nat.lt_add_of_pos_left⟩

protected theorem add_pos_left (h : 0 < m) (n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem add_pos_right (m) (h : 0 < n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem add_self_ne_one : ∀ n, n + n ≠ 1
  | n+1, h => by rw [Nat.succ_add, Nat.succ_inj'] at h; contradiction

/-! ### sub -/

attribute [simp] Nat.zero_sub Nat.add_sub_cancel succ_sub_succ_eq_sub

theorem sub_lt_succ (a b) : a - b < succ a :=
  lt_succ_of_le (sub_le a b)

protected theorem le_of_le_of_sub_le_sub_right : ∀ {n m k : Nat}, k ≤ m → n - k ≤ m - k → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, _, h₁ => h₁
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_le_of_sub_le_sub_right (le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_right {n m k : Nat} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h _⟩

protected theorem sub_one (n) : n - 1 = pred n := rfl

theorem succ_sub_one (n) : succ n - 1 = n := rfl

protected theorem le_of_sub_eq_zero : ∀ {n m}, n - m = 0 → n ≤ m
  | 0, _, _ => Nat.zero_le ..
  | _+1, _+1, h => Nat.succ_le_succ <| Nat.le_of_sub_eq_zero (Nat.succ_sub_succ .. ▸ h)

protected theorem sub_eq_zero_iff_le : n - m = 0 ↔ n ≤ m :=
  ⟨Nat.le_of_sub_eq_zero, Nat.sub_eq_zero_of_le⟩

protected theorem sub_eq_iff_eq_add {a b c : Nat} (h : b ≤ a) : a - b = c ↔ a = c + b :=
  ⟨fun | rfl => by rw [Nat.sub_add_cancel h], fun heq => by rw [heq, Nat.add_sub_cancel]⟩

protected theorem lt_of_sub_eq_succ (H : m - n = succ l) : n < m :=
  Nat.not_le.1 fun H' => by simp [Nat.sub_eq_zero_of_le H'] at H

protected theorem sub_le_sub_left : ∀ (k : Nat) {n m}, n ≤ m → k - m ≤ k - n
  | 0, _, _, _ => by simp only [Nat.zero_sub]
  | _, 0, _, _ => Nat.sub_le ..
  | _+1, _+1, _+1, h => by
    simp only [Nat.succ_sub_succ]; exact Nat.sub_le_sub_left _ (Nat.le_of_succ_le_succ h)

theorem succ_sub_sub_succ (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

protected theorem sub_right_comm (m n k : Nat) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

protected theorem sub_pos_of_lt (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right
  rwa [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt h)]

protected theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  (Nat.sub_eq_iff_eq_add (Nat.sub_le ..)).2 (Nat.add_sub_of_le h).symm

protected theorem sub_add_comm {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right ..))]
  rwa [Nat.add_right_comm, Nat.sub_add_cancel]

theorem sub_one_sub_lt (h : i < n) : n - 1 - i < n := by
  rw [Nat.sub_sub]
  apply Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) h)
  rw [Nat.add_comm]; apply Nat.zero_lt_succ

protected theorem sub_lt_self (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  Nat.sub_lt (Nat.lt_of_lt_of_le h₀ h₁) h₀

protected theorem add_sub_cancel' {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]

protected theorem add_le_of_le_sub_left {n k m : Nat} (H : m ≤ k) (h : n ≤ k - m) : m + n ≤ k :=
  Nat.not_lt.1 fun h' => Nat.not_lt.2 h (Nat.sub_lt_left_of_lt_add H h')

theorem le_sub_iff_add_le {x y k : Nat} (h : k ≤ y) : x ≤ y - k ↔ x + k ≤ y := by
  rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_iff_right h, Nat.add_sub_cancel]

protected theorem sub_le_iff_le_add {a b c : Nat} : a - b ≤ c ↔ a ≤ c + b :=
  ⟨Nat.le_add_of_sub_le, Nat.sub_le_of_le_add⟩

protected theorem sub_le_iff_le_add' {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c := by
  rw [Nat.sub_le_iff_le_add, Nat.add_comm]

protected theorem sub_le_sub_iff_left {n m k : Nat} (hn : n ≤ k) : k - m ≤ k - n ↔ n ≤ m := by
  refine ⟨fun h => ?_, Nat.sub_le_sub_left _⟩
  rwa [Nat.sub_le_iff_le_add', ← Nat.add_sub_assoc hn,
    le_sub_iff_add_le (Nat.le_trans hn (Nat.le_add_left ..)),
    Nat.add_comm, Nat.add_le_add_iff_right] at h

protected theorem sub_add_lt_sub (h₁ : m + k ≤ n) (h₂ : 0 < k) : n - (m + k) < n - m :=
  match k with
  | zero => Nat.lt_irrefl _ h₂ |>.elim
  | succ _ =>
    Nat.lt_of_lt_of_le
      (pred_lt (Nat.ne_of_lt $ Nat.sub_pos_of_lt $ lt_of_succ_le h₁).symm)
      (Nat.sub_le_sub_left _ $ Nat.le_add_right ..)

/-! ## min/max -/

protected theorem min_succ_succ (x y) : min (succ x) (succ y) = succ (min x y) := by
  simp [Nat.min_def, succ_le_succ_iff]; split <;> rfl

protected theorem le_min {a b c : Nat} (_ : a ≤ b) (_ : a ≤ c) : a ≤ min b c := by
  rw [Nat.min_def]; split <;> assumption

protected theorem le_min_iff {a b c : Nat} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Nat.le_trans h (Nat.min_le_left ..), Nat.le_trans h (Nat.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => Nat.le_min h₁ h₂⟩

protected theorem lt_min_iff {a b c : Nat} : a < min b c ↔ a < b ∧ a < c := Nat.le_min_iff

protected theorem min_eq_left {a b : Nat} : a ≤ b → min a b = a := (if_pos ·)

protected theorem min_eq_right {a b : Nat} : b ≤ a → min a b = b := by
  rw [Nat.min_comm]; exact Nat.min_eq_left

@[simp] protected theorem min_self (a : Nat) : min a a = a := Nat.min_eq_left (Nat.le_refl _)

@[simp] protected theorem min_zero_left (a) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le _)

@[simp] protected theorem min_zero_right (a) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le _)

protected theorem min_assoc : ∀ (a b c : Nat), min (min a b) c = min a (min b c)
| 0, _, _ => by rw [Nat.min_zero_left, Nat.min_zero_left, Nat.min_zero_left]
| _, 0, _ => by rw [Nat.min_zero_left, Nat.min_zero_right, Nat.min_zero_left]
| _, _, 0 => by rw [Nat.min_zero_right, Nat.min_zero_right, Nat.min_zero_right]
| _+1, _+1, _+1 => by simp only [Nat.min_succ_succ]; exact congrArg succ <| Nat.min_assoc ..

protected theorem sub_sub_eq_min : ∀ (a b : Nat), a - (a - b) = min a b
  | 0, _ => by rw [Nat.zero_sub, Nat.min_zero_left]
  | _, 0 => by rw [Nat.sub_zero, Nat.sub_self, Nat.min_zero_right]
  | _+1, _+1 => by
    rw [Nat.succ_sub_succ, Nat.min_succ_succ, Nat.succ_sub (Nat.sub_le ..)]
    exact congrArg succ <| Nat.sub_sub_eq_min ..

protected theorem sub_eq_sub_min (n m : Nat) : n - m = n - min n m := by
  rw [Nat.min_def]; split
  next h => rw [Nat.sub_eq_zero_of_le h, Nat.sub_self]
  next => rfl

@[simp] protected theorem sub_add_min_cancel (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]

protected theorem max_succ_succ (x y) : max (succ x) (succ y) = succ (max x y) := by
  simp [Nat.max_def, succ_le_succ_iff]; split <;> rfl

protected theorem max_le {a b c : Nat} : a ≤ c → b ≤ c → max a b ≤ c := by
  intros; rw [Nat.max_def]; split <;> assumption

protected theorem max_le_iff {a b c : Nat} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Nat.le_trans (Nat.le_max_left ..) h, Nat.le_trans (Nat.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => Nat.max_le h₁ h₂⟩

protected theorem max_lt_iff {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.max_succ_succ a b]; exact Nat.max_le_iff

protected theorem max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b := if_pos h

protected theorem max_eq_left {a b : Nat} (h : b ≤ a) : max a b = a := by
  rw [Nat.max_comm]; exact Nat.max_eq_right h

@[simp] protected theorem max_self (a : Nat) : max a a = a := Nat.max_eq_right (Nat.le_refl _)

@[simp] protected theorem max_zero_left (a) : max 0 a = a := Nat.max_eq_right (Nat.zero_le _)

@[simp] protected theorem max_zero_right (a) : max a 0 = a := Nat.max_eq_left (Nat.zero_le _)

protected theorem max_assoc : ∀ (a b c : Nat), max (max a b) c = max a (max b c)
| 0, _, _ => by rw [Nat.max_zero_left, Nat.max_zero_left]
| _, 0, _ => by rw [Nat.max_zero_left, Nat.max_zero_right]
| _, _, 0 => by rw [Nat.max_zero_right, Nat.max_zero_right]
| _+1, _+1, _+1 => by simp only [Nat.max_succ_succ]; exact congrArg succ <| Nat.max_assoc ..

protected theorem sub_add_eq_max : ∀ (a b : Nat), a - b + b = max a b
  | 0, _ => by rw [Nat.zero_sub, Nat.zero_add, Nat.max_zero_left]
  | _, 0 => by rw [Nat.max_zero_right]; rfl
  | _+1, _+1 => by
    rw [Nat.succ_sub_succ, Nat.max_succ_succ]
    exact congrArg succ <| Nat.sub_add_eq_max ..

protected theorem sub_eq_max_sub (n m : Nat) : n - m = max n m - m := by
  rw [Nat.max_def]; split
  next h => rw [Nat.sub_eq_zero_of_le h, Nat.sub_self]
  next => rfl

protected theorem max_min_distrib_left : ∀ (a b c : Nat), max a (min b c) = min (max a b) (max a c)
  | 0, _, _ => by simp only [Nat.max_zero_left]
  | _, 0, _ => by
    rw [Nat.min_zero_left, Nat.max_zero_right]
    exact Nat.min_eq_left (Nat.le_max_left ..) |>.symm
  | _, _, 0 => by
    rw [Nat.min_zero_right, Nat.max_zero_right]
    exact Nat.min_eq_right (Nat.le_max_left ..) |>.symm
  | _+1, _+1, _+1 => by
    simp only [Nat.max_succ_succ, Nat.min_succ_succ]
    exact congrArg succ <| Nat.max_min_distrib_left ..

protected theorem min_max_distrib_left : ∀ (a b c : Nat), min a (max b c) = max (min a b) (min a c)
  | 0, _, _ => by simp only [Nat.min_zero_left]
  | _, 0, _ => by simp only [Nat.min_zero_right, Nat.max_zero_left]
  | _, _, 0 => by simp only [Nat.min_zero_right, Nat.max_zero_right]
  | _+1, _+1, _+1 => by
    simp only [Nat.max_succ_succ, Nat.min_succ_succ]
    exact congrArg succ <| Nat.min_max_distrib_left ..

protected theorem max_min_distrib_right (a b c : Nat) :
    max (min a b) c = min (max a c) (max b c) := by
  repeat rw [Nat.max_comm _ c]
  exact Nat.max_min_distrib_left ..

protected theorem min_max_distrib_right (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  repeat rw [Nat.min_comm _ c]
  exact Nat.min_max_distrib_left ..

protected theorem max_add_add_right : ∀ (a b c : Nat), max (a + c) (b + c) = max a b + c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.max_succ_succ ..) <| congrArg _ (Nat.max_add_add_right ..)

protected theorem min_add_add_right : ∀ (a b c : Nat), min (a + c) (b + c) = min a b + c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.min_succ_succ ..) <| congrArg _ (Nat.min_add_add_right ..)

protected theorem max_add_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.max_add_add_right ..

protected theorem min_add_add_left (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.min_add_add_right ..

protected theorem min_pred_pred : ∀ (x y), min (pred x) (pred y) = pred (min x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.min_zero_left]
  | _, 0 => by simp only [Nat.pred_zero, Nat.min_zero_right]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.min_succ_succ]

protected theorem max_pred_pred : ∀ (x y), max (pred x) (pred y) = pred (max x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.max_zero_left]
  | _, 0 => by simp only [Nat.pred_zero, Nat.max_zero_right]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.max_succ_succ]

protected theorem min_sub_sub_right : ∀ (a b c : Nat), min (a - c) (b - c) = min a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.min_pred_pred ..) <| congrArg _ (Nat.min_sub_sub_right ..)

protected theorem max_sub_sub_right : ∀ (a b c : Nat), max (a - c) (b - c) = max a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.max_pred_pred ..) <| congrArg _ (Nat.max_sub_sub_right ..)

protected theorem min_sub_sub_left (a b c : Nat) : min (a - b) (a - c) = a - max b c := by
  induction b, c using Nat.recDiagAux with
  | zero_left => rw [Nat.sub_zero, Nat.max_zero_left]; exact Nat.min_eq_right (Nat.sub_le ..)
  | zero_right => rw [Nat.sub_zero, Nat.max_zero_right]; exact Nat.min_eq_left (Nat.sub_le ..)
  | succ_succ _ _ ih => simp only [Nat.sub_succ, Nat.max_succ_succ, Nat.min_pred_pred, ih]

protected theorem max_sub_sub_left (a b c : Nat) : max (a - b) (a - c) = a - min b c := by
  induction b, c using Nat.recDiagAux with
  | zero_left => rw [Nat.sub_zero, Nat.min_zero_left]; exact Nat.max_eq_left (Nat.sub_le ..)
  | zero_right => rw [Nat.sub_zero, Nat.min_zero_right]; exact Nat.max_eq_right (Nat.sub_le ..)
  | succ_succ _ _ ih => simp only [Nat.sub_succ, Nat.min_succ_succ, Nat.max_pred_pred, ih]

protected theorem max_mul_mul_right (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
  induction a, b using Nat.recDiagAux with
  | zero_left => simp only [Nat.zero_mul, Nat.max_zero_left]
  | zero_right => simp only [Nat.zero_mul, Nat.max_zero_right]
  | succ_succ _ _ ih => simp only [Nat.succ_mul, Nat.max_add_add_right, ih]

protected theorem min_mul_mul_right (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a, b using Nat.recDiagAux with
  | zero_left => simp only [Nat.zero_mul, Nat.min_zero_left]
  | zero_right => simp only [Nat.zero_mul, Nat.min_zero_right]
  | succ_succ _ _ ih => simp only [Nat.succ_mul, Nat.min_add_add_right, ih]

protected theorem max_mul_mul_left (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.max_mul_mul_right ..

protected theorem min_mul_mul_left (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.min_mul_mul_right ..

/-! ## mul -/

protected theorem mul_right_comm (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]

protected theorem mul_mul_mul_comm (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b]

protected theorem mul_two (n) : n * 2 = n + n := by rw [Nat.mul_succ, Nat.mul_one]

protected theorem two_mul (n) : 2 * n = n + n := by rw [Nat.succ_mul, Nat.one_mul]

theorem mul_eq_zero : ∀ {m n}, n * m = 0 ↔ n = 0 ∨ m = 0
  | 0, _ => ⟨fun _ => .inr rfl, fun _ => rfl⟩
  | _, 0 => ⟨fun _ => .inl rfl, fun _ => Nat.zero_mul ..⟩
  | _+1, _+1 => ⟨fun., fun.⟩

protected theorem mul_ne_zero_iff : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by rw [ne_eq, mul_eq_zero, not_or]

protected theorem mul_ne_zero : n ≠ 0 → m ≠ 0 → n * m ≠ 0 := (Nat.mul_ne_zero_iff.2 ⟨·,·⟩)

protected theorem le_mul_of_pos_left (n) (h : 0 < m) : n ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ h)

protected theorem le_mul_of_pos_right (m) (h : 0 < n) : m ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm) (Nat.mul_le_mul_right _ h)

protected theorem mul_lt_mul_of_lt_of_le (hac : a < c) (hbd : b ≤ d) (hd : 0 < d) : a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hbd) (Nat.mul_lt_mul_of_pos_right hac hd)

protected theorem mul_lt_mul_of_le_of_lt (hac : a ≤ c) (hbd : b < d) (hc : 0 < c) : a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hac) (Nat.mul_lt_mul_of_pos_left hbd hc)

protected theorem mul_lt_mul {a b c d : Nat} (hac : a < c) (hbd : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hac) hbd (Nat.zero_lt_of_lt hac)

theorem succ_mul_succ_eq (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_mul, mul_succ]; rfl

protected theorem mul_self_sub_mul_self_eq (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib]
  rw [Nat.mul_comm a b, Nat.sub_add_eq, Nat.add_sub_cancel]

/-! ## div/mod -/

-- TODO mod_core_congr, mod_def

-- TODO div_core_congr, div_def

theorem mod_add_div (m k : Nat) : m % k + k * (m / k) = m := by
  induction m, k using mod.inductionOn with rw [div_eq, mod_eq]
  | base x y h => simp [h]
  | ind x y h IH => simp [h]; rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]

@[simp] protected theorem div_one (n) : n / 1 = n := by
  have := mod_add_div n 1
  rwa [mod_one, Nat.zero_add, Nat.one_mul] at this

@[simp] protected theorem div_zero (n) : n / 0 = 0 := by
  rw [div_eq]; simp [Nat.lt_irrefl]

@[simp] protected theorem zero_div (n) : 0 / n = 0 :=
  (div_eq 0 _).trans <| if_neg <| And.rec Nat.not_le_of_gt

theorem le_div_iff_mul_le (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y := by
  induction y, k using mod.inductionOn generalizing x with
    (rw [div_eq]; simp [h]; cases x with simp [zero_le] | succ x => ?_)
  | base y k h =>
    simp [not_succ_le_zero x, succ_mul, Nat.add_comm]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right ..)
    exact Nat.not_le.1 fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [← add_one, Nat.add_le_add_iff_right, IH k0, succ_mul,
        ← Nat.add_sub_cancel (x*k) k, Nat.sub_le_sub_iff_right h.2, Nat.add_sub_cancel]

protected theorem div_le_of_le_mul : ∀ {k : Nat}, m ≤ k * n → m / k ≤ n
  | 0, _ => by simp [Nat.div_zero, n.zero_le]
  | succ k, h => by
    suffices succ k * (m / succ k) ≤ succ k * n from
      Nat.le_of_mul_le_mul_left this (zero_lt_succ _)
    have h1 : succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) := Nat.le_add_left _ _
    have h2 : m % succ k + succ k * (m / succ k) = m := by rw [mod_add_div]
    have h3 : m ≤ succ k * n := h
    rw [← h2] at h3
    exact Nat.le_trans h1 h3

theorem div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption

theorem div_eq_of_lt (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right

theorem div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)

theorem sub_mul_div (x n p : Nat) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  match eq_zero_or_pos n with
  | .inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | .inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n * p ≤ x := Nat.le_trans (Nat.mul_le_mul_left _ (le_succ _)) h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        exact h₁
      rw [sub_succ, ← IH h₂, div_eq_sub_div h₀ h₃]
      simp [add_one, Nat.pred_succ, mul_succ, Nat.sub_sub]

theorem div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m
  | m, 0   => by simp
  | m, n+1 => (le_div_iff_mul_le (Nat.succ_pos _)).1 (Nat.le_refl _)

@[simp] theorem add_div_right (x) (H : 0 < z) : (x + z) / z = succ (x / z) := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] theorem add_div_left (x) (H : 0 < z) : (z + x) / z = succ (x / z) := by
  rw [Nat.add_comm, add_div_right x H]

@[simp] theorem mul_div_right (n) (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]

@[simp] theorem mul_div_left (m) (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]

protected theorem div_self (H : 0 < n) : n / n = 1 := by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t

theorem add_mul_div_left (x z) (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl

theorem add_mul_div_right (x y) (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]

protected theorem mul_div_cancel (m) (H : 0 < n) : m * n / n = m := by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t

protected theorem mul_div_cancel_left (m) (H : 0 < n) : n * m / n = m :=
by rw [Nat.mul_comm, Nat.mul_div_cancel _ H]

protected theorem div_eq_of_eq_mul_left (H1 : 0 < n) (H2 : m = k * n) : m / n = k :=
by rw [H2, Nat.mul_div_cancel _ H1]

protected theorem div_eq_of_eq_mul_right (H1 : 0 < n) (H2 : m = n * k) : m / n = k :=
by rw [H2, Nat.mul_div_cancel_left _ H1]

protected theorem div_eq_of_lt_le (lo : k * n ≤ m) (hi : m < succ k * n) : m / n = k :=
have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun hn => by
  rw [hn, Nat.mul_zero] at hi lo; exact absurd lo (Nat.not_le_of_gt hi)
Nat.le_antisymm
  (le_of_lt_succ ((Nat.div_lt_iff_lt_mul npos).2 hi))
  ((Nat.le_div_iff_mul_le npos).2 lo)

theorem mul_sub_div (x n p) (h₁ : x < n*p) : (n * p - succ x) / n = p - succ (x / n) := by
  have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun n0 => by
    rw [n0, Nat.zero_mul] at h₁; exact not_lt_zero _ h₁
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    exact Nat.sub_le_sub_left _ <| (div_lt_iff_lt_mul npos).1 (lt_succ_self _)
  · show succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.sub_le_sub_left _ <| div_mul_le_self ..
    · rwa [div_lt_iff_lt_mul npos, Nat.mul_comm]

protected theorem div_div_eq_div_mul (m n k : Nat) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_
  apply Nat.le_antisymm
  · apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
    rw [Nat.mul_comm n k, ← Nat.mul_assoc]
    apply (le_div_iff_mul_le npos).1
    apply (le_div_iff_mul_le kpos).1
    (apply Nat.le_refl)
  · apply (le_div_iff_mul_le kpos).2
    apply (le_div_iff_mul_le npos).2
    rw [Nat.mul_assoc, Nat.mul_comm n k]
    apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
    apply Nat.le_refl

protected theorem mul_div_mul_left (n k) (H : 0 < m) : m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]

protected theorem mul_div_mul_right (n k) (H : 0 < m) : n * m / (k * m) = n / k := by
  rw [Nat.mul_comm, Nat.mul_comm k, Nat.mul_div_mul_left _ _ H]

theorem mul_div_le (m n : Nat) : n * (m / n) ≤ m := by
  match n, Nat.eq_zero_or_pos n with
  | _, Or.inl rfl => rw [Nat.zero_mul]; exact m.zero_le
  | n, Or.inr h => rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le h]; exact Nat.le_refl _

theorem mod_two_eq_zero_or_one (n) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by simp) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

theorem le_of_mod_lt {a b : Nat} (h : a % b < a) : b ≤ a :=
  Nat.not_lt.1 fun hf => (ne_of_lt h).elim (Nat.mod_eq_of_lt hf)

@[simp] theorem add_mod_right (x z : Nat) : (x + z) % z = x % z := by
  rw [mod_eq_sub_mod (Nat.le_add_left ..), Nat.add_sub_cancel]

@[simp] theorem add_mod_left (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm, add_mod_right]

@[simp] theorem add_mul_mod_self_left (x y z : Nat) : (x + y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, Nat.add_zero]
  | succ z => rw [mul_succ, ← Nat.add_assoc, add_mod_right, add_mul_mod_self_left (z := z)]

@[simp] theorem add_mul_mod_self_right (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp] theorem mul_mod_right (m n) : (m * n) % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]

@[simp] theorem mul_mod_left (m n) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]

theorem mul_mod_mul_left (z x y : Nat) : (z * x) % (z * y) = z * (x % y) :=
  if y0 : y = 0 then by
    rw [y0, Nat.mul_zero, mod_zero, mod_zero]
  else if z0 : z = 0 then by
    rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
  else by
    induction x using Nat.strongInductionOn with
    | _ n IH =>
      have y0 : y > 0 := Nat.pos_of_ne_zero y0
      have z0 : z > 0 := Nat.pos_of_ne_zero z0
      cases Nat.lt_or_ge n y with
      | inl yn => rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left yn z0)]
      | inr yn =>
        rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_left z yn),
          ← Nat.mul_sub_left_distrib]
        exact IH _ (sub_lt (Nat.lt_of_lt_of_le y0 yn) y0)

theorem mul_mod_mul_right (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left

-- TODO cont_to_bool_mod_two

theorem sub_mul_mod {x k n : Nat} (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  match k with
  | 0 => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k =>
    have h₂ : n * k ≤ x := Nat.le_trans (le_add_right _ n) h₁
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (b := n * k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, sub_mul_mod h₂]

@[simp] theorem mod_mod (a n : Nat) : (a % n) % n = a % n :=
  match eq_zero_or_pos n with
  | .inl n0 => by simp [n0, mod_zero]
  | .inr npos => Nat.mod_eq_of_lt (mod_lt _ npos)

theorem mul_mod (a b n : Nat) : a * b % n = (a % n) * (b % n) % n := by
  conv => lhs; rw [
    ← mod_add_div a n, ← mod_add_div b n, Nat.add_mul, Nat.mul_add, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add n, add_mul_mod_self_left,
    Nat.mul_comm _ (n * (b / n)), Nat.mul_assoc, add_mul_mod_self_left]

@[simp] theorem mod_add_mod (m n k : Nat) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm
  rwa [Nat.add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : Nat) : (m + n % k) % k = (m + n) % k := by
  rw [Nat.add_comm, mod_add_mod, Nat.add_comm]

theorem add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [add_mod_mod, mod_add_mod]

/-! ### pow -/

attribute [simp] Nat.pow_zero

theorem pow_succ' {m : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

@[simp] theorem pow_eq : Nat.pow m n = m ^ n := rfl

theorem shiftLeft_eq' (a b : Nat) : a <<< b = 2 ^ b * a := by
  induction b generalizing a with
  | zero => rw [Nat.pow_zero, Nat.one_mul]; rfl
  | succ _ ih => rw [Nat.pow_succ, Nat.mul_assoc, ←ih]; rfl

@[simp] theorem shiftLeft_eq (a b : Nat) : a <<< b = a * 2 ^ b := by
  rw [Nat.mul_comm, Nat.shiftLeft_eq']

theorem one_shiftLeft (n) : 1 <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq', Nat.mul_one]

protected theorem zero_pow : ∀ n, 0 < n → 0 ^ n = 0
  | _+1, _ => rfl

@[simp] protected theorem one_pow : ∀ (n : Nat), 1 ^ n = 1
  | 0 => rfl
  | _+1 => by rw [Nat.pow_succ, Nat.mul_one]; exact Nat.one_pow ..

@[simp] protected theorem pow_one (a : Nat) : a ^ 1 = a := by
  rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

protected theorem pow_two (a : Nat) : a ^ 2 = a * a := by rw [Nat.pow_succ, Nat.pow_one]

protected theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

protected theorem pow_add' (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [←Nat.pow_add, Nat.add_comm]

protected theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ _ ih => rw [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, ih]

protected theorem pow_mul' (a m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [←Nat.pow_mul, Nat.mul_comm]

protected theorem pow_right_comm (a m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [←Nat.pow_mul, Nat.pow_mul']

protected theorem mul_pow (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.mul_mul_mul_comm, ih]

/-! ### log2 -/

theorem le_log2 (h : n ≠ 0) : ∀ {k}, k ≤ n.log2 ↔ 2 ^ k ≤ n
  | 0 => by simp [show 1 ≤ n from Nat.pos_of_ne_zero h]
  | k+1 => by
    rw [log2]; split
    · have n0 : 0 < n / 2 := (Nat.le_div_iff_mul_le (by decide)).2 ‹_›
      simp [Nat.add_le_add_iff_right, le_log2 (Nat.ne_of_gt n0), le_div_iff_mul_le, Nat.pow_succ]
    · simp only [le_zero_eq, succ_ne_zero, false_iff]
      refine mt (Nat.le_trans ?_) ‹_›
      exact Nat.pow_le_pow_of_le_right (Nat.succ_pos 1) (Nat.le_add_left 1 k)

theorem log2_lt (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]

theorem log2_self_le (h : n ≠ 0) : 2 ^ n.log2 ≤ n := (le_log2 h).1 (Nat.le_refl _)

theorem lt_log2_self (h : n ≠ 0) : n < 2 ^ (n.log2 + 1) := (log2_lt h).1 (Nat.le_refl _)

/-! ### dvd -/

protected theorem dvd_refl (a : Nat) : a ∣ a := ⟨_, Nat.mul_one .. |>.symm⟩

protected theorem dvd_zero (a) : a ∣ 0 := ⟨0, rfl⟩

protected theorem one_dvd (a) : 1 ∣ a := ⟨_, Nat.one_mul _ |>.symm⟩

protected theorem dvd_mul_left (a b : Nat) : a ∣ b * a := ⟨_, Nat.mul_comm ..⟩

protected theorem dvd_mul_right (a b : Nat) : a ∣ a * b := ⟨_, rfl⟩

protected theorem dvd_trans : ∀ {a b c : Nat}, a ∣ b → b ∣ c → a ∣ c
  | _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ⟨_, Nat.mul_assoc ..⟩

protected theorem eq_zero_of_zero_dvd : ∀ {a}, 0 ∣ a → a = 0
  | _, ⟨_, rfl⟩ => Nat.zero_mul ..

protected theorem dvd_add : ∀ {a b c : Nat}, a ∣ b → a ∣ c → a ∣ b + c
  | _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ⟨_, Nat.mul_add .. |>.symm⟩

protected theorem dvd_sub : ∀ {a b c : Nat}, a ∣ b → a ∣ c → a ∣ b - c
  | _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ⟨_, Nat.mul_sub_left_distrib .. |>.symm⟩

protected theorem dvd_add_iff_left {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n :=
  ⟨fun h' => Nat.dvd_add h' h, fun h' => Nat.add_sub_cancel m n ▸ Nat.dvd_sub h' h⟩

protected theorem dvd_add_iff_right {k m n : Nat} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_left h

protected theorem mul_dvd_mul : ∀ {a b c d : Nat}, a ∣ b → c ∣ d → a * c ∣ b * d
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ⟨_, Nat.mul_mul_mul_comm ..⟩

protected theorem mul_dvd_mul_left (a : Nat) (h : b ∣ c) : a * b ∣ a * c :=
  Nat.mul_dvd_mul (Nat.dvd_refl _) h

protected theorem mul_dvd_mul_right (h: a ∣ b) (c : Nat) : a * c ∣ b * c :=
  Nat.mul_dvd_mul h (Nat.dvd_refl _)

theorem dvd_mod_iff {k m n : Nat} (h: k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  have := Nat.dvd_add_iff_left <| Nat.dvd_trans h <| Nat.dvd_mul_right n (m / n)
  by rwa [mod_add_div] at this

theorem le_of_dvd : ∀ {n m}, 0 < n → m ∣ n → m ≤ n
  | _, _, _, ⟨_+1, rfl⟩ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

protected theorem dvd_antisymm : ∀ {m n : Nat}, m ∣ n → n ∣ m → m = n
  | _, 0, _, h₂ => Nat.eq_zero_of_zero_dvd h₂
  | 0, _, h₁, _ => (Nat.eq_zero_of_zero_dvd h₁).symm
  | _+1, _+1, h₁, h₂ => Nat.le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
  Nat.pos_of_ne_zero fun m0 => Nat.ne_of_gt H2 <| Nat.eq_zero_of_zero_dvd (m0 ▸ H1)

theorem eq_one_of_dvd_one (H : n ∣ 1) : n = 1 :=
  Nat.dvd_antisymm H (Nat.one_dvd _)

theorem dvd_of_mod_eq_zero (H : n % m = 0) : m ∣ n :=
  ⟨n / m, (mod_add_div n m).symm.trans (H ▸ Nat.zero_add ..)⟩

theorem mod_eq_zero_of_dvd : ∀ {n}, m ∣ n → n % m = 0
  | _, ⟨_, rfl⟩ => Nat.mul_mod_right ..

theorem dvd_iff_mod_eq_zero (m n) : m ∣ n ↔ n % m = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @DecidableRel Nat (·∣·) :=
  fun _ _ => decidable_of_decidable_of_iff (dvd_iff_mod_eq_zero _ _).symm

protected theorem mul_div_cancel' : ∀ {n m : Nat}, n ∣ m →  n * (m / n) = m
  | 0, _, h => by rw [Nat.zero_mul, Nat.eq_zero_of_zero_dvd h]
  | _+1, _, ⟨_, rfl⟩ => by rw [Nat.mul_div_right]; exact Nat.succ_pos ..

protected theorem div_mul_cancel {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]

protected theorem mul_div_assoc (m : Nat) : ∀ {k n}, k ∣ n → m * n / k = m * (n / k)
  | 0, _, _ => by rw [Nat.div_zero, Nat.div_zero]; rfl
  | _+1, _, ⟨_, rfl⟩ => by
    rw [Nat.mul_left_comm, Nat.mul_div_right, Nat.mul_div_right] <;> exact Nat.succ_pos ..

protected theorem dvd_of_mul_dvd_mul_left (kpos : 0 < k) : k * m ∣ k * n → m ∣ n
  | ⟨_, h⟩ => ⟨_, Nat.eq_of_mul_eq_mul_left kpos (Nat.mul_assoc .. ▸ h)⟩

protected theorem dvd_of_mul_dvd_mul_right : 0 < k → m * k ∣ n * k → m ∣ n := by
  rw [Nat.mul_comm m, Nat.mul_comm n]; exact Nat.dvd_of_mul_dvd_mul_left

/-! ### sum -/

@[simp] theorem sum_nil : Nat.sum [] = 0 := rfl

@[simp] theorem sum_cons : Nat.sum (a :: l) = a + Nat.sum l := rfl

@[simp] theorem sum_append : Nat.sum (l₁ ++ l₂) = Nat.sum l₁ + Nat.sum l₂ := by
  induction l₁ <;> simp [*, Nat.add_assoc]

/-! ### deprecated -/

@[deprecated Nat.le_sub_iff_add_le]
theorem add_le_to_le_sub (x : Nat) {y k : Nat} (h : k ≤ y) : x + k ≤ y ↔ x ≤ y - k :=
  (Nat.le_sub_iff_add_le h).symm

@[deprecated Nat.succ_add_eq_add_succ]
theorem succ_add_eq_succ_add (n m : Nat) : succ n + m = n + succ m :=
  Nat.succ_add_eq_add_succ ..

@[deprecated Nat.mul_le_mul_left]
protected theorem mul_le_mul_of_nonneg_left {a b c : Nat} : a ≤ b → c * a ≤ c * b :=
  Nat.mul_le_mul_left c

@[deprecated Nat.mul_le_mul_right]
protected theorem mul_le_mul_of_nonneg_right {a b c : Nat} : a ≤ b → a * c ≤ b * c :=
  Nat.mul_le_mul_right c

@[deprecated Nat.mul_lt_mul_of_le_of_lt]
protected theorem mul_lt_mul' (hac : a ≤ c) (hbd : b < d) (hc : 0 < c) : a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt hac hbd hc

@[deprecated Nat.max_zero_left]
protected theorem zero_max (n) : max 0 n = n := Nat.max_zero_left ..

@[deprecated Nat.max_zero_right]
protected theorem max_zero (n) : max n 0 = n := Nat.max_zero_right ..

@[deprecated Nat.min_zero_left]
protected theorem zero_min (n) : min 0 n = 0 := Nat.min_zero_left ..

@[deprecated Nat.max_zero_right]
protected theorem min_zero (n) : min n 0 = 0 := Nat.min_zero_right ..
