/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas

namespace Fin

attribute [norm_cast] val_last

protected theorem le_antisymm_iff {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Fin.ext_iff.trans Nat.le_antisymm_iff

protected theorem le_antisymm {x y : Fin n} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  Fin.le_antisymm_iff.2 ⟨h1, h2⟩

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### foldl -/

theorem foldl_loop_lt (f : α → Fin n → α) (x) (h : m < n) :
    foldl.loop n f x m = foldl.loop n f (f x ⟨m, h⟩) (m+1) := by
  rw [foldl.loop, dif_pos h]

theorem foldl_loop_eq (f : α → Fin n → α) (x) : foldl.loop n f x n = x := by
  rw [foldl.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldl_loop (f : α → Fin (n+1) → α) (x) (h : m < n+1) :
    foldl.loop (n+1) f x m = foldl.loop n (fun x i => f x i.succ) (f x ⟨m, h⟩) m := by
  if h' : m < n then
    rw [foldl_loop_lt _ _ h, foldl_loop_lt _ _ h', foldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldl_loop_lt, foldl_loop_eq, foldl_loop_eq]
termination_by n - m

@[simp] theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x := by simp [foldl, foldl.loop]

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) := foldl_loop ..

theorem foldl_succ_last (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = f (foldl n (f · ·.castSucc) x) (last n) := by
  rw [foldl_succ]
  induction n generalizing x with
  | zero => simp [foldl_succ, Fin.last]
  | succ n ih => rw [foldl_succ, ih (f · ·.succ), foldl_succ]; simp [succ_castSucc]

theorem foldl_eq_foldl_finRange (f : α → Fin n → α) (x) :
    foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, List.finRange_zero, List.foldl_nil]
  | succ n ih =>
    rw [foldl_succ, ih, List.finRange_succ_eq_zero_cons_map, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

unseal foldr.loop in
theorem foldr_loop_zero (f : Fin n → α → α) (x) : foldr.loop n f ⟨0, Nat.zero_le _⟩ x = x :=
  rfl

unseal foldr.loop in
theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : m < n) :
    foldr.loop n f ⟨m+1, h⟩ x = foldr.loop n f ⟨m, Nat.le_of_lt h⟩ (f ⟨m, h⟩ x) :=
  rfl

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : m+1 ≤ n+1) :
    foldr.loop (n+1) f ⟨m+1, h⟩ x =
      f 0 (foldr.loop n (fun i => f i.succ) ⟨m, Nat.le_of_succ_le_succ h⟩ x) := by
  induction m generalizing x with
  | zero => simp [foldr_loop_zero, foldr_loop_succ]
  | succ m ih => rw [foldr_loop_succ, ih, foldr_loop_succ, Fin.succ]

@[simp] theorem foldr_zero (f : Fin 0 → α → α) (x) :
    foldr 0 f x = x := foldr_loop_zero ..

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_succ_last (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = foldr n (f ·.castSucc) (f (last n) x) := by
  induction n generalizing x with
  | zero => simp [foldr_succ, Fin.last]
  | succ n ih => rw [foldr_succ, ih (f ·.succ), foldr_succ]; simp [succ_castSucc]

theorem foldr_eq_foldr_finRange (f : Fin n → α → α) (x) :
    foldr n f x = (List.finRange n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, List.finRange_zero, List.foldr_nil]
  | succ n ih =>
    rw [foldr_succ, ih, List.finRange_succ_eq_zero_cons_map, List.foldr_cons, List.foldr_map]

/-! ### foldl/foldr -/

theorem foldl_rev (f : Fin n → α → α) (x) :
    foldl n (fun x i => f i.rev x) x = foldr n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ, foldr_succ_last, ← ih]; simp [rev_succ]

theorem foldr_rev (f : α → Fin n → α) (x) :
     foldr n (fun i x => f x i.rev) x = foldl n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ_last, foldr_succ, ← ih]; simp [rev_succ]
