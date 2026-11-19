/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

import all Init.Data.OfScientific -- remove when Float.ofNat is exposed

public section

namespace Float.Model.UnpackedFloat

/-- Returns true if the bits represent an NaN value -/
def isNaNBits {spec : Format} (b : BitVec spec.numBits) : Bool :=
  unpackExponent b = -1#_ ∧ unpackMantissa b ≠ 0#_

namespace Sign

@[simp]
theorem ofBitVec_toBitVec (s : Sign) :
    Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

@[simp]
theorem toBitVec_ofBitVec (b : BitVec 1) :
    (Sign.ofBitVec b).toBitVec = b := by
  decide +revert

protected theorem forall_iff {p : Sign → Prop} :
    (∀ s : Sign, p s) ↔ p .positive ∧ p .negative := by
  constructor
  · intro h; simp [h]
  · rintro ⟨h, h'⟩ (_ | _) <;> assumption

instance {p : Sign → Prop} [∀ s, Decidable (p s)] : Decidable (∀ s : Sign, p s) :=
  decidable_of_decidable_of_iff Sign.forall_iff.symm

@[simp] theorem neg_neg (s : Sign) : - -s = s := by cases s <;> rfl

@[simp] theorem neg_mul (s t : Sign) : -s * t = -(s * t) := by cases s <;> cases t <;> rfl

@[simp] theorem mul_neg (s t : Sign) : s * -t = -(s * t) := by cases s <;> cases t <;> rfl

@[simp] theorem neg_div (s t : Sign) : -s / t = -(s / t) := by cases s <;> cases t <;> rfl

@[simp] theorem div_neg (s t : Sign) : s / -t = -(s / t) := by cases s <;> cases t <;> rfl

theorem mul_comm (s t : Sign) : s * t = t * s := by cases s <;> cases t <;> rfl

theorem compare_def (s t : Sign) : compare s t =
    match s, t with
    | .negative, .positive => .lt | .positive, .negative => .gt | _, _ => .eq := by
  cases s <;> cases t <;> rfl

end Sign

@[simp]
theorem unpackSign_packComponents {spec : Format} (s e m) :
    unpackSign (packComponents spec s e m) = s.toBitVec := by
  ext i (_ | ⟨⟨⟩⟩)
  simp +arith [unpackSign, packComponents, BitVec.getElem_append]

theorem packComponents_unpackSign_unpackExponent_unpackMantissa
    {spec : Format} (b : BitVec spec.numBits) :
    packComponents spec
      (Sign.ofBitVec (unpackSign b)) (unpackExponent b) (unpackMantissa b) = b := by
  simp [packComponents]
  rw [unpackSign, unpackExponent, unpackMantissa]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
  · exact BitVec.extractLsb'_eq_self
  · simp
  · simp

theorem pack_unpack {spec : Format} (b : BitVec spec.numBits) :
    (unpack spec b).pack spec = if isNaNBits b then packedNaN spec else b := by
  conv => rhs; rw [← packComponents_unpackSign_unpackExponent_unpackMantissa b]
  unfold isNaNBits
  fun_cases unpack with
  | case1 mvec evec svec s hevec hmvec =>
    -- infinity
    simp +zetaDelta [pack, packedInfinity, hmvec, hevec]
  | case2 mvec evec hevec hmvec =>
    -- nan
    simp +zetaDelta [pack, packedNaN, hevec, hmvec]
  | case3 mvec evec svec s _ hevec hmvec =>
    -- zero
    simp +zetaDelta [pack, packedZero, hevec, hmvec]
  | case4 mvec evec e svec s _ hevec hmvec =>
    -- subnormal
    simp only [hevec, unpackExponent_packComponents, BitVec.zero_eq_neg_one_iff,
      Nat.ne_zero_of_lt spec.he, unpackMantissa_packComponents, ne_eq, false_and, decide_false,
      Bool.false_eq_true, ↓reduceIte, evec]
    unfold pack
    extract_lets mantbits biasedexp
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, mvec]
    rw [ite_eq_right, ite_eq_right]
    · rw [Format.mantissaBits, Nat.add_comm, Nat.add_left_cancel_iff]
      apply Nat.ne_of_lt
      have := mt BitVec.toNat_inj.mp hmvec
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      simp only [ne_eq, this, not_false_eq_true, Nat.log2_lt, gt_iff_lt, mantbits]
      exact BitVec.isLt _
    · simp +arith [biasedexp, e, hevec]
      have := Nat.pow_le_pow_right (n := 2) (by decide) spec.he
      lia
  | case5 mvec evec e svec s hevec hevec' =>
    -- normal
    simp only [unpackExponent_packComponents, hevec, unpackMantissa_packComponents, ne_eq,
      false_and, decide_false, Bool.false_eq_true, ↓reduceIte, evec]
    unfold pack
    extract_lets mantbits biasedexp
    rw [ite_eq_right, ite_eq_left]
    · congr 1
      · simp +arith [biasedexp, e, evec]
      · rw [BitVec.ofNat_toNat, BitVec.setWidth_append]
        simp [mvec]
    · subst mantbits
      have := Nat.two_pow_add_eq_or_of_lt mvec.isLt (a := 1)
      rw [Nat.mul_one] at this
      simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.pow_one, Nat.mod_succ,
        Format.mantissaBits, Nat.add_comm 1, Nat.add_right_cancel_iff,
        Nat.one_shiftLeft, ← this]
      rw [Nat.log2_eq_iff (by simp)]
      simp [Nat.two_pow_succ, mvec.isLt]
    · simp +arith [biasedexp, e]
      simp only [BitVec.neg_one_eq_allOnes, ← BitVec.lt_allOnes_iff, BitVec.lt_def,
        BitVec.toNat_allOnes] at hevec
      lia

theorem pack_unpack_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : (unpack spec b).pack spec = b := by
  rw [pack_unpack b]
  simp +contextual [isNaNBits, ← hvalid.eq_packedNaN]

theorem unpack_inj_of_valid {spec : Format} {b b' : BitVec spec.numBits}
    (hb : spec.Valid b) (hb' : spec.Valid b') :
    unpack spec b = unpack spec b' ↔ b = b' := by
  constructor
  · intro h
    replace h := congrArg (pack spec) h
    rwa [pack_unpack_of_valid hb, pack_unpack_of_valid hb'] at h
  · rintro rfl; rfl

theorem isNaNBits_packedNaN {spec : Format} : isNaNBits (packedNaN spec) := by
  simp only [isNaNBits, packedNaN, unpackExponent_packComponents, unpackMantissa_packComponents,
    ne_eq, true_and, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro h
  replace h := congrArg (·.getLsbD (spec.mantissaBitsWithoutImplicit - 1)) h
  simp [Nat.sub_one_lt (Nat.ne_of_gt spec.hm)] at h

@[simp]
theorem unpack_packedNaN {spec : Format} : unpack spec (packedNaN spec) = notANumber := by
  have := @isNaNBits_packedNaN spec
  simp only [isNaNBits, decide_eq_true_eq] at this
  simp [unpack, this]

@[simp]
theorem unpack_packedZero {spec : Format} {sign : Sign} :
    unpack spec (packedZero spec sign) = .zero sign := by
  simp [unpack, packedZero, Nat.ne_zero_of_lt spec.he]

@[simp]
theorem isNaN_iff : isNaN x ↔ x = notANumber := by
  cases x <;> simp [isNaN]

theorem unpack_eq_notANumber_iff_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : unpack spec b = notANumber ↔ b = packedNaN spec := by
  rw [← @unpack_packedNaN spec, unpack_inj_of_valid hvalid ⟨fun _ _ => rfl⟩]

theorem unpack_eq_zero_iff_of_valid {spec : Format} {sign : Sign} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : unpack spec b = zero sign ↔ b = packedZero spec sign := by
  rw [← @unpack_packedZero spec, unpack_inj_of_valid hvalid ⟨by simp [packedZero]⟩]

theorem isNaN_unpack_iff_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : (unpack spec b).isNaN ↔ b = packedNaN spec := by
  rw [isNaN_iff, unpack_eq_notANumber_iff_of_valid hvalid]

theorem beq_iff_ne_notANumber_and_eq (a b : UnpackedFloat) :
    a.beq b ↔ a ≠ notANumber ∧ b ≠ notANumber ∧
      (a = b ∨ (a = .zero .positive ∧ b = .zero .negative) ∨
        (a = .zero .negative ∧ b = .zero .positive)) := by
  simp only [UnpackedFloat.beq, beq_iff_eq, ne_eq]
  fun_cases UnpackedFloat.compare a b <;> simp_all [eq_comm (α := UnpackedFloat), and_comm] <;>
    rename_i s₁ s₂ <;> revert s₁ s₂ <;> decide

theorem unpack_beq_unpack_iff {spec : Format} {b b' : BitVec spec.numBits}
    (hb : spec.Valid b) (hb' : spec.Valid b') :
    (unpack spec b).beq (unpack spec b') ↔ b ≠ packedNaN spec ∧ b' ≠ packedNaN spec ∧
        (b = b' ∨ (b = packedZero spec .positive ∧ b' = packedZero spec .negative) ∨
          (b = packedZero spec .negative ∧ b' = packedZero spec .positive)) := by
  rw [beq_iff_ne_notANumber_and_eq]
  simp [unpack_eq_notANumber_iff_of_valid, unpack_eq_zero_iff_of_valid, unpack_inj_of_valid, *]

@[simp] theorem neg_neg (u : UnpackedFloat) : u.neg.neg = u := by
  cases u <;> simp [neg]

theorem unpack_eq_notANumber_of_isNaNBits {spec : Format} {b : BitVec spec.numBits}
    (h : isNaNBits b) : unpack spec b = notANumber := by
  simp only [isNaNBits, decide_eq_true_eq] at h
  simp [unpack, h.1, h.2]

/-- Unpacking forgets everything that packing an unpacked float could change. -/
@[simp] theorem unpack_pack_unpack {spec : Format} (b : BitVec spec.numBits) :
    unpack spec (pack spec (unpack spec b)) = unpack spec b := by
  rw [pack_unpack]
  split
  · rw [unpack_packedNaN, unpack_eq_notANumber_of_isNaNBits ‹_›]
  · rfl

/-- Flipping the sign bit negates the unpacked float. -/
theorem unpack_packComponents_neg {spec : Format} (s e m) :
    unpack spec (packComponents spec (-s) e m) = (unpack spec (packComponents spec s e m)).neg := by
  cases s <;>
  · simp only [unpack, unpackSign_packComponents, unpackExponent_packComponents,
      unpackMantissa_packComponents]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl

/-- The bit pattern `b` with its sign bit flipped. -/
def flipSign {spec : Format} (b : BitVec spec.numBits) : BitVec spec.numBits :=
  packComponents spec (-Sign.ofBitVec (unpackSign b)) (unpackExponent b) (unpackMantissa b)

theorem unpack_flipSign {spec : Format} (b : BitVec spec.numBits) :
    unpack spec (flipSign b) = (unpack spec b).neg := by
  conv => rhs; rw [← packComponents_unpackSign_unpackExponent_unpackMantissa b]
  exact unpack_packComponents_neg ..

@[simp] theorem unpack_pack_neg_unpack {spec : Format} (b : BitVec spec.numBits) :
    unpack spec (pack spec (unpack spec b).neg) = (unpack spec b).neg := by
  rw [← unpack_flipSign, unpack_pack_unpack]

theorem flipSign_packComponents {spec : Format} (s e m) :
    flipSign (packComponents spec s e m) = packComponents spec (-s) e m := by
  simp [flipSign]

/-- Packing commutes with negation, except on NaN. -/
theorem pack_neg {spec : Format} {u : UnpackedFloat} (h : u ≠ notANumber) :
    pack spec u.neg = flipSign (pack spec u) := by
  cases u with
  | notANumber => contradiction
  | infinity s => simp [neg, pack, packedInfinity, flipSign_packComponents]
  | zero s => simp [neg, pack, packedZero, flipSign_packComponents]
  | finite s m e hm =>
    simp only [neg, pack]
    split
    · simp [packedInfinity, flipSign_packComponents]
    · split <;> simp [flipSign_packComponents]

theorem roundWithAccuracy_neg (spec : Format) (s m e a) :
    roundWithAccuracy spec (-s) m e a = (roundWithAccuracy spec s m e a).neg := by
  simp only [roundWithAccuracy]
  split <;> simp [neg]

theorem neg_mul (spec : Format) (u v : UnpackedFloat) :
    mul spec u.neg v = (mul spec u v).neg := by
  cases u <;> cases v <;> simp [neg, mul, roundWithAccuracy_neg]

theorem mul_neg (spec : Format) (u v : UnpackedFloat) :
    mul spec u v.neg = (mul spec u v).neg := by
  cases u <;> cases v <;> simp [neg, mul, roundWithAccuracy_neg]

theorem neg_div (spec : Format) (u v : UnpackedFloat) :
    div spec u.neg v = (div spec u v).neg := by
  cases u <;> cases v <;> simp [neg, div, roundWithAccuracy_neg]

theorem div_neg (spec : Format) (u v : UnpackedFloat) :
    div spec u v.neg = (div spec u v).neg := by
  cases u <;> cases v <;> simp [neg, div, roundWithAccuracy_neg]

theorem mul_comm (spec : Format) (u v : UnpackedFloat) :
    mul spec u v = mul spec v u := by
  cases u <;> cases v <;> simp [mul, Sign.mul_comm, Nat.mul_comm, Int.add_comm]

theorem add_comm (spec : Format) (u v : UnpackedFloat) :
    add spec u v = add spec v u := by
  cases u <;> cases v <;> simp only [add]
  · rename_i s t; cases s <;> cases t <;> rfl
  · rename_i s t; cases s <;> cases t <;> rfl
  · rw [Int.min_comm, Int.add_comm]

/-! ### Order -/

local macro "cases_uf " a:ident : tactic =>
  `(tactic| rcases $a:ident with ⟨_|_⟩ | _ | ⟨_|_⟩ | ⟨_|_, _, _, _⟩)

section

attribute [local simp] Sign.compare_def UnpackedFloat.compare UnpackedFloat.lt UnpackedFloat.le
  Ordering.then_eq_lt Ordering.then_eq_gt Ordering.swap_eq_lt Ordering.swap_eq_gt
  Int.compare_eq_lt Int.compare_eq_gt Int.compare_eq_eq Nat.compare_eq_lt Nat.compare_eq_gt
  Nat.compare_eq_eq Ordering.isLE_iff_eq_lt_or_eq_eq Ordering.isGE_iff_eq_gt_or_eq_eq
  Ordering.swap_eq_eq Ordering.then_eq_eq Ordering.swap_then Int.compare_swap Nat.compare_swap

theorem compare_swap (a b : UnpackedFloat) :
    b.compare a = (a.compare b).map Ordering.swap := by
  cases_uf a <;> cases_uf b <;> simp

theorem lt_irrefl (a : UnpackedFloat) : ¬ a.lt a := by
  cases_uf a <;> simp

theorem lt_asymm {a b : UnpackedFloat} : a.lt b → ¬ b.lt a := by
  cases_uf a <;> cases_uf b <;> simp <;> omega

theorem lt_trans {a b c : UnpackedFloat} : a.lt b → b.lt c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> omega

theorem le_trans {a b c : UnpackedFloat} : a.le b → b.le c → a.le c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> omega

theorem lt_of_lt_of_le {a b c : UnpackedFloat} : a.lt b → b.le c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> omega

theorem lt_of_le_of_lt {a b c : UnpackedFloat} : a.le b → b.lt c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> omega

theorem le_of_lt {a b : UnpackedFloat} : a.lt b → a.le b := by
  cases_uf a <;> cases_uf b <;> simp <;> omega

theorem lt_iff_le_not_ge {a b : UnpackedFloat} : a.lt b ↔ a.le b ∧ ¬ b.le a := by
  cases_uf a <;> cases_uf b <;> simp <;> omega

theorem le_refl_iff {a : UnpackedFloat} : a.le a ↔ a ≠ notANumber := by
  cases_uf a <;> simp

theorem not_le {a b : UnpackedFloat} (ha : a ≠ notANumber) (hb : b ≠ notANumber) :
    ¬ a.le b ↔ b.lt a := by
  cases_uf a <;> cases_uf b <;> simp at ha hb ⊢ <;> omega

@[simp] theorem notANumber_le (a : UnpackedFloat) : notANumber.le a = false := rfl
@[simp] theorem le_notANumber (a : UnpackedFloat) : a.le notANumber = false := by cases a <;> rfl
@[simp] theorem notANumber_lt (a : UnpackedFloat) : notANumber.lt a = false := rfl
@[simp] theorem lt_notANumber (a : UnpackedFloat) : a.lt notANumber = false := by cases a <;> rfl

theorem neg_lt_neg (a b : UnpackedFloat) : a.neg.lt b.neg = b.lt a := by
  cases_uf a <;> cases_uf b <;> simp [neg] <;> omega

theorem neg_le_neg (a b : UnpackedFloat) : a.neg.le b.neg = b.le a := by
  cases_uf a <;> cases_uf b <;> simp [neg] <;> omega

theorem minimum_comm (a b : UnpackedFloat) : a.minimum b = b.minimum a := by
  cases_uf a <;> cases_uf b <;> simp [minimum] <;> split <;> split <;>
    first | rfl | (exfalso; omega) | (congr 1 <;> omega)

theorem maximum_comm (a b : UnpackedFloat) : a.maximum b = b.maximum a := by
  cases_uf a <;> cases_uf b <;> simp [maximum] <;> split <;> split <;>
    first | rfl | (exfalso; omega) | (congr 1 <;> omega)

end

end Float.Model.UnpackedFloat

theorem Float.toBits_inj {f f' : Float} : f.toBits = f'.toBits ↔ f = f' := by
  rcases f with ⟨⟨⟩⟩; rcases f' with ⟨⟨⟩⟩; simp [toBits]

theorem Float32.toBits_inj {f f' : Float32} : f.toBits = f'.toBits ↔ f = f' := by
  rcases f with ⟨⟨⟩⟩; rcases f' with ⟨⟨⟩⟩; simp [toBits]

@[simp]
theorem Float.ofBits_toBits (f : Float) : ofBits f.toBits = f :=
  toBits_inj.mp <| UInt64.toBitVec_inj.mp <|
    Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid

@[simp]
theorem Float32.ofBits_toBits (f : Float32) : ofBits f.toBits = f :=
  toBits_inj.mp <| UInt32.toBitVec_inj.mp <|
    Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid

@[simp]
theorem Float.isNaN_eq_decide_eq_nan {f : Float} : isNaN f = decide (f = nan) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← toBits_inj, ← UInt64.toBitVec_inj]
  exact Float.Model.UnpackedFloat.isNaN_unpack_iff_of_valid f.toModel.valid

@[simp]
theorem Float32.isNaN_eq_decide_eq_nan {f : Float32} : isNaN f = decide (f = nan) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← toBits_inj, ← UInt32.toBitVec_inj]
  exact Float.Model.UnpackedFloat.isNaN_unpack_iff_of_valid f.toModel.valid

theorem Float.beq_iff_ne_nan_and_eq {f f' : Float} :
    f == f' ↔ f ≠ nan ∧ f' ≠ nan ∧ (f = f' ∨ (f = 0 ∧ f' = -0) ∨ (f = -0 ∧ f' = 0)) := by
  simp only [ne_eq, ← toBits_inj, ← UInt64.toBitVec_inj]
  exact Float.Model.UnpackedFloat.unpack_beq_unpack_iff f.toModel.valid f'.toModel.valid

theorem Float32.beq_iff_ne_nan_and_eq {f f' : Float32} :
    f == f' ↔ f ≠ nan ∧ f' ≠ nan ∧ (f = f' ∨ (f = 0 ∧ f' = -0) ∨ (f = -0 ∧ f' = 0)) := by
  simp only [ne_eq, ← toBits_inj, ← UInt32.toBitVec_inj]
  exact Float.Model.UnpackedFloat.unpack_beq_unpack_iff f.toModel.valid f'.toModel.valid

@[simp]
theorem Float.nan_beq_eq_false (f : Float) : (nan == f) = false := by
  simp [← Bool.not_eq_true, beq_iff_ne_nan_and_eq]

@[simp]
theorem Float32.nan_beq_eq_false (f : Float32) : (nan == f) = false := by
  simp [← Bool.not_eq_true, beq_iff_ne_nan_and_eq]

@[simp]
theorem Float.beq_nan_eq_false (f : Float) : (f == nan) = false := by
  simp [← Bool.not_eq_true, beq_iff_ne_nan_and_eq]

@[simp]
theorem Float32.beq_nan_eq_false (f : Float32) : (f == nan) = false := by
  simp [← Bool.not_eq_true, beq_iff_ne_nan_and_eq]

@[simp]
theorem Float.beq_self_iff {f : Float} : f == f ↔ f ≠ nan := by
  grind [beq_iff_ne_nan_and_eq]

@[simp]
theorem Float32.beq_self_iff {f : Float32} : f == f ↔ f ≠ nan := by
  grind [beq_iff_ne_nan_and_eq]

@[simp]
theorem Float.beq_self_eq_false_iff {f : Float} : (f == f) = false ↔ f = nan := by
  grind [beq_self_iff]

@[simp]
theorem Float32.beq_self_eq_false_iff {f : Float32} : (f == f) = false ↔ f = nan := by
  grind [beq_self_iff]

/--
This theorem is true for all types but most other types have `LawfulBEq` where
`bne_self_eq_false` or `bne_iff_ne` apply.
-/
@[simp] theorem Float.bne_eq {f : Float} : (f != f) = (!f == f) := (rfl)

/--
This theorem is true for all types but most other types have `LawfulBEq` where
`bne_self_eq_false` or `bne_iff_ne` apply.
-/
@[simp] theorem Float32.bne_eq {f : Float32} : (f != f) = (!f == f) := (rfl)

/--
Boolean equality on `Float`s is symmetric and transitive, but not reflexive, as demonstrated
by `nan != nan`.
-/
instance : PartialEquivBEq Float where
  symm := by grind [Float.beq_iff_ne_nan_and_eq]
  trans := by grind [Float.beq_iff_ne_nan_and_eq]

/--
Boolean equality on `Float32`s is symmetric and transitive, but not reflexive, as demonstrated
by `nan != nan`.
-/
instance : PartialEquivBEq Float32 where
  symm := by grind [Float32.beq_iff_ne_nan_and_eq]
  trans := by grind [Float32.beq_iff_ne_nan_and_eq]

namespace Float.Model

theorem unpack_pack_unpack (a : Float.Model) : (pack a.unpack).unpack = a.unpack := by
  simp [pack, unpack]

theorem unpack_pack_neg_unpack (a : Float.Model) :
    (pack a.unpack.neg).unpack = a.unpack.neg := by
  simp [pack, unpack]

theorem pack_unpack (a : Float.Model) : pack a.unpack = a := by
  rcases a with ⟨⟨b⟩, h⟩
  simp only [pack, unpack]
  congr 2
  exact UnpackedFloat.pack_unpack_of_valid h

/-- Negation of a packed float. -/
theorem neg_pack (u : UnpackedFloat) : -(pack u) = pack u.neg := by
  by_cases h : u = .notANumber
  · subst h; rfl
  · change pack (pack u).unpack.neg = pack u.neg
    have : (pack u).unpack.neg = (pack u.neg).unpack := by
      simp only [pack, unpack, UInt64.toBitVec_ofBitVec, UnpackedFloat.pack_neg h,
        UnpackedFloat.unpack_flipSign]
    rw [this, pack_unpack]

@[simp] theorem neg_neg (a : Float.Model) : - -a = a := by
  change pack (pack a.unpack.neg).unpack.neg = a
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_neg, pack_unpack]

theorem neg_mul (a b : Float.Model) : -a * b = -(a * b) := by
  change pack (UnpackedFloat.mul _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_mul, neg_pack]

theorem mul_neg (a b : Float.Model) : a * -b = -(a * b) := by
  change pack (UnpackedFloat.mul _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.mul_neg, neg_pack]

theorem neg_div (a b : Float.Model) : -a / b = -(a / b) := by
  change pack (UnpackedFloat.div _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_div, neg_pack]

theorem div_neg (a b : Float.Model) : a / -b = -(a / b) := by
  change pack (UnpackedFloat.div _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.div_neg, neg_pack]

theorem mul_comm (a b : Float.Model) : a * b = b * a := by
  change pack (UnpackedFloat.mul _ a.unpack b.unpack) = pack (UnpackedFloat.mul _ b.unpack a.unpack)
  rw [UnpackedFloat.mul_comm]

theorem add_comm (a b : Float.Model) : a + b = b + a := by
  change pack (UnpackedFloat.add _ a.unpack b.unpack) = pack (UnpackedFloat.add _ b.unpack a.unpack)
  rw [UnpackedFloat.add_comm]

theorem lt_iff_unpack_lt {a b : Float.Model} : a < b ↔ a.unpack.lt b.unpack := Iff.rfl

theorem le_iff_unpack_le {a b : Float.Model} : a ≤ b ↔ a.unpack.le b.unpack := Iff.rfl

theorem eq_nan_iff_unpack_eq {a : Float.Model} : a = nan ↔ a.unpack = .notANumber := by
  constructor
  · rintro rfl; simp [nan, unpack, pack, UnpackedFloat.pack]
  · intro h; rw [← pack_unpack a, h]; rfl

theorem unpack_neg (a : Float.Model) : (-a).unpack = a.unpack.neg := unpack_pack_neg_unpack a

theorem lt_irrefl (a : Float.Model) : ¬a < a := UnpackedFloat.lt_irrefl _

theorem lt_asymm {a b : Float.Model} : a < b → ¬b < a := UnpackedFloat.lt_asymm

theorem lt_trans {a b c : Float.Model} : a < b → b < c → a < c := UnpackedFloat.lt_trans

theorem le_trans {a b c : Float.Model} : a ≤ b → b ≤ c → a ≤ c := UnpackedFloat.le_trans

theorem lt_of_lt_of_le {a b c : Float.Model} : a < b → b ≤ c → a < c :=
  UnpackedFloat.lt_of_lt_of_le

theorem lt_of_le_of_lt {a b c : Float.Model} : a ≤ b → b < c → a < c :=
  UnpackedFloat.lt_of_le_of_lt

theorem le_of_lt {a b : Float.Model} : a < b → a ≤ b := UnpackedFloat.le_of_lt

theorem lt_iff_le_not_ge {a b : Float.Model} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  UnpackedFloat.lt_iff_le_not_ge

theorem le_refl_iff {a : Float.Model} : a ≤ a ↔ a ≠ nan := by
  rw [ne_eq, eq_nan_iff_unpack_eq, le_iff_unpack_le]; exact UnpackedFloat.le_refl_iff

theorem not_le {a b : Float.Model} (ha : a ≠ nan) (hb : b ≠ nan) : ¬a ≤ b ↔ b < a := by
  rw [ne_eq, eq_nan_iff_unpack_eq] at ha hb
  exact UnpackedFloat.not_le ha hb

@[simp] theorem not_nan_lt (a : Float.Model) : ¬nan < a := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_lt_nan (a : Float.Model) : ¬a < nan := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_nan_le (a : Float.Model) : ¬nan ≤ a := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_le_nan (a : Float.Model) : ¬a ≤ nan := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem neg_lt_neg_iff {a b : Float.Model} : -a < -b ↔ b < a := by
  simp only [lt_iff_unpack_lt, unpack_neg, UnpackedFloat.neg_lt_neg]

@[simp] theorem neg_le_neg_iff {a b : Float.Model} : -a ≤ -b ↔ b ≤ a := by
  simp only [le_iff_unpack_le, unpack_neg, UnpackedFloat.neg_le_neg]

theorem minimum_comm (a b : Float.Model) : a.minimum b = b.minimum a := by
  simp only [minimum, UnpackedFloat.minimum_comm]

theorem maximum_comm (a b : Float.Model) : a.maximum b = b.maximum a := by
  simp only [maximum, UnpackedFloat.maximum_comm]

end Float.Model

namespace Float

@[simp] theorem neg_neg (x : Float) : - -x = x := by
  change ofModel (- -x.toModel) = x
  rw [Model.neg_neg]

@[simp] theorem neg_mul (x y : Float) : -x * y = -(x * y) := by
  change ofModel (-x.toModel * y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.neg_mul]

@[simp] theorem mul_neg (x y : Float) : x * -y = -(x * y) := by
  change ofModel (x.toModel * -y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.mul_neg]

@[simp] theorem neg_div (x y : Float) : -x / y = -(x / y) := by
  change ofModel (-x.toModel / y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.neg_div]

@[simp] theorem div_neg (x y : Float) : x / -y = -(x / y) := by
  change ofModel (x.toModel / -y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.div_neg]

theorem mul_comm (x y : Float) : x * y = y * x := by
  change ofModel (x.toModel * y.toModel) = ofModel (y.toModel * x.toModel)
  rw [Model.mul_comm]

theorem add_comm (x y : Float) : x + y = y + x := by
  change ofModel (x.toModel + y.toModel) = ofModel (y.toModel + x.toModel)
  rw [Model.add_comm]

@[simp] theorem toModel_nan : nan.toModel = .nan := rfl

@[simp] theorem toModel_neg (x : Float) : (-x).toModel = -x.toModel := rfl

theorem lt_iff_toModel_lt {x y : Float} : x < y ↔ x.toModel < y.toModel := by
  change Float.lt x y = true ↔ _
  simp [Float.lt]

theorem le_iff_toModel_le {x y : Float} : x ≤ y ↔ x.toModel ≤ y.toModel := by
  change Float.le x y = true ↔ _
  simp [Float.le]

theorem eq_nan_iff_toModel_eq {x : Float} : x = nan ↔ x.toModel = .nan := by
  cases x; simp [nan]

theorem lt_irrefl (x : Float) : ¬x < x := by
  simpa [lt_iff_toModel_lt] using Model.lt_irrefl x.toModel

theorem lt_asymm {x y : Float} : x < y → ¬y < x := by
  simpa [lt_iff_toModel_lt] using @Model.lt_asymm x.toModel y.toModel

theorem lt_trans {x y z : Float} : x < y → y < z → x < z := by
  simpa [lt_iff_toModel_lt] using @Model.lt_trans x.toModel y.toModel z.toModel

theorem le_trans {x y z : Float} : x ≤ y → y ≤ z → x ≤ z := by
  simpa [le_iff_toModel_le] using @Model.le_trans x.toModel y.toModel z.toModel

theorem lt_of_lt_of_le {x y z : Float} : x < y → y ≤ z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_lt_of_le x.toModel y.toModel z.toModel

theorem lt_of_le_of_lt {x y z : Float} : x ≤ y → y < z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_le_of_lt x.toModel y.toModel z.toModel

theorem le_of_lt {x y : Float} : x < y → x ≤ y := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.le_of_lt x.toModel y.toModel

theorem lt_iff_le_not_ge {x y : Float} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.lt_iff_le_not_ge x.toModel y.toModel

theorem le_refl_iff {x : Float} : x ≤ x ↔ x ≠ nan := by
  simpa [le_iff_toModel_le, eq_nan_iff_toModel_eq] using @Model.le_refl_iff x.toModel

theorem not_le {x y : Float} (hx : x ≠ nan) (hy : y ≠ nan) : ¬x ≤ y ↔ y < x := by
  rw [ne_eq, eq_nan_iff_toModel_eq] at hx hy
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using Model.not_le hx hy

@[simp] theorem not_nan_lt (x : Float) : ¬nan < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_lt_nan (x : Float) : ¬x < nan := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_nan_le (x : Float) : ¬nan ≤ x := by
  simp [le_iff_toModel_le]

@[simp] theorem not_le_nan (x : Float) : ¬x ≤ nan := by
  simp [le_iff_toModel_le]

@[simp] theorem neg_lt_neg_iff {x y : Float} : -x < -y ↔ y < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem neg_le_neg_iff {x y : Float} : -x ≤ -y ↔ y ≤ x := by
  simp [le_iff_toModel_le]

protected theorem min_comm (x y : Float) : min x y = min y x := by
  change ofModel (x.toModel.minimum y.toModel) = ofModel (y.toModel.minimum x.toModel)
  rw [Model.minimum_comm]

protected theorem max_comm (x y : Float) : max x y = max y x := by
  change ofModel (x.toModel.maximum y.toModel) = ofModel (y.toModel.maximum x.toModel)
  rw [Model.maximum_comm]

end Float

namespace Float32.Model

open Float.Model

theorem unpack_pack_unpack (a : Float32.Model) : (pack a.unpack).unpack = a.unpack := by
  simp [pack, unpack]

theorem unpack_pack_neg_unpack (a : Float32.Model) :
    (pack a.unpack.neg).unpack = a.unpack.neg := by
  simp [pack, unpack]

theorem pack_unpack (a : Float32.Model) : pack a.unpack = a := by
  rcases a with ⟨⟨b⟩, h⟩
  simp only [pack, unpack]
  congr 2
  exact UnpackedFloat.pack_unpack_of_valid h

/-- Negation of a packed float. -/
theorem neg_pack (u : UnpackedFloat) : -(pack u) = pack u.neg := by
  by_cases h : u = .notANumber
  · subst h; rfl
  · change pack (pack u).unpack.neg = pack u.neg
    have : (pack u).unpack.neg = (pack u.neg).unpack := by
      simp only [pack, unpack, UInt32.toBitVec_ofBitVec, UnpackedFloat.pack_neg h,
        UnpackedFloat.unpack_flipSign]
    rw [this, pack_unpack]

@[simp] theorem neg_neg (a : Float32.Model) : - -a = a := by
  change pack (pack a.unpack.neg).unpack.neg = a
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_neg, pack_unpack]

theorem neg_mul (a b : Float32.Model) : -a * b = -(a * b) := by
  change pack (UnpackedFloat.mul _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_mul, neg_pack]

theorem mul_neg (a b : Float32.Model) : a * -b = -(a * b) := by
  change pack (UnpackedFloat.mul _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.mul_neg, neg_pack]

theorem neg_div (a b : Float32.Model) : -a / b = -(a / b) := by
  change pack (UnpackedFloat.div _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_div, neg_pack]

theorem div_neg (a b : Float32.Model) : a / -b = -(a / b) := by
  change pack (UnpackedFloat.div _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.div_neg, neg_pack]

theorem mul_comm (a b : Float32.Model) : a * b = b * a := by
  change pack (UnpackedFloat.mul _ a.unpack b.unpack) = pack (UnpackedFloat.mul _ b.unpack a.unpack)
  rw [UnpackedFloat.mul_comm]

theorem add_comm (a b : Float32.Model) : a + b = b + a := by
  change pack (UnpackedFloat.add _ a.unpack b.unpack) = pack (UnpackedFloat.add _ b.unpack a.unpack)
  rw [UnpackedFloat.add_comm]

theorem lt_iff_unpack_lt {a b : Float32.Model} : a < b ↔ a.unpack.lt b.unpack := Iff.rfl

theorem le_iff_unpack_le {a b : Float32.Model} : a ≤ b ↔ a.unpack.le b.unpack := Iff.rfl

theorem eq_nan_iff_unpack_eq {a : Float32.Model} : a = nan ↔ a.unpack = .notANumber := by
  constructor
  · rintro rfl; simp [nan, unpack, pack, UnpackedFloat.pack]
  · intro h; rw [← pack_unpack a, h]; rfl

theorem unpack_neg (a : Float32.Model) : (-a).unpack = a.unpack.neg := unpack_pack_neg_unpack a

theorem lt_irrefl (a : Float32.Model) : ¬a < a := UnpackedFloat.lt_irrefl _

theorem lt_asymm {a b : Float32.Model} : a < b → ¬b < a := UnpackedFloat.lt_asymm

theorem lt_trans {a b c : Float32.Model} : a < b → b < c → a < c := UnpackedFloat.lt_trans

theorem le_trans {a b c : Float32.Model} : a ≤ b → b ≤ c → a ≤ c := UnpackedFloat.le_trans

theorem lt_of_lt_of_le {a b c : Float32.Model} : a < b → b ≤ c → a < c :=
  UnpackedFloat.lt_of_lt_of_le

theorem lt_of_le_of_lt {a b c : Float32.Model} : a ≤ b → b < c → a < c :=
  UnpackedFloat.lt_of_le_of_lt

theorem le_of_lt {a b : Float32.Model} : a < b → a ≤ b := UnpackedFloat.le_of_lt

theorem lt_iff_le_not_ge {a b : Float32.Model} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  UnpackedFloat.lt_iff_le_not_ge

theorem le_refl_iff {a : Float32.Model} : a ≤ a ↔ a ≠ nan := by
  rw [ne_eq, eq_nan_iff_unpack_eq, le_iff_unpack_le]; exact UnpackedFloat.le_refl_iff

theorem not_le {a b : Float32.Model} (ha : a ≠ nan) (hb : b ≠ nan) : ¬a ≤ b ↔ b < a := by
  rw [ne_eq, eq_nan_iff_unpack_eq] at ha hb
  exact UnpackedFloat.not_le ha hb

@[simp] theorem not_nan_lt (a : Float32.Model) : ¬nan < a := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_lt_nan (a : Float32.Model) : ¬a < nan := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_nan_le (a : Float32.Model) : ¬nan ≤ a := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_le_nan (a : Float32.Model) : ¬a ≤ nan := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem neg_lt_neg_iff {a b : Float32.Model} : -a < -b ↔ b < a := by
  simp only [lt_iff_unpack_lt, unpack_neg, UnpackedFloat.neg_lt_neg]

@[simp] theorem neg_le_neg_iff {a b : Float32.Model} : -a ≤ -b ↔ b ≤ a := by
  simp only [le_iff_unpack_le, unpack_neg, UnpackedFloat.neg_le_neg]

theorem minimum_comm (a b : Float32.Model) : a.minimum b = b.minimum a := by
  simp only [minimum, UnpackedFloat.minimum_comm]

theorem maximum_comm (a b : Float32.Model) : a.maximum b = b.maximum a := by
  simp only [maximum, UnpackedFloat.maximum_comm]

end Float32.Model

namespace Float32

@[simp] theorem neg_neg (x : Float32) : - -x = x := by
  change ofModel (- -x.toModel) = x
  rw [Model.neg_neg]

@[simp] theorem neg_mul (x y : Float32) : -x * y = -(x * y) := by
  change ofModel (-x.toModel * y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.neg_mul]

@[simp] theorem mul_neg (x y : Float32) : x * -y = -(x * y) := by
  change ofModel (x.toModel * -y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.mul_neg]

@[simp] theorem neg_div (x y : Float32) : -x / y = -(x / y) := by
  change ofModel (-x.toModel / y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.neg_div]

@[simp] theorem div_neg (x y : Float32) : x / -y = -(x / y) := by
  change ofModel (x.toModel / -y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.div_neg]

theorem mul_comm (x y : Float32) : x * y = y * x := by
  change ofModel (x.toModel * y.toModel) = ofModel (y.toModel * x.toModel)
  rw [Model.mul_comm]

theorem add_comm (x y : Float32) : x + y = y + x := by
  change ofModel (x.toModel + y.toModel) = ofModel (y.toModel + x.toModel)
  rw [Model.add_comm]

@[simp] theorem toModel_nan : nan.toModel = .nan := rfl

@[simp] theorem toModel_neg (x : Float32) : (-x).toModel = -x.toModel := rfl

theorem lt_iff_toModel_lt {x y : Float32} : x < y ↔ x.toModel < y.toModel := by
  change Float32.lt x y = true ↔ _
  simp [Float32.lt]

theorem le_iff_toModel_le {x y : Float32} : x ≤ y ↔ x.toModel ≤ y.toModel := by
  change Float32.le x y = true ↔ _
  simp [Float32.le]

theorem eq_nan_iff_toModel_eq {x : Float32} : x = nan ↔ x.toModel = .nan := by
  cases x; simp [nan]

theorem lt_irrefl (x : Float32) : ¬x < x := by
  simpa [lt_iff_toModel_lt] using Model.lt_irrefl x.toModel

theorem lt_asymm {x y : Float32} : x < y → ¬y < x := by
  simpa [lt_iff_toModel_lt] using @Model.lt_asymm x.toModel y.toModel

theorem lt_trans {x y z : Float32} : x < y → y < z → x < z := by
  simpa [lt_iff_toModel_lt] using @Model.lt_trans x.toModel y.toModel z.toModel

theorem le_trans {x y z : Float32} : x ≤ y → y ≤ z → x ≤ z := by
  simpa [le_iff_toModel_le] using @Model.le_trans x.toModel y.toModel z.toModel

theorem lt_of_lt_of_le {x y z : Float32} : x < y → y ≤ z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_lt_of_le x.toModel y.toModel z.toModel

theorem lt_of_le_of_lt {x y z : Float32} : x ≤ y → y < z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_le_of_lt x.toModel y.toModel z.toModel

theorem le_of_lt {x y : Float32} : x < y → x ≤ y := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.le_of_lt x.toModel y.toModel

theorem lt_iff_le_not_ge {x y : Float32} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.lt_iff_le_not_ge x.toModel y.toModel

theorem le_refl_iff {x : Float32} : x ≤ x ↔ x ≠ nan := by
  simpa [le_iff_toModel_le, eq_nan_iff_toModel_eq] using @Model.le_refl_iff x.toModel

theorem not_le {x y : Float32} (hx : x ≠ nan) (hy : y ≠ nan) : ¬x ≤ y ↔ y < x := by
  rw [ne_eq, eq_nan_iff_toModel_eq] at hx hy
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using Model.not_le hx hy

@[simp] theorem not_nan_lt (x : Float32) : ¬nan < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_lt_nan (x : Float32) : ¬x < nan := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_nan_le (x : Float32) : ¬nan ≤ x := by
  simp [le_iff_toModel_le]

@[simp] theorem not_le_nan (x : Float32) : ¬x ≤ nan := by
  simp [le_iff_toModel_le]

@[simp] theorem neg_lt_neg_iff {x y : Float32} : -x < -y ↔ y < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem neg_le_neg_iff {x y : Float32} : -x ≤ -y ↔ y ≤ x := by
  simp [le_iff_toModel_le]

protected theorem min_comm (x y : Float32) : min x y = min y x := by
  change ofModel (x.toModel.minimum y.toModel) = ofModel (y.toModel.minimum x.toModel)
  rw [Model.minimum_comm]

protected theorem max_comm (x y : Float32) : max x y = max y x := by
  change ofModel (x.toModel.maximum y.toModel) = ofModel (y.toModel.maximum x.toModel)
  rw [Model.maximum_comm]

end Float32
