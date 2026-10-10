import Batteries.Data.Nat.Digits

open Nat

/-! ## `ofDigitsBE` -/

#guard ofDigitsBE (base := 10) [2,3,4] == 234
#guard ofDigitsBE (base := 2) [0,1,0,0] == 4
#guard ofDigitsBE (base := 0) [] == 0
#guard ofDigitsBE (base := 1) [] == 0
#guard ofDigitsBE (base := 12345) [] == 0
#guard ofDigitsBE (base := 1) [0,0,0,0,0] == 0

/-! ## `toDigitsUpToBE` -/

#guard toDigitsUpToBE 123 10 3 == ([1,2,3] : List (Fin 10))
#guard toDigitsUpToBE 123 10 2 == ([2,3] : List (Fin 10))
#guard toDigitsUpToBE 4 2 4 == ([0,1,0,0] : List (Fin 2))
#guard toDigitsUpToBE 12345 1 5 == ([0,0,0,0,0] : List (Fin 1))

/-! ## `toDigitsBE` -/

#guard toDigitsBE 123 10 == ([1,2,3] : List (Fin 10))
#guard toDigitsBE 4 2 == ([1,0,0] : List (Fin 2))
#guard toDigitsBE 0 12345 == ([] : List (Fin 12345))

/-! ## Large inputs -/

#guard (toDigitsBE (10 ^ 5000) 10).length == 5001
#guard ofDigitsBE (toDigitsBE (3 ^ 20000) 7) == 3 ^ 20000
#guard ofDigitsBE (toDigitsUpToBE (3 ^ 20000) 10 3000) == 3 ^ 20000 % 10 ^ 3000
#guard toDigitsBE (2 ^ 3000 - 1) 2 == List.replicate 3000 1
#guard (toDigitsBE (7 ^ 3000) 10).map Fin.val == (Nat.toDigits 10 (7 ^ 3000)).map (·.toNat - 48)
