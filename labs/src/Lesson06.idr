module Lesson06

import Data.Vect
import Decidable.Equality

%default total

---- Lygybė ----

-- Norime įsitikinti, kad:
--   len == m
exactlLenght : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
--                                   👇 idris negali pasitikėti, kad šis metodas
--                                      _įrodo_ vectorių ilgio lygybę
exactlLenght {m} len input = case m == len of
                                  False => Nothing
                                  True => Just (?eq_input input )
                                  -- `?eq_input` pridėtas, kad kompiliuotosi
                                  -- lakyti, kad `?eq_input` = id

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
    Same : (num : Nat) -> EqNat num num

-- Galima sukonstruoti tipą, kuris turi skirtingas reikšmes
-- Lesson06> :t EqNat 4 5
-- EqNat 4 5 : Type
-- 
-- Beeeeet, vienintelis data konstruktorius `Same``
-- leidžia sukurti tik tokias reikšmes, kur abu Same tipo argumentai yra lygtūs
-- Lesson06> :t Same 5
-- Same 5 : EqNat 5 5

-- jeigu turim įrodymą, kad j == k
-- tai galim pagalimti įrodymą, kad (S j) == (S k)
sameS : (k: Nat) -> (j : Nat) -> EqNat k j -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

-- (EqNat num1 num2) - _įrodymas_, kad num1 ir num2 lygūs
checkEqNat : (num1: Nat) -> (num2: Nat) -> Maybe (EqNat num1 num2)
checkEqNat 0 0 = Just (Same 0)
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (sameS k j x)

exactLenght' : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLenght' {m} len input = case checkEqNat len m of
                                   Nothing => Nothing
                                   (Just (Same blah)) => Just input

-- yra `=` tipas
-- Lesson06> :doc =
-- Definition or equality type

-- Lesson06> :t 4 = 4
-- 4 = 4 : Type
-- 
-- Lesson06> :t 4 = 3
-- 4 = 3 : Type
-- 
-- Lesson06> :t 4 = 5
-- 4 = 5 : Type
-- 
-- Lesson06> the (4 = 4) Refl
-- Refl
-- 
-- Lesson06> the (4 = 5) Refl
-- Error: When unifying:
--     5
-- and:
--     4
-- Mismatch between: 5 and 4.
-- 
-- (Interactive):1:13--1:17
--  1 | the (4 = 5) Refl
--                  ^^^^

checkEqNat' : (num1: Nat) -> (num2: Nat) -> Maybe (num1 = num2)
checkEqNat' 0 0 = Just Refl
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
-- checkEqNat' (S k) (S j) = case checkEqNat' k j of
--                                      Nothing => Nothing
--                                      (Just x) => Just Refl -- (cong S x)
checkEqNat' (S k) (S j) = (\Refl => Refl) <$> checkEqNat' k j

-- myReverse : Vect n e -> Vect n e
-- myReverse [] = []
-- myReverse (x :: xs) = myReverse xs ++ [x]
--                       👆 gauname error'ą:
--                          Can't solve constraint between: plus len 1 and S len.
-- Lesson06> :t plus
-- Prelude.plus : Nat -> Nat -> Nat
--
-- Prelude.plus : Nat -> Nat -> Nat
-- plus 0 y = y
-- plus (S k) y = S (plus k y)
-- 
-- Lesson06> \k => plus k 1
-- \k => plus k 1
-- Lesson06> \k => plus 1 k
-- \k => S k
-- 
-- kadangi pattern match'inama ant pirmo argumento
-- tai idris nežino, kad jeigu antras argumentas 1, tai = ( S k )

myReverse : {n : Nat} -> Vect n e -> Vect n e
myReverse [] = []
-- myReverse (x :: xs) = myReverse xs ++ [x]
myReverse {n = S k} (x :: xs) =
    let rev_xs = myReverse xs
        result = rev_xs ++ [x]
    in rewrite plusCommutative 1 k
    in result

-- hole : S (plus n k) = S (plus k n)
myPlusCommute : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommute n 0 = rewrite plusZeroRightNeutral n in Refl
myPlusCommute n (S k) = rewrite sym ( plusSuccRightSucc n k )
                        in cong S (myPlusCommute n k)
-- iš esmės reikia įrodyti sudėties komutatyumą
pEq : S k = plus k 1
pEq = rewrite myPlusCommute 1 k in Refl
-- proof : plus k 1 = plus k 1
-- new rewrite'as perrašė visus `S k` į plus `plus k 1`

myReverseProof :  Vect (plus len 1) e -> Vect (S len) e
myReverseProof xs = rewrite myPlusCommute 1 len in xs

myReverse' : {n : Nat} -> Vect n e -> Vect n e
myReverse' [] = []
myReverse' (x :: xs) = myReverseProof ( myReverse' xs ++ [x] )

---- LAB TIME ✨ ----

--- PART 1 ---
-- Galima naudotis
--  * plusZeroRightNeutral
--  * plusSuccRightSucc
--  * sym
--  * cong


--- PART 2 ---
-- myReverse su accumulator

revListAcc : (acc : List el) -> List el -> List el
revListAcc acc []        = acc
revListAcc acc (x :: xs) = revListAcc (x :: acc) xs

revList : List el -> List el
revList = revListAcc []

revVectAcc : (acc : Vect n el) -> {m : Nat} -> Vect m el -> Vect (n+m) el
revVectAcc acc [] = rewrite plusZeroRightNeutral n in acc
revVectAcc acc {m = (S len)} (x :: xs) =
    rewrite sym $ plusSuccRightSucc n len
    in revVectAcc (x :: acc) xs

revVect : {n: Nat} -> Vect n el -> Vect n el
revVect = revVectAcc []

