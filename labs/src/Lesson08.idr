module Lesson08

--- Sąryšiai

-- a,b - naturalūs skaičiai
-- a < b
-- R = { (1, 2), (1, 3) ... (2, 3) }
-- R ⊆ N x N
-- 
-- a R b   arba  R(a, b)  i.e   (a, b) ∈ R
--

----- Savybės -----

------ Reflexivity -------

-- (a, a) ∈ R
-- 
-- Operatoriai: <=, =          
-- (bet ne <, čia bus irefleksijus)


------ Symetry -------
-- (a, b) ∈ R => (b, a) ∈ R
-- 
-- a <= b   - nėra simetriškas

------ Transitivity -------
-- (a, b) ∈ R & (a, c) ∈ R => (a, c) ∈ R

--- DB ---

-- | Employee  |
-- |-----------|
-- | id        |
-- | name      |
-- | dept_id   |
-- | dept_desc |
--
-- nenormalizuota, n e s  egzistuoja transityvūs ryšiai, eg.: id -> dept_id, dept_id -> dept_desc

--- 🔥 IDRIS TIME 🔥 ---

import Data.Vect
import Data.Vect.Elem
import Data.String
import Decidable.Equality

%default total

removeElem : DecEq a => (val: a) -> (xs: Vect (S k) a) -> Vect k a
removeElem val (x :: xs) = case decEq val x of
                                (Yes prf) => xs
                                --                      👇 čia yra bad 'n sad, nes idris nėra įsitikinęs, kad čia `Vect n a`
                                (No contra) => ?asd --- x :: (removeElem value xs)

elemTest : Elem "Mary" ["Peter", "Paul", "Mary"]
elemTest = There (There Here)

removeElem' : (val: a) -> (xs: Vect (S k) a) -> (prf: Elem val xs) -> Vect k a
removeElem' val (val :: xs) Here = xs 
removeElem' val (x :: []) (There later) = absurd later
-- using `impossible` is also possible:
-- removeElem' {k=0}   val (y :: []) (There later) impossible
removeElem' {k=S k} val (x :: xs@(_ :: _)) (There later) = x :: (removeElem' val xs later)--?lol --(removeElem val xs later)

removeElem'' : (val: a) -> (xs: Vect (S k) a) -> { auto prf: Elem val xs } -> Vect k a
removeElem'' val (val :: xs) {prf = Here} = xs 
removeElem'' val (x :: []) {prf = There later} = absurd later
removeElem'' {k=S k} val (x :: xs@(_ :: _)) {prf = There later} = x :: (removeElem' val xs later)--?lol --(removeElem val xs later)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There later) impossible

notInTail : (val = x -> Void) -> (Elem val xs -> Void) -> Elem val (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem' : DecEq a => (val : a) -> (xs: Vect n a) -> Dec (Elem val xs)
isElem' val [] = No notInNil
isElem' val (x :: xs) = case decEq val x of
                            (Yes Refl) => Yes Here
                            (No notHere) => case (isElem' val xs) of
                                                (Yes prf) => Yes (There prf)
                                                (No notThere) => No (notInTail notHere notThere )
                            -- (No contra) => isElem' val xs

---- ✨ LAB TIME ✨ ----

-- elementas yra paskutinis sąrašo elementas
data Last : List a -> a -> Type where
    LastOne  : Last [val] val
    LastCons : (prf: Last xs val) -> Last (x :: xs) val

-- t: Last [1,2,3] 3
-- t = LastCons (LastCons LastOne)

isLast : DecEq a => (xs : List a) -> (val : a) -> Dec (Last xs val)
