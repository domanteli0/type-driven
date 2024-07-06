module Whatever

import Data.List
import Data.SnocList
import Data.Nat
import Data.Vect

data Parity : Nat -> Type where
     Even : {n : _} -> Parity (n + n)
     Odd  : {n : _} ->Parity (S (n + n))

-- parity : (n : Nat) -> Parity n
-- parity Z = Even {n = Z}
-- parity (S Z) = Odd {n = Z}
-- parity (S (S k)) with (parity k)
--   parity (S (S (j + j))) | Even
--       = rewrite plusSuccRightSucc j j in Even {n = S j}
--   parity (S (S (S (j + j)))) | Odd
--       = rewrite plusSuccRightSucc j j in Odd {n = S j}

helpEven : (j : Nat) -> Parity (S j + S j) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p

helpOdd : (j : Nat) -> Parity (S (S (j + S j))) -> Parity (S (S (S (j + j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even = helpEven j (Even {n = S j})
  parity (S (S (S (j + j)))) | Odd  = helpOdd j (Odd {n = S j})

%default total

data SnocList a =
    Lin
    | (:<) (Whatever.SnocList a) a

infix 1 @@

data As : a -> Type where
  (@@) : a -> a -> As a

as : a -> As a
as a = a @@ a

-- fac : Nat -> Nat
-- fac n with (as n)
--   fac _ | (n @@ 0) = 1
--   fac _ | (n @@ (S n'))
--     = n * fac n'

fac : Nat -> Nat

fac n @ Z = 1
fac n @ (S n')
    = n * fac n'


data MySnocList : List a -> Type where
     MyEmpty : MySnocList []
     MySnoc  : (x, xs:  _) -> (rec : MySnocList xs) -> MySnocList (xs ++ [x])
    --  MySnoc  : (rec : MySnocList xs) -> MySnocList (xs ++ [x])

mySnocListHelper : {input: _} -> (snoc : MySnocList input) -> (rest : List a) -> MySnocList (input ++ rest)
mySnocListHelper snoc [] = rewrite appendNilRightNeutral input in snoc
mySnocListHelper snoc (x :: xs) = 
    rewrite appendAssociative input [x] xs
    in mySnocListHelper (MySnoc x input snoc) xs

mySnocList : (xs : List a) -> MySnocList xs
mySnocList xs = mySnocListHelper MyEmpty xs

firstLast : List a -> Maybe (a, a)
firstLast [] = Nothing
firstLast (x :: xs) with (mySnocList xs)
  firstLast (x :: []) | MyEmpty = Nothing
  firstLast (x :: (ys ++ [y])) | (MySnoc y ys rec) = Just (x, y)

covering
efficientPow : Nat -> Nat -> Nat
efficientPow _ Z = 1
efficientPow x n with (parity n)
  efficientPow x (n + n)     | Even = efficientPow (x * x) n
  efficientPow x (S (n + n)) | Odd  = x * efficientPow (x * x) n

vecTest : Vect 3 String
vecTest = do
          a <- ["a", "b", "c"]
          b <- ["x", "y", "z"]
          pure $ a ++ b
