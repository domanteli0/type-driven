module Lesson02

import Data.Vect as Vec
import Data.Vect

%default total

insertion : Ord el => el -> Vect len el -> Vect (S len) el
insertion x [] = [x]
insertion x (y :: xs) = case x < y of
                             False => y :: insertion x xs
                             True => x :: (y :: xs)

insSort : Ord el => Vect n el -> Vect n el
insSort [] = []
insSort (x :: xs) = let sorted = insSort xs in
                        insertion x sorted

empties' : (n : Nat) ->  Vect n (Vect 0 e)
empties' 0 = []
empties' (S k) = [] :: empties' k

empties : {n : Nat} -> Vect n (Vect 0 e)
empties {n = 0} = []
empties {n = (S k)} = [] :: empties {n=k}

transposeHelp : Vect n e -> Vect n (Vect len e) -> Vect n (Vect (S len) e)
transposeHelp [] [] = []
transposeHelp (x :: xs) (y :: ys) = (x :: y) :: transposeHelp xs ys

transposeMat : {n:Nat} -> Vect m (Vect n e) -> Vect n (Vect m e)
transposeMat [] = empties' n
transposeMat (x :: xs) = let transposed = (transposeMat xs) in
                             transposeHelp x transposed


vectAdd : Num e => Vect n e -> Vect n e -> Vect n e
-- vectAdd xs ys = map (\(x, y) => x + y) (zip xs ys)
-- vectAdd xs ys = map (uncurry (+)) (zip xs ys)
vectAdd xs ys = zipWith (+) xs ys

addMatrics : Num e => Vect row (Vect col e) -> 
                      Vect row (Vect col e) ->
                      Vect row (Vect col e)
addMatrics [] [] = []
addMatrics (x :: xs) (y :: ys) = (vectAdd x y) :: addMatrics xs ys

mulMatrics : Num e => {p: Nat} ->
                      Vect n (Vect m e) ->
                      Vect m (Vect p e) ->
                      Vect n (Vect p e)
mulMatrics [] [] = []
mulMatrics [] _  = []
mulMatrics (xs :: xx) yx = map (sum . zipWith (*) xs) yxT :: (mulMatrics xx yx)
    where
        yxT = transposeMat yx

-- [a_11*b_11 + a_12*b_21, a_21*b_11 + a_22*b_21, a_31*b_11 + a_32*b_21]
makeCol : Vect m e -> Vect p (Vect m e) -> Vect p e
makeCol xs yxT = ?hol

mulMatrix : Num e => {p: Nat} ->
                      Vect n (Vect m e) ->
                      Vect m (Vect p e) ->
                      Vect n (Vect p e)
mulMatrix [] _  = []
mulMatrix (xs :: xx) yx = makeCol xs yxT :: (mulMatrix xx yx)
    where
        yxT = transposeMat yx


append : Vect n e -> Vect m e -> Vect (n + m) e
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

Mtrx n m e = Vect n (Vect m e)

fun : Num e => Vect m e -> Vect p (Vect m e) -> Vect p e
fun v1 = map (sum . zipWith (*) v1 )

mulMatrix' : Num e => {n: Nat} -> {m: Nat} -> {p: Nat} -> Vect n (Vect m e) ->
                      Vect m (Vect p e) ->
                      Vect n (Vect p e)
mulMatrix' [] _ = []
mulMatrix' (x :: xs) ys = (fun x ysT) :: mulMatrix' xs ys
  where
    ysT = transposeMat ys
