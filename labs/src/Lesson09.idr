module Lesson09

import Data.List.Views
import Data.List
import Data.Vect
import Data.Nat

%default total

-- reverse x :: xs = reverse xs ++ [x]
-- 
-- ^ not labai gerai nes O(n^2) sudėtingumas

data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
    Empty => NonEmpty [] x
    --              iš esmės:   (x :: ys) ++ [y]
    (NonEmpty ys y) =>
      NonEmpty (x :: ys) y

describeHelper : (input: List Int) -> (form : (ListLast input)) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "NonEmpty; last one: " ++ show x

describe : (input : List Int) -> String
describe input = (describeHelper input (listLast input))

describe' : (input : List Int) -> String
describe' input with (listLast input)
  describe' [] | Empty = "Empty"
  describe' (xs ++ [x]) | (NonEmpty xs x) = "NonEmpty; last one: " ++ show x

describe'' : (input : List Int) -> String
describe'' input =
    case listLast input of
         Empty => "Empty"
         (NonEmpty xs x) => "NonEmpty; last one: " ++ show x

-- 👇 not total
covering
myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

-- merge sort:
-- 
-- [1, 2, 4, 1]
-- [1, 2] [4, 1]
-- [1, 2] [1, 4]
-- [1, 1, 2, 4]
--
-- > :doc merge
-- Data.List.merge : Ord a => List a -> List a -> List a
--   Merge two sorted lists using the default ordering for the type of their elements.

-- mergeSort : Ord a => List a -> List a
-- mergeSort [] = []
-- mergeSort [x] = [x]
-- -- jeigu būt galima parašyt taip:
-- mergeSort (left ++ right) = merge (mergeSort left) (mergeSort right)

data SplitList : List a -> Type where
     SplitNil  : SplitList []
     SplitOne  : SplitList [x]
     SplitPair : (left : List a) -> (right : List a) -> SplitList $ left ++ right


splitList : (input : List a) -> (SplitList input)
splitList input = splitList' input input
    where
        splitList' : List a -> (input : List a) -> SplitList input
        splitList' _ [] = SplitNil
        splitList' _ [x] = SplitOne {x=x}
        splitList' (_ :: _ :: counter) (item :: items) =
            case splitList' counter items of
                 SplitNil => SplitOne
                 SplitOne {x} => SplitPair [item] [x]
                 (SplitPair left right) => SplitPair (item :: left) right
        splitList' _ items = SplitPair [] items

covering
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (left ++ right) | (SplitPair left right) = merge (mergeSort left) (mergeSort right)

---- ✨ TOTALITY ✨ ----

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

reverse'' : List a -> List a
reverse'' xs with (mySnocList xs)
  reverse'' [] | MyEmpty = []
  reverse'' (ys ++ [x]) | (MySnoc x ys rec) = x :: (reverse'' ys) | rec

mergeSort'' : Ord a => List a -> List a
mergeSort'' input with (splitRec input)
  mergeSort'' [] | SplitRecNil = []
  mergeSort'' [x] | (SplitRecOne x) = [x]
  mergeSort'' (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
    = merge (mergeSort'' lefts | lrec) (mergeSort'' rights | rrec)

---- ✨ LAB TIME ✨ ----
data TakeN : List a -> Type where
     Fewer : TakeN xs
     -- Exact: List a -> (xs : List a) -> TakeN (xs ++ rest)
     Exact : (xs : List a) -> {rest : _} -> TakeN (xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN 0 xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) =
    case takeN k xs of
         Fewer => Fewer
         (Exact ys) => Exact (x :: ys)

covering
groupBy : (n : Nat) -> (xs : List a) -> List (List a)
groupBy n xs with (takeN n xs)
  groupBy n xs | Fewer = [xs]
  groupBy n (ys ++ rest) | (Exact ys {rest}) = ys :: (groupBy n ys)

-- halves : (List a) -> (List a, List a) -- length, divhalves xs = ?halves_rhs
-- halves xs =
--     case splitList xs of
--          SplitNil => ([], [])
--          SplitOne {x} => ([], [x])
--          (SplitPair left right) => (left, right)

-- halves : (List a) -> (List a, List a) -- length, div
-- halves xs = let n = length xs
--                 half_n = n `div` 2
--             in ?asd

halves : (List a) -> (List a, List a) -- length, div
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], [])
  halves (ys ++ rest) | (Exact ys) = (ys, rest)

data TakeN' : List a -> Type where
     Fewer' : TakeN' xs
     Exact' : (xs : _) -> (n_xs : TakeN' xs) -> {rest : _} -> TakeN' (xs ++ rest)

takeN' : (n : Nat) -> (input : List a) ->  TakeN' input
takeN' 0 xs = Exact' [] (Fewer')
takeN' (S k) [] = Fewer'
takeN' (S k) (x :: xs) =
    case takeN' k xs of
         Fewer' => Fewer'
         -- (Exact' ys n_xs) => Exact' (x :: ys) (Fewer')
         (Exact' ys n_xs {rest}) =>
            rewrite appendAssociative [x] ys rest in Exact' (x :: ys) (Fewer')

-- total:
covering
groupBy' : (n : Nat) -> (xs : List a) -> List (List a)
groupBy' n xs with (takeN' n xs)
  groupBy' n xs | Fewer' = [xs]
  groupBy' n (ys ++ rest) | (Exact' ys n_xs {rest=rest}) = ys :: (groupBy' n rest)
