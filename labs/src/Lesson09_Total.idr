module Lesson09_Total

import Data.List

%default total

-- krč, problema yra tame, kad mūsų views'ai nėra rekursyvūs

data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          --              iš esmės:   (x :: ys) ++ [y]
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

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

data MySnocList : List a -> Type where
     MyEmpty : MySnocList []
     -- SnocSnoc  : (x, xs: _) -> (rec : SnocList xs) -> SnocList (xs ++ [x])
     MySnoc  : (rec : MySnocList xs) -> MySnocList (xs ++ [x])

mySnocListHelper : (snoc : MySnocList input) -> List xs -> MySnocList (input ++ rest)
mySnocListHelper snoc [] = ?asd --rewrite appendNilRightNeutral input in snoc
mySnocListHelper snoc (x :: ys) = ?mySnocListHelper_rhs_1


mySnocList : (xs : List a) -> MySnocList xs
mySnocList xs = mySnocListHelper MyEmpty xs

