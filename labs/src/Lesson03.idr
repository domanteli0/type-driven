import Data.String
import Data.Vect
import System.REPL

%default total

-- Enumeration (liet. išvardinimai)
-- 
-- kairėje - tipo apibrėžimas
-- dešinėje - konstruktoriai
--
-- NOTE: nereikia būti Show interface'o egzempliorius, kad jį pavaizduoti/string'izuoti
data Direction = North
               | East
               | South
               | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East  = South
turnClockwise South = West
turnClockwise West  = North

-- Recommended literature:
--   [The little typer](https://mitpress.mit.edu/9780262536431/the-little-typer/)
east : Direction
east = East

-- Union
data Shape = Triangle Double Double
           | Rectangle Double Double
%name Shape shape, shape1, shape2 -- douda suggestion'us idris auto-complete'ui ir t.t.

-- krč algebraic tipai

-- Rekursyvūs duomenų tipai:
-- pvz: List, Vect, ...
data Picture = Primitive Shape
             | Combination Picture Picture
             | Rotate Double Picture
%name Picture pic, pic1, pic2

testPicture : Picture
testPicture = Combination (Primitive ?hrs) (Rotate 43 (?asd))

pictureArea : Picture -> Picture
pictureArea (Primitive shape) = ?pict
pictureArea (Combination pic pic1) = ?pictureArea_missing_case_1
pictureArea (Rotate dbl pic) = ?pictureArea_missing_case_2

-- Generic

data Tree a = Empty
            | Node (Tree a) a (Tree a)
%name Tree tree, tree1, tree2

insert : Ord e => e -> Tree e -> Tree e
insert x Empty = Node Empty x Empty
insert x orig@(Node left y right) = case compare x y of
                                    LT => Node (insert x left) y right
                                    EQ => orig
                                    GT => Node left y (insert x right)

-- Binary search tree
data BSTree : Type -> Type where
    -- 👇 a.k.a. Empty 
    BSEmpty : Ord e => BSTree e 
    -- 👇 a.k.a. Node
    BSNode  : Ord e => (left: BSTree e) -> e -> (right: BSTree e) -> BSTree e

-- implementacija turėtų būt panaši į `insert`
ins : e -> BSTree e -> BSTree e
ins x BSEmpty = ?sda
ins x (BSNode left y right) = ?ins_missing_case_1

-- Dependant
data PowerSource = Petrol | Pedal

-- galima klasifikuoti `Vehicle` į dvi šeimas (nes PowerSource turi dvi reikšmes)
--
-- `PowerSource` šiuo atveju galime vadinti indeksu
-- pvz.: `Vect n e`, n - indeksas
data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Car : (fuel : Nat) -> Vehicle Petrol
    Bus : (fuel : Nat) -> Vehicle Petrol

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car car) = Car 100
refuel (Bus bus) = Bus 200
-- optional keyword impossible
-- 👇 dabar akivaizdu, kad impossible, bet didelėje programoje pravartu
refuel Bicycle impossible

data Vec : Nat -> Type -> Type where
    Nil : Vec Z a
    (::) : (x: a) -> (xs: Vec k a) -> Vec (S k) a

-- REPL:
-- > the (Vec _ _) [1, 2, 3, 4]
-- [1, 2, 3, 4]
-- 
-- NOTE: [el1, el2, ..., elN] sintaksė tinka visiems tipams,
-- kurie turi konstruktorius `Nil` ir `(::)`
--
-- [el1, el2, ..., elN] => (el1 :: el2 :: ... :: elN :: Nil)

-- REPL:
--   > :doc Vect.index
--   Data.Vect.index : Fin len -> Vect len elem -> elem
--   Extract a particular element from a vector
--   ```idris example
--   index 1 [1,2,3,4]
--   ```
--   Totality: total
--   Visibility: public export
-- 
-- NOTE:
-- `Fin` - laiko skaičius mažesnius negu kažkoks skaičius

-- REPL:
-- > index 10 $ the (Vect _ Nat) [1,2,3,4]
-- Error: Can't find an implementation for So (with block in integerLessThanNat 10 False 4).
-- 
-- (Interactive):1:7--1:9
--  1 | index 10 $ the (Vect _ Nat) [1,2,3,4]


-- "labai praktiškas pavyzdys"
-- 
-- labai pravers mums šitas thing:
-- Main> :doc integerToFin
-- Data.Fin.integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
--   Convert an `Integer` to a `Fin`, provided the integer is within bounds.
--   @n The upper bound of the Fin
--   Totality: total
--   Visibility: public export

tryIndex : {n: Nat} -> Integer -> Vect n a -> Maybe a
-- tryIndex {n} i xs = map (\x => index x xs) (integerToFin i n)
tryIndex {n} i xs = case (integerToFin i n) of
                        Nothing => Nothing
                        Just x  => Just(index x xs)

data DataStore : Type where
    -- konvencija turėti konstruktorius, kurie prasideda su `Mk`
    MkData : (size: Nat) ->
             (items : Vect size String) ->
             DataStore

-- vėliau išmoksim, kai nerašyti `size` ir `items`:
size : DataStore -> Nat
size (MkData k _) = k

-- NOTE:                              👇 - funkcija `size` funkcijos tipo anotacijoje 
items : (store : DataStore) -> Vect (size store) String
items (MkData _ xs) = xs

emptyDS : DataStore
emptyDS = MkData 0 []

addToTail : Vect size_0 String -> String -> Vect (S size_0) String
addToTail [] str = [str]
addToTail (x :: xs) str = x :: addToTail xs str

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) str = MkData (S size) (addToTail items str)

getEntry : (pos : Integer) -> (ds : DataStore) -> Maybe String
getEntry pos ds = case integerToFin pos (size ds) of
                       Nothing => Nothing
                       (Just x) => Just (index x (items ds))

indexOfInVect : String -> {k: Nat} -> Vect k String -> Maybe Integer
indexOfInVect str (i :: items) = case str `isInfixOf` i of
                                                    True  => Just $ cast (S k)
                                                    False => indexOfInVect str items
indexOfInVect _ [] = Nothing

indexOf : String -> DataStore -> Maybe Integer
indexOf str (MkData k items) = indexOfInVect str items

-- searchTheStore : String -> DataStore -> Maybe String
-- searchTheStore str (MkData _ items) = find (isInfixOf str) items

-- REPL:
-- Main> addToStore emptyDS "vienas"
-- MkData 1 ["vienas"]

-- REPL:
-- Main> :let ds = addToStore (addToStore emptyDS "vienas") "du"
-- Main> ds
-- MkData 2 ["vienas", "vienas"]

-- REPL:
-- Main> getEntry 0 ds
-- Just "vienas"
-- Main> getEntry 2 ds
-- Nothing

-- pvz.:
--  put vienas
--  put du
--  get 0
data Command = Put String | Get Integer | Search String | Size

parseCommand : String -> String -> Maybe Command
parseCommand "size"   _   = Just Size
parseCommand "put"    str = Just (Put str)
parseCommand "search" str = Just (Search str)
parseCommand "get"    str = case all isDigit (unpack str) of
                              False => Nothing
                              True => Just $ Get $ cast str
parseCommand _ _ = Nothing

parse : String -> Maybe Command
parse str = case span (/= ' ') str of
                        (cmd, arg) => parseCommand cmd (ltrim arg)

processInputParsed : DataStore -> Command -> Maybe (String, DataStore)
processInputParsed ds Size = Just (cast ( size ds ), ds)
processInputParsed ds (Put str) = Just $ ("added: " ++ str ++ "\n", addToStore ds str)
processInputParsed ds (Get i) = map (\entry => (entry ++ "\n", ds)) $ getEntry i ds
processInputParsed ds (Search query) = map (\index => (cast index ++ "\n", ds)) $ indexOf query ds

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput ds str = case parse str of
                        Nothing => Nothing
                        Just cmd => processInputParsed ds cmd

covering
main : IO ()
main = replWith (emptyDS) ">>> " processInput

ds1 : DataStore
ds1 = addToStore emptyDS "labas"

ds2 : DataStore
ds2 = addToStore ds1 "simis"