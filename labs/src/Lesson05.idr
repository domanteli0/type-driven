module Lesson05

import Data.Vect

%default total

occurances : Eq ty => (item: ty) -> (values: List ty) -> Nat
occurances item [] = 0
occurances item (x :: xs) =
    case item == x of
         False => occurances item xs
         True  => 1 + (occurances item xs)

data Matter = Solid | Liquid | Gas

-- Before:
-- Lesson05> occurances Gas [Gas]
-- Error: Can't find an implementation for Eq Matter.

Eq Matter where
    (==) Solid Solid   = True
    (==) Liquid Liquid = True
    (==) Gas Gas       = True
    (==) _   _         = False

-- After:
-- Lesson05> occurances Gas [Gas]
-- 1


data Tree e = Empty | Node (Tree e) e (Tree e)

-- 👇 NOTE: e turi būti klasės e egzempliorius
Eq e => Eq (Tree e) where
    (==) Empty Empty = True
    (==) (Node l v r) (Node l' v' r') = l == l' && r == r' && v == v'
    (==) _ _ = False

tree1 : Tree Nat
tree1 = Node Empty 10 (Node Empty 15 (Node Empty 20 Empty))

-- Lesson05> tree1 == tree1
-- True 

record Album where
    constructor MkAlbum
    artist : String
    title  : String
    year   : Integer

a1 : Album
a1 = MkAlbum "A1" "t1" 2000

a2 : Album
a2 = MkAlbum "A2" "t2" 2001

Eq Album where
    (==) (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) = a1 == a2 && t1 == t2 && y1 == y2

Ord Album where
    compare (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) = 
        case compare a1 a2 of
             EQ => case compare t1 t2 of
                        EQ => compare y1 y2
                        diffT => diffT
             diffArtist => diffArtist

Show Album where
    show (MkAlbum artist title year) = artist ++ " " ++ title ++ " (" ++ show year ++ ")"

-- čia užsiminė apie tagless final (iš haskell kurso)
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Abs (Expr num)

expr1 : Expr Int
expr1 = Add (Val 1) (Mul (Val 4) (Abs (Val (-6))))

eval : (Num num, Integral num, Abs num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    (*) = Mul
    fromInteger = Val . fromInteger

Num ty => Abs (Expr ty) where
    abs = Abs

-- Lesson05> the (Expr Int) (1 + 1)
-- Add (Val 1) (Val 1)

-- Lesson05> eval (the (Expr Int) (1 + 1))
-- 2

-- dabar Epxr galima `show`inti, serializuoti į JSON ir siųsti į serverį,
-- the possibilities are endless


------- THEMATIC BREAK -------

Cast (Maybe a) (List a) where
    cast Nothing = []
    cast (Just x) = [x]

-- Lesson05> the (List Integer) $ cast (Just 5)
-- [5]

------- FUNCTOR -------

-- short history of `map` & `fmap` in haskell:
-- at the beginning, "let there be lists" said the haskellers
-- and as such they invented `map`, only for lists
-- later they came up with `Maybe`, `Either` and other stuffs
-- eventually then they invented `Functor` and it's method `fmap`
-- idris cleans this up by merging `fmap` and `map` by only having 
-- `Functor` and `map`

------- FOLDABLE -------

Foldable (\a => Tree a) where
    foldr f acc Empty = acc
    foldr f acc (Node left e right) = 
        let leftFold  = foldr f acc left
            rightFold = foldr f leftFold right
        in 
            f e rightFold

-- Lesson05> foldr (+) 0 tree1
-- 45

------- LAB TASK TIME -------

-----     FUNCTOR     -----

Functor (\a => Tree a) where
    map f Empty = Empty
    map f (Node l v r) = 
        let l' = map f l
            r' = map f r
        in
            Node l' (f v) r'

-----   Pretty Print  -----
up : Nat -> Nat -> Nat
up k = S . max k

-- Expr with priority
-- data Expr' : Expr Int -> Type where
--     Val' : (n : Nat) -> ( el : Int ) -> Expr' (Val el)
--     -- Add' : Expr' n el -> Expr' m el -> Expr' ( S ( n > k && m > k) ) el
--     Add' : Expr' n el -> Expr' m el -> Expr' (up n m) el
--     -- :ditto
--     Mul' : Expr' n el -> Expr' m el -> Expr' (up n m) el
--     -- Abs' : Expr' n el -> Expr' (S n) el
--     Abs' : Expr' n el -> Expr' (S n) el
--     -- Add' : (l: Expr pl ty) -> (r: Expr' pr ty) -> Epxr' 
--     -- Mul' (Expr' p num) (Expr' p num)
--     -- Abs' (Expr' p num)

data Expr' = Val' Int
           | Add' Nat (Expr') (Expr')
           | Mul' Nat (Expr') (Expr')
           | Abs' Nat (Expr')

depth : Expr' -> Nat
depth (Val' _)     = 0
depth (Add' k _ _) = k
depth (Mul' k _ _) = k
depth (Abs' k _)   = k


-- Num ( Expr') where
--     -- (+) e1 e2 = Add' (up (depth e1) (depth e2)) e1 e2
--     (+) v1@(Val' _) v2@(Val' _)   = Add' 0 v1 v2
--     (+) v@(Val' i)   a@(Add' j x y) = Add' j v a
--     (+) v@(Val' i)   m@(Mul' j x y) = Add' j v m
--     (+) (Val' i)     (Abs' j x)   = ?plus_7
--     (+) a@(Add' k x y) v@(Val' i) = ( flip (+) ) a v
--     -- (+) (Add' k x y) (Add' j z w) = Add' (max j k)
--     (+) (Add' k x y) (Mul' j z w) = ?plus_6
--     (+) (Add' k x y) (Abs' j z) = ?plus_8
--     (+) (Mul' k x y) e2 = ?plus_2
--     (+) (Abs' k x)   e2 = ?plus_3
--     (*) e1 e2 = Mul' (up (depth e1) (depth e2)) e1 e2
--     fromInteger = Val' 0 . fromInteger

-- implementation {n : Nat} -> Num ty => Abs (Expr' n ty) where
--     abs {n} el = Abs' el

pp : Show a => Expr a -> String
pp (Val x) = show x
pp (Add x y) = "(" ++ (pp x) ++ " + " ++ (pp y) ++ ")"
pp (Mul x y) = (pp x) ++ " * " ++ (pp y)
pp (Abs x) = "|" ++ ( pp x ) ++ "|"

-----   Pretty Print  v2 -----

ppp : Show a => Bool -> Expr a -> String
ppp _ (Val x) = show x
ppp False (Add x y) = ?rhs_5
ppp True  (Add x y) = ?rhs_6
ppp False (Mul x y) = ?rhs_7
ppp True  (Mul x y) = ?rhs_8
ppp _ (Abs x)       = "|" ++ (ppp False x) ++ "|"

-- pp : Show a => Expr a -> String
-- pp = ppp False

-- https://en.wikipedia.org/wiki/Disjunctive_normal_form
-- Mul (Val x) (And y z) = And (Mul x y) (Mul x z)
-- Mul (And y z) (Val x) = And (Mul x z) (Mul y z)

dnf : (Num e) => Expr e -> Expr e
dnf v@(Val _) = v
dnf (Add x y) = Add (dnf x) (dnf y)
dnf e@(Mul (Val x) (Val y)) = e
dnf (Mul (Val x) (Add y z)) = Add (Mul (Val x) ( dnf y )) (?hole)
dnf (Mul (Val x) (Mul y z)) = ?dnf_rhs_10
dnf (Mul (Val x) (Abs y)) = ?dnf_rhs_11
dnf (Mul (Add x z) y) = ?dnf_rhs_5
dnf (Mul (Mul x z) y) = ?dnf_rhs_6
dnf (Mul (Abs x) y) = ?dnf_rhs_7
dnf (Abs x) = ?dnf_rhs_3
