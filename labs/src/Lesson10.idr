module Lesson10

import Data.Vect

%default total

infixr 5 .+.

public export --  <- eksportuoja tipą ir konstruktorius
data Schema = SString
            | SInt
            | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString   = String
SchemaType SInt      = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) ->
             (store : DataStore schema) ->
             DataStore schema
addToStore value (MkData _ items) = MkData _ $ value :: items

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $
            addToStore ("Venus", "Venera", 1961) $
            empty

-- public export
-- data StoreView : (schema : _) -> DataStore schema -> Type where
--   SNil : StoreView schema empty
--   SAdd : (value, store : _) ->
--          (rec : StoreView schema store) ->
--          StoreView schema $ addToStore value store

-- storeViewHelper : {size : _} ->
--                   (items : Vect size (SchemaType schema)) ->
--                   StoreView schema (MkData size items)
-- storeViewHelper [] = SNil
-- storeViewHelper (x :: xs) = SAdd x _ (storeViewHelper xs)

-- storeView : (store : DataStore schema) -> StoreView schema store
-- storeView (MkData size items) = storeViewHelper items

-- listItems : DataStore schema -> List (SchemaType schema)
-- listItems x with (storeView x)
--   listItems x | SNil = []
--   listItems (addToStore value store) | (SAdd value store rec) =
--     value :: listItmes store | rec

---- ✨ PASKAITA #10: Electric boogaloo ✨ ----

-- p & q -> p v q

f1 : (p, q) -> Either p q
f1 (x, y) = Left x

f21 : Either (p, q) r -> (Either p r, Either q r)
f21 (Left (p, q)) = (Left p, Left q)
f21 (Right r) = (Right r, Right r)

f22 : (Either p r, Either q r) -> Either (p, q) r
f22 ((Left p), (Left q))    = Left (p, q)
f22 ((Left p), (Right e))   = Right e
f22 ((Right r), (Left q))   = Right r
f22 ((Right r), (Right r')) = Right r'

f3 : (p -> r) -> ( (q -> r) -> (Either p q -> r))
f3 f g (Left p) = f p
f3 f g (Right q) = g q

f4 : p -> ((p -> Void) -> Void)
f4 x f = f x

f5 : ((p, q) -> Void ) -> (p -> (q -> Void))
f5 = curry

f61 : (Either p q -> Void) -> ((p -> Void), (q -> Void))
f61 f = (\x => f (Left x), \x => f (Right x))

f62 : ((p -> Void), (q -> Void)) -> (Either p q -> Void)
f62 (not_p, not_q) (Left p)  = not_p p
f62 (not_p, not_q) (Right q) = not_q q

f71 : ((p, q) -> Void) -> Either (p -> Void) (q -> Void)
f71 f = let f' = curry f
         in Right (\arg => ?asd_1)

-- f : (p, q) -> Void

f72 : Either (p -> Void) (q -> Void) -> ((p, q) -> Void)
f72 (Left  not_p) (p, q) = not_p p
f72 (Right not_q) (p, q) = not_q q

f8 : (p -> q) -> ((q -> Void) -> (p -> Void))
f8 f g x = g (f x)

