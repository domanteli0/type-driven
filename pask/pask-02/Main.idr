import Data.Vect

-- Nusako, kad visos funkcijos turi būti totalios
%default total

tup : (Int, Bool, Double)
tup = ?tup_

-- Mes visiškai apie IO neisim, nes ėjom šitą per funkcinį
-- "verta paminėti", kad `IO` irgi yra totali
io : IO ()
io = putStrLn "Labas"

-- Naturalūs skaičiai:
--  Z           - nulis
--  S Z         - vienas
--  S S Z       - du
--  S k         - t.t.
-- 
-- Sveiki skaičiai biški blogai, nes sveiki skaičiai, nes neprasideda (minus begalybė)

-- n : Nat
-- n = 45555
-- idris moka juos atvaizduoti kaip skaičius:
-- ```
-- > n
-- 45555
-- ```
-- 
-- Tačiau vidine struktūra vis tiek bus S k

-- list lenght
l : List a -> Nat
l [] = Z
l (x :: xs) = S (l (xs))

isEven : Nat -> Bool
isEven 0 = True
isEven (S k) = not (isEven k)

isOdd : Nat -> Bool
isOdd 0 = False
isOdd (S k) = isEven k

v0 : Vect 1 Double
v0 = [1]

allLength : Vect n String -> Vect n Nat
allLength [] = []
allLength (x :: xs) = length x :: ll xs

-- iSort : Vect n el -> Vect n el
-- iSort [] = []
-- iSort (x :: xs) = let sorted = iSort xs in
                   
