module Lesson07

import Data.Vect.Elem
import Data.Vect
import Data.String
import Decidable.Equality

%default total

----- 7️⃣ Lygybė: electric boogaloo -----

apppend' : Vect n e -> Vect m e -> Vect (n + m) e
apppend' [] ys = ys
apppend' (x :: xs) ys = x :: apppend' xs ys

-- viskas kaip ir čiki piki, bet
-- idriui nėra akivaizdu, kad n + m = m + n

append_nil : Vect m e -> Vect (plus m 0) e
append_nil xs = 
    rewrite plusCommutative m 0
    in xs

append_xs : Vect (S (plus m len)) e -> Vect (plus m (S len)) e
append_xs xs = rewrite sym (plusSuccRightSucc m len) in xs

apppend'' : Vect n e -> Vect m e -> Vect (m + n) e
apppend'' [] ys = append_nil ys
apppend'' (x :: xs) ys = append_xs $ x :: apppend'' xs ys

test : Void -> Vect 1 Int
test x = [42]

test' : Void -> 3 = 2
test' _ impossible
-- šitas pavyzdys [👆], parodo

test'' : 2 + 2 = 6 -> Void
test'' Refl impossible

test''' : the (Vect _ _) [1] = [0] -> Void

-- meanwhile:
--
-- test''' : 2 + 2 = 4 -> Void
-- test''' Refl impossible
-- 
-- gaunam error'ą:
-- test''' Refl is not a valid impossible case.

-- iš praeitos paskaitos:
-- checkEqNat' : (num1: Nat) -> (num2: Nat) -> Maybe (num1 = num2)
-- šičia naudojant `Maybe`, mes prarandamę informaciją,
-- apie nelygybę

-- kad neprarasti šios informacijos galime pasinaudoti `Dec`,
-- i.e. Either, bet su įrodymais

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

noRec : (k = j -> Void) -> S k = S j -> Void
noRec f Refl = f Refl

checkEqNat : (num1: Nat) -> (num2: Nat) -> Dec (num1 = num2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc
checkEqNat (S k) 0 = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                               (Yes prf) => Yes $ cong S prf
                               (No contra) => No (noRec contra)


exactlLenght : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactlLenght {m} len input = case decEq m len of
                                  (Yes prf) => Just $ rewrite sym prf in input
                                  (No _) => Nothing

checkEqInt : (num1: Int) -> (num2: Int) -> Dec (num1 = num2)
checkEqInt num1 num2 = decEq num1 num2

---- ✨ LAB TIME ✨ ----
-- xs_ : e -> Vect n e -> Vect (S n) e
-- xs_ x xs = x :: xs

noRec' : (xs : Vect n e) => (ys : Vect n e) => xs = ys ->
    (k = j -> Void) -> k :: xs = j :: ys -> Void
noRec' prf1 f prf2 = ?noRec'_rhs

--- PART 1 ---
headUnEq : 
           {xs: Vect n a} ->
           {ys: Vect n a} ->
           (contr : x = y -> Void) ->
           (x :: xs = y :: ys -> Void)
headUnEq contr Refl = contr Refl
    -- let prf1 = decEq 

--- PART 2 ---

tailUnEq : {xs: Vect n a} ->
           {ys: Vect m a} ->
           (contr : xs = ys -> Void) ->
           (x :: xs = y :: ys -> Void)
tailUnEq contr Refl = contr Refl

--- PART 3 ---

-- copy pasted from stdlib
data MyVect : (len : Nat) -> (elem : Type) -> Type where
  ||| Empty vector
  Nil  : MyVect Z elem
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : elem) -> (xs : MyVect len elem) -> MyVect (S len) elem

welp :
    (contr : x = y -> Void) ->
    (Lesson07.(::) x Nil) = ((::) y Nil) -> Void
welp contr Refl = contr Refl

myTailUnEq :
    {x : a} ->
    {y : a} ->
    {xs: MyVect n a} ->
    {ys: MyVect m a} ->
    (contr : xs = ys -> Void) ->
    (Lesson07.(::) x xs = Lesson07.(::) y ys -> Void)
myTailUnEq contr Refl = contr Refl

myTeadUnEq : 
          {xs: MyVect n a} ->
          {ys: MyVect n a} ->
          (contr : x = y -> Void) ->
          (x :: xs = y :: ys -> Void)
myTeadUnEq contr Refl = contr Refl

DecEq a => DecEq (MyVect n a) where
    decEq [] [] = Yes Refl
    decEq [x] [y] =
        case decEq x y of
             (Yes Refl) => Yes $ cong ( (flip (::)) Nil ) Refl
             (No contra) => No $ welp contra

    decEq (x :: xs) (y :: ys) =
        case decEq xs ys of
             (No contra) => No $ myTailUnEq contra
             (Yes Refl) =>
                case decEq x y of
                     (No contra) => No $ myTeadUnEq contra
                     (Yes Refl) => Yes $ cong ( (flip (::)) ys ) Refl
