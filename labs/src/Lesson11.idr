module Lesson11

import Decidable.Equality
import Decidable.Decidable
import Data.Nat
import Data.So

%default total

-- Logika      ~ Idris
-- A & B       ~ (A, B)
-- A ∨ B       ~ Either A B
-- A -> B      ~ A -> B
-- not A       ~ A -> Void
-- True        ~ ()            [bet kuris tipas, kuris turi bent vieną reikšmę]
-- False       ~ Void
-- 
-- Jeigu sugebame parašyti funkciją aprašytam funkcijos tipui, tai turine įrodymą, kad
-- teiginys yra teisingas

--   expr ⊢ e_1 : t -> u      env ⊢ e_2 : t
--  -----------------------------------------
--            env ⊢  e_1 e_2 : u
--
--   t -> u, t
--  ----------  (Modus Ponens)
--      u
-- 
--   env ⊢ e_1 : (a, b) 
--  ------------------------ (&-elim_1)
--   env  :  [unintelligable]_1 t e_1 : a
--
-- Type     ~  Proposition (Teigininys)
-- Program  ~  Proof
-- Eval     ~  Supaprastinimas

-- ⬇️ Bandymas įrodyti: B => A => (A & B)
-- No

-- \V x \in X. P(x) -- f : (x : Type) -> P(x)
-- ∃x \in X. P(X)   --  ( x : Type ** P(x) )   -- DPair [dependant pair]

--  \A a b : Nat. \E m : Nat. (m = A & m >= b) v (m = b & m >= a)
mmax : Nat -> Nat -> Nat
mmax k j = if k >= j then k else j
-- ⬆️ beleka tinka, bet:
-- tinka ir šitas
mmax' : Nat -> Nat -> Nat
mmax' k j = 0
-- problema: nepakankamai griežtas tipas

-- max : (a : Nat) -> (b : Nat) -> X(a, b)
-- max : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, m >= b) ())
max' : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, GTE m b) (m = b, GTE m a))
max' 0 0 = (0 ** Left (Refl, LTEZero))
max' 0 (S k) = (S k ** Right (Refl, LTEZero))
max' (S k) 0 = (S k ** Left (Refl, LTEZero))
max' (S k) (S j) =
    case max' k j of
         ((val ** Left (xval, xprf))) => (S val ** Left ((cong S xval), LTESucc xprf))
         ((val ** (Right (xval, xprf)))) => (S val ** Right ((cong S xval), LTESucc xprf))

-- max'' : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, GTE m b) (m = b, GTE m a))
max'' : (a : Nat) -> (b : Nat) -> Either (GTE a b) (LTE a b)
max'' 0 k = Right LTEZero
max'' (S k) 0 = Left LTEZero
max'' (S k) (S j) =
    case max'' k j of
         (Left x) => Left (LTESucc x)
         (Right x) => Right (LTESucc x)

data Max : (m : Nat) -> (a : Nat) -> (b : Nat) -> Type where
     Max0 : Max 0 0 0
     MaxA : Max (S a) (S a) 0
     MaxB : Max (S b) 0 (S b)
     MaxX : Max m a b -> Max (S m) (S a) (S b)

max4 : (a : Nat) -> (b : Nat) -> (m : Nat ** Max m a b)
max4 0 0 = (0 ** Max0)
max4 0 (S k) = (S k ** MaxB)
max4 (S k) 0 = (S k ** MaxA)
max4 (S k) (S j) =
    let (val ** prf) = max4 k j
    in (S val ** MaxX prf)


max5 : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, So(  m >= b )) (m = b, So ( m >= a )))
max5 a b =
    case choose (a >= b) of
         (Left x) => (a ** Left (Refl, x))
         (Right x) => (a ** Right (?max5_rhs_5, ?max5_rhs_6))

data Maax : Type where
     Maa0 : Maax -> Maax

xx : Nat -> Nat -> Nat
xx a b = a + b

P : a -> Type
P = const Type

Q : a -> Type

---- ✨ LAB TIME ✨ ----
-- Vx. (Px => Px)
t_1 : x -> P x -> P x
t_1 y z = z

-- asda : (y : P x) -> (z : Q x) -> P z
-- asda y z = ?asda_rhs

-- Ex. (Px & Qx) => (EyPy) & (EzPz)
t_2 : (P x, Q x) -> ((y : Type ** P y), (z : Type ** P z))
t_2 (y, z) = (
        (y ** P y),
        (y ** P y)
    )

-- En \in N. Vm \in N. n <= m
t_3 : (n : Nat ** (( m : Nat ) -> LTE n m))
t_3 = (0 ** \m => LTEZero)

-- so_fun : (n : Nat) -> (m : Nat) -> So (equalNat n m)
-- so_fun n m =
--     case choose ( n == m ) of
--          (Left x) => x
--          (Right x) =>
--             case choose (n /= m) of
--                  (Left y) => ?asdasdasdasd_0
--                  (Right y) => ?asdasdasdasd_1

-- -- fun_fn : (n : Nat ) -> (( n' : Nat ) -> So (n == n'))
-- fun_fn : {n : Nat} -> (( n' : Nat ) -> So (n == n'))
-- fun_fn {n=n'} n =
--     case choose (n == n) of
--          (Left x) => ?asdasd_0
--          (Right x) => ?asdasd_1

-- -- Vn \in N. Em \in N. n <= m (2 būdas)
-- t_4 : (n : Nat ** (( m : Nat ) -> So ( n <= m )))
-- -- t_4 = (0 ** case choose (0 <= 1) of
-- --     (Left x) => \m => ?asasd_2
-- --     (Right x) => \m => ?asasd_3
-- -- )
-- t_4 = let x = choose (compareNat 1 0 == GT)
--       in ?asdasd

-- \V x \in X. P(x)    ~   f : (x : Type) -> P(x)
-- ∃x \in X. P(X)      ~    ( x : Type ** P(x) )   -- DPair [dependant pair]

--  \V a b : Nat. \E m : Nat. (m = A & m >= b) v (m = b & m >= a)
-- max : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, m >= b) ())
