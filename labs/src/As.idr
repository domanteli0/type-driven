module AS

data As : a -> Type where
  MkAs : a -> a -> As a

as : a -> As a
as a = MkAs a a

fac : Nat -> Nat
fac n with (as n)
  fac _ | (MkAs n 0) = 1
  fac _ | (MkAs n (S n')) = n * fac n'
