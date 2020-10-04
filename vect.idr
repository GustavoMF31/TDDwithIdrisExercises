module HandMadeVectorStuff

import Data.Fin

%default total

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

%name Vect xs, ys, zs

append : Vect m a -> Vect n a -> Vect (m + n) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vect m a -> Vect m b -> Vect m (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

vectTake : (n : Fin m) -> Vect m a -> Vect (finToNat n) a
vectTake FZ xs = []
vectTake (FS x) (y :: xs) = y :: vectTake x xs

vectGet : (x : Fin n) -> Vect n a -> a
vectGet FZ (x :: xs) = x
vectGet (FS x) (y :: xs) = vectGet x xs

sumEntries : Num e => Integer -> Vect n e -> Vect n e -> Maybe e
sumEntries {n} i xs ys = map sumAtIndex (integerToFin i n)
  where sumAtIndex fin = vectGet fin xs + (vectGet fin ys)


-- tryIndex : Integer -> Vect n a -> Maybe a
-- tryIndex {n} x xs = map (\fin => ?index fin xs) (integerToFin x n)


