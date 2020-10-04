twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

equalSuccEqual : S k = S j -> k = j 
equalSuccEqual Refl = Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No (\prf => (case prf of
                                       Refl impossible))

checkEqNat (S k) Z = No (\prf => (case prf of
                                       Refl impossible))

checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes $ cong prf
                              (No contra) => No (contra . equalSuccEqual)

||| Invariant functor
interface Invariant (i : Type -> Type) where
  xmap : (a -> b) -> (b -> a) ->  i a -> i b

Invariant Dec where
  xmap f g (Yes prf) = Yes (f prf)
  xmap f g (No contra) = No (contra . g)

castMap : (Cast a b, Cast b a, Invariant i) => i a -> i b
castMap x = xmap cast cast x

Cast (S k = S j) (k = j) where
  cast Refl = Refl

Cast (k = j) (S k = S j) where
  cast Refl = Refl

checkEqNat2 : (x : Nat) -> (y : Nat) -> Dec (x = y)
checkEqNat2 Z Z = Yes Refl
checkEqNat2 Z (S k) = No (\prf => case prf of
                                       Refl impossible)
checkEqNat2 (S k) Z = No (\prf => case prf of
                                       Refl impossible)
checkEqNat2 (S k) (S j) = castMap (checkEqNat2 k j)

data Vect : Nat -> a -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> x :: xs = y :: ys -> Void 
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                   (Yes Refl) => case decEq xs ys of
                                                    (Yes Refl) => Yes Refl
                                                    (No contra) => No (tailUnequal contra)
                                   (No contra) => No (headUnequal contra)
                              
                              




