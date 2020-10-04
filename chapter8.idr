data Vect : Nat -> Type -> Type where
  Nil  : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

-- Recursion works fine:
--exactLength Z [] = Just []
--exactLength Z (x :: y) = Nothing
--exactLength (S k) [] = Nothing
--exactLength (S k) (x :: y) = map (x ::) $ exactLength k y

data EqNat : Nat -> Nat -> Type where
  Same : (a : Nat) -> EqNat a a

natEqSucc : EqNat k j -> EqNat (S k) (S j)
natEqSucc (Same k) = Same (S k)

checkEqNat : (a : Nat) -> (b : Nat) -> Maybe (EqNat a b)
checkEqNat Z Z = Just $ Same Z
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = [| natEqSucc (checkEqNat k j) |]


replaceLength : EqNat m n -> Vect m a -> Vect n a
replaceLength (Same m) y = y

exactLength : (len : Nat) -> Vect n Nat -> Maybe (Vect len Nat)
exactLength {n} len v = [| replaceLength (checkEqNat n len) (pure v) |]

checkEqNat' : (a : Nat) -> (b : Nat) -> Maybe (a = b) 
checkEqNat' Z Z = Just Refl
checkEqNat' Z (S k) = Nothing
checkEqNat' (S k) Z = Nothing
checkEqNat' (S k) (S j) = [| cong $ checkEqNat' k j |]

sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons Refl = Refl

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  ThreeSame : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z ThreeSame = ThreeSame

--append : (x : a) -> Vect n a -> Vect (S n) a
--append x [] = [x]
--append x (y :: z) = y :: append x z

