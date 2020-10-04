import Data.Vect

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

elemOfEmptyAbsurd : Elem a [] -> Void
elemOfEmptyAbsurd Here impossible
elemOfEmptyAbsurd (There _) impossible

removeElem : (elem : a) -> (v : Vect (S n) a) -> Elem elem v -> Vect n a
removeElem elem (elem :: xs) Here = xs
removeElem {n = Z} elem (x :: []) (There later) = absurd later
removeElem {n = (S k)} elem (x :: xs) (There later) = x :: removeElem elem xs later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

isElem' : DecEq a => (elem : a) -> (v : Vect n a) -> Dec (Elem elem v)
isElem' elem [] = No absurd
isElem' elem (x :: xs) = case decEq elem x of
                              (Yes Refl) => Yes Here
                              (No contraHead) => case isElem' elem xs of
                                                      (Yes prf) => Yes (There prf)
                                                      (No contraTail) => No (\prf => (case prf of
                                                                                           Here => contraHead Refl
                                                                                           (There later) => contraTail later))

data ListElem : a -> List a -> Type where
  Here : ListElem x (x :: ys)
  There : ListElem x xs -> ListElem x (y :: xs)

data Last : List a -> a -> Type where
  LastOne : Last [a] a
  LastCons : Last as a -> Last (x :: as) a

noLastElemForEmptyList : Last [] a -> Void
noLastElemForEmptyList LastOne impossible
noLastElemForEmptyList (LastCons _) impossible

isLast : DecEq a => (xs : List a) -> (elem : a) -> Dec (Last xs elem)
isLast [] elem = No noLastElemForEmptyList
isLast [e] elem = case decEq elem e of
                       (Yes Refl) => Yes LastOne
                       (No contra) => No (\prf => (case prf of
                                                        LastOne => contra Refl
                                                        (LastCons x) => noLastElemForEmptyList x))
isLast (_ :: y :: ys) elem = case isLast (y::ys) elem of
                               (Yes prf) => Yes $ LastCons prf
                               (No contra) => No (\prf => (case prf of
                                                                (LastCons x) => contra x)) 


