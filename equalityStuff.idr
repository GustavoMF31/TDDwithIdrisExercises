import Data.Vect

--myReverse : Vect n a -> Vect n a
--myReverse [] = []
--myReverse {n=S k} (x :: xs) = reverseProof $ myReverse xs ++ [x] 
--  where
--    reverseProof : Vect (plus len 1) a -> Vect (S len) a
--    reverseProof {len} xs = rewrite plusCommutative 1 len in xs

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m =  m + n
myPlusCommutes Z m = rewrite sym (plusZeroRightNeutral m) in Refl
myPlusCommutes (S k) m = let rec = cong {f=S} (myPlusCommutes k m)
                         in rewrite sym (plusSuccRightSucc m k) in rec

vectLenPlusZero : Vect n a -> Vect (n + 0) a
vectLenPlusZero {n} xs = rewrite plusZeroRightNeutral n in xs

vectLenPlusSuccRight : Vect (S (n + len)) a -> Vect (n + (S len)) a
vectLenPlusSuccRight {n} {len} xs = rewrite sym (plusSuccRightSucc n len) in xs


reverse' : Vect n a -> Vect m a -> Vect (n+m) a
reverse' xs [] = vectLenPlusZero xs
reverse' xs (x :: ys) = vectLenPlusSuccRight $ reverse' (x :: xs) ys

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
