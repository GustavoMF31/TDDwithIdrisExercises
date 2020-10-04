import Data.Vect 

Matrix : Nat -> Nat -> Type -> Type 
Matrix m n elem = Vect m (Vect n elem)

qualify : (name : String) -> (adjective : String) -> String
qualify name adjective = name ++ " is " ++ adjective

repeat : (n : Nat) -> a -> Vect n a
repeat Z x = []
repeat (S k) x = x :: repeat k x

insertCol :    (x : Vect n elem)
            -> (xs : Matrix n len elem)
            -> Matrix n (S len) elem
insertCol [] [] = []
insertCol (x :: xs) (y :: ys) = (x :: y) :: insertCol xs ys

insertCol' : (x : Vect n elem) -> (xs : Matrix n len elem) -> Matrix n (S len) elem
insertCol' = zipWith (::)

-- The tutorial shows that just putting an underscore instead
-- of n does the job in this case
-- (An there would be no need for the {n} there)
transpose' : Matrix m n elem -> Matrix n m elem
transpose' {n} [] = repeat n []
transpose' (x :: xs) = insertCol x $ transpose' xs

addMatrix : Num e => Matrix m n e -> Matrix m n e -> Matrix m n e
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = [| x + y |] :: addMatrix xs ys 

productSum : Num e => Vect n e -> Vect n e -> e
productSum xs ys = sum [| xs * ys |]

distributeOver : (a -> a -> c)
               -> a -> Vect m a -> Vect m c
distributeOver f x xs = map (f x) xs

multMatrixHelper : Num e => Matrix m n e
                         -> Matrix o n e
                         -> Matrix m o e
multMatrixHelper [] [] = []
multMatrixHelper [] (x :: xs) = []
multMatrixHelper (x :: xs) ys =
  -- let distributed = distributeOver productSum x ys
  let distributed = map (productSum x) ys
  in distributed :: multMatrixHelper xs ys

multMatrix : Num e => Matrix m n e
                   -> Matrix n o e
                   -> Matrix m o e
multMatrix x y = multMatrixHelper x (transpose' y)








