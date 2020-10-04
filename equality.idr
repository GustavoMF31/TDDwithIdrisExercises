data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

data Tree a = Empty
            | Node (Tree a) a (Tree a)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node x y z) (Node w s t) = x == w && y == s && z == t
  (==) _ _ = False

record Album where
  constructor MkAlbum
  artist : String
  name : String
  year : Integer

Eq Album where
  (==) (MkAlbum artist name year) (MkAlbum artist' name' year') =
          artist == artist' && name == name' && year == year'

Ord Album where
  compare (MkAlbum artist name year) (MkAlbum artist' name' year') =
    case compare artist artist' of
         EQ => (case compare year year' of
                     EQ => compare name name
                     different => different)
         different => different


data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
  (==) (Triangle x y) (Triangle z w) = x == z && y == w
  (==) (Rectangle x y) (Rectangle z w) = x == z && y == w
  (==) (Circle x) (Circle y) = x == y
  (==) _ _ = False

area : Shape -> Double
area (Triangle x y) = x * y / 2
area (Rectangle x y) = x * y
area (Circle x) = x * pi * pi

Ord Shape where
  compare shape1 shape2  = compare (area shape1) (area shape2)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Abs num, Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x)  = abs (eval x)


Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Num ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub

Abs ty => Abs (Expr ty) where
  abs = Abs

parens : String -> String
parens s = "(" ++ s ++ ")"

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = parens $ show x ++ " + " ++ show y
  show (Sub x y) = parens $ show x ++ " - " ++ show y
  show (Mul x y) = parens $ show x ++ " * " ++ show y
  show (Div x y) = parens $ show x ++ " / " ++ show y
  show (Abs x) = "|" ++ show x ++ "|"

(Eq ty, Abs ty, Neg ty, Integral ty) => Eq (Expr ty) where
  (==) expr1 expr2 = (eval expr1) == (eval expr2)

(Abs num, Neg num, Integral num) => Cast (Expr num) num where
  cast e = eval e

Functor Tree where
  map f Empty = Empty
  map f (Node left val right) = Node (map f left) (f val) (map f right)

foldLength : List String -> Nat
foldLength = sum . map length
-- foldLength xs = foldl (\n, str => n + length str) 0 xs

Foldable Tree where
  foldr f initialVal Empty = initialVal
  foldr f initialVal (Node left val right) = f val $ foldr f (foldr f initialVal left) right

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y) 
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)

data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

Eq a => Eq (Vect n a) where
  [] == [] = True
  (x :: xs) == (y :: ys) = x == y && xs == ys 

Foldable (Vect n) where
  foldr f initialVal [] = initialVal
  foldr f initialVal (x :: y) = f x (foldr f initialVal y)




