data Shape = ||| A triangle with a base and a height
             Triangle Double Double
           | ||| A square with base and a height 
             Rectangle Double Double
           | ||| A circle with it's radius
             Circle Double
%name Shape shape, shape1, shape2 

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle base height) = base * height
area (Circle radius) = pi * radius * radius

data Picture = Primitive Shape
             | Combine Picture Picture 
             | Rotate Double Picture
             | Translate Double Double Picture
%name Picture pic, pic1, pic2 

testPicture : Picture
testPicture = Combine (Translate 5  5  (Primitive (Rectangle 20 10)))
            $ Combine (Translate 35 5  (Primitive (Circle    5    )))
                      (Translate 15 25 (Primitive (Triangle  10 10)))

pictureArea: Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + (pictureArea pic1)
pictureArea (Rotate _ pic) = pictureArea pic
pictureArea (Translate _ _ pic) = pictureArea pic

data Tree a = Empty
            | Node (Tree a) a (Tree a)

insert : Ord a => a -> Tree a -> Tree a
insert a Empty = Node Empty a Empty
insert a node@(Node left val right) =
  case compare a val of
      LT => Node (insert a left) val right
      EQ => node
      GT => Node left val (insert a right) 

listToTree : Ord a => List a -> Tree a
listToTree = foldr insert Empty

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ (treeToList right)

data Expr = Val Int
          | Sum Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr

eval : Expr -> Int
eval (Val x) = x
eval (Sum x y) = eval x + (eval y)
eval (Sub x y) = eval x - (eval y)
eval (Mul x y) = eval x * (eval y)

liftA2' : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2' f x y = map f x <*> y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just $ max x y

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle x y)) = Just $ area triangle
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine pic pic1) = maxMaybe (biggestTriangle pic) (biggestTriangle pic1)
biggestTriangle (Rotate _ pic) = biggestTriangle pic
biggestTriangle (Translate _ _ pic) = biggestTriangle pic







