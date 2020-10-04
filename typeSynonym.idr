import Data.Vect

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

triangle : Polygon 3
triangle = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (b : Bool) -> StringOrInt b
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

-- valToString : (isInt : Bool) -> StringOrInt isInt -> String
-- valToString False x = trim x
-- valToString True x = cast x

valToString : (isInt : Bool) -> (case isInt of
                                      False => String
                                      True => Int) -> String
valToString False y = trim y
valToString True y = cast y

-- Should be a profunctor
MultivariableFunction : Nat -> Type -> Type -> Type
MultivariableFunction Z argumentType resultType = resultType
MultivariableFunction (S k) argumentType resultType =
  argumentType -> MultivariableFunction k argumentType resultType

multiAdder : (n : Nat) -> Nat -> MultivariableFunction n Nat Nat
multiAdder Z n = n
multiAdder (S argsToReceiveCount) n =
  (\receivedNat => multiAdder argsToReceiveCount (n + receivedNat))

asMultiVariable : (a -> a -> a) -> (n : Nat) -> a -> MultivariableFunction n a a
asMultiVariable f Z x = x
asMultiVariable f (S k) x =
  (\receivedArg => asMultiVariable f k (f x receivedArg))

multiProduct : (n : Nat) -> Nat -> MultivariableFunction n Nat Nat
multiProduct = asMultiVariable (*)


