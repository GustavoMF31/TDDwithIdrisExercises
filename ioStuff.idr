import System
import Data.Fin

%default total

monadMap : Monad m => (a -> b) -> m a -> m b
monadMap f ma = ma >>= pure . f

infixr 2 >=>
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g a = join $ monadMap g (f a)

infixr 2 <=<
(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

(>>) : Monad m => m a -> m b -> m b
g >> f = (>>=) g (const f)

printLength : IO ()
printLength = putStr "Input string: "
              >> getLine
              >>= (putStrLn . show . Strings.length)

printLonger : IO ()
printLonger = do putStr "First string: "
                 first <- getLine
                 putStr "Second string: "
                 second <- getLine
                 let fLen = length first
                 let sLen = length second
                 let message = case compare fLen sLen of
                                    GT => "The biggest is the first one with " ++ show fLen
                                    EQ => "They're the same bro"
                                    LT => "The biggest is the second one with " ++ show sLen
                 putStrLn message
  
readNat : IO (Maybe Nat)
readNat = do
  input <- getLine
  if all isDigit (unpack input)
     then pure $ Just (cast input) 
     else pure Nothing

readPair : IO (String, String)
readPair = [| MkPair getLine getLine |]

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do 
  Just num1 <- readNat | Nothing => pure Nothing
  Just num2 <- readNat | Nothing => pure Nothing
  pure $ Just (num1, num2)

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Get up and stretch"
countdown (S secs) = do printLn secs
                        -- A million of microseconds, that is, one second.
                        usleep 1000000
                        countdown secs

partial
guessGame : Nat -> IO ()
guessGame n = do
  putStr "Guess: "
  Just guess <- readNat
      | Nothing => do putStrLn "Whaaaat?"
                      guessGame n
  case compare guess n of
       LT => putStrLn "Too small!!" >> guessGame n
       EQ => putStrLn "Hooray!!"
       GT => putStrLn "Too big!!" >> guessGame n

partial myReplWith : (state : a) -> (prompt : String)
             -> (a -> String -> Maybe (String, a))
             -> IO ()
myReplWith state prompt step = do
  putStr prompt
  input <- getLine
  case step state input of
      Nothing => pure ()
      Just (output, nextState) => do
        putStr output
        myReplWith nextState prompt step

partial myRepl : (prompt : String) -> (String -> String) -> IO ()
myRepl prompt f = do
  putStr prompt
  input <- getLine
  putStr (f input)
  myRepl prompt f

partial main : IO ()
main = do
  -- Let's use the time as randomness
  currentTime <- time
  guessGame (cast $ mod currentTime 100)

