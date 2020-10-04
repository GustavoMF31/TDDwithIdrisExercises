import Data.Vect

data WordState : (guessesRemaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guessesRemaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won  : (game : WordState (S guesses) 0) -> Finished

readSingleChar : IO (Maybe Char)
readSingleChar = [| head' (unpack <$> getLine) |]

--readSingleChar = do
--  line <- getLine
--  pure (head' (unpack line))

game : WordState (S guesses) (S letters) -> IO Finished
game state@(MkWordState word missing) = do
  char <- getLine
  Just guessedChar <- readSingleChar
        | Nothing => putSrlLn >>= ?h --game state
  ?rest

