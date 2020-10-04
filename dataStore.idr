module Main

import Data.Vect
import Data.Fin

%default total

infixr 5 .+.
data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

data Command : Schema -> Type where
  Quit : Command s
  Size : Command s
  Get  : Nat -> Command s
  ShowEntries : Command s
  Add  : SchemaType schema -> Command schema
  SetSchema : Schema -> Command s

consToTheEnd : a -> Vect n a -> Vect (S n) a
consToTheEnd x [] = [x]
consToTheEnd x (y :: xs) = y :: consToTheEnd x xs

appendToStore : (ds : DataStore) -> (SchemaType $ schema ds) -> DataStore
appendToStore (MkData schema size items) item =
  MkData schema (S size) (consToTheEnd item items)


getEntry : (store : DataStore) -> (i : Nat) -> Maybe (SchemaType $ schema store)
getEntry store i = case natToFin i (size store) of
                        Nothing => Nothing
                        (Just fin) => Just $ Vect.index fin (items store)

chompChar : Char -> String -> Maybe String
chompChar char str = case span (\c => c == char) str of
                          ("", _) => Nothing
                          (chomped, rest) => (case chomped == cast char of
                                                   False => Nothing
                                                   True => Just rest)

stringUncons : String -> Maybe (Char, String)
stringUncons str = case unpack str of
                      [] => Nothing
                      (x :: xs) => Just (x, pack xs)

parsePrefix : (s : Schema) -> String -> Maybe (SchemaType s, String)
parsePrefix SString str = case chompChar '"' str of
                               Nothing => Nothing
                               (Just rest) => 
                                 case span (\c => c /= '"') rest of
                                      (string, rest') =>
                                         case chompChar '"' rest' of
                                              Nothing => Nothing
                                              (Just rest'' ) => Just (string, ltrim rest'')

parsePrefix SInt str = case span isDigit str of
                          ("", rest) => Nothing 
                          (digit, rest) => Just (cast digit, ltrim rest)

parsePrefix SChar str = case stringUncons str of
                             Nothing => Nothing
                             (Just (c, rest)) => Just (c, ltrim rest)

parsePrefix (x .+. y) str = do
  (pX, rest)  <- parsePrefix x str
  (pY, rest') <- parsePrefix y rest
  pure ((pX, pY), rest')

readSchema : List String -> Maybe Schema
readSchema ("String" :: []) = Just SString
readSchema ((::) "String" rest@(x :: xs)) = [| pure SString .+. readSchema rest |]
readSchema ("Int" :: []) = Just SInt
readSchema ((::) "Int" rest@(x :: xs)) = [| pure SInt .+. readSchema rest |]
readSchema ("Char" :: []) = Just SChar
readSchema ((::) "Char" rest@(x :: xs)) = [| pure SChar .+. readSchema rest |]
readSchema _ = Nothing

readValueOfSchema : (s : Schema) -> String -> Maybe (SchemaType s)
readValueOfSchema s str = case parsePrefix s str of
                               -- The value must be all there is
                               (Just (val, "")) => Just val
                               _ => Nothing

parseCommandHelper : (s : Schema) -> (cmd : String) -> (rest : String)
                     -> Maybe (Command s)
parseCommandHelper schema "add" rest = [| Add (readValueOfSchema schema rest) |]
parseCommandHelper schema "get" rest = case all isDigit (unpack rest) of
                                     False => Nothing
                                     True => Just $ Get (cast rest) 
parseCommandHelper schema "quit" "" = Just Quit
parseCommandHelper schema "size" "" = Just Size
-- parseCommandHelper schema "search" searchQuery = Just $ Search searchQuery
parseCommandHelper schema "schema" rest = [| SetSchema (readSchema $ words rest) |]
parseCommandHelper _ _ _ = Nothing

parseCommand : (s : Schema) -> String -> Maybe (Command s)
parseCommand schema str = case span (/= ' ') str of
                     (cmd, rest) => parseCommandHelper schema cmd (ltrim rest)

vectFilter : (a -> Bool) -> Vect n a -> List a
vectFilter f [] = []
vectFilter f (x :: xs) = case f x of
                              False => vectFilter f xs
                              True => x :: vectFilter f xs

--searchInDataStore : DataStore -> String -> List String
--searchInDataStore (MkData size items) query = vectFilter (isInfixOf query) items

mapFst : (a -> b) -> (a, c) -> (b, c)
mapFst f (a, b) = (f a, b)

vectWithIndices : Vect n a -> Vect n (Fin n, a)
vectWithIndices [] = []
vectWithIndices (x :: xs) = (FZ, x) :: map (mapFst FS) (vectWithIndices xs)

--searchWithIndices : DataStore -> String -> List (Nat, String)
--searchWithIndices (MkData size items) query =
--  map (mapFst finToNat) $ vectFilter (isInfixOf query . snd) (vectWithIndices items)


joinWithNewlines : Vect n String -> String
joinWithNewlines [] = ""
joinWithNewlines (x :: xs) = x ++ "\n" ++ joinWithNewlines xs

formatWithId : Vect n (Fin n, SchemaType schema) -> String
-- formatWithId = joinWithNewlines . map (\(id, item) => show (the Nat (cast id)) ++ ": " ++ (showSchemaItem item))
formatWithId [] = ""
formatWithId ((index, item) :: xs) = (show (the Nat $ cast index) ++ ": ") -- ++ (showSchemaItem item) -- ++ "\n" -- ++ (formatWithId xs)

showSchemaItem : SchemaType s -> String
showSchemaItem {s = SString} str = str
showSchemaItem {s = SInt} i = cast i
showSchemaItem {s = SChar} c = "'" ++ cast c ++ "'"
showSchemaItem {s = (l .+. r)} (lVal, rVal) = "(" ++ (showSchemaItem lVal) ++ ", " ++ (showSchemaItem rVal) ++ ")" 


-- Update kind of like in model view update
update : (store : DataStore) -> (input : String) -> Maybe (String, DataStore)
update store input =
  case parseCommand (schema store) input of
       Nothing => Just ("Whaaat?", store)
       (Just Quit) => Nothing
       (Just (Get i)) => Just ( fromMaybe "Invalid index"
                                  [| showSchemaItem $ getEntry store i |]
                              , store
                              )
       (Just (Add str)) => Just ( "ID " ++ show (size store)
                                , appendToStore store str
                                )
       (Just Size) => Just (show (size store), store)
       (Just (SetSchema s)) => Just ("Nice!", MkData s 0 [])
       (Just (ShowEntries)) => Just (formatWithId $ vectWithIndices (items store), store)
    -- (Just (Search query)) => Just (formatWithId $ searchWithIndices store query, store)

partial main : IO ()
main = replWith (MkData (SString .+. SInt) 0 []) "\nInstruction: " update

--------
plusOneIsSucc : n + 1 = S n
plusOneIsSucc {n = Z} = Refl
plusOneIsSucc {n = (S k)} = cong $ plusOneIsSucc {n=k}
