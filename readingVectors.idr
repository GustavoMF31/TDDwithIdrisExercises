import Data.Vect

readStringVector : IO (n ** Vect n String)
readStringVector = do
  elem <- getLine
  if elem == ""
     then pure (0 ** [])
     else do
       (restSize ** rest) <- readStringVector
       pure (S restSize ** elem :: rest) 

zipInputs : IO (n ** Vect n (String, String))
zipInputs = do
  (len1 ** v1) <- readStringVector
  (len2 ** v2) <- readStringVector
  case exactLength len1 v2 of  
       Nothing => putStrLn "Oh no! Bad lengths..." >>= const zipInputs
       (Just rightLenV2) => pure $ (len1 ** zip v1 rightLenV2)

readUntilBlank : IO (List String)
readUntilBlank = do
  elem <- getLine
  if elem == "" 
     then pure []
     else do
       rest <- readUntilBlank
       pure (elem :: rest)

joinWithNewlines : List String -> String
joinWithNewlines [] = ""
joinWithNewlines (x :: xs) = x ++ "\n" ++ joinWithNewlines xs

readAndSave : IO ()
readAndSave = do
  content <- readUntilBlank
  name <- getLine
  Right () <- writeFile name (joinWithNewlines content)
    | Left fileError => printLn fileError
  pure ()

readVectFileHelper : File -> IO (n ** Vect n String)
readVectFileHelper file = do
  False <- fEOF file
    | True => pure (_ ** [])
  Right line <- fGetLine file
    | Left fileError => pure (_ ** [])
  (len ** rest) <- readVectFileHelper file
  pure (S len ** line :: rest)

readVectFile : IO (n ** Vect n String)
readVectFile = do
  -- Let's open the file
  Right file <- openFile "written.txt" Read
    | Left fileError => pure (_ ** [])
  readVectFileHelper file

