%default total

data Format = Number Format
            | Str Format
            | FChar Format
            | FDouble Format
            | Lit String Format
            | End

%name Format f

PrintfType : Format -> Type
PrintfType (Number f)  = Int    -> PrintfType f
PrintfType (Str f)     = String -> PrintfType f
PrintfType (FChar f)   = Char   -> PrintfType f
PrintfType (FDouble f) = Double -> PrintfType f
PrintfType (Lit str f) =           PrintfType f
PrintfType End         =           String

parseFormatString : List Char -> Format 
parseFormatString [] = End
parseFormatString ('%' :: 'd' :: xs) = Number $ parseFormatString xs
parseFormatString ('%' :: 's' :: xs) = Str $ parseFormatString xs
parseFormatString ('%' :: 'c' :: xs) = FChar $ parseFormatString xs
parseFormatString ('%' :: 'f' :: xs) = FDouble $ parseFormatString xs
parseFormatString (x :: xs) = case parseFormatString xs of
                                   (Lit str f) => Lit (strCons x str) f
                                   format => Lit (cast x) format

printFormat : (f : Format) -> (acc : String) -> PrintfType f
printFormat (Number  f) acc = \i      => printFormat f (acc ++ show i     )
printFormat (Str     f) acc = \str    => printFormat f (acc ++ str        )
printFormat (FDouble f) acc = \double => printFormat f (acc ++ show double)
printFormat (FChar   f) acc = \c      => printFormat f (acc ++ cast c     )
printFormat (Lit str f) acc =            printFormat f (acc ++ str        )
printFormat  End        acc =                           acc

printf : (s : String) -> PrintfType (parseFormatString $ unpack s)
printf s with (parseFormatString $ unpack s)
  printf s | format = printFormat format ""

TupleVect : Nat -> Type -> Type
TupleVect Z x = ()
TupleVect (S k) x = (x, TupleVect k x)

test : TupleVect 4 Nat
test = (1,2,3,4,())
