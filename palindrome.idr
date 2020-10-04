ap : (a -> b -> c) -> (a -> b) -> a -> c
ap f g x = f x (g x)

-- the one with Lazy Bool was making type checking tricky
||| A strict version of the && operator
and : Bool -> Bool -> Bool
and False _ = False
and True x = x

isPalindrome : String -> Bool
isPalindrome = ap (==) reverse

isPalindromeIgnoringCase : String -> Bool
isPalindromeIgnoringCase = (ap (==) reverse) . toLower

-- Maybe I should just give up with this point free thing
-- but it's way too fun to stop
isBigPalindrome : String -> Bool
isBigPalindrome =
  ap (and . ((> 10) . length)) ((ap (==) reverse) . toLower)

-- Ok I give up
isPalindromeOfSize : Nat -> String -> Bool
isPalindromeOfSize n str =
  str == (reverse str) && length str > n

counts : String -> (Nat, Nat)
counts str = ((length . words) str, length str)

topTen : Ord a => List a -> List a
topTen = List.take 10 . reverse . sort 

overLen : Nat -> List String -> Nat
overLen n = length . filter ((> n) . length)

main : IO ()
main = repl "\n>> " (show . isBigPalindrome)
