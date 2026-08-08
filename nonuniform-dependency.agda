open import Data.Nat
open import Data.Nat.Show
open import Data.String
open import Data.Integer
open import Data.Integer.Show
open import Data.Bool
open import Data.Char

open import Data.List

nary : Set -> ℕ -> Set
nary A 0 = A
nary A (suc n) = ℕ -> nary A n

data Token : Set where
  char : Char -> Token
  intTok : Token
  natTok : Token
  chrTok : Token
  strTok : Token

lex : List Char -> List Token
lex [] = []
lex ('%' ∷ '%' ∷ cs)= char '%' ∷ lex cs
lex ('%' ∷ 'd' ∷ cs)= intTok ∷ lex cs
lex ('%' ∷ 'u' ∷ cs)= natTok ∷ lex cs
lex ('%' ∷ 'c' ∷ cs)= chrTok ∷ lex cs
lex ('%' ∷ 's' ∷ cs)= strTok ∷ lex cs
lex (c ∷ cs)= char c ∷ lex cs

args : List Token -> Set
args [] = String
args (char _ ∷ toks) = args toks
args (intTok ∷ toks) = ℤ -> args toks
args (natTok ∷ toks) = ℕ -> args toks
args (chrTok ∷ toks) = Char -> args toks
args (strTok ∷ toks) = String -> args toks

printfType : String -> Set
printfType s = args (lex (toList s))

sprintf : (s : String) -> printfType s
sprintf str = loop (lex (toList str)) ""
  where
    loop : (toks : List Token) -> String -> args toks
    loop [] accum = accum
    loop (char c ∷ toks) accum = loop toks (accum Data.String.++ fromList (c ∷ []))
    loop (intTok ∷ toks) accum = \i -> loop toks (accum Data.String.++ Data.Integer.Show.show i)
    loop (natTok ∷ toks) accum = \n -> loop toks (accum Data.String.++ Data.Nat.Show.show n)
    loop (chrTok ∷ toks) accum = \c -> loop toks (accum Data.String.++ fromList (c ∷ []))
    loop (strTok ∷ toks) accum = \str -> loop toks (accum Data.String.++ str)
