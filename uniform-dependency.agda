open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String

data ListOfNats : Set where
  [] : ListOfNats
  _::_ : Nat -> ListOfNats -> ListOfNats

data ListOfStrings : Set where
  [] : ListOfStrings
  _::_ : String -> ListOfStrings -> ListOfStrings

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

tail : {A : Set} {n : Nat} -> Vec A (suc n) -> Vec A n
tail (x :: xs) = xs

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

filterLen : {A : Set} {n : Nat} -> (A -> Bool) -> Vec A n -> Nat
filterLen f [] = 0
filterLen f (x :: xs) with f x
... | true = suc (filterLen f xs)
... | false = filterLen f xs

filter : {A : Set} {n : Nat} -> (f : A -> Bool) -> (l : Vec A n) -> Vec A (filterLen f l)
filter f [] = []
filter f (x :: xs) with f x
... | true = x :: filter f xs
... | false = filter f xs
