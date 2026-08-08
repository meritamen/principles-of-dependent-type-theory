open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

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

lemma : {A : Set} {n : Nat} -> (l : Vec A n) -> filterLen (\l -> false) l ≡ 0
lemma [] = refl
lemma (x :: xs) = lemma xs

filterAll : {A : Set} {n : Nat} -> Vec A n -> Vec A 0
filterAll {A} l = subst (Vec A) (lemma l) (filter (\x -> false) l)
