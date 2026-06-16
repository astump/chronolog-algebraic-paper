module Tp where
open import lib

{- μD is the sole datatype, with signature functor D -}
data Tp : Set where
  D_ : Tp → Tp
  _⟶_ : Tp → Tp → Tp
  D⇒ : Tp → Tp
  μD : Tp 
  V : ℕ → Tp -- type variables, for reasoning about solving non-ground constraints 
  R : ℕ → Tp -- variables introduced in bodies of algebras

infixr 9 _⟶_
infixr 10 D_


