module Tp where
open import lib

{- D is the sole datatype, with signature functor F -}
data Tp : Set where
  F_ : Tp → Tp
  _⇒_ : Tp → Tp → Tp
  Alg : Tp → Tp
  D : Tp 

infixr 9 _⇒_
infixr 10 F_


