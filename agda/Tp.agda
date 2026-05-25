module Tp where
open import lib

{- D is the sole datatype, with signature functor F -}
data Tp : Set where
  D_ : Tp → Tp
  _⟶_ : Tp → Tp → Tp
  D⇒ : Tp → Tp
  μD : Tp 

infixr 9 _⟶_
infixr 10 D_


