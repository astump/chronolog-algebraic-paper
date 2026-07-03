-- terms without coercions
module Tm where

open import lib

infixl 8 _·_

data Tm : Set where
  S : Tm
  K : Tm
  _·_ : Tm → Tm → Tm
  Suc : Tm
  Zero : Tm
  Case : Tm → Tm → Tm → Tm
  Alg : Tm → Tm

