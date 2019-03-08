module Statix.Regex where

data Regex l
  = RMatch l
  | RStar (Regex l)
  | RSeq  (Regex l) (Regex l)
  | RAlt (Regex l) (Regex l)
  | Rε
  | REmp
  deriving (Show)

(⍮) = RSeq
(∥) = RAlt
rplus r = RSeq r (RStar r)

empty :: Regex l → Bool
empty REmp = True
empty _    = False

matchε :: Regex l → Bool
matchε Rε           = True
matchε (RStar r)    = True
matchε (RSeq r₁ r₂) = matchε r₁ && matchε r₂
matchε (RAlt r₁ r₂) = matchε r₁ || matchε r₂
matchε REmp         = False
matchε (RMatch _)   = False

match :: (Eq l) ⇒ l → Regex l → Regex l
match l r = case r of
  (RMatch l') →
    if l == l' then Rε else REmp
  (RStar r) → match l r ⍮ (RStar r)
  (RSeq r₁ r₂) →
    let left = (match l r₁) ⍮ r₂
    in if matchε r₁
      then left ∥ (match l r₂)
      else left
  (RAlt r₁ r₂) → (match l r₁ ∥ match l r₂)
  REmp → REmp
  Rε   → REmp

matchₙ :: (Eq l) ⇒ [l] → Regex l → Regex l
matchₙ xs r = foldl (flip match) r xs
