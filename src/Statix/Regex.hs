module Statix.Regex where

data Regex l
  = RMatch l
  | RStar (Regex l)
  | RSeq  (Regex l) (Regex l)
  | RAlt (Regex l) (Regex l)
  | Rε
  | REmp
  | RNeg (Regex l)
  | RAnd (Regex l) (Regex l)
  deriving (Eq, Ord)

(⍮) = RSeq
(∥) = RAlt
(&) = RAnd
rplus r = RSeq r (RStar r)
rquestion r = RAlt Rε r

empty :: Regex l → Bool
empty REmp = True
empty (RAnd r₁ r₂) = empty r₁ || empty r₂
empty (RAlt r₁ r₂) = empty r₁ && empty r₂
empty (RSeq r₁ r₂) = empty r₁ || empty r₂
empty (RNeg r) = not (empty r)
empty _ = False

matchε :: Regex l → Bool
matchε Rε           = True
matchε (RStar r)    = True
matchε (RSeq r₁ r₂) = matchε r₁ && matchε r₂
matchε (RAlt r₁ r₂) = matchε r₁ || matchε r₂
matchε REmp         = False
matchε (RMatch _)   = False
matchε (RNeg r)     = not (matchε r)
matchε (RAnd r₁ r₂) = matchε r₁ && matchε r₂

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
  RNeg r → RNeg (match l r)
  RAnd r₁ r₂ → (match l r₁) & (match l r₂)

matchₙ :: (Eq l) ⇒ [l] → Regex l → Regex l
matchₙ xs r = foldl (flip match) r xs

instance Show l => Show (Regex l) where
  show (RMatch l)   = show l
  show (RStar r)    = show r ++ "*"
  show (RSeq r1 r2) = "(" ++ show r1 ++ " " ++ show r2 ++ ")"
  show (RAlt r1 r2) = "(" ++ show r1 ++ " | " ++ show r2 ++ ")"
  show (Rε)         = "e"
  show (REmp)       = "0"
  show (RNeg r)     = "~" ++ show r
  show (RAnd r1 r2) = "(" ++ show r1 ++ " & " ++ show r2 ++ ")"
