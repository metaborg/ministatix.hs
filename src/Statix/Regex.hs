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
  | RAny
  deriving (Eq, Ord)

(⍮) = RSeq
(∥) = RAlt
(&) = RAnd
rplus r = RSeq r (RStar r)
rquestion r = RAlt Rε r

nullable :: Regex l → Bool
nullable Rε           = True
nullable (RStar r)    = True
nullable (RSeq r₁ r₂) = nullable r₁ && nullable r₂
nullable (RAlt r₁ r₂) = nullable r₁ || nullable r₂
nullable REmp         = False
nullable (RMatch _)   = False
nullable RAny         = False
nullable (RNeg r)     = not (nullable r)
nullable (RAnd r₁ r₂) = nullable r₁ && nullable r₂

match :: (Eq l) ⇒ l → Regex l → Regex l
match l r = case r of
  (RMatch l') →
    if l == l' then Rε else REmp
  (RStar r) → match l r ⍮ (RStar r)
  (RSeq r₁ r₂) →
    let left = (match l r₁) ⍮ r₂
    in if nullable r₁
      then left ∥ (match l r₂)
      else left
  (RAlt r₁ r₂) → (match l r₁ ∥ match l r₂)
  REmp → REmp
  Rε   → REmp
  RAny → Rε
  RNeg r → RNeg (match l r)
  RAnd r₁ r₂ → (match l r₁) & (match l r₂)

nomatch :: (Eq l) ⇒ l → Regex l → Bool
nomatch l r = case r of
  (RMatch l') → not (l == l')
  (RStar r) → nomatch l r
  (RSeq r₁ r₂) → nomatch l r₁ && (not (nullable r₁) || nomatch l r₂) 
  (RAlt r₁ r₂) → nomatch l r₁ && nomatch l r₂
  REmp → True
  Rε   → True
  RAny → False
  RNeg r → not (nomatch l r)
  RAnd r₁ r₂ → nomatch l r₁ || nomatch l r₂

matchₙ :: (Eq l) ⇒ [l] → Regex l → Regex l
matchₙ xs r = foldl (flip match) r xs

instance Show l => Show (Regex l) where
  show (RMatch l)   = show l
  show (RStar r)    = show r ++ "*"
  show (RSeq r1 r2) = "(" ++ show r1 ++ " " ++ show r2 ++ ")"
  show (RAlt r1 r2) = "(" ++ show r1 ++ " | " ++ show r2 ++ ")"
  show (Rε)         = "e"
  show (RAny)       = "."
  show (REmp)       = "0"
  show (RNeg r)     = "~" ++ show r
  show (RAnd r1 r2) = "(" ++ show r1 ++ " & " ++ show r2 ++ ")"
