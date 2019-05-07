{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
module Statix.Syntax.Pretty where

import Data.List

import Control.Monad.State
import Control.Monad.Writer

import Statix.Syntax.Terms
import Statix.Syntax.Typing
import Statix.Syntax.Constraint

prettyBranch :: forall t c m. (MonadWriter String m) ⇒ (t → m ()) → (Maybe [Ident] → c → m ()) → Branch t c → m ()
prettyBranch tm id (Branch mtch c) = do
  tell "_ -> _"

prettyF :: forall p t l m c. (MonadWriter String m) ⇒ (p → m ()) → (l → m ()) → (t → m ()) → (Maybe [Ident] → c → m ()) → ConstraintF p l t c → m ()
prettyF pr id tm constr c = prettyF_ c
  where
    prettyF_ :: ConstraintF p l t c → m ()
    prettyF_ CTrueF            = tell "true"
    prettyF_ CFalseF           = tell "false"
    prettyF_ (CEqF t₁ t₂)     = do
      tm t₁
      tell " == "
      tm t₂
    prettyF_ (CNewF n t)      = do
      tell "new "
      id n
      tm t
    prettyF_ (CDataF l t)     = do
      id l
      tell " -> "
      tm t
    prettyF_ (CEdgeF n₁ l n₂) = do
      id n₁
      tell "-[ " >> tm l >> tell "]-> "
      id n₂
    prettyF_ (CAndF c d)      = do
      constr Nothing c
      constr Nothing d
    prettyF_ (CExF ns c)      = do
      tell "{"
      mapM_ (\id → do tell id; tell " ") ns
      tell "}"
      constr (Just ns) c
    prettyF_ (CQueryF x r y)  = do
      tell "query " 
      id x
      tell $ show r
      tell " as "
      id y
    prettyF_ (COneF x t)      = do
      tell "single(" >> id x >> tell ", " >> tm t >> tell ")"
    prettyF_ (CEveryF x b)    = do
      tell "every " >> id x >> tell "(" >> prettyBranch tm constr b >> tell ")"
    prettyF_ (CMinF x p t)    = do
      tell "min " >> id x >> tell "..." >> id t
    prettyF_ (CFilterF x p t) = do
      tell "filter " >> id x >> tell "..." >> id t
    prettyF_ (CApplyF p ts)   = do
      pr p
      sequence_ (intersperse (tell ", ") (fmap tm ts))
    prettyF_ (CMatchF t brs)  = do
      tm t
      tell " match { "
      -- sequence_ (intersperse (tell "\n|") (fmap (prettyBranch tm constr) brs))
      tell "_ -> _"
      tell " }"

