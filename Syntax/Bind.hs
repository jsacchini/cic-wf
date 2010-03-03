{-# LANGUAGE FlexibleInstances #-}

module Syntax.Bind where

import Data.Foldable hiding (notElem)
import Data.Monoid

import Syntax.Name

data Bind a = Bind Name a
            | NoBind a
            | BindDef Name a a
            deriving(Show)

class BindClass a where
    bind :: a -> Name

expr (Bind _ e) = e
expr (NoBind e) = e

instance BindClass (Bind a) where
    bind (Bind x _) = x
    bind (NoBind _) = "_"
    bind (BindDef x _ _) = x

instance Functor Bind where
    fmap f (NoBind t) = NoBind $ f t
    fmap f (Bind x t) = Bind x $ f t
    fmap f (BindDef x t1 t2) = BindDef x (f t1) (f t2)

instance Foldable Bind where
    foldMap f (NoBind t) = f t
    foldMap f (Bind _ t) = f t
    foldMap f (BindDef _ t1 t2) = f t1 `mappend` f t2
