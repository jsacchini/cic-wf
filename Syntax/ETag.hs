{-# LANGUAGE EmptyDataDecls, FlexibleInstances #-}

module Syntax.ETag where

data NM -- no meta
data EVAR

class ETag a where

instance ETag NM where
instance ETag EVAR where
