{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, PackageImports,
  FlexibleInstances, UndecidableInstances #-}
module Syntax.Name where

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Trans

type Name = String


-- these classes are used by Bind
-- The use of these classes and definition of Bind should be revised
class HasName a where
  getName :: a -> Name

class HasNames a where
  getNames :: a -> [Name]


freshName :: [Name] -> Name -> Name
freshName xs y | y `notElem` xs = y
               | otherwise = addSuffix 0
                             where addSuffix n | (y++show n) `notElem` xs = y++show n
                                               | otherwise = addSuffix (n+1)

class (Monad m) => LookupName a m | m -> a where
    lookupName :: Name -> m (Maybe a)
    definedName :: Name -> m Bool

class (Monad m) => ExtendName a m | m -> a where
    extendName :: Name -> a -> m ()

instance (LookupName a m) => LookupName a (ReaderT r m) where
    lookupName = lift . lookupName
    definedName = lift . definedName

instance (ExtendName a m) => ExtendName a (ReaderT r m) where
    extendName x = lift . extendName x
