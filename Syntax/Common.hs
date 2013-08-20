{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
    FlexibleInstances, DeriveFunctor, DeriveFoldable
  #-}

-- | Some common datatypes that are used by both "Syntax.Abstract" and
--   "Syntax.Internal"

module Syntax.Common where

import qualified Data.Foldable as Fold
import Data.List
import Data.Monoid hiding ((<>))

import Text.PrettyPrint

import Syntax.Position

import Utils.Pretty
import Utils.Sized
import Utils.Value

------------------------------------------------------------
-- * Identifiers
------------------------------------------------------------

newtype Name = Id { unName :: Maybe String }
               deriving(Eq, Ord)

instance Show Name where
  show (Id (Just xs)) = xs
  show (Id Nothing) = "_"

instance Sized Name where
  size (Id Nothing) = 1
  size (Id (Just xs)) = genericLength xs

noName :: Name
noName = Id Nothing

isNull :: Name -> Bool
isNull (Id Nothing) = True
isNull _       = False

mkName :: String -> Name
mkName = Id . Just

modifyName :: (String -> String) -> Name -> Name
modifyName f (Id Nothing) = noName
modifyName f (Id (Just x)) = mkName (f x)

instance Pretty Name where
  prettyPrint = text . show


data Named a = Named { nameTag :: Name
                     , namedValue :: a }
             deriving(Eq)

instance Show a => Show (Named a) where
  show (Named x v) = show x ++ " : " ++ show v

instance Functor Named where
  fmap f (Named x a) = Named x (f a)

instance HasValue (Named a) a where
  value = namedValue

mkNamed :: Name -> a -> Named a
mkNamed = Named

instance HasRange a => HasRange (Named a) where
  range = range . namedValue

-- | Used for bindings
class HasNames a where
  name :: a -> [Name]

instance HasNames a => HasNames [a] where
  name = concatMap name

instance HasNames Name where
  name n = [n]

instance HasNames a => HasNames (Maybe a) where
  name = maybe [] name

instance HasNames (Named a) where
  name x = [nameTag x]

instance HasNames a => HasNames (Ranged a) where
  name = name . rangedValue

------------------------------------------------------------
-- * Implicit
------------------------------------------------------------

data Implicit a = Implicit { implicitTag :: Bool
                           , implicitValue :: a }
                  deriving(Eq)

instance Show a => Show (Implicit a) where
  show (Implicit b v) = around (show v)
    where
      around x = if b then "{{" ++ x ++ "}}" else "((" ++ x ++ "))"

mkImplicit :: Bool -> a -> Implicit a
mkImplicit = Implicit

class HasImplicit a where
  isImplicit :: a -> Bool
  modifyImplicit :: (Bool -> Bool) -> a -> a

  setImplicit :: Bool -> a -> a
  setImplicit = modifyImplicit . const

instance HasImplicit (Implicit a) where
  isImplicit = implicitTag
  modifyImplicit f (Implicit x v) = mkImplicit (f x) v

instance Functor Implicit where
  fmap f x = x { implicitValue = f (implicitValue x) }

instance HasNames a => HasNames (Implicit a) where
  name = name . implicitValue

instance HasImplicit a => HasImplicit (Named a) where
  isImplicit = isImplicit . namedValue
  modifyImplicit f (Named x v) = mkNamed x (modifyImplicit f v)

instance HasImplicit a => HasImplicit (Ranged a) where
  isImplicit = isImplicit . rangedValue
  modifyImplicit f (Ranged x v) = mkRanged x (modifyImplicit f v)

instance HasRange a => HasRange (Implicit a) where
  range = range . implicitValue

instance HasValue (Implicit a) a where
  value = implicitValue

------------------------------------------------------------
-- * Polarities
------------------------------------------------------------

data Polarity = Pos
              | Neg
              | SPos
              | Neut

instance Show Polarity where
  show Pos  = "+"
  show Neg  = "-"
  show SPos = "⊕"
  show Neut = "○"

instance Pretty Polarity where
  prettyPrint = text . show

data Polarized a = Pol { polarity :: Polarity,
                         unPol :: a }
                   deriving(Show)

instance Functor Polarized where
  fmap f x = x { unPol = f (unPol x) }

instance HasValue (Polarized a) a where
  value = unPol

instance HasNames a => HasNames (Polarized a) where
  name = name . unPol

mkPolarized :: Polarity -> a -> Polarized a
mkPolarized = Pol

------------------------------------------------------------
-- * Inductive kind (data/codata, fixpoint/cofixpoint)
------------------------------------------------------------

data InductiveKind = I | CoI
                   deriving(Eq,Show)

------------------------------------------------------------
-- * Contexts (isomorphic to lists)
------------------------------------------------------------

data Ctx a = CtxEmpty
           | CtxExtend a (Ctx a)
           deriving(Eq, Functor, Fold.Foldable)

instance Show a => Show (Ctx a) where
  show e = "[" ++ showCtx e ++ "]"
    where
      showCtx CtxEmpty = ""
      showCtx (CtxExtend x xs) = show x ++ "," ++ showCtx xs

bindings :: Ctx a -> [a]
bindings CtxEmpty = []
bindings (CtxExtend x xs) = x : bindings xs

instance HasNames a => HasNames (Ctx a) where
  name CtxEmpty = []
  name (CtxExtend x xs) = name x ++ name xs

ctxIsNull :: Ctx a -> Bool
ctxIsNull CtxEmpty = True
ctxIsNull (CtxExtend _ _) = False

ctxFromList :: [a] -> Ctx a
ctxFromList = foldr CtxExtend CtxEmpty

(+:) :: Ctx a -> Ctx a -> Ctx a
(+:) CtxEmpty ctx = ctx
(+:) (CtxExtend x xs) ctx = CtxExtend x (xs +: ctx)

ctxEmpty :: Ctx a
ctxEmpty = CtxEmpty

instance Sized (Ctx a) where
  size CtxEmpty = 0
  size (CtxExtend _ xs) = 1 + size xs

ctxLen :: Ctx a -> Int
ctxLen = size

(<|) :: a -> Ctx a -> Ctx a
(<|) = CtxExtend

ctxSingle :: a -> Ctx a
ctxSingle x = x <| ctxEmpty

(|>) :: Ctx a -> a -> Ctx a
(|>) CtxEmpty y = ctxSingle y
(|>) (CtxExtend x xs) y = CtxExtend x (xs |> y)

ctxSplit :: Ctx a -> (a, Ctx a)
ctxSplit (CtxExtend x xs) = (x, xs)

ctxSplitAt :: Int -> Ctx a -> (Ctx a, Ctx a)
ctxSplitAt 0 ctx = (ctxEmpty, ctx)
ctxSplitAt n (CtxExtend x xs) = (CtxExtend x l, r)
  where (l, r) = ctxSplitAt (n-1) xs

------------------------------------------------------------
-- * Environment (isomorphic to snoc lists)
------------------------------------------------------------

data Env a = EnvEmpty
           | EnvExtend (Env a) a
           deriving(Eq, Functor, Fold.Foldable)

instance Show a => Show (Env a) where
  show e = "[" ++ showEnv e ++ "]"
    where
      showEnv EnvEmpty = ""
      showEnv (EnvExtend es x) = showEnv es ++ "," ++ show x


instance HasNames a => HasNames (Env a) where
  name EnvEmpty = []
  name (EnvExtend es e) = name e ++ name es

envIsNull :: Env a -> Bool
envIsNull EnvEmpty = True
envIsNull (EnvExtend _ _) = False

envEmpty :: Env a
envEmpty = EnvEmpty

instance Sized (Env a) where
  size EnvEmpty = 0
  size (EnvExtend es _) = 1 + size es


envToList :: Env a -> [a]
envToList = flip envToList_ []
  where
    envToList_ EnvEmpty r = r
    envToList_ (EnvExtend es e) r = envToList_ es (e:r)

envLen :: Env a -> Int
envLen = size

envSingle :: a -> Env a
envSingle x = EnvExtend EnvEmpty x

(||>) :: Env a -> a -> Env a
(||>) = EnvExtend

envSplit :: Env a -> (Env a, a)
envSplit (EnvExtend es e) = (es, e)

envGet :: Env a -> Int -> a
envGet (EnvExtend _ e) 0 = e
envGet (EnvExtend es _) n = envGet es (n-1)

envSplitAt :: Int -> Env a -> (Env a, Env a)
envSplitAt 0 es               = (es, EnvEmpty)
envSplitAt n (EnvExtend es e) = (el, EnvExtend er e)
  where (el, er) = envSplitAt (n-1) es

(+>) :: Env a -> Env a -> Env a
(+>) es EnvEmpty = es
(+>) es (EnvExtend es' e') = EnvExtend (es +> es') e'

(+:+) :: Env a -> Ctx a -> Env a
(+:+) es CtxEmpty = es
(+:+) es (CtxExtend x xs) = EnvExtend es x +:+ xs

ctxToEnv :: Ctx a -> Env a
ctxToEnv = (EnvEmpty +:+)
