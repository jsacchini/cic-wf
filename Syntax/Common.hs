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

{-# LANGUAGE MultiParamTypeClasses,
    FlexibleInstances, DeriveFunctor, DeriveFoldable
  #-}

-- | Some common datatypes that are used by both "Syntax.Abstract" and
--   "Syntax.Internal"

module Syntax.Common where

import qualified Data.Foldable as Fold
import Data.List
import Data.Monoid

import qualified Text.PrettyPrint as PP

import Syntax.Position

import Utils.Pretty
import Utils.Sized


------------------------------------------------------------
-- * Variable names
------------------------------------------------------------

newtype Name = Id { unName :: Maybe String }
               deriving(Eq, Ord)

instance Show Name where
  show (Id (Just xs)) = xs
  show (Id Nothing) = "_"

instance Sized Name where
  size (Id Nothing) = 1
  size (Id (Just xs)) = genericLength xs

instance Pretty Name where
  prettyPrint = PP.text . show

-- | A variable of which we do not care of its name (typically \'_\').
noName :: Name
noName = Id Nothing

-- | Checks if the variable has a name.
isNull :: Name -> Bool
isNull (Id Nothing) = True
isNull _            = False

-- | Make a 'Name' from a 'String'.
mkName :: String -> Name
mkName = Id . Just

-- | Modify the underlying name of a variable (if there is one).
modifyName :: (String -> String) -> Name -> Name
modifyName _ (Id Nothing)  = noName
modifyName f (Id (Just x)) = mkName (f x)



-- | Things with 'Name'.
data Named a = Named { nameTag :: Name
                     , namedValue :: a }
             deriving(Eq)

instance Show a => Show (Named a) where
  show (Named x v) = show x ++ " : " ++ show v

instance HasRange a => HasRange (Named a) where
  range = range . namedValue

instance Functor Named where
  fmap f (Named x a) = Named x (f a)

-- | Make a 'Named' thing.
mkNamed :: Name -> a -> Named a
mkNamed = Named


-- | Types that have 'Name'. Used for bindings.

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

showImplicit :: (HasImplicit a) => a -> String -> String
showImplicit b x | isImplicit b = "{" ++ x ++ "}"
                 | otherwise    = "(" ++ x ++ ")"

prettyImplicit :: (HasImplicit a) => a -> PP.Doc -> PP.Doc
prettyImplicit b | isImplicit b = PP.braces
                 | otherwise    = PP.parens


------------------------------------------------------------
-- * Polarities
------------------------------------------------------------

data Polarity
  = Pos           -- ^ Positive;
  | Neg           -- ^ Negative;
  | SPos          -- ^ Strictly positive;
  | Neut          -- ^ Neutral.

instance Show Polarity where
  show Pos  = "+"
  show Neg  = "-"
  show SPos = "⊕"
  show Neut = "○"

instance Pretty Polarity where
  prettyPrint = PP.text . show


-- | Things with 'Polarity'.
data Polarized a = Pol { polarity :: Polarity,
                         unPol :: a }
                   deriving(Show)

instance Functor Polarized where
  fmap f x = x { unPol = f (unPol x) }

instance HasNames a => HasNames (Polarized a) where
  name = name . unPol

-- | Make a 'Polarized' thing.
mkPolarized :: Polarity -> a -> Polarized a
mkPolarized = Pol


------------------------------------------------------------
-- * Inductive kind (data\/codata, fixpoint\/cofixpoint)
------------------------------------------------------------

data InductiveKind = I | CoI
                   deriving(Eq,Show)


------------------------------------------------------------
-- * Contexts (isomorphic to lists)
------------------------------------------------------------

data Ctx a = CtxEmpty
           | a :> (Ctx a)
           deriving(Eq, Functor, Fold.Foldable)

instance Show a => Show (Ctx a) where
  show e = "[" ++ showCtx e ++ "]"
    where
      showCtx CtxEmpty = ""
      showCtx (x :> xs) = show x ++ "," ++ showCtx xs

instance Sized (Ctx a) where
  size = Fold.foldr (\ _ r -> r + 1) 0

instance HasNames a => HasNames (Ctx a) where
  name CtxEmpty = []
  name (x :> xs) = name x ++ name xs

instance HasRange a => HasRange (Ctx a) where
  range CtxEmpty = noRange
  range (x :> xs) = fuseRange (range x) (range xs)

instance Monoid (Ctx a) where
  mempty = CtxEmpty
  mappend CtxEmpty ctx = ctx
  mappend (x :> xs) ctx = x :> (mappend xs ctx)

bindings :: Ctx a -> [a]
bindings = Fold.toList

ctxIsNull :: Ctx a -> Bool
ctxIsNull CtxEmpty = True
ctxIsNull (_ :> _) = False

ctxFromList :: [a] -> Ctx a
ctxFromList = foldr (:>) CtxEmpty

ctxEmpty :: Ctx a
ctxEmpty = CtxEmpty

ctxLen :: Ctx a -> Int
ctxLen = size

ctxSingle :: a -> Ctx a
ctxSingle x = x :> ctxEmpty

ctxPush :: Ctx a -> a -> Ctx a
ctxPush CtxEmpty y = ctxSingle y
ctxPush (x :> xs) y = x :> (xs `ctxPush` y)

ctxSplit :: Ctx a -> (a, Ctx a)
ctxSplit (x :> xs) = (x, xs)

ctxSplitAt :: Int -> Ctx a -> (Ctx a, Ctx a)
ctxSplitAt 0 ctx = (ctxEmpty, ctx)
ctxSplitAt n (x :> xs) = (x :> l, r)
  where (l, r) = ctxSplitAt (n-1) xs


------------------------------------------------------------
-- * Environment (isomorphic to snoc lists)
------------------------------------------------------------

data Env a = EnvEmpty
           | (Env a) :< a
           deriving(Eq, Functor, Fold.Foldable)

instance Show a => Show (Env a) where
  show e = "[" ++ showEnv e ++ "]"
    where
      showEnv EnvEmpty = ""
      showEnv (es :< x) = showEnv es ++ "," ++ show x

instance HasNames a => HasNames (Env a) where
  name EnvEmpty = []
  name (es :< e) = name e ++ name es

instance Sized (Env a) where
  size = Fold.foldr (\ _ r -> r + 1) 0

instance Monoid (Env a) where
  mempty = EnvEmpty
  mappend es EnvEmpty = es
  mappend es (es' :< e') = mappend es es' :< e'


envIsNull :: Env a -> Bool
envIsNull EnvEmpty = True
envIsNull (_ :< _) = False


envEmpty :: Env a
envEmpty = EnvEmpty

envToList :: Env a -> [a]
envToList = flip envToList_ []
  where
    envToList_ EnvEmpty r = r
    envToList_ (es :< e) r = envToList_ es (e:r)

envLen :: Env a -> Int
envLen = size

envSingle :: a -> Env a
envSingle = (EnvEmpty :<)

envSplit :: Env a -> (Env a, a)
envSplit (es :< e) = (es, e)
envSplit EnvEmpty = error "Env.envSplit EnvEmpty"

envGet :: Env a -> Int -> a
envGet (_ :< e) 0 = e
envGet (es :< _) n = envGet es (n-1)

envSplitAt :: Int -> Env a -> (Env a, Env a)
envSplitAt 0 es        = (es, EnvEmpty)
envSplitAt n (es :< e) = (el, er :< e)
  where (el, er) = envSplitAt (n-1) es

(<:>) :: Env a -> Ctx a -> Env a
infix 8 <:>
(<:>) es CtxEmpty = es
(<:>) es (x :> xs) = es :< x <:> xs

(>:<) :: Env a -> Ctx a -> Ctx a
infix 8 >:<
(>:<) EnvEmpty ctx = ctx
(>:<) (es :< e) ctx = es >:< e :> ctx

ctxToEnv :: Ctx a -> Env a
ctxToEnv = (EnvEmpty <:>)
