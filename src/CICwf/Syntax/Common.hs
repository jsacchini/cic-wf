{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
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

{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Some common datatypes that are used by both "CICwf.Syntax.Abstract" and
--   "CICwf.Syntax.Internal"

module CICwf.Syntax.Common where

import qualified Data.Foldable    as Fold
import           Data.List
import           Data.Monoid
import           Data.Traversable

import           CICwf.Syntax.Position

import           CICwf.Utils.Pretty
import           CICwf.Utils.Sized


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
  pretty = text . show

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
data Named a = Named { nameTag    :: Name
                     , namedValue :: a }
             deriving(Eq, Fold.Foldable, Traversable)

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

-- instance HasNames (Maybe Name) where
--   name = maybe [noName] name

instance HasNames (Named a) where
  name x = [nameTag x]

instance HasNames a => HasNames (Ranged a) where
  name = name . rangedValue


data ArgType
  = ArgType { argImplicit   :: Bool
            , argInferrable :: Bool
            } deriving(Eq)

instance Show ArgType where
  show (ArgType impl infr) = showImpl ++ showInfr
    where
      showImpl | impl = "{}"
               | otherwise = "()"
      showInfr | infr = "1"
               | otherwise = "0"

explicitArg :: ArgType
explicitArg = ArgType { argImplicit = False
                      , argInferrable = False }

data Arg a
  = Arg { unArg   :: a
        , argType :: ArgType
        } deriving(Functor, Fold.Foldable, Traversable)

instance Show a => Show (Arg a) where
  show (Arg x t) = show x ++ " " ++ show t

mkArg :: a -> Arg a
mkArg x = Arg { unArg = x, argType = explicitArg }

mkArgType :: a -> ArgType -> Arg a
mkArgType x t = Arg { unArg = x, argType = t }


instance HasRange a => HasRange (Arg a) where
  range = range . unArg

------------------------------------------------------------
-- * Implicit
------------------------------------------------------------

data Implicit a = Implicit { implicitTag   :: Bool
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

instance HasImplicit ArgType where
  isImplicit = argImplicit
  modifyImplicit f arg = arg { argImplicit = f (argImplicit arg) }

instance HasImplicit (Arg a) where
  isImplicit = isImplicit . argType
  modifyImplicit f arg = arg { argType = modifyImplicit f (argType arg) }


showImplicit :: (HasImplicit a) => a -> String -> String
showImplicit b x | isImplicit b = "{" ++ x ++ "}"
                 | otherwise    = "(" ++ x ++ ")"

prettyImplicit :: (HasImplicit a) => a -> Doc -> Doc
prettyImplicit b | isImplicit b = braces
                 | otherwise    = parens


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
  pretty = text . show


-- | Things with 'Polarity'.
data Polarized a = Pol { polarity :: Polarity,
                         unPol    :: a }
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
-- * Case kind
------------------------------------------------------------

data CaseKind a = CaseKind | CocaseKind a
                  deriving(Eq,Show,Functor,Fold.Foldable,Traversable)

------------------------------------------------------------
-- * Contexts (isomorphic to lists)
------------------------------------------------------------

data Ctx a = CtxEmpty
           | a :> (Ctx a)
           deriving(Eq, Functor, Fold.Foldable)

infixr :>

instance Show a => Show (Ctx a) where
  show e = "[" ++ showCtx e ++ "]"
    where
      showCtx CtxEmpty = ""
      showCtx (x :> CtxEmpty) = show x
      showCtx (x :> xs) = show x ++ "," ++ showCtx xs

instance Pretty a => Pretty (Ctx a) where
  pretty (CtxEmpty) = empty
  pretty (c :> ctx) = pretty c <+> pretty ctx

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

ctxGet :: Ctx a -> Int -> Maybe a
ctxGet CtxEmpty _ = Nothing
ctxGet (x :> xs) 0 = Just x
ctxGet (x :> xs) n = ctxGet xs (n-1)

ctxPush :: Ctx a -> a -> Ctx a
ctxPush CtxEmpty y = ctxSingle y
ctxPush (x :> xs) y = x :> (xs `ctxPush` y)

ctxSplit :: Ctx a -> (a, Ctx a)
ctxSplit (x :> xs) = (x, xs)

ctxSplitAt :: Int -> Ctx a -> (Ctx a, Ctx a)
ctxSplitAt 0 ctx = (ctxEmpty, ctx)
ctxSplitAt n (x :> xs) = (x :> l, r)
  where (l, r) = ctxSplitAt (n-1) xs

ctxCat :: Ctx a -> Ctx a -> Ctx a
ctxCat ctx1 ctx2 = Fold.foldr (:>) ctx2 ctx1

ctxUpdate :: Ctx a -> Int -> (a -> a) -> Ctx a
ctxUpdate (x :> xs) 0 f = f x :> xs
ctxUpdate (x :> xs) n f = x :> ctxUpdate xs (n-1) f

revCtxUpdate :: Ctx a -> Int -> (a -> a) -> Ctx a
revCtxUpdate ctx n f = envToCtx (envUpdate (ctxToEnv ctx) n f)


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
      showEnv (EnvEmpty :< x) = show x
      showEnv (es :< x) = showEnv es ++ "," ++ show x

instance Pretty a => Pretty (Env a) where
  pretty e = vcat (map pretty (envToList e))

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

envFind :: (a -> Bool) -> Env a -> a
envFind f (es :< e) | f e = e
                    | otherwise = envFind f es

envFindi :: (a -> Bool) -> Env a -> (Int, a)
envFindi f = findAux 0
  where
    findAux n (es :< e) | f e       = (n, e)
                        | otherwise = findAux (n+1) es

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

envCat :: Env a -> Env a -> Env a
envCat env1 EnvEmpty = env1
envCat env1 (es :< e) = envCat env1 es :< e


ctxToEnv :: Ctx a -> Env a
ctxToEnv = (EnvEmpty <:>)

envToCtx :: Env a -> Ctx a
envToCtx = (>:< CtxEmpty)


envUpdate :: Env a -> Int -> (a -> a) -> Env a
envUpdate (es :< e) 0 f = es :< f e
envUpdate (es :< e) n f = envUpdate es (n-1) f :< e

------------------------------------------------------------
-- * Universes
------------------------------------------------------------

data Sort
  = Type Int
  | Prop
  deriving(Eq)


instance Show Sort where
  show Prop = "Prop"
  show (Type n) | n == 0 = "Type"
                | otherwise = "Type" ++ show n


instance Pretty Sort where
  pretty = text . show
