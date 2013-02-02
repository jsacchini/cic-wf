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

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, UndecidableInstances
  #-}

module Kernel.PrettyTCM where

import Control.Applicative hiding (empty)

import qualified Data.Foldable as Fold
import Data.Functor

import qualified Text.PrettyPrint as PP

import qualified Utils.Pretty as MP

import Syntax.Internal as I
import Syntax.InternaltoAbstract
import Syntax.Common
import Syntax.Position
import Syntax.Size
import qualified Syntax.Abstract as A
import Kernel.TCM

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
--   Mostly stolen from Agda
---------------------------------------------------------------------------

type Doc = PP.Doc


empty, dot, defEq, doubleColon, implies, bar, arrow, langle, rangle, comma :: (MonadTCM tcm) => tcm Doc

empty       = return PP.empty
dot         = return MP.dot
defEq       = return MP.defEq
doubleColon = return MP.doubleColon
implies     = return MP.implies
bar         = return MP.bar
arrow       = return MP.arrow
langle      = return MP.langle
rangle      = return MP.rangle
comma       = return MP.comma
text :: (MonadTCM tcm) => String -> tcm Doc
text s	    = return $ PP.text s
sep, fsep, hsep, vcat :: (MonadTCM tcm) => [tcm Doc] -> tcm Doc
sep ds	    = PP.sep <$> sequence ds
fsep ds     = PP.fsep <$> sequence ds
hsep ds     = PP.hsep <$> sequence ds
vcat ds     = PP.vcat <$> sequence ds
($$), ($+$), (<>), (<+>) :: (MonadTCM tcm) => tcm Doc -> tcm Doc -> tcm Doc
d1 $$ d2    = (PP.$$) <$> d1 <*> d2
d1 $+$ d2   = (PP.$+$) <$> d1 <*> d2
d1 <> d2    = (PP.<>) <$> d1 <*> d2
d1 <+> d2   = (PP.<+>) <$> d1 <*> d2
nest n d    = PP.nest n <$> d
braces d    = PP.braces <$> d
brackets d  = PP.brackets <$> d
parens d    = PP.parens <$> d
int :: (MonadTCM tcm) => Int -> tcm Doc
int         = return . PP.int

parensIf :: (MonadTCM tcm) => Bool -> tcm Doc -> tcm Doc
parensIf True = fmap PP.parens
parensIf False = id

prettyList ds = brackets $ fsep $ punctuate comma ds

punctuate _ [] = []
punctuate d ds = zipWith (<>) ds (replicate n d ++ [empty])
    where
	n = length ds - 1


---------------------------------------------------------------------------
-- * The PrettyTCM class
---------------------------------------------------------------------------

class PrettyTCM a where
  prettyPrintTCM :: (MonadTCM tcm) => a -> tcm Doc
  prettyPrintDecTCM :: (MonadTCM tcm) => Int -> a -> tcm Doc

  prettyPrintTCM = prettyPrintDecTCM 0
  prettyPrintDecTCM = const prettyPrintTCM

-- instance MP.Pretty a => PrettyTCM a where
--   prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM a => PrettyTCM [a] where
  prettyPrintTCM = hsep . map prettyPrintTCM

instance PrettyTCM Int where
  prettyPrintTCM = int

instance PrettyTCM Name where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM Term where
  prettyPrintTCM x = reify x >>= return . MP.prettyPrint

instance PrettyTCM TCEnv where
  prettyPrintTCM (TCEnv env) = do ds <- ppEnv env
                                  return $ PP.hsep (PP.punctuate MP.comma ds)

ppEnv :: (MonadTCM tcm) => [I.Bind] -> tcm [Doc]
ppEnv [] = return []
ppEnv (Bind x impl t def: bs) = do b' <- reify t
                                   def' <- maybeReify def
                                   dbs <- pushBind (Bind x impl t def) $ ppEnv bs
                                   return $ (around impl
                                             (PP.hsep [MP.prettyPrint x,
                                                       ppDef def',
                                                       PP.text ":", MP.prettyPrint b'])) : dbs
  where
      around True x  = PP.text "{" PP.<> x PP.<> PP.text "}"
      around False x = PP.text "(" PP.<> x PP.<> PP.text ")"
      ppDef Nothing  = PP.text ""
      ppDef (Just x) = PP.text ":=" PP.<+> MP.prettyPrint x
      maybeReify Nothing = return Nothing
      maybeReify (Just x) = do x' <- reify x
                               return $ Just x'

instance PrettyTCM StageVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM SortVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM MetaVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM Context where
  prettyPrintTCM x = reify (Fold.toList x) >>= return . MP.prettyPrint

instance PrettyTCM A.Expr where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM I.Goal where
  prettyPrintTCM g = do ppbs <- ppEnv bs
                        ppt <- withCtx (goalCtx g) $ prettyPrintTCM (goalType g)
                        return $ PP.vcat (ppbs ++
                                          [ PP.text "-------------------------"
                                          , ppt])
    where
      bs = Fold.toList (goalCtx g)