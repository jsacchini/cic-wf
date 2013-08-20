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

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances
  #-}

module Kernel.PrettyTCM where

import Control.Applicative hiding (empty)
import Control.Monad.Reader

import qualified Data.Foldable as Fold

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
sep, fsep, hsep, hcat, vcat :: (MonadTCM tcm) => [tcm Doc] -> tcm Doc
sep ds	    = PP.sep <$> sequence ds
fsep ds     = PP.fsep <$> sequence ds
hsep ds     = PP.hsep <$> sequence ds
hcat ds     = PP.hcat <$> sequence ds
vcat ds     = PP.vcat <$> sequence ds
($$), ($+$), (<>), (<+>) :: (MonadTCM tcm) => tcm Doc -> tcm Doc -> tcm Doc
d1 $$ d2    = (PP.$$) <$> d1 <*> d2
d1 $+$ d2   = (PP.$+$) <$> d1 <*> d2
d1 <> d2    = (PP.<>) <$> d1 <*> d2
d1 <+> d2   = (PP.<+>) <$> d1 <*> d2
nest :: (MonadTCM tcm) => Int -> tcm Doc -> tcm Doc
nest n d    = PP.nest n <$> d
braces, brackets, parens :: (MonadTCM tcm) => tcm Doc -> tcm Doc
braces d    = PP.braces <$> d
brackets d  = PP.brackets <$> d
parens d    = PP.parens <$> d
int :: (MonadTCM tcm) => Int -> tcm Doc
int         = return . PP.int

parensIf :: (MonadTCM tcm) => Bool -> tcm Doc -> tcm Doc
parensIf True = fmap PP.parens
parensIf False = id

prettyList :: (MonadTCM tcm) => [tcm Doc] -> tcm Doc
prettyList ds = brackets $ fsep $ punctuate comma ds

punctuate :: (MonadTCM tcm) => tcm Doc -> [tcm Doc] -> [tcm Doc]
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

printTCM :: (MonadTCM tcm) => tcm Doc -> tcm ()
printTCM d = do d' <- d
                liftIO $ putStr $ PP.render d'

printTCMLn :: (MonadTCM tcm) => tcm Doc -> tcm ()
printTCMLn d = printTCM (d <> text "\n") -- TODO: this does not seem the right way

instance PrettyTCM Int where
  prettyPrintTCM = int

instance PrettyTCM Range where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM a => PrettyTCM (Maybe a) where
  prettyPrintTCM (Just x) = prettyPrintTCM x
  prettyPrintTCM Nothing = empty

instance PrettyTCM a => PrettyTCM (a,a) where
  prettyPrintTCM (x,y) = parens $ prettyPrintTCM x <> comma <+> prettyPrintTCM y

instance PrettyTCM Name where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM Term where
  prettyPrintTCM x = do traceTCM 99 $ hsep [text "prettyPrintTCM term",
                                            text ("reifying " ++ show x)]
                        x' <- reify x
                        traceTCM 99 $ hsep [text "reified ",
                                            return (MP.prettyPrint x')]
                        return (MP.prettyPrint x')


instance PrettyTCM A.Declaration where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM TCEnv where
  prettyPrintTCM env = do ds <- ppEnv env
                          return $ PP.fsep (PP.punctuate MP.comma ds)
    where
      ppEnv EnvEmpty = return []
      ppEnv (EnvExtend es e) = do ds <- ppEnv es
                                  d <- local (const es) $ prettyPrintTCM e
                                  return (ds ++ [d])

instance PrettyTCM Bind where
  prettyPrintTCM b =
    do
      b' <- reify (I.bindType b)
      def' <- maybeReify (I.bindDef b)
      return $ (around (isImplicit b)
                (PP.hsep [MP.prettyPrint (I.bindName b),
                          ppDef def',
                          PP.text ":", MP.prettyPrint b']))
    where
      around True x  = PP.text "{" PP.<> x PP.<> PP.text "}"
      around False x = PP.text "(" PP.<> x PP.<> PP.text ")"
      ppDef Nothing  = PP.text ""
      ppDef (Just x) = PP.text ":=" PP.<+> MP.prettyPrint x
      maybeReify Nothing = return Nothing
      maybeReify (Just x) = do x' <- reify x
                               return $ Just x'

instance PrettyTCM Context where
  prettyPrintTCM ctx = do ds <- prettyCtx ctx
                          return $ PP.fsep (PP.punctuate MP.comma ds)
    where
      prettyCtx CtxEmpty = return []
      prettyCtx (CtxExtend b bs) = do d <- prettyPrintTCM b
                                      ds <- pushBind b $ prettyCtx bs
                                      return (d:ds)

instance PrettyTCM CaseIn where
  prettyPrintTCM c = do c' <- reify c
                        return $ MP.prettyPrint c'

instance PrettyTCM a => PrettyTCM [a] where
  prettyPrintTCM = brackets . hcat . punctuate (text ", ") . map prettyPrintTCM


instance PrettyTCM (Named Global) where
  prettyPrintTCM g = reify g >>= return . MP.prettyPrint

instance PrettyTCM StageVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM SortVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM MetaVar where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM A.Expr where
  prettyPrintTCM = return . MP.prettyPrint

instance PrettyTCM I.Goal where
  prettyPrintTCM g =
    vcat [ prettyPrintTCM (goalEnv g)
         , text "-------------------------"
         , local (const (goalEnv g)) $ prettyPrintTCM (goalType g)]
