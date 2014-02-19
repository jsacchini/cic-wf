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

{-# LANGUAGE FlexibleInstances    #-}

module CICminus.TypeChecking.PrettyTCM where

import           Control.Applicative       hiding (empty)
import           Control.Monad.Reader

import qualified CICminus.Utils.Pretty as PP

import qualified CICminus.Syntax.Abstract           as A
import qualified CICminus.Syntax.Concrete           as C
import           CICminus.Syntax.Internal           as I
import           CICminus.Syntax.InternalToAbstract
import qualified CICminus.Syntax.AbstractToConcrete as AC
import           CICminus.Syntax.Common
import           CICminus.Syntax.Position
-- import           CICminus.Syntax.Size
import           CICminus.TypeChecking.TCM

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
--   Mostly stolen from Agda
---------------------------------------------------------------------------

type Doc = PP.Doc

white :: (MonadTCM tcm) => Doc -> tcm Doc
white = return . PP.white

empty, dot, defEq, doubleColon, implies, bar, arrow, langle, rangle, comma :: (MonadTCM tcm) => tcm Doc

empty       = return PP.empty
dot         = return PP.dot
defEq       = return PP.defEq
doubleColon = return PP.doubleColon
implies     = return PP.implies
bar         = return PP.bar
arrow       = return PP.arrow
langle      = return PP.langle
rangle      = return PP.rangle
comma       = return PP.comma
text :: (MonadTCM tcm) => String -> tcm Doc
text s	    = return $ PP.text s
sep, fsep, hsep, hcat, vcat :: (MonadTCM tcm) => [tcm Doc] -> tcm Doc
sep ds	    = PP.sep <$> sequence ds
fsep ds     = PP.sep <$> sequence ds
hsep ds     = PP.hsep <$> sequence ds
hcat ds     = PP.hcat <$> sequence ds
vcat ds     = PP.vcat <$> sequence ds
($$), ($+$), (<>), (<+>) :: (MonadTCM tcm) => tcm Doc -> tcm Doc -> tcm Doc
d1 $$ d2    = (PP.$$) <$> d1 <*> d2
d1 $+$ d2   = (PP.</>) <$> d1 <*> d2
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
  prettyTCM :: (MonadTCM tcm) => a -> tcm Doc
  prettyDecTCM :: (MonadTCM tcm) => Int -> a -> tcm Doc

  prettyTCM = prettyDecTCM 0
  prettyDecTCM = const prettyTCM

printTCM :: (MonadTCM tcm) => tcm Doc -> tcm ()
printTCM d = do d' <- d
                liftIO $ putStr $ PP.displayS (PP.renderPretty 0.4 100 d') ""

printTCMLn :: (MonadTCM tcm) => tcm Doc -> tcm ()
printTCMLn d = printTCM (d <> (return PP.line))

instance PrettyTCM Int where
  prettyTCM = int

instance PrettyTCM Integer where
  prettyTCM = return . PP.integer

instance PrettyTCM I.StageVar where
  prettyTCM = return . PP.text . show

instance PrettyTCM Range where
  prettyTCM = return . PP.pretty

instance PrettyTCM a => PrettyTCM (Maybe a) where
  prettyTCM (Just x) = prettyTCM x
  prettyTCM Nothing = empty

instance (PrettyTCM a, PrettyTCM b) => PrettyTCM (a,b) where
  prettyTCM (x,y) = parens $ prettyTCM x <> comma <+> prettyTCM y

instance (PrettyTCM a, PrettyTCM b, PrettyTCM c) => PrettyTCM (a,b,c) where
  prettyTCM (x,y,z) = parens $ prettyTCM x <> comma <+> prettyTCM y <> comma <+> prettyTCM z

-- instance (Reify a b, PP.Pretty b) => PrettyTCM a where
--   prettyTCM x = reify x >>= return . PP.pretty

instance PrettyTCM Bind where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM Term where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM Context where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM SinglePattern where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM ConstrType where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM FixTerm where prettyTCM b = reify b >>= return . PP.pretty
instance PrettyTCM (Named Global) where prettyTCM b = reify b >>= return . PP.pretty



instance PrettyTCM A.Expr where prettyTCM b = AC.concretize b >>= return . PP.pretty
instance PrettyTCM A.Context where prettyTCM b = AC.concretize b >>= return . PP.pretty
instance PrettyTCM A.IndicesSpec where prettyTCM b = AC.concretize b >>= return . PP.pretty
instance PrettyTCM A.SinglePattern where prettyTCM b = AC.concretize b >>= return . PP.pretty

instance PrettyTCM Name where
  prettyTCM = return . PP.pretty

instance PrettyTCM TCEnv where
  prettyTCM env = do ds <- ppEnv env
                     return $ PP.sep (PP.punctuate PP.comma ds)
    where
      ppEnv EnvEmpty = return []
      ppEnv (es :< e) = do ds <- ppEnv es
                           d <- local (const es) $ prettyTCM e
                           return (ds ++ [d])

instance PrettyTCM a => PrettyTCM [a] where
  prettyTCM = brackets . hcat . punctuate (text ", ") . map prettyTCM

instance PrettyTCM LocalScope where
  prettyTCM = prettyTCM . envToList

-- instance PrettyTCM (Named (Maybe I.Term)) where
--   prettyTCM x = hsep [ prettyTCM (nameTag x)
--                      , defEq
--                      , prettyTCM (namedValue x) ]


-- instance (AC.ToConcrete a b, PP.Pretty b) => PrettyTCM a where
--   prettyTCM e = AC.concretize e >>= return . PP.pretty


instance PrettyTCM C.Expr where
  prettyTCM = return . PP.pretty

instance PrettyTCM Sort where
  prettyTCM = return . PP.pretty

instance PrettyTCM C.Declaration where
  prettyTCM = return . PP.pretty

-- instance PrettyTCM I.Goal where
--   prettyTCM g =
--     vcat [ prettyTCM (goalEnv g)
--          , text "-------------------------"
--          , local (const (goalEnv g)) $ prettyTCM (goalType g)]

instance PrettyTCM InductiveKind where
  prettyTCM = text . show

instance PrettyTCM StageNode where
  prettyTCM = text . show
