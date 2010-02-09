module Syntax.Global where

import Syntax.Internal 
import Syntax.ETag

data Global
    = Def Type Term
    | IndDef NamedCxt NamedCxt Sort -- [Constr]
    | Axiom Type
    deriving(Show)

instance Show Syntax.ETag.NM where
    show = const ""

class (Monad m) => MonadGE m where
    lookupGE :: Name -> m (Maybe Global)

