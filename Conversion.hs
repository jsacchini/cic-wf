{-# LANGUAGE PackageImports #-}

module Conversion where

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.State
import Environment
import Internal
import TCM

-- Normal forms (values) and neutral terms (atomic normal terms)

data Ne
    = NFree Name
    | NBound Int
    | NApp Ne Value
    deriving(Show, Eq)

data Value
    = VSort Sort
    | VLam Value Value
    | VPi Value Value
    | VNe Ne
--    | VConstr Name [Value] [Value]
    deriving(Show, Eq)
        
vfree :: Name -> Value
vfree = VNe . NFree

vbound :: Int -> Value
vbound = VNe . NBound


valterm :: Value -> Term
valterm (VSort s) = TSort s
valterm (VLam t v) = Lam "" (valterm t) (valterm v)
valterm (VPi v1 v2) = Pi "" (valterm v1) (valterm v2)
-- valterm (VConstr x ps as) = Constr x (map valterm ps) (map valterm as)
valterm (VNe v) = neterm v
                  where neterm (NFree x) = Free x
                        neterm (NBound n) = Bound n
                        neterm (NApp n v) = App (neterm n) (valterm v)



-- norm takes the global environment and a term to normalize
norm :: (MonadTCM tcm) => Term -> tcm Value
norm (TSort s) = return $ VSort s
norm (Pi _ t1 t2) = do u1 <- norm t1
                       u2 <- norm t2
                       return $ VPi u1 u2
norm (Bound n) = return $ vbound n
norm (Free x) = do t <- lookupGlobal x 
                   case t of
                     Def _ t -> norm t
                     Axiom _ -> return $ vfree x
norm (Lam _ t u) = do t1 <- norm t
                      u1 <- norm u
                      return $ VLam t1 u1
norm (App t1 t2) = do u1 <- norm t1
                      case u1 of 
                        VLam t v -> norm $ subst t2 (valterm v)
                        VNe n -> do u2 <- norm t2
                                    return $ VNe (NApp n u2)
                        otherwise -> internalError "algo"

conversion :: (MonadTCM tcm) => Term -> Term -> tcm ()
conversion t1 t2 = do v1 <- norm t1
                      v2 <- norm t2
                      unless (v1 == v2) $ typeError $ NotConvertible t1 t2

