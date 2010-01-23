{-# LANGUAGE PackageImports #-}

module Conversion where

import "mtl" Control.Monad.Error
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
norm :: GEnv -> Term -> Value
norm g (TSort s) = VSort s
norm g (Pi _ t1 t2) = VPi (norm g t1) (norm g t2)
norm g (Bound n) = vbound n
norm g (Free x) = case genvGet g x of
                    Def _ t -> norm g t
                    Axiom _ -> vfree x
norm g (Lam _ t u) = VLam (norm g t) (norm g u)
norm g (App t1 t2) = case norm g t1 of
                       VLam t v -> norm g $ subst t2 (valterm v)
                       VNe n -> VNe (NApp n (norm g t2))
                       otherwise -> error "type error"

norme = norm $ MkGE []

conversion :: GEnv -> Term -> Term -> Result ()
conversion g t1 t2 = unless (norm g t1 == norm g t2) $
		     throwError $ NotConvertible t1 t2

