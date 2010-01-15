{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts 
  #-}

module Typing where

import "mtl" Control.Monad.Error hiding (lift)
import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import Environment
import Internal
import qualified Term as T
import Parser

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

-- Type checking

data TCErr 
    = Undefined
    | NotConvertible Term Term
    | NotFunction Term
    | NotSort Term
    | InvalidProductRule Term Term
    deriving(Show)

instance Error TCErr where
    noMsg = Undefined

-- type Result a = Either TCErr a -- result of type checking and type inference

newtype MonadTCM m a = MonadTCM { rrr :: ErrorT TCErr m a } -- result of type checking and type inference
                       deriving(Monad, MonadError TCErr) 
type Result = MonadTCM Identity

instance (Show a) => Show (Identity a) where
    show (Identity x) = show x

instance (Show a, Show b) => Show (ErrorT a Identity b) where
    show (ErrorT (Identity (Left e))) = "Error: " ++ show e
    show (ErrorT (Identity (Right t))) = show t

instance (Show a) => Show (Result a) where
    show (MonadTCM x) = show x

--    show (Res (ErrorT (Identity (Left e)))) = "Error: " ++ show e
--    show (Res (ErrorT (Identity (Right t)))) = show t

conversion :: GEnv -> Term -> Term -> Result ()
conversion g t1 t2 = unless (norm g t1 == norm g t2) $
		     throwError $ NotConvertible t1 t2

checkSort :: T.Sort -> Result Term
checkSort T.Star = return (TSort Box)
checkSort T.Box = return (TSort Box)

isSort :: Term -> Result ()
isSort (TSort _) = return ()
isSort t = throwError $ NotSort t

checkProd :: Term -> Term -> Result Term
checkProd (TSort s1) (TSort Box) = return $ TSort Box
checkProd (TSort s1) (TSort Star) = return $ TSort Star
checkProd t1 t2 = throwError $ InvalidProductRule t1 t2

-- We assume that in the global environment, types are normalized

infer :: GEnv -> LEnv -> T.Expr -> Result Term
infer g l (T.Ann _ t u) = let clu = interp u in
	                    do check g l t clu
                               return clu
infer g l (T.TSort _ s) = checkSort s
infer g l (T.Pi _ x t1 t2) = do r1 <- infer g l t1
                                isSort r1
                                r2 <- infer g ((x,r1):l) t2
                                isSort r2
                                checkProd r1 r2
infer g l (T.Bound _ n) = return $ lift (n+1) 0 $ snd $ l !! n
infer g l (T.Free _ x) = case genvGet g x of
                           Def _ t -> return t
                           Axiom t -> return t
infer g l (T.Lam _ x t u) = do r1 <- infer g l t
                               isSort r1
                               r2 <- infer g ((x,interp t):l) u
                               -- s <- infer g l (Pi t r2)
                               -- isSort s
                               return $ Pi x (interp t) r2
infer g l (T.App _ t1 t2) = do r1 <- infer g l t1
                               r2 <- infer g l t2
                               case r1 of
                                   Pi _ u1 u2 -> do conversion g r2 u1
                                                    return $ subst (interp t2) u2
                                   otherwise -> throwError $ NotFunction r2

mapp :: Term -> [Term] -> Term
mapp = foldl App

-- mpi :: Term -> NamedCxt -> Term
-- mpi = foldr $ uncurry $ Pi

if_ :: Monad m => Bool -> m () -> m ()
if_ True t = t
if_ False _ = return ()

check :: GEnv -> LEnv -> T.Expr -> Term -> Result ()
check g l t u = do r <- infer g l t
                   conversion g r u

lcheck :: GEnv -> LEnv -> [T.Expr] -> [Term] -> Result ()
lcheck _ _ [] [] = return ()
lcheck g l (t:ts) (u:us) = do check g l t u
			      lcheck g l ts (mapsubst 0 (interp t) us)
