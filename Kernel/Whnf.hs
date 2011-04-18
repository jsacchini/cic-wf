{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances,
  CPP #-}

module Kernel.Whnf where

#include "../undefined.h"
import Utils.Impossible

import Syntax.Internal
import Kernel.TCM

whnf :: (MonadTCM tcm) => Term -> tcm Term
whnf t@(App f ts) =
  do w <- whnf f
     case w of
       Lam bs u -> whnf $ applyTerms bs u ts
       u        -> return $ App u ts
whnf t@(Var x) =
  do d <- getGlobal x
     case d of
       Definition _ u   -> return u
       Assumption _     -> return t
       _                -> __IMPOSSIBLE__
whnf t = return t

class NormalForm a where
  normalForm :: (MonadTCM tcm) => a -> tcm a

  normalForm = error "Default impl of NormalForm. COMPLETE!"

instance NormalForm Bind where
  normalForm (Bind x t) = do t' <- normalForm t
                             return $ Bind x t'
  normalForm (LocalDef x t1 t2) = do t1' <- normalForm t1
                                     t2' <- normalForm t2
                                     return $ LocalDef x t1' t2'

instance NormalForm Term where
  normalForm t@(Sort _) = return t
  normalForm (Pi bs t) = do bs' <- mapM normalForm bs
                            t' <- normalForm t
                            return $ Pi bs' t'
  normalForm t@(Bound _) = return t
  normalForm t@(Var x) = do u <- getGlobal x
                            case u of
                              Definition _ t' -> normalForm  t'
                              Assumption _    -> return t
  normalForm (Lam bs t) = do bs' <- mapM normalForm bs
                             t' <- normalForm t
                             return $ Lam bs' t'
  normalForm (App t1 ts) = do t1' <- normalForm t1
                              case t1' of
                                Lam bs u -> normalForm $ applyTerms bs u ts
                                App u1 us -> do ts' <- mapM normalForm ts
                                                return $ App u1 (us ++ ts')
                                Bound _ -> do ts' <- mapM normalForm ts
                                              return $ App t1' ts'
                                Var _  -> do ts' <- mapM normalForm ts
                                             return $ App t1' ts'
                                otherwise -> __IMPOSSIBLE__

