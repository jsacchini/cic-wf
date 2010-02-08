{-# LANGUAGE PackageImports, UndecidableInstances, MultiParamTypeClasses,
  FunctionalDependencies, FlexibleInstances, GeneralizedNewtypeDeriving
  #-}

module Utils.MonadUndo (
        UndoT(..), evalUndoT, execUndoT, runUndoT, mapUndoT,
--        Undo, evalUndo, execUndo,
        MonadUndo, undo, redo, history, checkpoint, noUndo, oneStep,
        History, current, undos, redos,
        module Control.Monad.State
    ) where
import Prelude hiding (catch)
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Identity

import System.Console.Haskeline
 
data History s = History { current :: s, undos :: [s], redos :: [s] }
    deriving (Eq, Show, Read)
 
blankHistory :: s -> History s
blankHistory s = History { current = s, undos = [], redos = [] }
 
newtype Monad m => UndoT s m a = UndoT (StateT (History s) m a)
    deriving (Functor, Monad, MonadTrans, MonadIO)
 
class (MonadState s m) => MonadUndo s m | m -> s where
    undo :: m Bool -- undo the last state change, returns whether successful
    redo :: m Bool -- redo the last undo
    history :: m (History s) -- gets the current undo/redo history
    checkpoint :: m () -- kill the history, leaving only the current state
    noUndo :: m a -> m a -- executes an action, without recording in the history
    oneStep :: m a -> m a -- executes an action, removing intermediate states from the history

instance (MonadReader r m) => MonadReader r (UndoT s m) where
    ask = lift ask
    local f (UndoT m) = UndoT $ local f m

instance (MonadException m) => MonadException (UndoT s m) where
    catch (UndoT f) h = UndoT $ StateT $ \ur -> runStateT f ur `catch` \e -> let UndoT h' = h e in runStateT h' ur
    block = mapUndoT block
    unblock = mapUndoT unblock

instance (Monad m) => MonadState s (UndoT s m) where
    get = UndoT $ do
            ur <- get
            return (current ur)
    put x = UndoT $ do
              ur <- get
              put (History { current = x, undos = current ur : undos ur,
                             redos = [] })
 
instance (Monad m) => MonadUndo s (UndoT s m) where
    undo = UndoT $ do
        ur <- get
        case undos ur of
            []     -> return False
            (u:us) -> do put (History { current = u, undos = us,
                                        redos = current ur : redos ur })
                         return True
    redo = UndoT $ do
        ur <- get
        case redos ur of
            []     -> return False
            (r:rs) -> do put (History { current = r, undos = current ur : undos ur,
                                        redos = rs })
                         return True
    history = UndoT get
    checkpoint = UndoT $ do
        s <- liftM current get
        put $ blankHistory s
    noUndo (UndoT x) = UndoT $ do old <- get
                                  a <- x
                                  new <- get
                                  put (History { current = current new, undos = undos old,
                                                 redos = [] })
                                  return a
    oneStep (UndoT x) = UndoT $ do old <- get
                                   a <- x
                                   new <- get
                                   put (History { current = current new, undos = current old : undos old,
                                                  redos = [] })
                                   return a

evalUndoT :: (Monad m) => UndoT s m a -> s -> m a
evalUndoT (UndoT x) = evalStateT x . blankHistory

execUndoT :: (Monad m) => UndoT s m a -> s -> m s
execUndoT (UndoT x) = liftM current . execStateT x . blankHistory

runUndoT :: (Monad m) => UndoT s m a -> s -> m (a, History s)
runUndoT (UndoT x) = runStateT x . blankHistory

mapUndoT :: (Monad m, Monad n) => (m (a, History s) -> n (b, History s)) -> UndoT s m a -> UndoT s n b
mapUndoT f (UndoT x) = UndoT $ mapStateT f x

-- newtype Undo s a = Undo (UndoT s Identity a)
--     deriving (Functor, Monad, MonadState s, MonadUndo s)
 
-- evalUndo (Undo x) = runIdentity . evalUndoT x
-- execUndo (Undo x) = runIdentity . execUndoT x
