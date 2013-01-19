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

module Main where

import Prelude hiding (catch)

import System.IO

import System.Environment

import Control.Monad.Trans
import Control.Monad.State

import qualified Syntax.Abstract as A
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope

import Utils.Pretty

import Kernel.TCM
import Kernel.TypeChecking
import Syntax.InternaltoAbstract

main :: IO ()
main =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     mapM_ runFile args
    where runFile f =
            do h <- openFile f ReadMode
               ss <- hGetContents h
               case parse fileParser ss of
                 ParseOk ts ->
                   do print $ prettyPrint ts
                      r <- runTCM $ typeCheckFile ts
                      case r of
                        Left err -> putStrLn $ "Error!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d = do d' <- scope d
                               gs <- inferDecl d'
                               forM_ gs (uncurry addGlobal)
          typeCheckFile :: [A.Declaration] -> TCM ()
          typeCheckFile ds =
            do forM_ ds typeCheckDecl
