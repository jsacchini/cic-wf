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
import Data.Functor
import Data.List

import qualified Text.PrettyPrint as PP

import qualified Syntax.Abstract as A
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope
import Syntax.Internal

import qualified Utils.Pretty as MP

import qualified Kernel.Constraints as CS
import Kernel.TCM
import Kernel.PrettyTCM
import Kernel.TypeChecking
import Syntax.InternaltoAbstract

import TopLevel.Monad
import TopLevel.TopLevel


main :: IO ()
-- main = runTop mainLoop
main = evalFile

evalFile =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     mapM_ runFile args
    where runFile f =
            do h <- openFile f ReadMode
               ss <- hGetContents h
               case parse fileParser ss of
                 ParseOk ts ->
                   do putStrLn $ PP.render $ MP.prettyPrint ts
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
               csStage <- stConstraints <$> get
               csType <- stTypeConstraints <$> get
               traceTCM 40 $ vcat (text "Universe constraints:"
                                   : map (\(x,y,k) -> hsep [prettyPrintTCM x,
                                                            if k == 0 then text "<=" else text "<",
                                                            prettyPrintTCM y
                                                           ]) (CS.toList csType))
               traceTCM 40 $ case find (\x -> CS.findNegCycle x csType /= []) (map (\(x,_,_)->x) (CS.toList csType)) of
                              Just x -> hsep [text "Cycle:", prettyPrintTCM (CS.findNegCycle x csType)]
                              Nothing -> text "No cycle"
