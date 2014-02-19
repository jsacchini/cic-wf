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

module CICminus.Syntax.Colors where

import CICminus.Utils.Pretty


-- keywordColor :: Doc -> Doc
-- keywordColor = setSGRCode [ SetConsoleIntensity BoldIntensity
--                             , SetColor Foreground Vivid White ]

-- coinductiveColor :: String
-- coinductiveColor = setSGRCode [ SetConsoleIntensity NormalIntensity
--                               , SetColor Foreground Vivid Green ]

-- constructorColor :: String
-- constructorColor = setSGRCode [ SetConsoleIntensity NormalIntensity
--                               , SetColor Foreground Vivid Magenta ]

-- localColor :: String
-- localColor = reset

-- globalColor :: String
-- globalColor = setSGRCode [ SetConsoleIntensity NormalIntensity
--                          , SetColor Foreground Vivid Cyan ]

-- annotationColor :: String
-- annotationColor = setSGRCode [ SetConsoleIntensity BoldIntensity
--                              , SetColor Foreground Vivid Red ]

-- sortColor :: String
-- sortColor = setSGRCode [ SetConsoleIntensity BoldIntensity
--                        , SetColor Foreground Vivid Yellow ]



-- reset :: String
-- reset = setSGRCode [ Reset ]

colored :: String -> String -> String
-- colored color xs = reset ++ color ++ xs ++ reset
colored _ xs = xs

colorize :: String -> Doc -> Doc
-- colorize color d = text color <> d <> text reset
colorize _ d = d
