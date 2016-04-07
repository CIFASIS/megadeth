{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Megadeth.DeriveShow where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Megadeth.Prim
import Data.DeriveTH
import Data.Derive.Show

isArbInsName = isinsName ''Show

devShow :: Name -> Q [Dec]
devShow = megaderive (derive makeShow) (\_-> return False) isArbInsName 

