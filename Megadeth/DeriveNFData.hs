{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns#-}
{-# LANGUAGE FlexibleInstances,UndecidableInstances#-}
module Megadeth.DeriveNFData where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Megadeth.Prim

import Control.DeepSeq

as :: [Name]
as = map (\x -> mkName $ 'a':show x) ([1..] :: [Int])

rnfC :: Name -> [Name] -> ExpQ
rnfC c [] = conE '() 
rnfC c vars = foldr (\ n r -> appE (appE (varE 'seq) (varE n)) r) (conE '()) vars

deriveNF :: Name -> Q [Dec]
deriveNF name = do
    info <- reify name 
    case info of
        TyConI (DataD _ _ params cons _) -> do
            let fnm = mkName $ "rnf"
            let f = funD fnm $ foldl ( \ p c ->
                    let
                        SimpleCon n rec vs = simpleConView name c
                        vars = take (length vs) as
                        vp = map varP vars
                    in
                     (clause [conP n vp] (normalB $ rnfC n vars) []) 
                    : p) [] cons 
            let ns = map varT $ paramNames params
            if not $ null ns then
                        instanceD (cxt $ (map (appT (conT ''NFData)) ns))
                                (appT (conT ''NFData) (applyTo (conT name) ns))
                                [f] 
                        >>= \x -> return [x]
            else
                        instanceD (cxt []) [t| NFData $(applyTo (conT name) ns) |] [f]
                        >>= \x -> return [x]

devNFData :: Name -> Q [Dec]
devNFData = derive deriveNF (isinsName ''NFData)
