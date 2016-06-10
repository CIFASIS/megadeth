{-# Language TemplateHaskell #-}
module Megadeth.DeriveArbitrary where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Test.QuickCheck
import Control.Monad
import Control.Arrow
import Control.Applicative
import Data.List

import Megadeth.Prim

import Data.DeriveTH
import Data.Derive.Show

-- | Build the arbitrary function with makeArbs
chooseExpQ :: Name -> Name -> Name -> Integer -> Type -> ExpQ
chooseExpQ g n t bf (AppT ListT ty) = [| listOf $ resize ($(varE  n) `div` 10) arbitrary |]
chooseExpQ g n t bf ty | headOf ty /= t = [| resize $(varE n) arbitrary |]
chooseExpQ g n t bf ty =
  case bf of
    0  -> [| arbitrary |] --varE 'arbitrary
    1  -> [| $(varE g) $ $(varE n) - 1 |]
--appE (varE (mkName "go")) [| () |]
    bf -> [| $(varE g) $ $(varE n) `div` bf |]
--appE (varE (mkName "go")) [|  |]


makeArbs :: Name -> Name -> Name ->  [ConView] -> [ExpQ]
makeArbs g n t xs = map (fmap fixAppl) [ foldl (\h ty -> uInfixE h (varE '(<*>)) (chooseExpQ g n t bf ty)) (conE name) tys' | SimpleCon name bf tys' <- xs]

-- | Generic function used to create arbitrarily large tuples
-- @
-- do
--  a1 <- arbitrary
--  a2 <- arbitrary
--  ....
--  return $ (a1,a2,...)
-- @
genTupleArbs :: Int -> ExpQ
genTupleArbs n = 
    let ys = take n varNames
        xs = map mkName ys
         in
        doE $
             map (\x -> bindS (varP x) (varE 'arbitrary)) xs
            ++ [ noBindS $ appE (varE 'return) (tupE (map varE xs))]


-- | Give an arbitrary instance for its argument.
-- It doesn't check anything, just assume that it is ok to instance
-- its argument. And define the function arbitrary depending what type its
-- argument references to.
deriveArbitrary :: Name -> Q [Dec]
deriveArbitrary t = do
    inf <- reify t
    runIO $ print $ "Deriving:" ++ show inf
    case inf of
        TyConI (DataD _ _ params constructors _) -> do
              let ns  = map varT $ paramNames params
                  scons = map (simpleConView t) constructors
                  fcs = filter ((==0) . bf) scons
                  gos g n = if length scons > 1
                          then
                                if length fcs > 1 
                                then
                                    [|  if $(varE n) <= 1
                                    then oneof $(listE (makeArbs g n t fcs))
                                    else oneof $(listE (makeArbs g n t scons))|]
                                else
                                    [|  if $(varE n) <= 1
                                    then $(head (makeArbs g n t fcs))
                                    else oneof $(listE (makeArbs g n t scons))|]
                          else
                                [| $(head (makeArbs g n t scons)) |]
              if not $ null ns then
               [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                            => Arbitrary $(applyTo (conT t) ns) where
                              arbitrary = sized go
                                where go n = $(gos 'go 'n) |]
               else
                [d| instance Arbitrary $(applyTo (conT t) ns) where
                               arbitrary = sized go
                                 where go n = $(gos 'go 'n)|]
        TyConI (NewtypeD _ _ params con _) -> do 
            let ns = map varT $ paramNames params
                scon = simpleConView t con
            if not $ null ns then
               [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                            => Arbitrary $(applyTo (conT t) ns) where
                              arbitrary = sized go 
                                where go n = $(head (makeArbs 'go 'n t [scon])) |]
               else
                [d| instance Arbitrary $(applyTo (conT t) ns) where
                               arbitrary = sized go
                                where go n = $(head (makeArbs 'go 'n t [scon])) |]
        TyConI inp@(TySynD _ params ty) ->
            case (getTy ty) of
                (TupleT n) -> 
                        let ns = map varT $ paramNames params in
                        if not $ null ns then
                           [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                                        => Arbitrary $(applyTo (conT t) ns) where
                                          arbitrary = $(genTupleArbs n) |]
                        else
                           [d| instance Arbitrary $(applyTo (conT t) ns) where
                                          arbitrary = $(genTupleArbs n) |]
                (ConT n) -> return [] -- This type should had been derived already,
                                        -- It is clearly a dependency and it
                                        -- should be put before in the topsort.
                _ -> do
                     runIO $ print "IGNORING"
                     runIO $ print ty
                     return [] 
        d -> do
          if (isPrim inf) then return [] else
            (fail $ "Case not defined: " ++ show d)

isArbInsName = isinsName ''Arbitrary

devArbitrary :: Name -> Q [Dec]
devArbitrary = megaderive deriveArbitrary (\_-> return False) isArbInsName 

devDeriveArbitrary :: Name -> Q [Dec]
devDeriveArbitrary = megaderive (derive makeArbitrary) (const $ return False) isArbInsName  
