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
chooseExpQ :: Name -> Integer -> Type -> ExpQ
chooseExpQ t bf (AppT ListT ty) = appE ( varE (mkName "listOf")) (appE (appE (varE (mkName "resize")) ([| ($(varE (mkName "n")) `div` 10) |])) (varE 'arbitrary))
chooseExpQ t bf ty | headOf ty /= t = appE (appE (varE (mkName "resize")) ([|$(varE (mkName "n"))|])) (varE 'arbitrary)
chooseExpQ t bf ty =
  case bf of
    0  -> varE 'arbitrary
    1  -> appE (varE (mkName "go")) [| ($(varE (mkName "n")) - 1) |]
    bf -> appE (varE (mkName "go")) [| ($(varE (mkName "n")) `div` bf) |]


makeArbs t xs = map (fmap fixAppl) [ foldl (\h ty -> uInfixE h (varE '(<*>)) (chooseExpQ t bf ty)) (conE name) tys' | SimpleCon name bf tys' <- xs]

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
              if not $ null ns then
               [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                            => Arbitrary $(applyTo (conT t) ns) where
                              arbitrary = sized go --(arbitrary :: Gen Int) >>= go
                                where go n | n <= 1 = oneof $(listE (makeArbs t fcs))
                                           | otherwise = oneof ( ($(listE (makeArbs t fcs))) ++ $(listE (makeArbs t scons))) |]
               else
                let reccall = if (length ns > 1)
                                then [|  oneof ( ($(listE (makeArbs t fcs)))++ $(listE (makeArbs t scons))) |]
                                else [| oneof $(listE (makeArbs t scons))|] in
                [d| instance Arbitrary $(applyTo (conT t) ns) where
                               arbitrary = sized go --(arbitrary :: Gen Int) >>= go
                                 where go n | n <= 1 = oneof $(listE (makeArbs t fcs))
                                            | otherwise = $(reccall) |]
        TyConI (NewtypeD _ _ params con _) -> do
            let ns = map varT $ paramNames params
                scon = simpleConView t con
            if length ns > 0 then
               [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                            => Arbitrary $(applyTo (conT t) ns) where
                              arbitrary = sized go --(arbitrary :: Gen Int) >>= go
                                where go n | n <= 1 = oneof $(listE (makeArbs t [scon]))
                                           | otherwise = oneof ($(listE (makeArbs t [scon]))) |]
               else
                [d| instance Arbitrary $(applyTo (conT t) ns) where
                               arbitrary = sized go --(arbitrary :: Gen Int) >>= go
                                where go n | n <= 1 = oneof $(listE (makeArbs t [scon]))
                                           | otherwise = oneof ($(listE (makeArbs t [scon]))) |]
        TyConI inp@(TySynD _ params ty) ->
            case (getTy ty) of
                (TupleT n) -> 
                        let ns = map varT $ paramNames params in
                        if (length ns > 0 ) then
                           [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                                        => Arbitrary $(applyTo (conT t) ns) where
                                          arbitrary = $(genTupleArbs n) |]
                        else -- Don't think we could ever enter here
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
