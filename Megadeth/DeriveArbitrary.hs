{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Megadeth.DeriveArbitrary where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Test.QuickCheck
import Control.Monad
import Control.Arrow
import Control.Applicative
import Data.List

import Megadeth.Prim

-- | Build the arbitrary function.
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
-- do
--  a1 <- arbitrary
--  a2 <- arbitrary
--  ....
--  return $ (a1,a2,...)
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
                [d| instance Arbitrary $(applyTo (conT t) ns) where
                               arbitrary = sized go --(arbitrary :: Gen Int) >>= go
                                 where go n | n <= 1 = oneof $(listE (makeArbs t fcs))
                                            | otherwise = oneof ( ($(listE (makeArbs t fcs)))++ $(listE (makeArbs t scons))) |]
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
        TyConI (TySynD _ params ty) ->
            case (getTy ty) of
                (TupleT n) -> do
                        let ns = map varT $ paramNames params 
                        if (length ns > 0 ) then
                           [d| instance $(applyTo (tupleT (length ns)) (map (appT (conT ''Arbitrary)) ns))
                                        => Arbitrary $(applyTo (conT t) ns) where
                                          arbitrary = $(genTupleArbs n) |]
                        else -- Don't think we could ever enter here
                            fail "Tuple without arguments"
                (ConT n) -> return [] -- This type should had been derived already,
                                        -- It its a clearly dependency and it
                                        -- should be put before in the topsort.
                pepe -> do
                     runIO $ print "IGNORING"
                     runIO $ print ty
                     return []
        d -> do
          if (isPrim inf) then return [] else
            (fail $ "Case not defined: " ++ show d)

-- | Automatic recursive arbitrary derivation, DEPRECATED?
deriveArbitraryRec :: Name -> Q [Dec]
deriveArbitraryRec t = do
  d <- reify t
  case d of
       TyConI (DataD _ _ _ constructors _) -> do
          let innerTypes = nub $ concat [ findLeafTypes ty | (simpleConView t -> SimpleCon _ 0 tys) <- constructors, ty <- tys, not (isVarT ty) ]
          runIO $ print innerTypes
          decs <- fmap concat $ forM innerTypes $ \ty ->
            do 
               tincho <- reify $ headOf ty
               if (isPrim tincho) then return [] 
               else do 
                       q <- isInstance ''Arbitrary [ty]
                       if not q
                         then do runIO $ putStrLn ("recursively deriving Arbitrary instance for " ++ show (headOf ty))
                                 deriveArbitraryRec (headOf ty)
                         else return []
          d <- deriveArbitrary t
          return (decs ++ d)
       e -> do
            runIO $ print $ "+++++++++++" ++ show e
            return []

isArbInsName = isinsName ''Arbitrary

devArbitrary :: Name -> Q [Dec]
devArbitrary = megaderive deriveArbitrary (\_-> return False) isArbInsName 
-- TODO: add debugging flag, or remove all those prints.
{-
   devArbitrary :: Name -> Q [Dec]
   devArbitrary t = do
           ts' <- prevDev t
           runIO $ print $ "Topologically sorted types" ++ show ts'
           ts'' <- filterM isArbInsName ts'
           runIO $ print $ "We should derive in this order ---" ++ show ts''
           ts <- mapM (\t -> (runIO $ print $ show t) >> deriveArbitrary t) ts'' -- Notice here, we call
           -- deriveArbitrary directly, because we are fully confident we can
           -- derive all the types in that order.
           return $ concat ts
-}
