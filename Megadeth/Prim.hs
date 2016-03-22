{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Megadeth.Prim where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Control.Monad
import Control.Arrow
import Control.Applicative
import Data.List

--import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Graph as G
import qualified Data.Map.Strict as M
import Control.Monad.Trans.State.Lazy
import qualified Control.Monad.Trans.Class as TC

-- | View Pattern for Types
data ConView = SimpleCon {nm :: Name, bf :: Integer, tt :: [Type]}

-- | Count 'how many times' a type is recursive to himself.
-- Used to make an arbitrary instance that reduce the size more accurate
countCons :: (Name -> Bool) -> Type -> Integer
countCons p ty =
  case ty of
    ForallT _ _ t  -> countCons p t
    AppT ty1 ty2   -> countCons p ty1 + countCons p ty2
    SigT t _       -> countCons p t
    ConT t         -> if p t then 1 else 0
    _              -> 0

varNames = map (('a':) . show) [0..]

paramNames :: [TyVarBndr] -> [Name]
paramNames = map f
  where f (PlainTV n) = n
        f (KindedTV n _) = n

applyTo :: TypeQ -> [TypeQ] -> TypeQ
applyTo c ns =
  foldl (\h pn -> appT h pn) c ns

fixAppl :: Exp -> Exp
fixAppl (UInfixE e1@(UInfixE {}) op e2) = UInfixE (fixAppl e1) op e2
fixAppl (UInfixE con op e) = UInfixE con (VarE '(<$>)) e
fixAppl e = AppE (VarE 'return) e
                                          
-- | Look up  the first type name in a type structure.
headOf :: Type -> Name
headOf (AppT ListT ty) = headOf ty
headOf (AppT (TupleT _) ty) = headOf ty 
headOf (AppT ty1 _) = headOf ty1
headOf (SigT ty _) = headOf ty
headOf (ConT n) = n
headOf (VarT n) = n

-- | Check whether a type is a Primitive Type.
-- Something like Int#, Bool#, etc.
isPrim :: Info -> Bool
isPrim (PrimTyConI _ _ _ ) = True
isPrim _ = False

-- | View Pattern for Constructors
simpleConView :: Name -> Con -> ConView
simpleConView tyName c =
  let count = sum . map (countCons (== tyName))
  in case c of
  NormalC n sts -> let ts = map snd sts
                   in SimpleCon n (count ts) ts
  RecC n vsts   -> let ts = map proj3 vsts
                       proj3 (_,_,z) = z
                   in SimpleCon n (count ts) ts
  InfixC (_,t1) n (_,t2) ->
    SimpleCon n (countCons (== tyName) t1 + countCons (== tyName) t2) [t1,t2]
  ForallC _ _ innerCon -> simpleConView tyName innerCon
                                              

-- | Get the first type in a type application.
-- Maybe we should improve this one
getTy :: Type -> Type
getTy (AppT t _) = getTy t
getTy t = t

isVarT (VarT _) = True
isVarT _ = False

-- | Find all simple Types that are part of another Type.
findLeafTypes :: Type -> [Type]
findLeafTypes (AppT ListT ty) = findLeafTypes ty
findLeafTypes (AppT (TupleT n) ty) = findLeafTypes ty
findLeafTypes (AppT p@(ConT _) ty) = p : findLeafTypes ty
findLeafTypes (AppT ty1 ty2) = findLeafTypes ty1 ++ findLeafTypes ty2
findLeafTypes (VarT _) = []
findLeafTypes (ForallT _ _ ty) = findLeafTypes ty 
findLeafTypes ArrowT = []
findLeafTypes ListT = []
findLeafTypes StarT = []
findLeafTypes ty = [ty]

type StQ s a = StateT s Q a
type Names = [Name]

member :: Name -> StQ (M.Map Name Names) Bool
member t = do
    mk <- get
    return $ M.member t mk

addDep :: Name -> Names -> StQ (M.Map Name Names) ()
addDep n ns = do
    mapp <- get
    let newmapp = M.insert n ns mapp
    put newmapp

headOfNoVar :: Type -> [Name]
headOfNoVar (ConT n) = [n]
headOfNoVar (VarT _) = []
headOfNoVar (SigT t _ ) = headOfNoVar t
headOfNoVar (AppT ty1 ty2) = headOfNoVar ty1 ++ headOfNoVar ty2
headOfNoVar _ = []

getDeps :: Name -> StQ (M.Map Name Names) ()
getDeps t = do
  visited <- member t
  if (visited || hasArbIns t) then return ()
  else do
              TC.lift $ runIO $ print $ "PreVisiting:" ++ show t
              tip <- TC.lift $ reify t
              TC.lift $ runIO $ print $ "Visiting: " ++ show tip
              case tip of
                TyConI (DataD _ _ _ constructors _) -> do
                      let innerTypes = nub $ concat [ findLeafTypes ty | (simpleConView t -> SimpleCon _ _ tys) <- constructors, ty <- tys, not (isVarT ty) ]
                      let hof = map headOf innerTypes
                      addDep t hof
                      mapM_ getDeps hof
                TyConI (NewtypeD _ nm _ constructor _) -> do 
                      let (SimpleCon _ 0 ts )= simpleConView nm constructor
                      let innerTypes = nub $ concat $ map findLeafTypes $ filter (not . isVarT) ts
                      let hof = map headOf innerTypes
                      addDep t hof
                      mapM_ getDeps hof
                TyConI (TySynD _ _ m) -> do
                    addDep t (headOfNoVar m)
                    mapM_ getDeps (headOfNoVar m) 
                d -> 
                    if (isPrim tip) then return () else return ()


tocheck :: [TyVarBndr] -> Name -> Type
tocheck bndrs nm =
    let ns = map VarT $ paramNames bndrs in foldl (\r a -> AppT r a) (ConT nm) ns

hasArbIns :: Name -> Bool
--hasArbIns n = isPrefixOf "GHC." (show n) || isPrefixOf "Data.Vector" (show n) || isPrefixOf "Data.Text" (show n) || isPrefixOf "Codec.Picture.Types" (show n) || isPrefixOf "Data.ByteString" (show n) || isPrefixOf "Data.Map" (show n) 
hasArbIns n = isPrefixOf "GHC." (show n) || isPrefixOf "Data." (show n) || isPrefixOf "Codec.Picture.Types" (show n)

isinsName :: Name -> Name -> Q Bool
isinsName className n = do
        inf <- reify n
        case inf of
            TyConI (DataD _ _ preq _ _) -> 
                        if length preq > 0 then
                                (isInstance className [tocheck preq n]) >>= (return . not)
                        else
                                (isInstance className [(ConT n)]) >>= (return . not)
            TyConI (NewtypeD _ _ preq _ _) -> 
                        if length preq > 0 then
                                (isInstance className [tocheck preq n]) >>= (return . not)
                        else
                                (isInstance className [(ConT n)]) >>= (return . not)
            TyConI (TySynD _ preq _ ) -> 
                        if length preq > 0 then
                                (isInstance className [tocheck preq n]) >>= (return . not)
                        else
                                (isInstance className [(ConT n)]) >>= (return . not)
            d -> do
                runIO $ print $ "Weird case:: " ++ show d
                isInstance className [(ConT n)] >>= (return . not)

prevDev :: Name -> Q [Name]
prevDev t = do
        mapp <- execStateT (getDeps t) M.empty 
        let rs = M.foldrWithKey (\ k d ds -> (k,k,d) : ds) [] mapp
        let (graph, v2ter, f) = G.graphFromEdges rs
        let topsorted = reverse $ G.topSort graph
        return (map (\p -> (let (n,_,_) = v2ter p in n)) topsorted)
