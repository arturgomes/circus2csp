{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Gensym where

import Control.Monad.State

import qualified Language.Haskell.Exts as Hsx (Name(..), QName(..))
import qualified Importer.Isa as Isa (Name(..))


newtype GensymM a = GensymM (State Int a)
  deriving (Applicative, Monad, Functor, MonadFix, MonadState Int)

gensym :: String -> GensymM String
gensym prefix = do count <- get
                   put (count + 1)
                   return (prefix ++ show count)

genHsName :: Hsx.Name -> GensymM Hsx.Name
genHsName (Hsx.Ident  prefix) = liftM Hsx.Ident  (gensym prefix)
genHsName (Hsx.Symbol prefix) = liftM Hsx.Symbol (gensym prefix)

genHsQName :: Hsx.QName -> GensymM Hsx.QName
genHsQName (Hsx.Qual m prefix)  = liftM (Hsx.Qual m) (genHsName prefix)
genHsQName (Hsx.UnQual prefix)  = liftM Hsx.UnQual   (genHsName prefix)
genHsQName junk = error ("junk = " ++ show junk)

genIsaName :: Isa.Name -> GensymM Isa.Name
genIsaName (Isa.QName t prefix) = liftM (Isa.QName t) (gensym prefix)
genIsaName (Isa.Name prefix)    = liftM Isa.Name      (gensym prefix)

evalGensym :: Int -> GensymM a -> a
evalGensym init (GensymM state) = evalState state init

runGensym :: Int -> GensymM a -> (a, Int)
runGensym init (GensymM state)  = runState state init
