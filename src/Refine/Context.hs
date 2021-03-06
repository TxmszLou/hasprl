{-# LANGUAGE FlexibleInstances #-}
module Refine.Context where

import Compute.TermDeBruijn

{- the refinement context/environment for when working with judgments -}

class (Eq a,Show a) => Telescope a where
  empty :: a
  isEmpty :: a -> Bool
  get :: Int -> a -> Maybe Tm
  extend :: Int -> Tm -> a -> a
  -- linearize :: a -> [(Int, String)]
  liftCtxt :: Int -> Int -> a -> a

-- typing context
type LCtxt = [Tm]

instance Telescope LCtxt where
  empty = []
  isEmpty = null
  get n tel
    | n < len = Just $ tel !! (len - n - 1)
    | otherwise            = Nothing
      where len = length tel
  liftCtxt c k = map (\x -> lift x c k)
  extend _ e ctxt = e : ctxt

-- environment
type LEnv = [(Int, Tm)]

instance Telescope LEnv where
  empty = []
  isEmpty = null
  get n = foldl (\acc (x,e) -> if n == x then Just e else acc) Nothing
  -- insert in front (i.e. backwards from the normal paper convention)
  liftCtxt c k = map (\(x,e) -> (x, lift e c k))
  extend x e ctxt = (x,e) : ctxt
