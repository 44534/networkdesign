{-#LANGUAGE FlexibleInstances #-}
module Language where

import Data.Set as S
import Data.List as L

import GraphHelper (Edge, Tree (..) )

class PPrint a where
  pprint :: a -> String

instance Show a => PPrint (Edge a) where
  pprint e =
    let [u,v] = S.toList e
    in "{" ++ show u ++ "," ++ show v ++ "}"

instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x,y) = "(" ++ pprint x ++ "," ++ pprint y ++ ")"

instance (PPrint a, PPrint b, PPrint c) => PPrint (a,b,c) where
  pprint (x,y,z) = "(" ++ pprint x ++ "," ++ pprint y ++ "," ++ pprint z ++ ")"

instance (PPrint a) => PPrint [a] where
  pprint xs = "[ " ++ intercalate " , " (L.map pprint xs) ++ " ]"

prec = 8

instance PPrint Rational where
  pprint r =
    let sr = show $ fromRational r
        (pre, post) = span ('.' /= ) sr
        (p, end) = span ('e' /=) post
    in pre ++ L.take (prec+1) p ++ end

instance Show a => PPrint (Tree a) where
  pprint (Tree r []) = show r
  pprint (Tree r xs) = show r ++ " " ++ pprint xs

instance PPrint a => PPrint (Maybe a) where
  pprint Nothing = "Nothing"
  pprint (Just x) = pprint x
