module Util

import Data.SortedMap
import Data.SortedSet

%default total
%access public export

(Show k, Show v) => Show (SortedMap k v) where
    show m = "[" ++ (unwords $ intersperse "," $ map {b=String} (\(k,v) => "(" ++ show k ++ "->" ++ show v ++ ")") $ SortedMap.toList m) ++ "]"
 
 Show v => Show (SortedSet v) where
    show s = show $ SortedSet.toList s

snoc : List a -> a -> List a 
snoc xs x = xs ++ [x]
