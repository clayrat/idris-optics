module Map

import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Lens
import Data.Profunctor.Lens.At
import Util

%default total

_key : Lensing p => Lens' {p} (SortedMap String a) (Maybe a)
_key = lens getter setter
  where
  getter = lookup "key"
  setter whole (Just new) = insert "key" new whole
  setter whole Nothing = delete "key" whole

_atKey : Lensing p => k -> Lens' {p} (SortedMap k v) (Maybe v)
_atKey k = lens getter setter
  where
  getter = lookup k
  setter whole (Just new) = insert k new whole
  setter whole Nothing = delete k whole  

testAt : set (at "key") (Just 3) SortedMap.empty = insert "key" 3 SortedMap.empty
testAt = Refl

-- over (at "key") (map {b=Integer} negate) $ fromList[("key", 3)] = insert "key" (-3) SortedMap.empty

-- view (at {b=()} 1) $ SortedSet.fromList [1] = Just ()

-- set (at 'b') (Just ()) $ SortedSet.fromList ['a'] = SortedSet.fromList ['a', 'b']

composed : At p f Integer x => Lens' {p} ((a, f), b) (Maybe x)
composed = _1 . _2 . at 3

threeDeep : ((String, SortedMap Integer String), String)
threeDeep = (("one", SortedMap.fromList [(3, "match")]), "two")

-- view (composed {x=String}) threeDeep = Just "match"

-- over (composed {x=String}) (map toUpper) threeDeep = (("one", SortedMap.fromList [(3, "MATCH")]), "two")