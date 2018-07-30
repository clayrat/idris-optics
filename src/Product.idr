module Product

import Data.Profunctor
import Data.Profunctor.Lens

%default total

-- 1.1 tuples

_first : Lensing p => p a c -> p (a, b) (c, b)
_first = lens getter setter
  where
  getter = fst
  setter (_, kept) new = (new, kept)

_first' : Lensing p => Lens {p} (a, x) (b, x) a b
_first' = _first    

-- can't infer b
testView : view {b=()} Product._first' ("one",1) = "one"
testView = Refl

testSet : set Product._first' "harangue" ("one",1) = ("harangue", 1)
testSet = Refl

testOver : over Product._first' Strings.toUpper ("one", 1) = ("ONE", 1)
testOver = Refl

testOverP : over Product._first' Strings.length ("one", 1) = (3, 1)
testOverP = Refl

test2 : set Lens._2 "no-longer-an-Int" ("one",1) = ("one", "no-longer-an-Int")
test2 = Refl

-- 1.2 records

record Event where
  constructor MkEvent
  subject : String
  object : String
  action : String
  count : Nat

Show Event where
  show (MkEvent s o a c) = "{ action: " ++ a ++ ", count " ++ show c ++ ", object : " ++ o ++ ", subject : " ++ s ++ " }"

duringNetflix : Event
duringNetflix = MkEvent "Brian" "Dawn" "cafune" 0

_action : Lensing p => Lens' {p} Event String
_action = lens getter setter
  where
  getter = action
  setter whole new = record { action = new } whole

_count : Lensing p => Lens' {p} Event Nat
_count = lens count (\w,n => record { count = n } w)

testAction : view Product._action Product.duringNetflix = "cafune"  
testAction = Refl

testOverA : over Product._action Strings.toUpper Product.duringNetflix = Product.MkEvent "Brian" "Dawn" "CAFUNE" 0
testOverA = Refl

testSetC : set Product._count 999 Product.duringNetflix = Product.MkEvent "Brian" "Dawn" "cafune" 999
testSetC = Refl

-- won't work as easily, needs polymorphic records
--over _action String.length duringNetflix

-- 1.3 composing

both : (String, Event)
both = ("example", duringNetflix)

_bothCount : Lensing p => Lens' {p} (String, Event) Nat
_bothCount = _2 . _count

testBoth : view Product._bothCount Product.both = 0
testBoth = Refl

testBoth2 : view Product._bothCount $ set Product._bothCount 55 $ Product.both = 55
testBoth2 = Refl

-- 1.4 compose ex

_object : Lensing p => Lens' {p} Event String
_object = lens object (\w,n => record { object = n } w)

stringified : (String, String)
stringified = over _2 show both

bothObj : (String, String)
bothObj = set _2 (view (_2 . _object) both) both

-- 1.6 compose 2 ex

fourLong : (Int, Int, Int, Int)
fourLong = (1, 2, 3, 4)

get1 : (a, x) -> a
get1 = fst

get2 : (x, a, y) -> a
get2 = fst . snd

get3 : (x, y, a, z) -> a
get3 = Basics.fst . snd . snd

set1 : (a, x) -> b -> (b, x)
set1 (a,x) b = (b,x)

set2 : (x, a, y) -> b -> (x, b, y)
set2 (x,t) b = (x,set1 t b)

set3 : (x, y, a, z) -> b -> (x, y, b, z)
set3 (x,t) b = (x,set2 t b)

_elt1 : Lensing p => Lens {p} (f, r) (n, r) f n
_elt1 = lens get1 set1

_elt2 : Lensing p => Lens {p} (p1, f, r) (p1, n, r) f n
_elt2 = lens get2 set2

_elt3 : Lensing p => Lens {p} (p1, p2, f, r) (p1, p2, n, r) f n
_elt3 = lens get3 set3

testElt : over Product._elt3 (* 60000) Product.fourLong = (1, 2, 180000, 4)
testElt = Refl

-- 1.7 laws

setGet : (l1 : Lens {p=Forgotten a} t t a b) -> (l2 : Lens {p=Arr} s t a b) -> (x : b) -> (y : s) -> view l1 (set l2 x y) = x
