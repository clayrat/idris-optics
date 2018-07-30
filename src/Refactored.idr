module Refactored

import Data.SortedMap
import Data.Profunctor
import Data.Profunctor.Lens
import Data.Profunctor.Lens.At
import Util

%default total
%access public export

Id : Type
Id = Int

Ids : Type
Ids = List Id

Tags : Type
Tags = List String

record Animal where
  constructor MkAnimal
  id : Id
  name : String

Show Animal where
  show (MkAnimal i n) = show i ++ ":" ++ n

named : String -> Id -> Animal
named name id = MkAnimal id name

-- TAG DB (many2many)

record TagDb where
  constructor MkTagDb
  tagsById : SortedMap Id Tags
  idsByTag : SortedMap String Ids

Show TagDb where  
  show (MkTagDb tbi ibt) = "<" ++ show tbi ++ " x " ++ show ibt ++ ">"

empty : TagDb
empty = MkTagDb empty empty

_tagsById : Lensing p => Lens' {p} TagDb (SortedMap Id Tags)
_tagsById = lens tagsById (\w,n => record { tagsById = n } w)

_idsByTag : Lensing p => Lens' {p} TagDb (SortedMap String Ids)
_idsByTag = lens idsByTag (\w,n => record { idsByTag = n } w)

_idTags : (Wander p, Lensing p) => Id -> Lens' {p} TagDb (Maybe (List String))
_idTags id = _tagsById . at id

_tagIds : (Wander p, Lensing p) => String -> Lens' {p} TagDb (Maybe (List Id))
_tagIds tag = _idsByTag . at tag

appendOrCreate : {f : Type -> Type} -> Monoid (f a) => a -> (a -> f a) -> Maybe (f a) -> Maybe (f a)
appendOrCreate new wrap mfa = Just $ fromMaybe neutral mfa <+> wrap new

addTagTo : Id -> String -> TagDb -> TagDb
addTagTo id tag = over (_idTags id) $ appendOrCreate tag (\x => [x])

addIdTo : String -> Id -> TagDb -> TagDb
addIdTo tag id = over (_tagIds tag) $ appendOrCreate id (\x => [x])

addTag : Id -> String -> TagDb -> TagDb
addTag id tag = addIdTo tag id . addTagTo id tag

tagsFor : Id -> TagDb -> Tags
tagsFor id = fromMaybe [] . view (_idTags id)

idsFor : String -> TagDb -> Ids
idsFor name = fromMaybe [] . view (_tagIds name)

-- MODEL

record Model where
  constructor MkModel
  animals : SortedMap Id Animal
  tagDb : TagDb

Show Model where
  show (MkModel m t) = "model: " ++ show m ++ "|" ++ show t

_animals : Lensing p => Lens' {p} Model (SortedMap Id Animal) 
_animals = lens animals (\w,n => record { animals = n } w)

_oneAnimal : (Wander p, Lensing p) => Id -> Lens' {p} Model (Maybe Animal)
_oneAnimal id = _animals . at id 

_tagDb : Lensing p => Lens' {p} Model TagDb
_tagDb = lens tagDb (\w,n => record { tagDb = n } w)

initialModel : Model
initialModel = MkModel (SortedMap.fromList [(Animal.id startingAnimal, startingAnimal)]) (addTag (Animal.id startingAnimal) "mare" empty)
  where
  startingAnimal = named "Genesis" 3838

addAnimalTag : Id -> String -> Model -> Model
addAnimalTag id tag = over _tagDb $ addTag id tag

addAnimal : Id -> String -> Model -> Model
addAnimal id name = set (_oneAnimal id) (Just $ named name id)

data Action = AddAnimal Id String | AddTag Id String

update : Model -> Action -> Model
update model (AddAnimal animalId name) = addAnimal animalId name model
update model (AddTag animalId tag) = addAnimalTag animalId tag model 
