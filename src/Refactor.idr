module Refactor

import Data.SortedMap
import Data.Profunctor
import Data.Profunctor.Lens
import Data.Profunctor.Lens.At
import Util

%default total
%access public export

Id : Type
Id = Int

Tags : Type
Tags = List String

record Animal where
  constructor MkAnimal
  id : Id
  name : String
  tags : Tags

Show Animal where
  show (MkAnimal i n t) = show i ++ ":" ++ n ++ "(" ++ unwords t ++ ")"

_tags : Lensing p => Lens' {p} Animal Tags
_tags = lens tags (\w,n => record { tags = n } w)

named : String -> Id -> Animal
named name id = MkAnimal id name []

clearTags : Animal -> Animal
clearTags = set _tags []

-- Note: let's make it the UI's job to disallow duplicate tags.
addTag : String -> Animal -> Animal
addTag tag = over _tags (flip snoc tag)

-- MODEL

record Model where
  constructor MkModel
  animals : SortedMap Id Animal

Show Model where
  show (MkModel m) = "model: " ++ show m

_animals : Lensing p => Lens' {p} Model (SortedMap Id Animal) 
_animals = lens animals (\w,n => record { animals = n } w)

_oneAnimal : (Wander p, Lensing p) => Id -> Lens' {p} Model (Maybe Animal)
_oneAnimal id = _animals . at id 

initialModel : Model
initialModel = MkModel $ SortedMap.fromList [(Animal.id startingAnimal, startingAnimal)]
  where
  startingAnimal = addTag "mare" $ named "Genesis" 3838

addAnimalTag : Id -> String -> Model -> Model
addAnimalTag id tag = over (_oneAnimal id) (map (addTag tag))

addAnimal : Id -> String -> Model -> Model
addAnimal id name = set (_oneAnimal id) (Just $ named name id)

data Action = AddAnimal Id String | AddTag Id String

update : Model -> Action -> Model
update model (AddAnimal animalId name) = addAnimal animalId name model
update model (AddTag animalId tag) = addAnimalTag animalId tag model 
