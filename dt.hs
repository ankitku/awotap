import Data.Function

data F x = Empty | Cons x (F x)

instance Functor F where
  fmap f Empty = Empty
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)
