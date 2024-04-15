module Types10 where

data List a = Wrap a | Cons a (List a)
  deriving (Ord, Eq, Show)
                       
fold :: (a -> b) -> (a -> b -> b) -> List a -> b
fold w c (Wrap a)     =  w a
fold w c (Cons a as)  =  c a (fold w c as)

instance Functor List where
  fmap f = fold (Wrap . f) (\ a bs -> Cons (f a)  bs)


class POrd a where
  leq :: a -> a -> Bool

instance (POrd a, POrd b) => POrd (a, b) where
  (a1, b1) `leq` (a2, b2) = a1 `leq` a2 && b1 `leq` b2
  
sumList  ::   List (Float, Int) -> (Float, Int)
sumList  =    fold id c
  where       c (x, n) (x', n') = (x + x', n + n')
  
maxList  ::   List (Float, Int) -> (Float, Int)
maxList  =    fold id c
  where       c (x, n) (x', n') = (max x x', max n n')  
                               
testList             ::   List (Float, Int)
testList             =    Cons   (1.3, 10)
                     (    Cons   (3.7, 5)
                     (    Cons   (2.1, 2)      
                     (    Wrap   (21.8, 15))))     
                          
  


