module Kenogrammatics (
    Kenogram
  , KenogramSequence
  , tnf
  , dnf
  , pnf
  , teq
  , deq
  , peq
  , asList
  , tRef
  , dRef
  , pRef
  , pCard
  , dCard
  , tCard
  , p
  , s
  , pContexture
  , allperms
  , allsums
  , allpartitions
  , dContexture
  , tContexture
  , rd
  , dtConcrete

) where
import Data.List ( elemIndex )

type Kenogram = Int
newtype KenogramSequence = KenoSequence [Kenogram] deriving (Eq, Ord)

instance Show KenogramSequence where
  show (KenoSequence xs) =
    let xs' = map toKenoSymbol xs
     in show xs'
    where toKenoSymbol i = "ABCDEFGHIJKLMNOPQRSTUVWXXYZ" !! (i-1)

asList :: KenogramSequence -> [Kenogram]
asList (KenoSequence l) = l

pos :: Int -> [a] -> a
pos n list = list !! (n-1)

tnf :: (Eq a, Ord a) => [a] -> KenogramSequence
tnf ks =
  let
    firstocc item list = case elemIndex item list of
      Nothing    -> error "did not find element"
      Just index -> index + 1

    tnf1 [] res n k = res
    tnf1 (hd:tl) res 1 k = tnf1 tl [1] 2 2
    tnf1 (hd:tl) res n k =
      if pos n ks `elem` take (n-1) ks
        then tnf1 tl (res ++ [pos (firstocc (pos n ks) ks) res])(n+1) k
        else tnf1 tl (res ++ [k]) (n+1) (k+1);
  in
    KenoSequence $ tnf1 ks [] 1 1


rd :: Eq a => [a] -> [a]
rd []=[]
rd [x]=[x]
rd (x:xs) = x:rd(filter (/= x) xs);

dnf :: Ord a => [a] -> KenogramSequence
dnf ks =
  let
    count x []= 0
    count x (y:ys)= (if x==y then 1 else 0)+count x ys
  in
    KenoSequence $
      concatMap
        (\ k -> replicate (count k (asList (tnf ks))) k)
        (rd (asList (tnf ks)))


pnf :: Ord a => [a] -> KenogramSequence
pnf ks = KenoSequence $
  replicate (length ks - length(rd ks)) 1 ++ asList(tnf(rd ks))


teq :: (Ord a, Ord b) => [a] -> [b] -> Bool
teq a b = tnf a == tnf b

deq :: (Ord a, Ord b) => [a] -> [b] -> Bool
deq a b = dnf a == dnf b

peq :: (Ord a, Ord b) => [a] -> [b] -> Bool
peq a b = pnf a == pnf b;



tRef :: KenogramSequence -> KenogramSequence
tRef = tnf . reverse . asList

dRef :: KenogramSequence -> KenogramSequence
dRef = dnf . asList . tRef

pRef :: KenogramSequence -> KenogramSequence
pRef = pnf . asList . tRef


pCard :: p -> p
pCard n = n

sumWith :: (Ord t, Num p, Num t) => t -> t -> (t -> p) -> p
sumWith from to f =
  if from > to then 0
  else f from + sumWith (from + 1) to f

p (n, k)
  | k == 1 = 1
  | k >  n = 0
  | k == n = 1
  | otherwise = p(n-1,k-1) + p(n-k,k);

dCard n = sumWith 1 n (\k -> p(n,k))

s (n, k)
  | k == 1 = 1
  | k >  n = 0
  | k == n = 1
  | otherwise = s(n-1,k-1) + k*s(n-1,k)

tCard n = sumWith 1 n (\k -> s(n,k))


pContexture n =
   map (\k -> KenoSequence $ replicate (n-k) 1 ++ [1..k])
       [1..n]


combine a = map (a :)

allperms []=[]
allperms [x]=[[x]]
allperms [x,y]=[[x,y],[y,x]]
allperms l = concatMap (\a -> combine a (allperms (removeFirst a l))) l
  where removeFirst x [] = []
        removeFirst x (y:ys) = if x == y then ys else y:removeFirst x ys

allsums n 1 = [[n]]
allsums n k =
  if n==k then [replicate n 1]
  else concatMap (\e -> combine e (allsums (n-e) (k-1))) [1..(n-k+1)]

allpartitions n k=
  let
    remdups [] = []
    remdups (hd:tl) =
      if any (`elem` tl) (allperms hd)
        then remdups tl
        else hd:remdups tl
  in
   remdups (allsums n k)


pdConcrete ks =
   map (\p -> concatMap (\k -> replicate (pos k p) k)
                         [1.. length (rd ks)])
       (allpartitions (length ks) (length (rd ks)))

dContexture :: Int -> [KenogramSequence]
dContexture n = map KenoSequence (concatMap (pdConcrete . asList) (pContexture n))


dtConcrete :: Ord a => [a] -> [KenogramSequence]
dtConcrete ks = rd(map tnf (allperms ks))

tContexture :: Int -> [KenogramSequence]
tContexture n = concatMap (dtConcrete . asList) (dContexture n)