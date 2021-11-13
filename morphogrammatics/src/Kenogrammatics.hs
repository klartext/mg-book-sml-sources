module Kenogrammatics (
    Kenogram
  , KenogramSequence
  , EN (..)
  , ENstruc
  , ENrule
  , tnf
  , dnf
  , pnf
  , teq
  , deq
  , peq
  , asList
  , asKeno
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
  , dtConcrete
  , pairstructure
  , enStructure
  , teq'
  , enToKs
  , ag
  , ee
  , combinea
  , tConcat
  , dConcat
  , pConcat
  , eCard
  , nn
  , kligate
) where
import Data.List ( elemIndex, nub )

{--
  This module contains the implementation of chapter 3 "Kenogrammatik"
--}

type Kenogram = Int
newtype KenogramSequence = KS [Kenogram] deriving (Eq, Ord, Show)

-- instance Show KenogramSequence where
--   show (KS xs) =
--     let xs' = map toKenoSymbol xs
--      in show xs'
--     where toKenoSymbol i = "ABCDEFGHIJKLMNOPQRSTUVWXXYZ" !! (i-1)
  

asList :: KenogramSequence -> [Kenogram]
asList (KS l) = l

asKeno :: [Int] -> KenogramSequence
asKeno = tnf

pos :: Int -> [a] -> a
pos n list = list !! (n-1)

remove :: Eq a => a -> [a] -> [a]
remove item = filter (/= item)

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
    KS $ tnf1 ks [] 1 1


dnf :: Ord a => [a] -> KenogramSequence
dnf ks =
  let
    count x []= 0
    count x (y:ys)= (if x==y then 1 else 0)+count x ys
  in
    KS $
      concatMap
        (\ k -> replicate (count k (asList (tnf ks))) k)
        (nub (asList (tnf ks)))


pnf :: Ord a => [a] -> KenogramSequence
pnf ks = KS $
  replicate (length ks - length(nub ks)) 1 ++ asList(tnf(nub ks))


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

sumOver :: (Num p) => Int -> Int -> (Int -> p) -> p
sumOver from to fun =
  if from > to then 0
  else fun from + sumOver (from + 1) to fun

p :: (Int, Int) -> Int
p (n, k)
  | k == 1 = 1
  | k >  n = 0
  | k == n = 1
  | otherwise = p(n-1,k-1) + p(n-k,k);

dCard :: Int -> Int
dCard n = sumOver 1 n (\k -> p(n,k))

s :: (Int, Int) -> Int
s (n, k)
  | k == 1 = 1
  | k >  n = 0
  | k == n = 1
  | otherwise = s(n-1,k-1) + k*s(n-1,k)

tCard :: Int -> Int
tCard n = sumOver 1 n (\k -> s(n,k))


pContexture :: Int -> [KenogramSequence]
pContexture n =
  map (\k -> KS $ replicate (n-k) 1 ++ [1..k])
      [1..n]


combine :: a -> [[a]] -> [[a]]
combine a = map (a :)

allperms :: Eq t => [t] -> [[t]]
allperms []=[]
allperms [x]=[[x]]
allperms [x,y]=[[x,y],[y,x]]
allperms l = concatMap (\a -> combine a (allperms (removeFirst a l))) l
  where removeFirst x [] = []
        removeFirst x (y:ys) = if x == y then ys else y:removeFirst x ys

allsums :: Int -> Int -> [[Int]]
allsums n 1 = [[n]]
allsums n k =
  if n==k then [replicate n 1]
  else concatMap (\e -> combine e (allsums (n-e) (k-1))) [1..(n-k+1)]

allpartitions :: Int -> Int -> [[Int]]
allpartitions n k=
  let
    remdups [] = []
    remdups (hd:tl) =
      if any (`elem` tl) (allperms hd)
        then remdups tl
        else hd:remdups tl
  in
   remdups (allsums n k)


pdConcrete :: Eq a => [a] -> [[Int]]
pdConcrete ks =
   map (\p -> concatMap (\k -> replicate (pos k p) k)
                         [1.. length (nub ks)])
       (allpartitions (length ks) (length (nub ks)))

dContexture :: Int -> [KenogramSequence]
dContexture n = map KS (concatMap (pdConcrete . asList) (pContexture n))


dtConcrete :: Ord a => [a] -> [KenogramSequence]
dtConcrete ks = nub(map tnf (allperms ks))

tContexture :: Int -> [KenogramSequence]
tContexture n = concatMap (dtConcrete . asList) (dContexture n)

{--
  Epsilon / Nu Structure
--}
data EN = E|N deriving (Show, Eq)

delta :: Eq a => (Int, Int) -> [a] -> (Int, Int, EN)
delta (i,j) z =
   if pos i z == pos j z
     then (i,j,E)
     else (i,j,N);

type ENrule  = (Int, Int, EN)
type ENstruc = [[ENrule]]

-- | pairstructure n generates all possible pairs for a sequence of length n
pairstructure :: (Num a, Enum a) => a -> [[(a, a)]]
pairstructure n =
   map (\j -> map (\i -> (i,j)) [1..(j-1)])
       [1..n]

enStructure :: Eq a => [a] -> ENstruc
enStructure z =
   map (map (`delta` z))
       (pairstructure (length z))


teq' :: (Eq a1, Eq a2) => [a1] -> [a2] -> Bool
teq' a b = enStructure a == enStructure b


replace :: Eq a => a -> [a] -> a -> [a]
replace item [] w      = []
replace item (hd:tl) w =
        if hd==item then w:replace item tl w
        else hd:replace item tl w;


kmax :: (Ord a, Foldable t) => [t a] -> a
kmax l = maximum (map maximum l)


enToKs :: ENstruc -> KenogramSequence
enToKs enstruc =
  let
    entoks1 [] ks = ks
    entoks1 ((f,s,en):tl) ks =
      let
        fir = pos f ks
        sec = if length ks < s then [] else pos s ks
      in
        if en==E && null sec
          then entoks1 tl (ks ++ [fir])
          else if en==E && head fir `elem` sec
            then entoks1 tl (replace sec ks fir)
            else if en==E && notElem (head fir) sec
              then error "can not find identical element"
              else if en==N && null sec
                then entoks1 tl (ks++[remove (head fir) [1..kmax ks+1] ])
                else if en==N && fir==sec
                  then error "an element must always be identical to itself"
                  else if en==N && head fir `elem` sec
                    then entoks1 tl (replace sec ks (remove (head fir) sec))
                    else entoks1 tl ks
  in
    tnf (concat (entoks1 (concat enstruc) [[1]]))

-- concatenation of kenogram sequence
ag :: [Int] -> Int
ag = length . nub

ee :: (Int, Int) -> [[Int]]
ee (n,k) =
  let
    combinec item list = map (item :) list;

    mkfg from to 0    = [[]]
    mkfg from to step =
          concatMap (\i -> combinec i (mkfg (i+1) to (step-1)))
                    [from .. (max from to)]
  in
    mkfg  1 (n+1) k



mappat :: [Int] -> [Int] -> [Int]
mappat pat template=
   map (`pos` template) pat;

mkpats :: [Int] -> [Int] -> [[Int]]
mkpats a b =
  let
    free n [] = []
    free n (hd:tl) =
          if hd<=n then hd:free n tl
          else []
    possperms [] ag   = []
    possperms [x] ag  = [[x]]
    possperms rest ag =
          concatMap (\k -> combine k (possperms (remove k rest) (max k ag)))
                    (free (ag+1) rest )
  in
    concatMap (\e -> possperms e (ag a))
          (ee (ag a, ag b))


combinea :: [a] -> [[a]] -> [[a]]
combinea item = map (item ++)

tConcat :: KenogramSequence -> KenogramSequence -> [KenogramSequence]
tConcat (KS ks1) (KS ks2) =
   map tnf 
       (combinea ks1 (map (mappat ks2)
                          (mkpats ks1 ks2)))

dConcat :: KenogramSequence -> KenogramSequence -> [KenogramSequence]
dConcat a b = nub $ map (dnf . asList) (tConcat a b)

pConcat :: KenogramSequence -> KenogramSequence -> [KenogramSequence]
pConcat a b = nub $ map (pnf . asList) (tConcat a b)


eCard :: (Int, Int) -> Int
eCard (n,k) =
  let
   xi from to 0    = 1
   xi from to step =
         sumOver from to (\i -> xi (i+1) (max to (i+1)) (step-1))
  in
   xi 1 (n+1) k


nn :: ([Int], [Int]) -> Int
nn (a,b) =
  let
    m   = ee (ag a,ag b)
    e i = pos i m
    gn []     = 0
    gn (x:xs) = if x>ag a+1 then 1+gn xs else gn xs
  in
    sumOver 1 (eCard(ag a,ag b))
            (\i -> factorial (length (e i)) `div` factorial (1+gn(e i)) )

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)


collfits :: Eq a => [a] -> [[a]] -> ENrule -> [[a]]
collfits a [] rule = []
collfits a (b:bs) rule @(x,y,en)
  | en == E && pos x a == pos y b = b:collfits a bs rule
  | en == N && pos x a /= pos y b = b:collfits a bs rule
  | otherwise                     =   collfits a bs rule


mapvermat :: Eq a => [a] -> [[a]] -> [ENrule] -> [[a]]
mapvermat a bs []      = bs
mapvermat a [] enstruc = []
mapvermat a bs (rule:rules) = mapvermat a (collfits a bs rule) rules

kligate :: KenogramSequence -> KenogramSequence -> [ENrule] -> [KenogramSequence]
kligate (KS a) (KS b) enstruc =
  map tnf 
      (combinea a
        (mapvermat a
          (map (mappat b)
              (mkpats a b))
          enstruc))


