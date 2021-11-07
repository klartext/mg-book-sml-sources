--{-# LANGUAGE FlexibleContexts #-}
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
  , (+++)
) where
import Data.List ( elemIndex, nub )

type Kenogram = Int
newtype KenogramSequence = KenoSequence [Kenogram] deriving (Eq, Ord, Show)

-- instance Show KenogramSequence where
--   show (KenoSequence xs) =
--     let xs' = map toKenoSymbol xs
--      in show xs'
--     where toKenoSymbol i = "ABCDEFGHIJKLMNOPQRSTUVWXXYZ" !! (i-1)

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

-- rd :: Eq a => [a] -> [a]
-- rd = nub

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

{--
Epsilon / Nu Structure
--}
data EN = E|N deriving (Show, Eq)

delta :: Eq a => (Int, Int) -> [a] -> (Int, Int, EN)
delta (i,j) z =
   if pos i z == pos j z
     then (i,j,E)
     else (i,j,N);

type ENstruc = [[(Int, Int, EN)]]

{-- pairstructure n erzeugt die Struktur der möglichen Paare
   für eine Sequenz der Länge n   
--}
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
         (if en==E && null sec
            then entoks1 tl (ks ++ [fir])
            else if en==E && head fir `elem` sec
              then entoks1 tl (replace sec ks fir)
              else if en==E && notElem (head fir) sec
                then error "can not find identical element"
                else if en==N && null sec
                  then entoks1 tl (ks++[filter (/= head fir) [1..kmax ks+1] ])
                  else if en==N && fir==sec
                    then error "an element must always be identical to itself"
                    else if en==N && head fir `elem` sec
                      then entoks1 tl (replace sec ks
                                      (filter (/= head fir) sec))
                      else entoks1 tl ks)
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
          concatMap (\k -> combine k (possperms (filter (/= k) rest) (max k ag)))
                    (free (ag+1) rest )
  in
    concatMap (\e -> possperms e (ag a))
          (ee (ag a, ag b))


combinea :: [a] -> [[a]] -> [[a]]
combinea item = map (item ++)

tConcat :: [Int] -> [Int] -> [[Int]]
tConcat ks1 ks2 =
   combinea ks1 (map (mappat ks2)
                     (mkpats ks1 ks2))


(+++) :: KenogramSequence -> KenogramSequence -> [KenogramSequence]
(KenoSequence ks1) +++ (KenoSequence ks2) = map KenoSequence $ tConcat ks1 ks2


dConcat :: [Int] -> [Int] -> [KenogramSequence]
dConcat a b = nub $ map dnf (tConcat a b)

pConcat :: [Int] -> [Int] -> [KenogramSequence]
pConcat a b = nub $ map pnf (tConcat a b)

{--}


eCard (n,k) =
  let
   xi from to 0    = 1
   xi from to step =
         sumWith from to (\i -> xi (i+1) (max to (i+1)) (step-1))
  in
   xi 1 (n+1) k


nn (a,b) =
  let
    m   = ee (ag a,ag b)
    e i = pos i m
    gn []     = 0
    gn (x:xs) = if x>ag a+1 then 1+gn xs else gn xs
  in
    sumWith 1 (eCard(ag a,ag b))
            (\i -> factorial (length (e i)) `div` factorial (1+gn(e i)) )

factorial 0 = 1
factorial n = n * factorial (n-1)



collfits a [] rule = []
collfits a (b:bs) rule @(x,y,en)
  | en == E && pos x a == pos y b = b:collfits a bs rule
  | en == N && pos x a /= pos y b = b:collfits a bs rule
  | otherwise                     =   collfits a bs rule;


mapvermat a bs []      = bs
mapvermat a [] enstruc = []
mapvermat a bs (rule:rules) = mapvermat a (collfits a bs rule) rules;

kligate a b enstruc =
   combinea a
            (mapvermat a
                       (map (mappat b)
                            (mkpats a b))
                       enstruc)


