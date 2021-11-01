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

tnf :: (Eq a, Ord a) => [a] -> KenogramSequence
tnf ks =
  let
    pos n list = list !! (n-1)

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
allperms l =
  concatMap (\a -> combine a (allperms (filter (/= a) l))) l


-- fun allsums n 1=[[n]]
--    |allsums n k= 
--      if (n=k) then [nlistof n 1]
--      else 
--        flat(map (fn e => combine e (allsums (n-e) (k-1)))
--                 (nlist (n-k+1)));               

-- fun allpartitions n k=
--   let
--     fun Exists f [] = false
--        |Exists f (hd::tl)= 
--           if (f hd) then true
--           else Exists f tl;
--     fun remdups [] = []
--        |remdups (hd::tl)=
--           if Exists (fn x => (member x tl)) (allperms hd)
--             then remdups tl
--             else hd::(remdups tl);
--   in
--    remdups (allsums n k)
--   end;

-- fun PDconcrete ks =
--    map (fn p => flat (map (fn k => nlistof (pos k p) k)
--                          (nlist (length (rd ks)))))
--        (allpartitions (length ks) (length (rd ks)));

-- fun Dcontexture n =
--    flat(map PDconcrete (Pcontexture n));


-- fun DTconcrete ks =
--    rd(map (fn i => tnf i)
--           (allperms ks));

-- fun Tcontexture n=
--    flat(map DTconcrete (Dcontexture n));