module SMCDEL.Internal.Help (
  alleq,alleqWith,anydiff,anydiffWith,alldiff,
  apply,applyPartial,(!),(!=),
  powerset,restrict,rtc,tc,Erel,bl,fusion,seteq,subseteq,lfp
  ) where
import Data.List (nub,union,sort,foldl',(\\))

type Rel a b = [(a,b)]
type Erel a = [[a]]

alleq  :: Eq a => [a] -> Bool
alleq = alleqWith id

alleqWith :: Eq b => (a -> b) -> [a] -> Bool
alleqWith _ [] = True
alleqWith f (x:xs) = all (f x ==) (map f xs)

anydiff :: Eq a => [a] -> Bool
anydiff = anydiffWith id

anydiffWith :: Eq b => (a -> b) -> [a] -> Bool
anydiffWith _ [] = False
anydiffWith f (x:xs) = any (f x /=) (map f xs)

alldiff :: Eq a => [a] -> Bool
alldiff [] = True
alldiff (x:xs) = notElem x xs && alldiff xs

apply :: Show a => Show b => Eq a => Rel a b -> a -> b
apply rel left = case lookup left rel of
  Nothing -> error ("apply: Relation " ++ show rel ++ " not defined at " ++ show left)
  (Just this) -> this

(!) :: Show a => Show b => Eq a => Rel a b -> a -> b
(!) = apply

applyPartial :: Eq a => [(a,a)] -> a -> a
applyPartial rel left = case lookup left rel of
  Nothing     -> left
  (Just this) -> this

(!=) :: Eq a => [(a,a)] -> a -> a
(!=) = applyPartial

powerset :: [a] -> [[a]]
powerset []     = [[]]
powerset (x:xs) = map (x:) pxs ++ pxs where pxs = powerset xs

concatRel :: Eq a => Rel a a -> Rel a a -> Rel a a
concatRel r s = nub [ (x,z) | (x,y) <- r, (w,z) <- s, y == w ]

lfp :: Eq a => (a -> a) -> a -> a
lfp f x | x == f x  = x
        | otherwise = lfp f (f x)

dom :: Eq a => Rel a a -> [a]
dom r = nub (foldr (\ (x,y) -> ([x,y]++)) [] r)

restrict :: Ord a => [a] -> Erel a -> Erel a
restrict domain =  nub . filter (/= []) . map (filter (`elem` domain))

rtc :: Eq a => Rel a a -> Rel a a
rtc r = lfp (\ s -> s `union` concatRel r s) [(x,x) | x <- dom r ]

tc :: Eq a => Rel a a -> Rel a a
tc r = lfp (\ s -> s `union` concatRel r s) r

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
  EQ -> x : merge xs ys
  LT -> x : merge xs (y:ys)
  GT -> y : merge (x:xs) ys

mergeL :: Ord a => [[a]] -> [a]
mergeL = foldl' merge []

overlap :: Ord a => [a] -> [a] -> Bool
overlap [] _  = False
overlap _  [] = False
overlap (x:xs) (y:ys) = case compare x y of
  EQ -> True
  LT -> overlap xs (y:ys)
  GT -> overlap (x:xs) ys

bl :: Eq a => Erel a -> a -> [a]
bl r x = head (filter (elem x) r)

fusion :: Ord a => [[a]] -> Erel a
fusion [] = []
fusion (b:bs) = let
    cs = filter (overlap b) bs
    xs = mergeL (b:cs)
    ds = filter (overlap xs) bs
  in if cs == ds then xs : fusion (bs \\ cs) else fusion (xs : bs)

seteq :: Ord a => [a] -> [a] -> Bool
seteq as bs = sort as == sort bs

subseteq :: Eq a => [a] -> [a] -> Bool
subseteq xs ys = all (`elem` ys) xs
