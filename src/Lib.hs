{-# LANGUAGE ExistentialQuantification, RankNTypes #-}

module Lib
  ( plus4Times100_slow
    , plus4Times100_fast
    , filter_div6_slow
    , filter_div6_fast
    , filter_div6_fast2
    , yfiltered_functor ) where

import Prelude hiding (map,Functor,fmap,filter,and,foldr)

-- MAPS --

-- Classic map for lists
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (a:as) = f a : map f as

-- Claim: map id = id  (wherever equality makes sense for "a")
-- Proof:
--
-- Case 1:
-- map id [] = []
--
-- Case 2:
-- map id (a:as)
-- = id a : map id as.
-- By induction on list length, map id as = as, so
-- = id a : as
-- = a : as

-- Claim: map g . map f = map (g . f)  (wherever equality makes sense for "c")
-- where f: a -> b, g: b -> c
-- Proof:
--
-- Case 1: (map g . map f) [] = map g (map f []) = map g [] = [] = map (g . f) []
--
-- Case 2: (map g . map f) (a:as)
-- = map g (map f (a:as))
-- = map g (f a : map f as)
-- = g (f a) : map g (map f as)
-- = (g . f) a : (map g . map f) as
-- = (g . f) a : map (g . f) as  (induction on length of list)
-- = map (g . f) (a:as)
--
-- Remark: the above proofs work for finite lists only, but observe that if this didn't work
-- for infinite lists then there would be some infinite list bs such that (map g . map f) bs != map (g.f) bs.
-- This would mean the results are different on some finite index, so the corresponding initial segments
-- of output would differ, but this is impossible since we just showed they agree on all finite initial segments.

-- Satisfying these two laws mean that lists are a Functor:
class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor [] where
  fmap = map

-- Functors are not just "mappables": to be a valid Functor instance, the candidate "map"
-- *must* satisfy the above two laws (that's where the power comes from).

-- Upshot: we can fuse two list traversals into a single traversal, because math!
-- ... but, we had to see "map g . map f" and know to reduce this to "map (g . f)" by hand.
-- Can we do better? Yes!

-- Now here's something weird:
data Yoneda f a = forall r. Yoneda { unYoneda :: (r -> a, f r) }

-- Read: Having the type [a] is the same as having the type [r] for some unknown type
-- r, together with a map from r -> a.
--
-- Having an fa is the same as having a pair (id,fa) because the identity gives us no more
-- information
liftYoneda :: f a -> Yoneda f a
liftYoneda fa = Yoneda (id, fa)

-- [] is a functor so we can lift the stored map f: r -> a to a function f r -> f a and apply it to f r
-- to get back our original f a
lowerYoneda :: Functor f => Yoneda f a -> f a
lowerYoneda (Yoneda (f,fr)) = fmap f fr

-- WHY DO WE CARE? THIS IS CRAZY!
-- We care because Yoneda f is a functor just like f is, but it fuses traversals for us!
instance Functor (Yoneda f) where
  fmap m (Yoneda (f,fr)) = Yoneda (m . f, fr)
-- Here, f goes to the composite m . f when we map, but *defers* the traversal until we lowerYoneda back
-- down to f a

-- Exercise: show that lowerYoneda . liftYoneda = id whenever equality makes sense for "f a"
-- Strictly speaking: liftYoneda . lowerYoneda = id is true for types that can be represented as sets.
-- We cannot really talk about equality on things of type (r -> a, f r) where r is arbitrary

-- Example of traversing twice
plus4Times100_slow :: [Int] -> [Int]
plus4Times100_slow = fmap (*100) . fmap (+4)

-- The same thing, but travering once, for free
plus4Times100_fast :: [Int] -> [Int]
plus4Times100_fast = lowerYoneda . fmap (*100) . fmap (+4) . liftYoneda


-- FILTERS --

-- Classic list filters
listFilter :: (a -> Bool) -> [a] -> [a]
listFilter p []     = []
listFilter p (a:as) = if p a then a:(listFilter p as) else listFilter p as
-- Claim: filter p . filter q = filter (\x -> (p x) && (q x))
-- Proof:
--
-- Case 1: (filter p . filter q) [] = filter p (filter q []) = filter p [] = [] = filter (\x -> p x && q x) []
--
-- Case 2: (filter p . filter q) (a:as)
-- = filter p (filter q (a:as))
-- = filter p (if q a then a : filter q as else filter q as)
-- = if q a then filter p (a : filter q as) else filter p (filter q as)
-- = if q a then (if p a then a : filter p (filter q as) else filter p (filter q as)) else filter p (filter q as)
-- = if (p a && q a) then a : filter p (filter q as) else filter p (filter q as)
-- = if (p a && q a) then a : filter (\x -> p a && q a) as else filter (\x -> p a && q a) as  (by induction)
-- = filter (\x -> p x && q x) (a:as)

-- Upshot: each filter usually costs a separate traversal, but we can fuse them into a single traversal!

-- Here's the class of structures that can be Filtered
class Filtered f where
  filter :: (a -> Bool) -> f a -> f a
-- Filter Laws:
-- 1. filter (\x -> True) = id
-- 2. filter p . filter q = filter (\x -> p x && q x)

-- Lists can be filtered
instance Filtered [] where
  filter = listFilter

-- Introduce a useful way of combining predicates
and :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p `and` q = \x -> p x && q x

-- Example of traversing twice to filter
filter_div6_slow :: Filtered f => f Int -> f Int
filter_div6_slow =
  let p = \x -> x `mod` 2 == 0
      q = \x -> x `mod` 3 == 0
  in
    filter p . filter q

-- Tweaking the same to traverse once to get the same result
filter_div6_fast :: Filtered f => f Int -> f Int
filter_div6_fast =
  let p = \x -> x `mod` 2 == 0
      q = \x -> x `mod` 3 == 0
  in
    filter (p `and` q)

-- We can play a similar game as above to get cheaper filtering:
data YFiltered f a = YFiltered { unFiltered :: (a -> Bool) -> f a }

-- YFiltered is Filtered by combining predicates using `and`. Running "filter" is constant-time here
instance Filtered (YFiltered f) where
  filter p1 (YFiltered pfa) = YFiltered (\p2 -> pfa (p1 `and` p2))
-- Filter Law 1: filter (\x -> True) = id
-- Proof:
-- filter (\x -> True) (YFiltered pfa)
-- = YFiltered (\p2 -> pfa ((\x -> True) `and` p2))
-- = YFiltered (\p2 -> pfa p2)
-- = YFiltered pfa
--
-- Filter Law 2: filter p . filter q = filter (p `and` q)
-- Proof:
-- (filter p . filter q) (YFiltered pfa)
-- = filter p (filter q (YFiltered pfa))
-- = filter p (YFiltered (\p2 -> pfa (q `and` p2)))
-- = YFiltered (\p3 -> (\p2 -> pfa (q `and` p2)) (p `and` p3))
-- = YFiltered (\p3 -> pfa (q `and` (p `and` p3)))
-- = YFiltered (\p2 -> pfa ((p `and` q) `and` p2))
-- = filter (p `and` q) (YFiltered pfa)

-- We can lift any Filtered structure to one where we delay filtering
liftFiltered :: Filtered f => f a -> YFiltered f a
liftFiltered fa = YFiltered (flip filter fa)

-- Once we are done setting up filters, we can lower back down again to execute all filters
-- in a single traversal
lowerFiltered :: YFiltered f a -> f a
lowerFiltered (YFiltered yfa) = yfa (const True)
-- Here const :: Bool -> (a -> Bool) is the constant function on booleans

-- ... And now we no longer have to manually fuse using `and` !
filter_div6_fast2 :: Filtered f => f Int -> f Int
filter_div6_fast2 =
  let p = \x -> x `mod` 2 == 0
      q = \x -> x `mod` 3 == 0
  in
    lowerFiltered . filter p . filter q . liftFiltered

-- If f is a functor then so is YFiltered f
instance Functor f => Functor (YFiltered f) where
  fmap f (YFiltered pfa) = YFiltered (\pb -> fmap f (pfa (pb.f)))
-- Functor Law 1: fmap id = id
-- Proof:
-- fmap id (YFiltered pfa)
-- = YFiltered (\pb -> fmap id (pfa (pb.id)))
-- = YFiltered (\pb -> pfa pb)  since fmap id = id for functor "f"
-- = YFiltered pfa  (by eta reduction)
--
-- Functor Law 2: fmap g . fmap f = fmap (g.f)
-- Proof:
-- (fmap g . fmap f) (YFiltered pfa)
-- = fmap g (fmap f (YFiltered pfa))
-- = fmap g (YFiltered (\pb -> fmap f (pfa (pb.f))))
-- = YFiltered (\pc -> fmap g ((\pb -> fmap f (pfa (pb.f))) (pc.g)))
-- = YFiltered (\pc -> fmap g (fmap f (pfa (pc.g.f))))
-- = YFiltered (\pc -> fmap (g.f) (pfa (g.f)))  since fmap g . fmap f = fmap (g.f) for underlying functor "f"
-- = fmap (g.f) (YFiltered pfa)

-- Example of inheriting the functor instance for f
yfiltered_functor :: (Functor f, Filtered f) => f Int -> f Int
yfiltered_functor =
  lowerFiltered
  . filter (\x -> x `mod` 12 == 0)
  . fmap (*3)
  . filter (\x -> x `mod` 2 == 0)
  . liftFiltered

-- Unfortunately we have no reason to expect efficient filtering for Yoneda f a since in general none
-- of the elements of f a are computed yet! This means that Yoneda f is not Filtered even if f is Filtered.
-- In the end we pay at least two traversals with this approach: one to compute elements of f a, and another
-- to filter them. It's possible to separate maps and filters in a pipeline to ensure *at most* two traversals:

-- Example: Moving maps left past filters
-- Claim: filter p . map f = map f . filter (\x -> p (f x))
--
-- Proof:
-- Case 1: (filter p . map f) [] = filter p [] = [] = map f [] = (map f . filter (\x -> p (f x))) []
--
-- Case 2:
-- (filter p . map f) (a:as)
-- = filter p (f a : map f as)
-- = if p (f a) then f a : filter p (map f as) else filter p (map f as)
-- = if p (f a) then f a : (map f . filter (\x -> p (f x))) as else (map f . filter (\x -> p (f x)) as [by induction]
-- = map f (if p (f a) then a : filter (\x -> p (f x)) as else filter (\x -> p (f x)) as)
-- = (map f . filter (\x -> p (f x))) (a:as)

-- So maps fuse with eachother and filters fuse with eachother, and maps move left past filters, so we
-- get at most two traversals for any pipeline of maps and filters.
-- Can we do better?


-- FOLDS --

-- Textbook right fold for lists
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (a:as) = f a (foldr f z as)

-- Maps are folds
-- map f = foldr (\x acc -> f x : acc) []

-- Filters are folds
-- filter p = foldr (\x acc -> if p x then x : acc else acc) []

-- Claim: map f . filter p = foldr (\x acc -> if p x then f x : acc else acc) []
--
-- Proof:
-- Case 1: (map f . filter p) [] = map f (filter p []) = [] = foldr (\x acc -> if p x then x:acc else acc) [] []
--
-- Case 2:
-- (map f . filter p) (a:as)
-- = map f (filter p (a:as))
-- = map f (foldr (\x acc -> if p x then x : acc else acc) [] (a:as))
-- = map f (if p a then a : (foldr k [] as) else (foldr k [] as))
--     where k = \x acc -> if p x then x:acc else acc
-- = if p a then f a : map f (filter p as) else map f (filter p as)
-- = if p a then f a : (foldr j [] as) else (foldr j [] as)  [by induction]
--     where j = \x acc -> if p x then f x:acc else acc
-- = (\x acc -> if p x then f x : acc else acc) a (foldr j [] as)
-- = foldr (\x acc -> if p x then f x : acc else acc) [] (a:as)

-- In other words, every map following a filter can be fused into a single traversal (at least for lists). Upshot:
-- every composition of maps and filters on lists can be rewritten as a single traversal.
-- (This is because maps and filters are both examples of *catamorphisms* on lists, so catamorphism composition
--  applies)

-- Foldr Fusion Law:
--
-- Duplicate every element of the input list and then take the length. This costs two traversals since "length" itself
-- is a traversal
doubleElts :: [a] -> Int
doubleElts = length . foldr (\x y -> x:x:y) []

-- Claim: length . foldr (\x y -> x:x:y) [] = foldr (\x y -> 2 + y) 0
-- Observations:
-- 1. If this works, it reduces us back down to one traversal
-- 2. length [] = 0
-- 3. length (x:x:y) = f (g x y) = length (x:x:[]) + length y = h x (f y) where f = length, g x y = x:x:y.
-- Here h x y = length (x:x:[]) + y = 2 + y

doubleEltsFused :: [a] -> Int
doubleEltsFused = foldr (\x y -> 2 + y) 0

-- More General Claim: Suppose there is an h such that f (g x y) = h x (f y). Then f . foldr g a = foldr h (f a)
-- Proof:
-- Case 1: (f . foldr g a) [] = f (foldr g a []) = f a = foldr h (f a) [] = (foldr h (f a)) []
--
-- Case 2:
-- (f . foldr g a) (a:as)
-- = f (foldr g a (a:as))
-- = f (g a (foldr g a as))
-- = h a (f (foldr g a as))
-- = h a (foldr h (f a) as)  [by induction]
-- = foldr h (f a) (a:as)
--
-- As above, this is useful if we have a fold that builds up a big accumulator that we want to traverse again
-- afterwards.


