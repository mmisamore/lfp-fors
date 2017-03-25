{-# LANGUAGE ExistentialQuantification, RankNTypes #-}

module Lib
  ( plus4Times100_slow
    , plus4Times100_fast
    , filter_div6_slow
    , filter_div6_fast
    , filter_div6_fast2 ) where

import Prelude hiding (map,Functor,fmap,filter,and)

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
filter :: (a -> Bool) -> [a] -> [a]
filter p []     = []
filter p (a:as) = if p a then a:(filter p as) else filter p as

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
  filt :: (a -> Bool) -> f a -> f a
-- Laws: 1. filt (\x -> True) = id
--       2. filt p . filt q = filt (\x -> p x && q x)

-- Lists can be filtered
instance Filtered [] where
  filt = filter

-- Introduce a useful way of combining predicates
and :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p `and` q = \x -> p x && q x

-- Example of traversing twice to filter
filter_div6_slow :: Filtered f => f Int -> f Int
filter_div6_slow =
  let p = \x -> x `mod` 2 == 0
      q = \x -> x `mod` 3 == 0
  in
    filt p . filt q

-- Tweaking the same to traverse once to get the same result
filter_div6_fast :: Filtered f => f Int -> f Int
filter_div6_fast =
  let p = \x -> x `mod` 2 == 0
      q = \x -> x `mod` 3 == 0
  in
    filt (p `and` q)

-- We can play a similar game as above to get cheaper filtering:
data YFiltered f a = YFiltered { unFiltered :: (a -> Bool) -> f a }

-- YFiltered is Filtered by combining predicates using `and`. Running "filt" is constant-time here
instance Filtered (YFiltered f) where
  filt p1 (YFiltered pfa) = YFiltered (\p2 -> pfa (p1 `and` p2))
-- Law 1: filt (\x -> True) = id
-- Proof:
-- filt (\x -> True) (YFiltered pfa)
-- = YFiltered (\p2 -> pfa ((\x -> True) `and` p2))
-- = YFiltered (\p2 -> pfa p2)
-- = YFiltered pfa
--
-- Law 2: filt p . filt q = filt (p `and` q)
-- Proof:
-- (filt p . filt q) (YFiltered pfa)
-- = filt p (filt q (YFiltered pfa))
-- = filt p (YFiltered (\p2 -> pfa (q `and` p2)))
-- = YFiltered (\p3 -> (\p2 -> pfa (q `and` p2)) (p `and` p3))
-- = YFiltered (\p3 -> pfa (q `and` (p `and` p3)))
-- = YFiltered (\p2 -> pfa ((p `and` q) `and` p2))
-- = filt (p `and` q) (YFiltered pfa)

-- We can lift any Filtered structure to one where we delay filtering
liftFiltered :: Filtered f => f a -> YFiltered f a
liftFiltered fa = YFiltered (flip filt fa)

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
    lowerFiltered . filt p . filt q . liftFiltered


-- FOLDS --

