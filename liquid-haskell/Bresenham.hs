{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--exactdc" @-}
-- Dump constraints to .liquid/Bresenham.fq.prettified
{-@ LIQUID "--save" @-}
-- {-@ LIQUID "--reflection" @-}

module Bresenham where

-- import Language.Haskell.Liquid.ProofCombinators

{-@ data Bresenstate = Bresenstate
                         (dx :: Nat)
                         (dy :: Nat)
                         (x :: Nat)
                         (y :: Nat)
                         (d :: Int)
 @-}
data Bresenstate = Bresenstate Int Int Int Int Int

{-@ measure ideal_y_minus_half_times_2dx @-}
{-@ ideal_y_minus_half_times_2dx :: Bresenstate -> Int @-}
ideal_y_minus_half_times_2dx :: Bresenstate -> Int
ideal_y_minus_half_times_2dx (Bresenstate dx dy x _ _) = 2 * dy * x - dx

{-@ measure computed_y_times_2dx @-}
{-@ computed_y_times_2dx :: Bresenstate -> Nat @-}
computed_y_times_2dx :: Bresenstate -> Int
computed_y_times_2dx (Bresenstate dx _ _ y _) = y * 2 * dx

{-@ measure ideal_y_plus_half_times_2dx @-}
{-@ ideal_y_plus_half_times_2dx :: Bresenstate -> Int @-}
ideal_y_plus_half_times_2dx :: Bresenstate -> Int
ideal_y_plus_half_times_2dx (Bresenstate dx dy x _ _) = 2 * dy * x + dx

{-@
type Bresenstate' = {b: Bresenstate |
                            (dx b) > 0 &&
                            (dy b) <= (dx b) &&
                            (d b) == 2 * (dy b) * (x b) - 2 * (dx b) * (y b) + 2 * (dy b) - (dx b) &&

                            ideal_y_minus_half_times_2dx b <= computed_y_times_2dx b &&
                            computed_y_times_2dx b <= ideal_y_plus_half_times_2dx b &&

                            (dy b) / (dx b) * (x b) - 1/2 <= (y b) &&
                            True
                     }
@-}
type Bresenstate' = Bresenstate

{-@ lemma0 :: x:Int -> y:Int -> {z:Nat | z > 0} -> { x * z <= y => x <= y / z } @-}
lemma0 :: Int -> Int -> Int -> ()
lemma0 _ _ _ = ()

{-@ lemma1 :: x:Int -> y:Int -> {z:Nat | z > 0} -> { x * z <= y * z => x <= y } @-}
lemma1 :: Int -> Int -> Int -> ()
lemma1 _ _ _ = ()

{-@ lemma2 :: x:Nat -> y:Nat -> {dx:Nat | dx > 0} -> dy:Nat -> { 2 * dy * x - dx <= y * 2 * dx => dy / dx * x - 1/2 <= y } @-}
lemma2 :: Int -> Int -> Int -> Int -> ()
lemma2 _ _ _ _ = ()

{-@ lemma3 :: x:Nat -> y:Nat -> {dx:Nat | dx > 0} -> dy:Nat -> { y * 2 * dx <= (2 * dy * x) + dx      =>       y * dx <= (dy * x) + (dx / 2) } @-}
lemma3 :: Int -> Int -> Int -> Int -> ()
lemma3 _ _ _ _ = ()

{-@ lemma4 :: {x:Nat | x > 0} -> {y:Nat | y > 0} -> {dx:Nat | dx > 0} -> {dy:Nat | dy > 0} -> { y * dx <= dy * x       =>      y <= (dy * x) / dx } @-}
lemma4 :: Int -> Int -> Int -> Int -> ()
lemma4 _ _ _ _ = ()

{-@ lemma5 :: {x:Nat | x > 0} -> {y:Nat | y > 0} -> {dx:Nat | dx > 0} -> {dy:Nat | dy > 0} -> { y * dx <= (dy * x) + (dx / 2)      =>       y <= ((dy * x) + (dx / 2)) / dx } @-}
lemma5 :: Int -> Int -> Int -> Int -> ()
lemma5 _ _ _ _ = ()

{-@ distributivity_of_mult_over_plus :: {a:Nat | a > 0} -> {b:Nat | b > 0} -> {c:Nat | c > 0} -> { (a + b) * c == a*c + b*c } @-}
distributivity_of_mult_over_plus :: Int -> Int -> Int -> ()
distributivity_of_mult_over_plus _ _ _ = ()

-- {-@ distributivity_of_div_over_plus :: {a:Nat | a > 0} -> {b:Nat | b > 0} -> {c:Nat | c > 0} -> { (a + b) / c == a/c + b/c } @-}
-- distributivity_of_div_over_plus :: Int -> Int -> Int -> ()
-- distributivity_of_div_over_plus _ _ _ = ()

pulsed' :: Bresenstate' -> Bool
pulsed' (Bresenstate _ _ _ _ d) = d >= 0

{-@ measure ince @-}
{-@ ince :: Bresenstate' -> Int @-}
ince :: Bresenstate' -> Int
ince (Bresenstate dx dy x y d) = 2 * dy

{-@ measure incne @-}
{-@ incne :: Bresenstate' -> Int @-}
incne :: Bresenstate' -> Int
incne (Bresenstate dx dy x y d) = 2 * (dy - dx)

{-@ bresenstep :: b:Bresenstate' -> {res: Bresenstate' | x res = x b + 1} @-}
bresenstep :: Bresenstate' -> Bresenstate'
bresenstep b@(Bresenstate dx dy x y d)
  | d < 0 = Bresenstate dx dy (x + 1) y (d + (ince b))
  | otherwise = Bresenstate dx dy (x + 1) (y + 1) (d + (incne b))

{-@ bresinit :: {dx:Nat | dx > 0} -> {dy:Nat | dy <= dx} -> Bresenstate' @-}
bresinit :: Int -> Int -> Bresenstate'
bresinit dx dy = Bresenstate dx dy 0 0 (2 * dy - dx)

{-@ lazy bresenstates @-}
{-@ bresenstates :: Bresenstate' -> [Bresenstate'] @-}
bresenstates :: Bresenstate' -> [Bresenstate']
bresenstates b = iterate bresenstep b

{-@ bresenstates' :: {dx:Nat | dx > 0} -> {dy:Nat | dy <= dx} -> [Bresenstate'] @-}
bresenstates' :: Int -> Int -> [Bresenstate']
bresenstates' dx dy = bresenstates (bresinit dx dy)

{-@ pulses :: {dx:Nat | dx > 0} -> {dy:Nat | dy <= dx} -> [Bool] @-}
pulses :: Int -> Int -> [Bool]
pulses dx dy = map pulsed' (drop 1 (bresenstates' dx dy))
