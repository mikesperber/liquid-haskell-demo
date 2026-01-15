{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--exactdc" @-}
-- {-@ LIQUID "--reflection" @-}

module Bresenham where

-- import Language.Haskell.Liquid.ProofCombinators

{-@ data Bresenstate = Bresenstate
                         (dx :: {v: Nat | v > 0})
                         (dy :: {v: Nat | v <= dx})
                         (x :: Nat)
                         (y :: Nat)
                         (d :: {v: Int | v == 2 * dy * x - 2 * dx * y + 2 * dy - dx})
 @-}
data Bresenstate = Bresenstate Int Int Int Int Int

{-@ measure ideal_y_times_2dx @-}
{-@ ideal_y_times_2dx :: Bresenstate -> Nat @-}
ideal_y_times_2dx :: Bresenstate -> Int
ideal_y_times_2dx (Bresenstate _ dy x _ _) = 2 * dy * x

{-@ measure y_minus_half_times_2dx @-}
{-@ y_minus_half_times_2dx :: Bresenstate -> Int @-}
y_minus_half_times_2dx :: Bresenstate -> Int
y_minus_half_times_2dx (Bresenstate dx _ _ y _) = 2 * y * dx - dx

{-@ measure y_plus_half_times_2dx @-}
{-@ y_plus_half_times_2dx :: Bresenstate -> Int @-}
y_plus_half_times_2dx :: Bresenstate -> Int
y_plus_half_times_2dx (Bresenstate dx _ _ y _) = 2 * y * dx + dx

{-@
type Bresenstate' = {b: Bresenstate |
                            y_minus_half_times_2dx b <= ideal_y_times_2dx b &&
                            ideal_y_times_2dx b <= y_plus_half_times_2dx b }
@-}
type Bresenstate' = Bresenstate

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
