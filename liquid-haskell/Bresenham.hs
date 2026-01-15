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

{-@ type Bresenstate' = {b: Bresenstate | 2 * (y b) * (dx b) - (dx b) <= 2 * (dy b) * (x b) && 2 * (dy b) * (x b) <= 2 * (y b) * (dx b) + (dx b) } @-}
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
