module BenchPrimesSieveSeq where

import Control.Monad (forM_)
import Data.List (foldl')
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Text.Read (readMaybe)
import Data.Foldable (toList)

import BenchCommon (runIters)

data Primality = Prime | Composite deriving (Eq, Show)

{-# scc sieve #-}
sieve :: Int -> () -> Seq Primality
sieve limit () =
  let
    initArr =
      Seq.fromList $ [Composite, Composite] ++ replicate (limit - 2) Prime

    markMultiples arr n =
      case Seq.index arr n of
        Prime ->
          foldl' (\new i -> (Seq.update i $! Composite) $! new) arr $
          takeWhile (\i -> i < limit) $
          map (\i -> i * n) $
          [2..]

        Composite ->
          arr
  in
    foldl' markMultiples initArr [2..limit - 1]

main :: IO ()
main = do
  itersStr <- getLine
  limitStr <- getLine
  case (readMaybe itersStr, readMaybe limitStr) of
    (Just iters, Just limit) ->
      case runIters (sieve limit) iters of
        Just primes ->
          forM_ (zip [0 :: Int ..] $ toList primes) $ \(i, status) ->
            case status of
              Prime -> print i
              Composite -> return ()

        Nothing ->
          return ()

    (_, _) ->
      putStrLn "Please enter two positive integers (an iteration count and a limit)"
