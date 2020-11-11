module BenchPrimesSieveArray where

import Control.Monad (forM_)
import Text.Read (readMaybe)
import Data.Array.Unboxed (UArray, assocs)
import Data.Array.ST (STUArray, runSTUArray, newArray, writeArray, readArray)
import Control.Monad.ST (ST)

import BenchCommon (runIters)

{-# scc sieve #-}
sieve :: Int -> () -> UArray Int Bool
sieve limit () = runSTUArray $ do
  -- 'True' denotes 'Prime', 'False' denotes 'Composite'
  arr <- newArray (0, limit - 1) True :: ST s (STUArray s Int Bool)
  writeArray arr 0 False
  writeArray arr 1 False

  forM_ [2..limit - 1] $ \n -> do
    isPrime <- readArray arr n
    if isPrime then
      forM_ (takeWhile (< limit) $ map (* n) [2..]) $ \i ->
        writeArray arr i False
    else
      return ()

  return arr

main :: IO ()
main = do
  itersStr <- getLine
  limitStr <- getLine
  case (readMaybe itersStr, readMaybe limitStr) of
    (Just iters, Just limit) ->
      case runIters (sieve limit) iters of
        Just primes ->
          forM_ (assocs primes) $ \(i, isPrime) ->
            if isPrime then
              print i
            else
              return ()

        Nothing ->
          return ()

    (_, _) ->
      putStrLn "Please enter two positive integers (an iteration count and a limit)"
