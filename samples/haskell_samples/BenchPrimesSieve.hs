{-# language TupleSections #-}

module BenchPrimesSieve where

import Control.Monad (forM_)
import Data.List (foldl')
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Text.Read (readMaybe)

import BenchCommon (runIters)

data Primality = Prime | Composite deriving (Eq, Show)

{-# scc sieve #-}
sieve :: Int -> () -> IntMap Primality
sieve limit () =
  let
    initArr =
      IntMap.fromList $ [(0, Composite), (1, Composite)] ++ map (, Prime) [2..limit - 1]

    markMultiples arr n =
      case arr IntMap.! n of
        Prime ->
          foldl' (\new i -> IntMap.adjust (const Composite) i new) arr $
          takeWhile (< limit) $
          map (* n) $
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
          forM_ (IntMap.toAscList primes) $ \(i, status) ->
            case status of
              Prime -> print i
              Composite -> return ()

        Nothing ->
          return ()

    (_, _) ->
      putStrLn "Please enter two positive integers (an iteration count and a limit)"
