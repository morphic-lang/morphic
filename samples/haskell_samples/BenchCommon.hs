module BenchCommon (runIters) where

runIters :: (() -> a) -> Int -> Maybe a
runIters _ 0 = Nothing
runIters f 1 = Just $ f ()
runIters f n = f () `seq` runIters f (n - 1)
