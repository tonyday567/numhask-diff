module Main (main) where

import NumHask.Algebra.Field qualified as NHField
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Diff (Diff')
import NumHask.Diff.Curvature (surfaceOfRevolutionK)
import NumHask.Diff.Inverse (constDiff, implicit1N, inverseN, varDiff)
import NumHask.Diff.Jet (taylor)
import System.Exit (exitFailure)
import Prelude hiding ((*), (+), (-), (/))
import Prelude qualified as P

eps :: Double
eps = 1e-10

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

near :: [Double] -> [Double] -> Bool
near xs ys =
  P.length xs == P.length ys && P.all (\(x, y) -> abs (x - y) < eps) (P.zip xs ys)

main :: IO ()
main = do
  putStrLn "Jet oracle tests"

  assert "exp at 0" $
    taylor NHField.exp 5 (0.0 :: Double) `near` [1.0, 1.0, 1.0, 1.0, 1.0, 1.0]

  assert "sin at 0" $
    taylor NHField.sin 7 (0.0 :: Double) `near` [0.0, 1.0, 0.0, -1.0, 0.0, 1.0, 0.0, -1.0]

  assert "cos at 0" $
    taylor NHField.cos 7 (0.0 :: Double) `near` [1.0, 0.0, -1.0, 0.0, 1.0, 0.0, -1.0, 0.0]

  assert "log at 1" $
    taylor NHField.log 5 (1.0 :: Double) `near` [0.0, 1.0, -1.0, 2.0, -6.0, 24.0]

  assert "exp at 1" $
    let ds = taylor NHField.exp 5 (1.0 :: Double)
        e = NHField.exp 1.0
     in ds `near` [e, e, e, e, e, e]

  assert "composition: exp(sin(x)) at 0" $
    let ds = taylor (NHField.exp . NHField.sin) 5 (0.0 :: Double)
        expected = [1.0, 1.0, 1.0, 0.0, -3.0, -8.0]
     in ds `near` expected

  putStrLn "Inverse / implicit oracle tests"

  let x :: Diff' p Double Double
      x = varDiff

  assert "inverse: sqrt via x²" $
    let root = inverseN (x * x) 2.0 1.5 10
     in abs (root - P.sqrt 2.0) < 1e-12

  assert "inverse: log via exp" $
    let root = inverseN (NHField.exp x) (NHField.exp 1.0) 0.5 10
     in abs (root - 1.0) < 1e-12

  assert "implicit: circle y = sqrt(1 - x²)" $
    let xVal = 0.6 :: Double
        y0 = 0.8 :: Double
        y = varDiff
        g = constDiff xVal * constDiff xVal + y * y - one
        root = implicit1N g y0 10
        expected = P.sqrt (1.0 P.- xVal P.* xVal)
     in abs (root P.- expected) < 1e-12

  putStrLn "Curvature oracle tests"

  assert "S² Gaussian curvature = 1" $
    let profile z = NHField.sqrt (one - z * z)
        k = surfaceOfRevolutionK profile (0.0 :: Double)
     in abs (k P.- 1.0) < 1e-10
