{-# LANGUAGE OverloadedStrings, ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
import Control.Monad.Shell
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import Data.Monoid
default (T.Text)

main :: IO ()
main = T.writeFile "fib.sh" $ script $
	takeParameter () >>= fib >>= cmd "echo"

fib :: Var Integer -> Script (Var Integer)
fib n = do
	prev <- new1
	acc <- new1
	forCmd (cmd "seq" prev n) $ \_ -> do
		setVar acc (AVar acc `APlus` AVar prev)
		setVar prev (AVar acc `AMinus` AVar prev)
	return acc
  where
	new1 = newVarContaining "1" () :: Script (Var Integer)
