module HsToCoq.Util.Messages (printAll, printAll', printAllIfPresent) where

import Control.Monad
import Control.Monad.IO.Class

printAll :: MonadIO m
         => (a -> String)
         -> String
         -> String -> String -> String
         -> [a]
         -> m ()
printAll disp header noneEnd oneEnd manyEnd xs = liftIO $ do
  putStrLn $ header ++ case xs of
                         []  -> noneEnd
                         [_] -> oneEnd
                         _   -> manyEnd
  mapM_ (putStrLn . disp) xs

printAll' :: MonadIO m => (a -> String) -> String -> String -> [a] -> m ()
printAll' disp header what = printAll disp
                                      header
                                      "."
                                      (what ++ ":")
                                      (what ++ "s:")

printAllIfPresent :: MonadIO m => (a -> String) -> String -> [a] -> m ()
printAllIfPresent disp what xs = unless (null xs) $ printAll' disp "" what xs
