module PropHilberUI where

import PropHilbertParse

main = do
  cmd <- getLine
  putStrLn $ prettyPrintForm $ neg $ readFm $ cmd
