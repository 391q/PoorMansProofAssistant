module PropHilbertParse where

import PropHilbertStyle
import Data.Char (isLetter, isUpper, toLower)

prettyPrintForm :: Form -> String
prettyPrintForm Bot = "⊥"
prettyPrintForm (Var s) = s
prettyPrintForm (Bot :-> Bot) = "⊤"
prettyPrintForm (f :-> Bot) = "¬" ++ prettyPrintForm f
prettyPrintForm (p :-> q) = "(" ++ prP ++ " → " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]

prettyPrintForm (p :/\ q) = "(" ++ prP ++ " ∧ " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]

prettyPrintForm (p :\/ q) = "(" ++ prP ++ " ∨ " ++ prQ ++ ")"
  where
    [prP, prQ] = map prettyPrintForm [p, q]


data FormToken = TPropVar String | TMetaVar String
                | TOpenBracket | TClosedBracket
                | TBot | TTop
                | TOpImpl | TOpConj | TOpDisj | TOpNeg
                | TError
                deriving (Eq, Show)


tokenise :: String -> [FormToken]
tokenise fmStr = aux $ words $ padPars fmStr
  where
    padPars :: String -> String
    padPars str = concatMap padIfPar str
      where
        padIfPar :: Char -> String
        padIfPar '(' = " ( "
        padIfPar ')' = " ) "
        padIfPar x = [x]
    aux :: [String] -> [FormToken]
    aux [] = []
    aux ("":_) = [TError]
    aux (wrd:wrds)
      | wrd == "(" = TOpenBracket : aux wrds
      | wrd == ")" = TClosedBracket : aux wrds
      | wrdToLow `elem` ["_|_", "⊥", "bot", "false", "falsum", "0"] = TBot : aux wrds
      | wrdToLow `elem` ["T", "⊤", "top", "true", "taut", "1"] = TTop : aux wrds
      | wrdToLow `elem` ["neg", "not", "~", "¬"] = TOpNeg : aux wrds
      | wrdToLow `elem` ["->", "→", "le", "impl"] = TOpImpl : aux wrds
      | wrdToLow `elem` ["/\\", "∧", "&", "&&", "and"] = TOpConj : aux wrds
      | wrdToLow `elem` ["\\/", "∨", "||", "or"] = TOpDisj : aux wrds
      | not . (all isLetter) $ wrd = [TError]
      | isUpper (head wrd) = TMetaVar wrd : aux wrds
      | otherwise = TPropVar wrd : aux wrds
      where
        wrdToLow = map toLower wrd

readFm :: String -> Form
readFm = undefined
