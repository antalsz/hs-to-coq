{-# LANGUAGE OverloadedStrings #-}
import Control.Monad
import Data.Bifunctor
import Data.Bits ((.|.))
import Data.Char
import Data.Foldable
import Data.Monoid
import Data.Maybe
import Data.List
import Data.Ord
import Data.Traversable
import qualified Data.ByteString.Char8 as BS
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf
import Text.Regex.PCRE

type S = BS.ByteString

type Module = S

data What
    = VerifiedFunctions Int
    | UnverifiedFunctions Int
    | UntranslatedFunctions Int
    | Function Function

    | VerifiedTypeClasses Int
    | UnverifiedTypeClasses Int
    | UntranslatedTypeClasses Int
    | TypeClass TypeClass

    | Headers
    | Types
    | Tactics

    | WellFormedness
    | WellFormednessLemmas

    | Uniqueness

    | CoqInterface
    | Tests

    | Arith
    | Lists
    | Dyadic
    | Order
  deriving (Show, Eq, Ord)
type Group = What -- a buit ugly

-- Common up some highly related functions under a common name
normWhat :: Module -> Column -> What -> What
normWhat _ _ WellFormednessLemmas = WellFormedness -- disable this distinction
normWhat _ _ Types = Headers -- disable this distinction

-- normWhat "Utils" _ (Function _) = Functions

normWhat _ _ (Function "op_zrzr__") = Function "difference"
normWhat _ _ (Function "op_zn__") = Function "find"
normWhat _ _ (Function "op_znz3fU__") = Function "lookup"

normWhat "Set" _ (Function "balanced")  = Function "valid"
normWhat "Set" _ (Function "ordered")   = Function "valid"
normWhat "Set" _ (Function "validsize") = Function "valid"

normWhat "Set" _ (Function "split")   = Function "splitS"
normWhat _ _ (Function "foldrFB") = Function "foldr"
normWhat _ _ (Function "foldlFB") = Function "foldl"
normWhat _ _ (Function "match")   = Function "nomatch"
normWhat _ _ (Function "match_")  = Function "nomatch"
normWhat _ _ (Function "boolITE")  = Function "bool"
normWhat _ _ (Function "revNatSafe") = Function "revNat"

normWhat _ _ (Function "bit_N")  = Arith
normWhat _ _ (Function "shiftLL")  = Arith

-- record accessors
normWhat m c (Function "matchedKey")      = normWhat m c Types
normWhat m c (Function "getMergeSet")     = normWhat m c Types
normWhat m c (Function "missingKey")      = normWhat m c Types
normWhat m c (Function "missingSubtree")  = normWhat m c Types

normWhat m c (Function "delta")           = normWhat m c Types
normWhat m c (Function "ratio")           = normWhat m c Types
normWhat m c (Function "set_size")        = normWhat m c Types
normWhat m c (Function "map_size")        = normWhat m c Types
normWhat m c (Function "size_nat")        = normWhat m c Types
normWhat _ _ (Function f)
    | f `elem` BS.words "showTreeWith showWide showsBars showsTree showsTreeHang withBar withEmpty "
    = Function "showTree"
normWhat _ _ w = w

showWhat :: What -> BS.ByteString
showWhat (Function f)   = f
showWhat (TypeClass f)  = "instance " <> f
showWhat (VerifiedFunctions n)       = "Functions, verified (" <> showBS n <> ")"
showWhat (UnverifiedFunctions n)     = "Functions, unverified (" <> showBS n <> ")"
showWhat (UntranslatedFunctions n)   = "Functions, untranslated (" <> showBS n <> ")"
showWhat (VerifiedTypeClasses n)     = "Type classes, verified (" <> showBS n <> ")"
showWhat (UnverifiedTypeClasses n)   = "Type classes, unverified (" <> showBS n <> ")"
showWhat (UntranslatedTypeClasses n) = "Type classes, untranslated (" <> showBS n <> ")"
showWhat WellFormedness        = "Well-formedness"
showWhat WellFormednessLemmas  = "(lemmas)"
showWhat Headers  = "Headers and types"
showWhat Arith  = "Arithmetic"
showWhat CoqInterface  = "\\texttt{FSetInterface}"
showWhat w              = BS.pack (show w)

showWhatShort :: What -> BS.ByteString
showWhatShort (Function f)   = f
showWhatShort (TypeClass f)  = "instance " <> f
showWhatShort (VerifiedFunctions n)       = "Funcs, verf."
showWhatShort (UnverifiedFunctions n)     = "\\ldots, unverif."
showWhatShort (UntranslatedFunctions n)   = "\\ldots, untrans."
showWhatShort (VerifiedTypeClasses n)     = "Classes, verif."
showWhatShort (UnverifiedTypeClasses n)   = "\\ldots, unverif."
showWhatShort (UntranslatedTypeClasses n) = "\\ldots, untrans."
showWhatShort WellFormedness        = "WF"
showWhatShort WellFormednessLemmas  = "(lemmas)"
showWhatShort w              = BS.pack (show w)

type Function = S
type TypeClass = S
type Pats = [(Regex, ToFun)]
data Column = Haskell | Gallina | Proofs deriving (Show, Eq, Ord, Enum, Bounded)

files :: [(FilePath, Pats, Module, Column)]
files =
    [ ("theories/SetProofs.v",                                proofs,      "Set",    Proofs)
    , ("theories/MapProofs.v",                                proofs,      "Map",    Proofs)
    , ("theories/RevNatSlowProofs.v",                         proofs,      "IntSet", Proofs)
    , ("theories/IntSetProofs.v",                             proofs,      "IntSet", Proofs)
    , ("theories/IntSetUtil.v",                               all Tests,   "IntSet", Proofs)
    , ("theories/IntSetPropertyProofs.v",                     all Tests,   "IntSet", Proofs)
    , ("theories/OrdTactic.v",                                all Order,   "Utils",  Proofs)
    , ("theories/OrdTheories.v",                              all CoqInterface,   "Utils",  Proofs)
    , ("theories/Tactics.v",                                  all Tactics, "Utils",  Proofs)
    , ("theories/HSUtil.v",                                   all Lists,   "Utils",  Proofs)
    , ("theories/SortedUtil.v",                               all Lists,   "Utils",  Proofs)
    , ("lib/Data/Set/Internal.v",                             gallina,     "Set",    Gallina)
    , ("lib/Data/Map/Internal.v",                             gallina,     "Map",    Gallina)
    , ("lib/Data/IntSet/Internal.v",                          gallina,     "IntSet", Gallina)
    , ("lib/Utils/Containers/Internal/BitUtil.v",             gallina,     "IntSet", Gallina)
    , ("lib/IntSetValidity.v",                                all_valid,   "IntSet", Gallina)
    , ("hs-spec/IntSetProperties.v",                          all Tests,   "IntSet", Gallina)
    , ("lib/BitTerminationProofs.v",                          all Arith,   "IntSet", Gallina)
    , ("containers/Data/Set/Internal.hs",                     hs,          "Set",    Haskell)
    , ("containers/Data/Map/Internal.hs",                     hs,          "Map",    Haskell)
    , ("containers/Data/IntSet/Internal.hs",                  hs,          "IntSet", Haskell)
    , ("containers/tests/IntSetValidity.hs",                  all_valid,   "IntSet", Haskell)
    , ("containers/tests/intset-properties.hs",               all Tests,   "IntSet", Haskell)
    , ("containers/Utils/Containers/Internal/BitUtil.hs",     hs,          "IntSet", Haskell)
    , ("containers/Utils/Containers/Internal/PtrEquality.hs", hs,          "Utils",  Haskell)
    ]
  where
    all :: What -> Pats
    all w = [(mkM ".*", k w)]



type ToFun = MatchResult S -> What
k :: What -> ToFun
k = const
f1 :: ToFun
f1 = Function . head . mrSubList
tc1 :: ToFun
tc1 = TypeClass . head . mrSubList

hs :: Pats
hs = first mk <$>
    [ ("^data Set",                        k Types)
    , ("^data Map",                        k Types)
    , ("^data IntSet",                     k Types)
    , ("instance .* => (?:.*\\.)?(.*?) ",  tc1)
    , ("instance (?:.*\\.)?(.*) (?:Set|IntSet|Map)",      tc1)
    , ("^(insertMin)",                     f1)
    , ("^(insertMax)",                     f1)
    , ("^infixl . \\\\\\\\",               k (Function "difference"))
    , ("^\\(\\\\\\\\\\)",                  k (Function "difference"))
    , ("^\\(!\\)",                         k (Function "find"))
    , ("^\\(!\\?\\)",                      k (Function "lookup"))
    , ("^([a-zA-Z0-9'_]*?)(?:,.*)? +::",           f1)
    , ("^(mergeA)$",                       f1)
    ]

all_valid :: Pats
all_valid = first mk <$>
    [ ("^valid ::",                        k (Function "valid"))
    , ("^Definition",                      k (Function "valid"))
    ]
gallina :: Pats
gallina = first mk <$>
    [ ("^Definition Size",                 k Types)
    , ("^Inductive Set_",                  k Types)
    , ("^Inductive IntSet",                k Types)
    , ("^Inductive Map",                   k Types)
    , ("^Axiom patternFailure",            k Headers)
    , ("^Axiom unsafeFix",                 k Headers)
    , ("^Ltac",                            k Tactics)
    , ("^Local Definition (.+?)__",        tc1)
    , ("^Program Instance (.+?)__",        tc1)
    , ("^Fixpoint (.*?) ",                 f1)
    , ("^Program Fixpoint (.*?) ",         f1)
    , ("^Definition ([A-Z].*?) ",          k Types)
    , ("^Definition ([a-z].*?) ",          f1)
    , ("^Program Definition ([a-z].*?) ",  f1)
    ]

proofs :: Pats
proofs = first mk <$>
    [ (sect "Tactics",                               k Tactics)
    , (sect "General utility tactics",               k Tactics)
    , (sect "An omega that "         ,               k Tactics)
    , (sect "Utilities about sorted ",               k Lists)
    , (sect "The \\[nonneg\\] tactic",               k Tactics)
    , (sect "Lemmas about \\[N\\] and",              k Arith)
    , (sect "Dyadic intervals",                      k Dyadic)
    , (sect "Operation: \\[bitmapInRange\\]",        k Dyadic)
    , (sect "Bitmasks with",                         k Arith)
    , (sect "Verification of \\[Eq\\]",              k (TypeClass "Eq"))
    , (sect "Verification of \\[Ord\\]",             k (TypeClass "Ord"))
    , (sect "Verification of \\[(.*?)\\]",           f1)
    , (sect "Utilities for working with \\[Ord\\]",  k Order)
    , (sect "Lemmas related to well-formedness",     k WellFormednessLemmas)
    , (sect "Well-formedness",                       k WellFormedness)
    , (sect "Well-formed IntSets",                   k WellFormedness)
    , (sect "Uniqueness of representation *",        k Uniqueness)
    , (sect "A setup for complete specification",    k WellFormednessLemmas)
    , (sect "Instantiating the \\[FSetInterface\\]", k CoqInterface)
    ]
  where
    sect = ("^\\(\\*\\* \\*\\*?\\*? " <>)

mk, mkM :: S -> Regex
mk s = makeRegexOpts (defaultCompOpt .|. compMultiline) defaultExecOpt (s <> ".*$")
mkM  = makeRegexOpts (defaultCompOpt .|. compDotAll .|. compMultiline) defaultExecOpt

type Table = [(Module, What, Column, S, Int)]
type Summary = M.Map (Module, What, Column) Int
type GroupSummary = M.Map (Module, Group, Column) Int

summarizeGroups :: Summary -> GroupSummary
summarizeGroups summary =
    M.fromListWith (+) [ ((mod, groupOf mod what, col), n)
                       | ((mod, what, col), n) <- M.toList summary ]
  where
    isVerified     m w = (m,w,Proofs) `M.member` summary
    isUnverified   m w = not (isVerified m w) && (m,w,Gallina) `M.member` summary
    isUntranslated m w = not (isVerified m w) && not (isUnverified m w)

    verifiedFunctions = S.fromList
        [ w | ((m, w@Function{}, _), _) <- M.toList summary, isVerified m w ]
    unverifiedFunctions = S.fromList
        [ w | ((m, w@Function{}, _), _) <- M.toList summary, isUnverified m w ]
    untranslatedFunctions = S.fromList
        [ w | ((m, w@Function{}, _), _) <- M.toList summary, isUntranslated m w ]
    verifiedTypeClasses = S.fromList
        [ w | ((m, w@TypeClass{}, _), _) <- M.toList summary, isVerified m w ]
    unverifiedTypeClasses = S.fromList
        [ w | ((m, w@TypeClass{}, _), _) <- M.toList summary, isUnverified m w ]
    untranslatedTypeClasses = S.fromList
        [ w | ((m, w@TypeClass{}, _), _) <- M.toList summary, isUntranslated m w ]

    groupOf m w@Function{}  | isVerified     m w = VerifiedFunctions (S.size verifiedFunctions)
                            | isUnverified   m w = UnverifiedFunctions (S.size unverifiedFunctions)
                            | isUntranslated m w = UntranslatedFunctions (S.size untranslatedFunctions)
    groupOf m w@TypeClass{} | isVerified     m w = VerifiedTypeClasses (S.size verifiedTypeClasses)
                            | isUnverified   m w = UnverifiedTypeClasses (S.size unverifiedTypeClasses)
                            | isUntranslated m w = UntranslatedTypeClasses (S.size untranslatedTypeClasses)
    groupOf m w = w

summarize :: Table -> Summary
summarize table = M.fromListWith (+)
    [ ((mod, what, col), n)
    | (mod, what, col, _, n) <- table
    , n > 0
    ]

main :: IO ()
main = do
    table <- concat <$> (for files $ \(fn, pats, mod, col) -> do
        f <- BS.readFile fn
        pure $ classify pats mod col "" f Headers)

    BS.writeFile "tally.debug" $ BS.unlines $ concat
        [ (BS.pack $ printf "%s in %s %s (%d non-comment lines):" (BS.unpack $ showWhat what) (show col) (BS.unpack mod) n) :
          map ("    " <>) (BS.lines txt) -- (stripComments txt)
        | (mod, what, col, txt, n) <- table ]

    let summary = summarize table
    let gsummary = summarizeGroups summary

    BS.writeFile "tally.csv" $ printSummary summary
    BS.writeFile "tally.tex" $ mconcat
        [ def "summarytallytable"
        $ printLaTeXSummary gsummary
        , def "translationcoordinates"
        $ printTransCoordinateList summary
        , def "provingcoordinates"
        $ printProvingCoordinateList summary
        , def2 "modsummarysymboliccoords" "modsummaryplots"
        $ printModSummaryPlots gsummary
        , def2 "modsummarysymboliccoordsSet" "modsummaryplotsSet"
        $ printModSummaryPlots' "Set" gsummary
        , def2 "modsummarysymboliccoordsMap" "modsummaryplotsMap"
        $ printModSummaryPlots' "Map" gsummary
        , def2 "modsummarysymboliccoordsIntSet" "modsummaryplotsIntSet"
        $ printModSummaryPlots' "IntSet" gsummary
        , def2 "modsummarysymboliccoordsUtils" "modsummaryplotsUtils"
        $ printModSummaryPlots' "Utils" gsummary
        ]

printTransCoordinateList :: Summary -> S
printTransCoordinateList summary = BS.unwords
    [ coordinateData (showBS g) (showBS h) m
    | (m, w) <- S.toList $ S.fromList [ (m,w) | (m,w,_) <- M.keys summary, isInteresting w ]
    , Just h <- pure $ M.lookup (m,w,Haskell) summary
    , Just g <- pure $ M.lookup (m,w,Gallina) summary
    ]
  where
    isInteresting (Function _) = True
    isInteresting (TypeClass _) = True
    isInteresting _ = False

printProvingCoordinateList :: Summary -> S
printProvingCoordinateList summary = BS.unwords
    [ coordinateData (showBS p) (showBS g) m
    | (m, w) <- S.toList $ S.fromList [ (m,w) | (m,w,_) <- M.keys summary, isInteresting w ]
    , Just g <- pure $ M.lookup (m,w,Gallina) summary
    , Just p <- pure $ M.lookup (m,w,Proofs) summary
    ]
  where
    isInteresting (Function _) = True
    isInteresting (TypeClass _) = True
    isInteresting _ = False

printModSummaryPlots :: GroupSummary -> (S, S)
printModSummaryPlots summary = (symboliccoords, plots)
  where
    symboliccoords = "symbolic y coords={" <> commas [ barLabel c m | (m,c) <- bars] <> "}"
    plots = BS.unlines $
      [ "\\addplot coordinates {" <> BS.unwords
        [ coordinate (showBS n) (barLabel c m)
        | (m,c) <- bars
        , let n = lookupInt (m,g,c) summary
        ] <>
        "};"
      | g <- groups
      ] ++
      [ "\\legend{ " <> commas ["{" <> showWhatShort g <> "}"| g <- groups ] <> "}" ]
    barLabel Haskell m = m <> ".hs"
    barLabel Gallina m = m <> ".v"
    barLabel Proofs m  = m <> "Proofs.v"
    cols = [minBound..maxBound]
    mods = S.toList $ S.fromList [ m | (m,g,c) <- M.keys summary]
    bars = reverse $ (,) <$> ["Set", "Map", "IntSet"] <*> cols
    groups = S.toList $ S.fromList [ g | (m,g,c) <- M.keys summary]

printModSummaryPlots' :: Module -> GroupSummary -> (S, S)
printModSummaryPlots' mod summary = (symboliccoords, plots)
  where
    symboliccoords = "symbolic y coords={" <> commas [ showBS c | c <- cols] <> "}"
    plots = BS.unlines $
      [ "\\addplot coordinates {" <> BS.unwords
        [ coordinate (showBS n) (showBS c)
        | c <- cols
        , let n = lookupInt (mod,g,c) summary
        ] <>
        "};"
      | g <- groups
      ] ++
      [ "\\legend{ " <> commas ["{" <> showWhatShort g <> "}"| g <- groups ] <> "}" ]
    cols = reverse $ [minBound..maxBound]
    groups = S.toList $ S.fromList [ g | (m,g,c) <- M.keys summary]

pruneUnverified :: Summary -> Summary
pruneUnverified summary = M.filterWithKey test summary
  where test (mod,what,col) _ = M.member (mod,what,Proofs) summary


coordinate :: S -> S -> S
coordinate x y = "(" <> x <> "," <> y <> ")"

coordinateData :: S -> S -> S -> S
coordinateData x y d = "(" <> x <> "," <> y <> ") [" <> d <> "]"

def :: S -> S -> S
def n c = "\\newcommand{\\" <> n <> "}{" <> c <> "}\n"

def2 :: S -> S -> (S,S) -> S
def2 n1 n2 (c1,c2) = def n1 c1 <> def n2 c2


printSummary :: M.Map (S,What,Column) Int -> S
printSummary summary
    = BS.unlines $
    ( commas $ "Module" : "Function" : map (BS.pack . show) cols) :
    [ BS.intercalate "," $
       x : showWhat y : [ lookupIntS (x,y,c) summary | c <- cols]
    | (x,y) <- rows ]
  where
    cols = [minBound..maxBound]
    rows = S.toList $ S.fromList [ (x,y) | (x,y,_)   <- M.keys summary]


commas :: [S] -> S
commas = BS.intercalate ","

lookupInt :: Ord a => a -> M.Map a Int -> Int
lookupInt x = fromMaybe 0 . M.lookup x

lookupIntS :: Ord a => a -> M.Map a Int -> S
lookupIntS x = maybe "" (BS.pack . show) . M.lookup x

printLaTeXSummary :: GroupSummary -> S
printLaTeXSummary summary
    = BS.unlines $
    [ "\\begin{tabular}{l|rrr|rrr|rrr}"
    , row' ("" : map center (map showBS cols))
    , row  ("" : concatMap (const subColumns) cols)
    ] ++ concat
    [ [ "\\noalign{\\hrule height 0.4pt}" ] ++
      [ row' $ firstLine :
              [ lookupIntS (w,c) gsummary | c <- cols ]
      | showTotal
      ] ++
      [ row $ secondLine :
              [ lookupIntS (m,w,c) summary | c <- cols, m <- subColumns]
      ]
    | (w, groupRows) <- M.toList groupedRows
    , let showTotal = length groupRows > 1
    , let (firstLine, secondLine)
            | showTotal = second ("\\quad " <>) $ splitComma (showWhat w)
            | otherwise = (undefined, showWhat w)
    ] ++
    [ "\\end{tabular}" ]
  where
    splitComma x | BS.null b = (a,b)
                 | otherwise = (a <> ",", BS.tail b)
      where
        (a,b) = BS.break (','==) x
    center x = "\\multicolumn{1}{c}{" <> x <> "}"
    row xs = BS.intercalate " & " xs <> "\\\\"
    row' (x:xs) = BS.intercalate " & " ys <> "\\\\"
      where ys = x : concatMap (\y -> if BS.null y then ["","",""] else ["",y,""]) xs
    cols = [minBound..maxBound]
    rows = S.toList $ S.fromList [ (x,y) | (x,y,_)   <- M.keys summary]
    gsummary = M.fromListWith (+)
        [ ((what, col), n)
        | ((mod, what, col), n) <- M.toList summary
        ]
    groupedRows = M.fromListWith (++) [(w, [m]) | (m,w) <- rows]
    subColumns = ["Set", "Map", "IntSet"]


showBS :: Show a => a -> S
showBS = BS.pack . show

showMod :: Module -> S
showMod m = "{\\codefont " <> m <> "}"


classify :: Pats -> Module -> Column -> S -> S -> What -> Table
classify pats mod col = go
  where
    go :: S -> S -> What -> Table
    go begin rest current
        | not (BS.null rest)
        , Just (mr, toFun) <- matchFirst pats rest
        , let this = begin <> mrBefore mr
        , let next = normWhat mod col $ toFun mr
        = if current == next
          then go (begin <> mrBefore mr <> mrMatch mr) (mrAfter mr) next
          else (mod, current, col, this, countLines this)
               : go (mrMatch mr) (mrAfter mr) next
        | otherwise
        , let this = begin <> rest
        = [(mod, current, col, this, countLines this)]

countLines :: S -> Int
countLines = length . BS.lines . stripComments

stripComments :: S -> S
stripComments =
    BS.unlines .
    filter (not . BS.all isSpace) .
    BS.lines .
    del (mk "--") .
    del (mkM "\\(\\*.*?\\*\\)") .
    del (mkM "{-.*?-}")

del :: Regex -> S -> S
del r s | Just mr <- matchM r s
        = mrBefore mr <> del r (mrAfter mr)
        | otherwise
        = s

matchFirst :: [(Regex,a)] -> S -> Maybe (MatchResult S, a)
matchFirst regexes input
    = if null matches then Nothing else Just best
  where
    best = minimumBy (comparing (BS.length . mrBefore . fst)) matches
    matches = [ (mr, d) | (r,d) <- regexes, mr <- matchM r input]
