{-|
Module      : HsToCoq.Coq.Pretty
Description : An AST for Gallina, the surface language of Coq
Copyright   : Copyright © 2016 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental

-}

{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, OverloadedLists, LambdaCase, TemplateHaskell #-}

module HsToCoq.Coq.Pretty (
  renderGallina,
  showP, textP,
  Gallina(..),
  ) where

import Prelude hiding (Num)

import Data.Foldable
import HsToCoq.Util.Function

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as S

import Data.List.NonEmpty (NonEmpty(), (<|), nonEmpty)

import Data.Typeable
import Data.Data (Data(..))

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina.Orphans ()
import HsToCoq.PrettyPrint


-- https://coq.inria.fr/refman/Reference-Manual005.html#init-notations
-- todo: make PP monadic and update this table with new declarations?
-- The table is given in Coq levels, but stored in levels for our use
precTable :: [ (Qualid, (Int, Associativity)) ]
precTable =
    [ mkPrecEntry "<->" 95      NoAssociativity
    , mkPrecEntry "\\/" 85      RightAssociativity
    , mkPrecEntry "/\\" 80      RightAssociativity
    , mkPrecEntry "="   70      NoAssociativity
    , mkPrecEntry "<>"  70      NoAssociativity
    , mkPrecEntry "<"   70      NoAssociativity
    , mkPrecEntry ">"   70      NoAssociativity
    , mkPrecEntry "<="  70      NoAssociativity
    , mkPrecEntry ">="  70      NoAssociativity
    , mkPrecEntry "+"   50      LeftAssociativity
    , mkPrecEntry "||"  50      LeftAssociativity
    , mkPrecEntry "-"   50      LeftAssociativity
    , mkPrecEntry "*"   40      LeftAssociativity
    , mkPrecEntry "&&"  40      LeftAssociativity
    , mkPrecEntry "/"   40      LeftAssociativity
    , mkPrecEntry "^"   30      RightAssociativity
    ]
   where mkPrecEntry sym level assoc = (sym, (fromCoqLevel level, assoc))

-- precedence for various other expression forms
arrowPrec :: Int
arrowPrec = fromCoqLevel 90    -- right associative
  -- This number was found in here:
  -- https://github.com/coq/coq/blob/master/dev/doc/translate.txt#L95

appPrec   :: Int
appPrec   = fromCoqLevel 10    -- left associative

defaultOpPrec :: Int
defaultOpPrec = fromCoqLevel 99

scopePrec :: Int
scopePrec = fromCoqLevel 8   -- postfix, a%scope

funPrec   :: Int
funPrec   = fromCoqLevel 200

forallPrec :: Int
forallPrec = fromCoqLevel 200

matchPrec :: Int
matchPrec = fromCoqLevel 200

letPrec :: Int
letPrec = fromCoqLevel 200

ifPrec  :: Int
ifPrec  = fromCoqLevel 200

fixPrec :: Int
fixPrec = fromCoqLevel 200

castPrec :: Int
castPrec = fromCoqLevel 100

fromCoqLevel :: Int -> Int
fromCoqLevel cl = 400 - 2 * cl

-- Here are some precedence levels from Coq sources
-- https://github.com/coq/coq/blob/trunk/printing/ppconstr.ml
-- They do not apply directly to our pretty-printer, as the coq pretty-printer
-- function *returns* this precedence level that cause parenthesis to be added
-- if the context has a level lower than that. (hence latom = 0: Never add parens)
--
-- In our case, we *pass* a current levels as arguments and add parentheses when
-- the this level *exceeds* the level of the syntactic construct. Hence, for
-- atomic things, this level should be the maximum, 400.
--
-- We can thus transform a coq level to a level in our world using 400-2*coqLevel.
{-
latom = 0
lprod = 200
llambda = 200
lif = 200
lletin = 200
lletpattern = 200
lfix = 200
lcast = 100
larg = 9
lapp = 10
lposint = 0
lnegint = 35 -- (* must be consistent with Notation "- x" *)
ltop = 200
lproj = 1
ldelim = 1
lsimpleconstr = 8
lsimplepatt = 1
-}

parensN :: Doc -> Doc
parensN = parens . nest 1

maybeParen :: Bool -> Doc -> Doc
maybeParen True  = parensN
maybeParen False = id

class Gallina a where
  renderGallina' :: Int -> a -> Doc

textP :: Gallina a => a -> Text
textP = displayTStrict . renderOneLine . renderGallina

showP :: Gallina a => a -> String
showP = T.unpack . textP

renderGallina :: Gallina a => a -> Doc
renderGallina = renderGallina' 0

renderIdent :: Ident -> Doc
renderIdent = text

renderAccessIdent :: AccessIdent -> Doc
renderAccessIdent = text . T.cons '.'

renderModuleIdent :: ModuleIdent -> Doc
renderModuleIdent = text

renderNum :: Num -> Doc
renderNum = integer . toInteger

renderString :: Text -> Doc
renderString = dquotes . string .: T.concatMap $ \case
                 '"' -> "\"\""
                 c   -> T.singleton c

renderOp :: Op -> Doc
renderOp o = text $ o <> (if "." `T.isSuffixOf` o then "(**)" else "")
  -- [x .&. y] would be illegal, so print [x .&.(**) y]

renderQOp :: Qualid -> Doc
renderQOp qid = case qualidToOp qid of
    Just op -> renderOp op
    Nothing -> error $ "Cannot turn " ++ show qid ++ " into an operator"

renderQPrefix :: Qualid -> Doc
renderQPrefix qid = case qualidToPrefix qid of
    Just op -> renderOp op
    Nothing -> error $ "Cannot turn " ++ show qid ++ " into a prefix operator"

-- Module-local
render_type :: Term -> Doc
render_type ty = softline <> ":" <+> align (renderGallina ty)

-- Module-local
render_opt_type :: Maybe Term -> Doc
render_opt_type = maybe mempty render_type

-- Module-local
render_rtype :: Gallina a => a -> Doc
render_rtype rty = nest 2 $ softline <> "return" <+> renderGallina rty

-- Module-local
render_opt_rtype :: Gallina a => Maybe a -> Doc
render_opt_rtype = maybe mempty render_rtype

-- Module-local
render_in_annot :: Maybe (Qualid, [Pattern]) -> Doc
render_in_annot Nothing           = mempty
render_in_annot (Just (qid,pats)) = softline <> "in" <+> renderGallina qid
                                                     <+> render_args H pats

-- Module-local
data Orientation = H | V
                 deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- Module-local
ocat :: Foldable f => Orientation -> f Doc -> Doc
ocat H = fillSep
ocat V = vsep

-- Module-local
render_args :: (Functor f, Foldable f, Gallina a) => Orientation -> f a -> Doc
render_args = render_args' 0

-- Module-local
render_args' :: (Functor f, Foldable f, Gallina a) => Int -> Orientation -> f a -> Doc
render_args' p o = group . ocat o . fmap (renderGallina' p)


-- Module-local
render_args_ty :: (Functor f, Foldable f, Gallina a) => Orientation -> f a -> Term -> Doc
render_args_ty o args t = group $ render_args o args <$$> render_type t

-- Module-local
render_args_oty :: (Functor f, Foldable f, Gallina a) => Orientation -> f a -> Maybe Term -> Doc
render_args_oty o args ot = group $ render_args o args <$$> render_opt_type ot

-- Module-local
render_mutual_def :: Gallina a => Doc -> NonEmpty a -> [NotationBinding] -> Doc
render_mutual_def def bodies notations =
  def <+> lineSep "with" bodies
      <>  maybe mempty (((line <> "where") <+>) . lineSep "and  ") (nonEmpty notations)
      <> "."
  where
    lineSep sep = foldr1 (\body doc -> body <!> sep <+> doc) . fmap renderGallina

-- TODO: Precedence!
instance Gallina Term where
  renderGallina' p (Forall vars body) = maybeParen (p > forallPrec) $
    group $ "forall" <+> render_args V vars <> "," <!> renderGallina body

  -- Special case: Fun followed by a case with one pattern can use refutable syntax
  renderGallina' p (Fun vars (Match scruts Nothing [Equation mps body]))
    | check (toList vars) (toList scruts)
    , Just pats <- mapM (\mp -> do {MultPattern [pat] <- pure mp; pure pat}) mps
    = maybeParen (p > funPrec) $
      group $ "fun" <+> hcat (fmap (("'"<>) . parens . renderGallina) pats)
                    <+> nest 2 ("=>" <!> renderGallina' funPrec body)
    where fvs = getFreeVars body
          check (Inferred Explicit (Ident name) : vars) (MatchItem (Qualid v) Nothing Nothing:ss)
              = v `S.notMember` fvs  && name == v  && check vars ss
          check [] [] = True
          check _ _ = False

  renderGallina' p (Fun vars body) = maybeParen (p > funPrec) $
    group $ "fun" <+> render_args V vars <+> nest 2 ("=>" <!> renderGallina' funPrec body)

  renderGallina' p (Fix fbs) = group $ maybeParen (p > fixPrec) $
    "fix" <+> renderGallina fbs

  renderGallina' p (Cofix fbs) = group $ maybeParen (p > fixPrec) $
    "cofix" <+> renderGallina fbs

  -- the following are pattern synonyms and need to preceed the general Let case.
  renderGallina' p (LetFix def body) = group $ maybeParen (p > letPrec) $
    "let fix" <+> renderGallina def <+> "in" <!> align (renderGallina body)

  renderGallina' p (LetCofix def body) = group $ maybeParen (p > letPrec) $
    "let cofix" <+> renderGallina def <+> "in" <!> align (renderGallina body)

  renderGallina' p (Let var args oty val body) = group $ maybeParen (p > letPrec) $
         "let" <+> group (   renderGallina var
                         <>  spaceIf args <> render_args_oty V args oty
                         <+> nest 2 (":=" <!> renderGallina val))
               <+> "in"
    <!>  align (renderGallina body)

  renderGallina' p (LetTuple vars orty val body) = group $ maybeParen (p > letPrec) $
        "let" <+> group (   (parensN . commaList $ renderGallina <$> vars)
                        <>  render_opt_rtype orty
                        <+> nest 2 (":=" <!> renderGallina val))
    <+> "in" <!> align (renderGallina body)

  renderGallina' p (LetTick pat val body) = group $ maybeParen (p > letPrec) $
        "let" <+> align (group $   "'" <> align (renderGallina pat)
                               <+> nest 2 (":=" <!> renderGallina val))
    <+> "in" <!> align (renderGallina body)

  renderGallina' p (If SymmetricIf c odrty t f) = maybeParen (p > ifPrec) $
        "if"   <+> align (renderGallina c <> render_opt_rtype odrty)
    <!> "then" <+> align (renderGallina t)
    <!> "else" <+> align (renderGallina f)

  renderGallina' p (If LinearIf c odrty t f) = maybeParen (p > ifPrec) $ align $
    group ( "if"   <+> align (renderGallina c <> render_opt_rtype odrty)
        <!> "then" <+> align (renderGallina t) <+> "else")
    <!> align (renderGallina f)

  renderGallina' p (HasType tm ty) = maybeParen (p > castPrec) $
    renderGallina' (castPrec + 1) tm <+> ":" <+> renderGallina' castPrec ty

  renderGallina' p (CheckType tm ty) = maybeParen (p > castPrec) $
    renderGallina' (castPrec + 1) tm <+> "<:" <+> renderGallina' castPrec ty

  renderGallina' p (ToSupportType tm) = maybeParen (p > castPrec) $
    renderGallina' (castPrec + 1) tm <+> ":>"

  renderGallina' p (Arrow ty1 ty2) = maybeParen (p > arrowPrec) $ group $
    renderGallina' (arrowPrec + 1) ty1 <+> "->" <!> renderGallina' arrowPrec ty2

  -- Special notation for GHC.Num.fromInteger
  renderGallina' _ (App1 "GHC.Num.fromInteger" (Num num)) =
    char '#' <> renderNum num

  -- Special notation for somehting that looks like an operator an
  -- is applied to two arguments
  renderGallina' p (App2 (Qualid op) l r) | qualidIsOp op =
    case lookup op precTable of
      Just (n, LeftAssociativity)  ->
        maybeParen (n < p) $ group $
           renderGallina' n l </> renderQOp op <!> renderGallina' (n + 1) r
      Just (n, RightAssociativity) ->
        maybeParen (n < p) $ group $
           renderGallina' (n + 1) l </> renderQOp op <!> renderGallina' n r
      Just (n, NoAssociativity)    ->
        maybeParen (n < p) $ group $
           renderGallina' (n + 1) l </> renderQOp op <!> renderGallina' (n + 1) r
      Nothing                      ->
        maybeParen (p > defaultOpPrec) $ group $
           renderGallina' (defaultOpPrec + 1) l </> renderQOp op <!> renderGallina' (defaultOpPrec + 1) r

  renderGallina' p (App f args) =  maybeParen (p > appPrec) $
    let -- If we're providing a named argument, it turns out we can't use a
        -- notation, so we avoid doing that for operator names in that case.
        renderedFunction
          | Qualid qf <- f, any (\case NamedArg _ _ -> True ; _ -> False) args = renderGallina' appPrec qf
          | otherwise                                                          = renderGallina' appPrec f
    in renderedFunction </> align (render_args' (appPrec + 1) H args)

  renderGallina' _p (ExplicitApp qid args) = parensN $
    "@" <> renderGallina qid <> softlineIf args <> render_args' (appPrec + 1) H args

  renderGallina' p (InScope tm scope) = maybeParen (p > scopePrec) $
    renderGallina' scopePrec tm <> "%" <> renderIdent scope

  -- Special case the [let 'pat := scrut in body] syntax
  renderGallina' p (Match [scrut] Nothing [Equation [pat] body])
    = maybeParen (p > matchPrec) $
         "let" <+> nest 2 ("'" <> renderGallina pat <+> ":=" </> renderGallina scrut <+> "in")
          <!>  align (renderGallina body)

  renderGallina' p (Match discriminees orty eqns) = maybeParen (p > matchPrec) $
       "match" <+> align (  commaList (renderGallina <$> discriminees)
                          <> maybe mempty (\rty -> line <> renderGallina rty) orty)
               <+> "with"
    <> (case eqns of
          [] -> space
          _  -> (line <> "| " <> sepWith (<!>) (<+>) "|" (renderGallina <$> eqns))
             <> line)
    <> "end"

  renderGallina' p (Qualid qid)
    | qualidIsOp qid = renderQPrefix qid
    | otherwise      = renderGallina' p qid

  renderGallina' p (RawQualid qid) = renderGallina' p qid

  renderGallina' p (Sort sort) =
    renderGallina' p sort

  renderGallina' _ (Num num) =
    renderNum num

  renderGallina' _ (String str) =
    renderString str

  renderGallina' p (HsString str) =
    -- char '&' <> renderString str
    renderGallina' p (App (Qualid hs_stringQI) [PosArg (String str)])
    where
      hs_stringQI = Qualified "GHC.Base" "hs_string__"

  renderGallina' p (HsChar str) =
    -- string "&#" <> renderString (T.singleton str)
    renderGallina' p (App (Qualid hs_charQI) [PosArg (String (T.singleton str))])
    where
      hs_charQI = Qualified "GHC.Char" "hs_char__"

  renderGallina' _ Underscore =
    char '_'

  renderGallina' _ (Parens t) =
    parensN $ renderGallina t

  renderGallina' _ (Bang t) =
    char '!' <>  renderGallina t

  renderGallina' _ (Record defns) = nest 3 $
    "{|" <+> sepWith (<+>) (<!>) ";" (map (\(f,def) -> renderGallina f <+> ":=" <+> renderGallina def) defns)
        <+> "|}"

instance Gallina Arg where
  renderGallina' p (PosArg t) =
    renderGallina' p t
  renderGallina' _ (NamedArg name t) =
    hang 2 . parensN $ renderIdent name </> ":=" <+> align (renderGallina t)

-- Module-local
if_explicit :: Explicitness -> (Doc -> Doc) -> Doc -> Doc
if_explicit Explicit = ($)
if_explicit Implicit = const braces

-- Module-local
-- The 'Bool' is 'True' if parentheses are always necessary and 'False' otherwise.
binder_decoration :: Generalizability -> Explicitness -> Bool -> Doc -> Doc
binder_decoration Ungeneralizable ex b = if_explicit ex (if b then parensN else id)
binder_decoration Generalizable   ex _ = ("`" <>) . if_explicit ex parensN

instance Gallina Binder where
  renderGallina' _ (Inferred ex name)  =
    binder_decoration Ungeneralizable ex False $ renderGallina name
  renderGallina' _ (Typed gen ex names ty) =
    binder_decoration gen ex True $ render_args_ty H names ty
  renderGallina' _ (Generalized ex ty)  =
    binder_decoration Generalizable ex True $ renderGallina ty

instance Gallina Name where
  renderGallina' _ (Ident ident)  = renderGallina ident
  renderGallina' _ UnderscoreName = char '_'

instance Gallina Qualid where
  renderGallina' _ (Bare ident)        = renderIdent ident
  renderGallina' _ (Qualified mid aid) = renderModuleIdent mid <> renderAccessIdent aid

instance Gallina Sort where
  renderGallina' _ Prop = "Prop"
  renderGallina' _ Set  = "Set"
  renderGallina' _ Type = "Type"

instance Gallina FixBodies where
  renderGallina' p (FixOne fb) =
    renderGallina' p fb
  renderGallina' p (FixMany fb fbs var) =
    spacedSepPre "with" (align . renderGallina' p <$> fb <| fbs) </> "for" <+> renderGallina var

instance Gallina FixBody where
  renderGallina' _ (FixBody f args oannot oty def) =
    hang 2 $
      renderGallina f </> align (    fillSep (renderGallina <$> args)
                                </?> (renderGallina <$> oannot))
                      <>  render_opt_type oty <!> ":=" <+> align (renderGallina def)

instance Gallina MatchItem where
  renderGallina' _ (MatchItem scrutinee oas oin) =
    hang 2 $
      renderGallina' (letPrec + 1) scrutinee
        <> maybe mempty (\as -> softline <> "as" <+> renderGallina as) oas
        <> render_in_annot oin

instance Gallina DepRetType where
  renderGallina' _ (DepRetType oname rty) =
    maybe mempty (\name -> "as" <+> renderGallina name <> softline) oname <> renderGallina rty

instance Gallina ReturnType where
  renderGallina' _ (ReturnType ty) = "return" <+> align (renderGallina ty)

instance Gallina Equation where
  renderGallina' _ (Equation mps body) = nest 4 $ group $
    spacedSepPre "|" (align . renderGallina <$> mps) <+> "=>" <!>
    align (renderGallina body)

instance Gallina MultPattern where
  renderGallina' _ (MultPattern pats) = commaList $ renderGallina <$> pats

instance Gallina Pattern where
  renderGallina' _ (ArgsPat qid []) = renderGallina qid

  renderGallina' p (ArgsPat qid args) = maybeParen (p > appPrec) $
    renderGallina' appPrec qid </> render_args' (appPrec + 1) H args

  renderGallina' p (ExplicitArgsPat qid args) = maybeParen (p > appPrec) $
    "@" <> renderGallina' appPrec qid <> softlineIf args <> render_args' (appPrec +1) H args

  renderGallina' _p (InfixPat l op r) = parensN $ -- TODO precedence
    renderGallina l </> renderOp op </> renderGallina r

  renderGallina' _p (AsPat pat x) = parensN $
    renderGallina pat <+> "as" <+> renderGallina x

  renderGallina' _p (InScopePat pat scope) = parensN $
    renderGallina pat <> "%" <> renderIdent scope

  renderGallina' _p (QualidPat qid) =
    renderGallina qid

  renderGallina' _ (UnderscorePat) =
    char '_'

  renderGallina' _ (NumPat n) =
    renderNum n

  renderGallina' _ (StringPat s) =
    renderString s

  renderGallina' _ (OrPats orPats) =
    parensN . align . group $ sepWith (<>) (</>) "," (renderGallina <$> orPats)

instance Gallina OrPattern where
  renderGallina' _ (OrPattern pats) = spacedSepPre "|" (align . renderGallina <$> pats)

instance Gallina Comment where
  renderGallina' _ (Comment com) = "(* " <> align (fillSep . map (text . T.replace "*)" "* )") $ T.words com) <> " *)"

renderObligation :: Maybe Tactics -> Doc
renderObligation (Just "admit") = "Admit Obligations."
    -- Strangly, `Solve Obligations with (admit).` does not actually discharge
    -- the obligations; some Program mode weirdness. So lets use `Admit Obligations.`
renderObligation (Just t)       = "Solve Obligations with ("<> text t <>")."
renderObligation Nothing        = empty

instance Gallina Sentence where
  renderGallina' p (AssumptionSentence      ass)    = renderGallina' p ass
  renderGallina' p (DefinitionSentence      def)    = renderGallina' p def
  renderGallina' p (InductiveSentence       ind)    = renderGallina' p ind
  renderGallina' p (FixpointSentence        fix)    = renderGallina' p fix
  renderGallina' p (ProgramSentence         sen pf) = "Program" <+> renderGallina' p sen <!> renderObligation pf
  renderGallina' p (AssertionSentence       ass pf) = renderGallina' p ass <!> renderGallina' p pf
  renderGallina' p (ModuleSentence          mod)    = renderGallina' p mod
  renderGallina' p (ClassSentence           cls)    = renderGallina' p cls
  renderGallina' p (RecordSentence          rcd)    = renderGallina' p rcd
  renderGallina' p (InstanceSentence        ins)    = renderGallina' p ins
  renderGallina' p (NotationSentence        not)    = renderGallina' p not
  renderGallina' p (ArgumentsSentence       arg)    = renderGallina' p arg
  renderGallina' p (CommentSentence         com)    = renderGallina' p com
  renderGallina' p (LocalModuleSentence     lmd)    = renderGallina' p lmd

instance Gallina Assumption where
  renderGallina' p (Assumption kw ass) = renderGallina' p kw <+> align (renderGallina ass) <> "."

instance Gallina AssumptionKeyword where
  renderGallina' _ Axiom      = "Axiom"
  renderGallina' _ Axioms     = "Axioms"
  renderGallina' _ Conjecture = "Conjecture"
  renderGallina' _ Parameter  = "Parameter"
  renderGallina' _ Parameters = "Parameters"
  renderGallina' _ Variable   = "Variable"
  renderGallina' _ Variables  = "Variables"
  renderGallina' _ Hypothesis = "Hypothesis"
  renderGallina' _ Hypotheses = "Hypotheses"

instance Gallina Assums where
  renderGallina' _ (Assums ids ty) = renderAss ids ty
    where
      renderAss ids ty = fillSep (renderGallina <$> ids) <> nest 2 (render_type ty)

instance Gallina Locality where
  renderGallina' _ Global = "(*Global*)"
  renderGallina' _ Local  = "Local"

renderLocality :: Locality -> Doc
renderLocality Global = empty
renderLocality Local  = "Local" <> space

renderFullLocality :: Maybe Locality -> Doc
renderFullLocality Nothing       = empty
renderFullLocality (Just Global) = "Global" <> space
renderFullLocality (Just Local)  = "Local"  <> space

instance Gallina Definition where
  renderGallina' _ = \case
    DefinitionDef loc name args oty body ex -> renderDef (renderLocality loc <> "Definition") name args oty body
                                           <$$> renderEx ex name
    LetDef            name args oty body -> renderDef "Let"                                name args oty body
    where
      renderEx NotExistingClass _ = mempty
      renderEx ExistingClass qid  = "Existing Class" <+> renderGallina qid <> "."
      renderDef def name args oty body =
        hang 2 ((def <+> renderGallina name
                     <>  spaceIf args <> render_args_oty H args oty
                     <+> ":=") <$$> renderGallina body <>  ".")

instance Gallina Inductive where
  renderGallina' _ (Inductive   bodies nots) = render_mutual_def "Inductive"   bodies nots
  renderGallina' _ (CoInductive bodies nots) = render_mutual_def "CoInductive" bodies nots

instance Gallina IndBody where
  renderGallina' _ (IndBody name params ty cons) = nest 2 $ group $
    renderGallina name <> spaceIf params <> render_args_ty H params ty
                       <!> renderCons cons
    where
      renderCons []         = ":="
      renderCons (con:cons) = align $ foldl' (<!>) (renderCon ":= |" con) (renderCon "| " <$> cons)

      renderCon delim (cname, cargs, coty) =
        delim <+> renderGallina cname <> spaceIf cargs <> render_args_oty H cargs coty

instance Gallina Fixpoint where
  renderGallina' _ (Fixpoint   bodies nots) = render_mutual_def "Fixpoint"   bodies nots
  renderGallina' _ (CoFixpoint bodies nots) = render_mutual_def "CoFixpoint" bodies nots

instance Gallina Order where
  renderGallina' _ (StructOrder var) = braces $
    "struct" <+> renderGallina var
  renderGallina' _ (MeasureOrder expr rel) = braces $
    "measure" <+> renderGallina' (appPrec+1) expr <+> maybe empty (parensN . renderGallina) rel
  renderGallina' _ (WFOrder rel ident) = braces $
    "wf" <+> renderGallina' (appPrec+1) rel <+> renderGallina ident


instance Gallina Assertion where
  renderGallina' _ (Assertion kw name args ty) =
    renderGallina kw <+> renderGallina name <> spaceIf args <> group (render_args V args)
                     <+> group (nest 2 $ ":" </> renderGallina ty)
                     <>  "."

instance Gallina AssertionKeyword where
  renderGallina' _ Theorem      = "Theorem"
  renderGallina' _ Lemma        = "Lemma"
  renderGallina' _ Remark       = "Remark"
  renderGallina' _ Fact         = "Fact"
  renderGallina' _ Corollary    = "Corollary"
  renderGallina' _ Proposition  = "Proposition"
  renderGallina' _ Definition   = "Definition"
  renderGallina' _ Example      = "Example"

instance Gallina Proof where
  renderGallina' _ = \case
    ProofQed      body -> renderProof "Qed"      body
    ProofDefined  body -> renderProof "Defined"  body
    ProofAdmitted body -> renderProof "Admitted" body
    where
      renderProof end body = "Proof." <!> string body <!> end <> "."

instance Gallina ImportExport where
  renderGallina' _ Import = "Import"
  renderGallina' _ Export = "Export"

instance Gallina ModuleSentence where
  renderGallina' _ (ModuleImport ie mods) =
    renderGallina ie <+> align (fillSep $ renderModuleIdent <$> mods) <> "."
  renderGallina' _ (Require mfrom mie mods) =
       (("From" <+>) . renderModuleIdent) ?? mfrom
    <> "Require" <+> renderGallina ?? mie
    <> align (fillSep $ renderModuleIdent <$> mods) <> "."
    where render ?? mx = maybe mempty render mx <> spaceIf mx
          infix 9 ??
  renderGallina' _ (ModuleAssignment modNew modOld) =
    "Module" <+> renderModuleIdent modNew <+> nest 2 (":=" </> renderModuleIdent modOld <> ".")

instance Gallina ClassDefinition where
  renderGallina' _ (ClassDefinition cl params osort fields) =
    "Class" <+> renderGallina cl <> spaceIf params <> render_args_oty H params (Sort <$> osort)
            <+> nest 2 (":=" </> "{" <> lineIf fields
                                     <> sepWith (<+>) (<!>) ";" (map (\(f,ty) -> renderGallina f <+> ":" <+> renderGallina ty) fields)
                                     <> spaceIf fields <> "}.")

instance Gallina RecordDefinition where
  renderGallina' _ (RecordDefinition cl params osort build fields) =
    "Record" <+> renderGallina cl <> spaceIf params <> render_args_oty H params (Sort <$> osort)
            <+> nest 2 (":=" </> maybe empty renderGallina build <+>
                                 "{" <> lineIf fields
                                     <> sepWith (<+>) (<!>) ";" (map (\(f,ty) -> renderGallina f <+> ":" <+> renderGallina ty) fields)
                                     <> spaceIf fields <> "}.")

instance Gallina InstanceDefinition where
  renderGallina' _ (InstanceDefinition inst params cl defns mpf) = (group $ nest 2 $
    "Instance" <+> renderGallina inst <> spaceIf params <> render_args_ty H params cl <+> ":="
        <!> "{" <> lineIf defns
                <> sepWith (<+>) (<!>) ";" (map (\(f,def) -> renderGallina f <+> ":=" <+> renderGallina def) defns)
                <> spaceIf defns <> "}."
    ) <!> maybe empty renderGallina mpf
  renderGallina' _ (InstanceTerm inst params cl term mpf) = (group $ nest 2 $
    "Instance" <+> renderGallina inst <> spaceIf params <> render_args_ty H params cl <+> ":="
        <!> renderGallina term <> "."
    ) <!> maybe empty renderGallina mpf

instance Gallina Associativity where
  renderGallina' _ LeftAssociativity  = "left"
  renderGallina' _ RightAssociativity = "right"
  renderGallina' _ NoAssociativity    = "no"

instance Gallina Level where
  renderGallina' _ (Level n) = "at level" <+> renderNum n

instance Gallina Notation where
  renderGallina' _ (ReservedNotationIdent x) =
    "Reserved" <+> "Notation" <+> dquotes (squotes $ renderIdent x) <> "."
  renderGallina' _ (NotationBinding nb) =
    "Notation" <+> renderGallina nb <> "."
  renderGallina' _ (InfixDefinition op def oassoc level) =
    "Infix" <+> dquotes (renderOp op) <+> ":="
      </> nest 2 (parensN (renderGallina def) </> parensN (assoc <> renderGallina level) <> ".")
    where assoc = maybe mempty (\assoc -> renderGallina assoc <+> "associativity," <> softline) oassoc

instance Gallina NotationBinding where
  renderGallina' _ (NotationIdentBinding x def) =
    dquotes (squotes $ renderIdent x) <+> nest 2 (":=" </> parensN (renderGallina def))

-- TODO: Collapse successive arguments with the same spec?
instance Gallina Arguments where
  renderGallina' _ (Arguments floc qid args) =
    renderFullLocality floc <> "Arguments" <+> renderGallina qid <> softlineIf args <> render_args H args <> "."

instance Gallina ArgumentSpec where
  renderGallina' _ (ArgumentSpec eim arg oscope) =
    let wrap = case eim of
                 ArgExplicit -> id
                 ArgImplicit -> brackets
                 ArgMaximal  -> braces
    in wrap (renderGallina arg) <> maybe mempty (("%" <>) . renderIdent) oscope

instance Gallina LocalModule where
  renderGallina' _ (LocalModule name sentences) = vcat $
    [ "Module" <+> text name <> "." ] ++
    [ renderGallina s | s <- sentences ] ++
    [ "End" <+> text name <> "." ]


{- Do we really use this?

-- Make all 'Gallina' types 'Pretty' types in the default way
let abort = fail "Internal error: unexpected result from `reify'" in
  TH.reify ''Gallina >>= \case
    TH.ClassI _ is ->
      forFold is $ \case
        TH.InstanceD _ _ (TH.AppT (TH.ConT _gallina) ty) _ ->
          [d|instance Pretty $(pure ty) where pretty = renderGallina|]
        _ -> abort
    _ -> abort
-}
