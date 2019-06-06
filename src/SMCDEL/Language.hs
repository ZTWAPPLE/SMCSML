{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses  #-}

module SMCDEL.Language where

import Data.List (nub,intercalate,(\\))
import Data.Maybe (fromMaybe)

import Test.QuickCheck
import SMCDEL.Internal.Help (powerset)
import SMCDEL.Internal.TexDisplay

newtype Prp = P Int deriving (Eq,Ord,Show)

instance Enum Prp where
  toEnum = P
  fromEnum (P n) = n

instance Arbitrary Prp where
  arbitrary = P <$> choose (0,4)

freshp :: [Prp] -> Prp
freshp [] = P 1
freshp prps = P (maximum (map fromEnum prps) + 1)

class HasVocab a where
  vocabOf :: a -> [Prp]

type Agent = String

alice,bob,carol :: Agent
alice = "Alice"
bob   = "Bob"
carol = "Carol"

newtype AgAgent = Ag Agent deriving (Eq,Ord,Show)

instance Arbitrary AgAgent where
  arbitrary = oneof $ map (pure . Ag . show) [1..(5::Integer)]

class HasAgents a where
  agentsOf :: a -> [Agent]

class Pointed a b

instance (HasVocab a, Pointed a b) => HasVocab (a,b) where vocabOf = vocabOf . fst

instance (HasAgents a, Pointed a b) => HasAgents (a,b) where agentsOf = agentsOf . fst

newtype Group = Group [Agent] deriving (Eq,Ord,Show)

-- generate a non-empty group of up to 5 agents
instance Arbitrary Group where
  arbitrary = fmap (Group.("1":)) $ sublistOf $ map show [2..(5::Integer)]

data Form
  = Top                           -- ^ True Constant
  | Bot                           -- ^ False Constant
  | PrpF Prp                      -- ^ Atomic Proposition
  | Neg Form                      -- ^ Negation
  | Conj [Form]                   -- ^ Conjunction
  | Disj [Form]                   -- ^ Disjunction
  | Xor [Form]                    -- ^ n-ary X-OR
  | Impl Form Form                -- ^ Implication
  | Equi Form Form                -- ^ Bi-Implication
  | Forall [Prp] Form             -- ^ Boolean Universal Quantification
  | Exists [Prp] Form             -- ^ Boolean Existential Quantification
  | K Agent Form                  -- ^ Knowing that
  | Ck [Agent] Form               -- ^ Common knowing that
  | Kw Agent Form                 -- ^ Knowing whether
  | Ckw [Agent] Form              -- ^ Common knowing whether
  | PubAnnounce Form Form         -- ^ Public announcement that
  | PubAnnounceW Form Form        -- ^ Public announcement whether
  | Announce [Agent] Form Form    -- ^ (Semi-)Private announcement that
  | AnnounceW [Agent] Form Form   -- ^ (Semi-)Private announcement whether
  | SabotageALE Agent Form Form   -- ^ Deletion of all local edges of the required condition
  | SabotageOLE Agent Form Form   -- ^ Deletion of any local edge of the required condition
  | SabotageAGE Agent Form Form   -- ^ Deletion of all global edges of the required condition
  | SabotageOGE Agent Form Form   -- ^ Deletion of any global edge of the required condition
  | SabotageALV Agent Form Form   -- ^ Deletion of all local vertices of the required condition
  | SabotageOLV Agent Form Form   -- ^ Deletion of any local vertice of the required condition
  | SabotageOGV Agent Form Form   -- ^ Deletion of any global vertice of the required condition
  deriving (Eq,Ord,Show)

class HasVocab a => Semantics a where
  isTrue :: a -> Form -> Bool

class Optimizable a where
  optimize :: [Prp] -> a -> a

class HasPrecondition a where
  preOf :: a -> Form

-- | Formulas used as public announcements are their own precondition.
instance HasPrecondition Form where
  preOf = id

class (HasAgents a, Semantics a, HasPrecondition b) => Update a b where
  {-# MINIMAL unsafeUpdate #-}
  unsafeUpdate :: a -> b -> a
  checks :: [a -> b -> Bool]
  checks = [preCheck]
  preCheck :: a -> b -> Bool
  preCheck x y = isTrue x (preOf y)
  update :: a -> b -> a
  update x y = if and checkResults
                 then unsafeUpdate x y
                 else error $ "Update failed. Checks: " ++ show checkResults
               where checkResults = [ c x y | c <- checks ]

updates :: Update a b => a -> [b] -> a
updates = foldl update

haveSameAgents :: (HasAgents a, HasAgents b) => a -> b -> Bool
haveSameAgents x y = agentsOf x == agentsOf y

showSet :: Show a => [a] -> String
showSet xs = intercalate "," (map show xs)

-- | Pretty print a formula, possibly with a translation for atoms:
ppForm :: Form -> String
ppForm = ppFormWith (\(P n) -> show n)

ppFormWith :: (Prp -> String)-> Form -> String
ppFormWith _     Top           = "T"
ppFormWith _     Bot           = "F"
ppFormWith trans (PrpF p)      = trans p
ppFormWith trans (Neg f)       = "~" ++ ppFormWith trans f
ppFormWith trans (Conj fs)     = "(" ++ intercalate " & " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Disj fs)     = "(" ++ intercalate " | " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Xor fs)      = "XOR{" ++ showSet (map (ppFormWith trans) fs) ++ "}"
ppFormWith trans (Impl f g)    = "(" ++ ppFormWith trans f ++ "->" ++ ppFormWith trans g ++ ")"
ppFormWith trans (Equi f g)    = ppFormWith trans f ++ "=" ++ ppFormWith trans g
ppFormWith trans (Forall ps f) = "Forall {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (Exists ps f) = "Exists {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (K i f)       = "K " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ck is f)     = "Ck " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (Kw i f)      = "Kw " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ckw is f)    = "Ckw " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (PubAnnounce f g)  = "[! " ++ ppFormWith trans f ++ "] " ++ ppFormWith trans g
ppFormWith trans (PubAnnounceW f g) = "[?! " ++ ppFormWith trans f ++ "] " ++ ppFormWith trans g
ppFormWith trans (Announce is f g)  = "[" ++ intercalate ", " is ++ " ! " ++ ppFormWith trans f ++ "]" ++ ppFormWith trans g
ppFormWith trans (AnnounceW is f g) = "[" ++ intercalate ", " is ++ " ?! " ++ ppFormWith trans f ++ "]" ++ ppFormWith trans g
ppFormWith trans (SabotageOGV i f g) = "[-" ++ ppFormWith trans f ++ "]_OGV " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageOLV i f g) = "[-" ++ ppFormWith trans f ++ "]_OLV " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageALV i f g) = "[-" ++ ppFormWith trans f ++ "]_ALV " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageOGE i f g) = "[-" ++ ppFormWith trans f ++ "]_OGE " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageAGE i f g) = "[-" ++ ppFormWith trans f ++ "]_AGE " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageOLE i f g) = "[-" ++ ppFormWith trans f ++ "]_OLE " ++ i ++ " " ++ ppFormWith trans g
ppFormWith trans (SabotageALE i f g) = "[-" ++ ppFormWith trans f ++ "]_ALE " ++ i ++ " " ++ ppFormWith trans g

pubAnnounceStack :: [Form] -> Form -> Form
pubAnnounceStack = flip $ foldr PubAnnounce

pubAnnounceWhetherStack :: [Form] -> Form -> Form
pubAnnounceWhetherStack = flip $ foldr PubAnnounceW

booloutofForm :: [Prp] -> [Prp] -> Form
booloutofForm ps qs = Conj $ [ PrpF p | p <- ps ] ++ [ Neg $ PrpF r | r <- qs \\ ps ]

subformulas :: Form -> [Form]
subformulas Top           = [Top]
subformulas Bot           = [Bot]
subformulas (PrpF p)      = [PrpF p]
subformulas (Neg f)       = Neg f : subformulas f
subformulas (Conj fs)     = Conj fs : nub (concatMap subformulas fs)
subformulas (Disj fs)     = Disj fs : nub (concatMap subformulas fs)
subformulas (Xor fs)      = Xor  fs : nub (concatMap subformulas fs)
subformulas (Impl f g)    = Impl f g : nub (concatMap subformulas [f,g])
subformulas (Equi f g)    = Equi f g : nub (concatMap subformulas [f,g])
subformulas (Forall ps f) = Forall ps f : subformulas f
subformulas (Exists ps f) = Exists ps f : subformulas f
subformulas (K i f)       = K i f : subformulas f
subformulas (Ck is f)     = Ck is f : subformulas f
subformulas (Kw i f)      = Kw i f : subformulas f
subformulas (Ckw is f)    = Ckw is f : subformulas f
subformulas (PubAnnounce  f g) = PubAnnounce  f g : nub (subformulas f ++ subformulas g)
subformulas (PubAnnounceW f g) = PubAnnounceW f g : nub (subformulas f ++ subformulas g)
subformulas (Announce  is f g) = Announce  is f g : nub (subformulas f ++ subformulas g)
subformulas (AnnounceW is f g) = AnnounceW is f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageALE i f g) = SabotageALE i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageOLE i f g) = SabotageOLE i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageAGE i f g) = SabotageAGE i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageOGE i f g) = SabotageOGE i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageALV i f g) = SabotageALV i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageOLV i f g) = SabotageOLV i f g : nub (subformulas f ++ subformulas g)
subformulas (SabotageOGV i f g) = SabotageOGV i f g : nub (subformulas f ++ subformulas g)

shrinkform :: Form -> [Form]
shrinkform f =
  if f /= simplify f
    then [simplify f]
    else (subformulas f \\ [f]) ++ otherShrinks f
  where
    otherShrinks (Conj     fs) = [Conj     gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Disj     fs) = [Disj     gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Xor      fs) = [Xor      gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Ck     is g) = [Ck     js g | js <- powerset is \\ [is]]
    otherShrinks (Ckw    is g) = [Ckw    js g | js <- powerset is \\ [is]]
    otherShrinks (Forall ps g) = [Forall qs g | qs <- powerset ps \\ [ps]]
    otherShrinks (Exists ps g) = [Exists qs g | qs <- powerset ps \\ [ps]]
    otherShrinks _ = []

substit :: Prp -> Form -> Form -> Form
substit _ _   Top           = Top
substit _ _   Bot           = Bot
substit q psi (PrpF p)      = if p==q then psi else PrpF p
substit q psi (Neg form)    = Neg (substit q psi form)
substit q psi (Conj forms)  = Conj (map (substit q psi) forms)
substit q psi (Disj forms)  = Disj (map (substit q psi) forms)
substit q psi (Xor  forms)  = Xor  (map (substit q psi) forms)
substit q psi (Impl f g)    = Impl (substit q psi f) (substit q psi g)
substit q psi (Equi f g)    = Equi (substit q psi f) (substit q psi g)
substit q psi (Forall ps f) = if q `elem` ps
  then error ("substit failed: Substituens "++ show q ++ " in 'Forall " ++ show ps ++ " " ++ show f)
  else Forall ps (substit q psi f)
substit q psi (Exists ps f) = if q `elem` ps
  then error ("substit failed: Substituens " ++ show q ++ " in 'Exists " ++ show ps ++ " " ++ show f)
  else Exists ps (substit q psi f)
substit q psi (K  i f)     = K  i (substit q psi f)
substit q psi (Kw i f)     = Kw i (substit q psi f)
substit q psi (Ck ags f)   = Ck ags (substit q psi f)
substit q psi (Ckw ags f)  = Ckw ags (substit q psi f)
substit q psi (PubAnnounce f g)   = PubAnnounce (substit q psi f) (substit q psi g)
substit q psi (PubAnnounceW f g)  = PubAnnounceW (substit q psi f) (substit q psi g)
substit q psi (Announce ags f g)  = Announce ags (substit q psi f) (substit q psi g)
substit q psi (AnnounceW ags f g) = AnnounceW ags (substit q psi f) (substit q psi g)
substit q psi (SabotageALE i f g) = SabotageALE i (substit q psi f) (substit q psi g)
substit q psi (SabotageOLE i f g) = SabotageOLE i (substit q psi f) (substit q psi g)
substit q psi (SabotageAGE i f g) = SabotageAGE i (substit q psi f) (substit q psi g)
substit q psi (SabotageOGE i f g) = SabotageOGE i (substit q psi f) (substit q psi g)
substit q psi (SabotageALV i f g) = SabotageALV i (substit q psi f) (substit q psi g)
substit q psi (SabotageOLV i f g) = SabotageOLV i (substit q psi f) (substit q psi g)
substit q psi (SabotageOGV i f g) = SabotageOGV i (substit q psi f) (substit q psi g)

substitSet :: [(Prp,Form)] -> Form -> Form
substitSet [] f = f
substitSet ((q,psi):rest) f = substitSet rest (substit q psi f)

substitOutOf :: [Prp] -> [Prp] -> Form -> Form
substitOutOf truths allps = substitSet [(p, if p `elem` truths then Top else Bot) | p <- allps]

replPsInP :: [(Prp,Prp)] -> Prp -> Prp
replPsInP repl p = fromMaybe p (lookup p repl)

replPsInF :: [(Prp,Prp)] -> Form -> Form
replPsInF _       Top      = Top
replPsInF _       Bot      = Bot
replPsInF repl (PrpF p)    = PrpF $ replPsInP repl p
replPsInF repl (Neg f)     = Neg $ replPsInF repl f
replPsInF repl (Conj fs)   = Conj $ map (replPsInF repl) fs
replPsInF repl (Disj fs)   = Disj $ map (replPsInF repl) fs
replPsInF repl (Xor  fs)   = Xor  $ map (replPsInF repl) fs
replPsInF repl (Impl f g)  = Impl (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Equi f g)  = Equi (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Forall ps f) = Forall (map (replPsInP repl) ps) (replPsInF repl f)
replPsInF repl (Exists ps f) = Exists (map (replPsInP repl) ps) (replPsInF repl f)
replPsInF repl (K i f)     = K i (replPsInF repl f)
replPsInF repl (Kw i f)    = Kw i (replPsInF repl f)
replPsInF repl (Ck ags f)  = Ck ags (replPsInF repl f)
replPsInF repl (Ckw ags f) = Ckw ags (replPsInF repl f)
replPsInF repl (PubAnnounce f g)   = PubAnnounce   (replPsInF repl f) (replPsInF repl g)
replPsInF repl (PubAnnounceW f g)  = PubAnnounceW  (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Announce ags f g)  = Announce  ags (replPsInF repl f) (replPsInF repl g)
replPsInF repl (AnnounceW ags f g) = AnnounceW ags (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageALE i f g) = SabotageALE i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageOLE i f g) = SabotageOLE i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageAGE i f g) = SabotageAGE i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageOGE i f g) = SabotageOGE i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageALV i f g) = SabotageALV i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageOLV i f g) = SabotageOLV i (replPsInF repl f) (replPsInF repl g)
replPsInF repl (SabotageOGV i f g) = SabotageOGV i (replPsInF repl f) (replPsInF repl g)

propsInForm :: Form -> [Prp]
propsInForm Top                = []
propsInForm Bot                = []
propsInForm (PrpF p)           = [p]
propsInForm (Neg f)            = propsInForm f
propsInForm (Conj fs)          = nub $ concatMap propsInForm fs
propsInForm (Disj fs)          = nub $ concatMap propsInForm fs
propsInForm (Xor  fs)          = nub $ concatMap propsInForm fs
propsInForm (Impl f g)         = nub $ concatMap propsInForm [f,g]
propsInForm (Equi f g)         = nub $ concatMap propsInForm [f,g]
propsInForm (Forall ps f)      = nub $ ps ++ propsInForm f
propsInForm (Exists ps f)      = nub $ ps ++ propsInForm f
propsInForm (K _ f)            = propsInForm f
propsInForm (Kw _ f)           = propsInForm f
propsInForm (Ck _ f)           = propsInForm f
propsInForm (Ckw _ f)          = propsInForm f
propsInForm (Announce _ f g)   = nub $ propsInForm f ++ propsInForm g
propsInForm (AnnounceW _ f g)  = nub $ propsInForm f ++ propsInForm g
propsInForm (PubAnnounce f g)  = nub $ propsInForm f ++ propsInForm g
propsInForm (PubAnnounceW f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageALE _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageOLE _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageAGE _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageOGE _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageALV _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageOLV _ f g) = nub $ propsInForm f ++ propsInForm g
propsInForm (SabotageOGV _ f g) = nub $ propsInForm f ++ propsInForm g

propsInForms :: [Form] -> [Prp]
propsInForms fs = nub $ concatMap propsInForm fs

instance TexAble Prp where
  tex (P 0) = " p "
  tex (P n) = " p_{" ++ show n ++ "} "

instance TexAble [Prp] where
  tex [] = " \\varnothing "
  tex ps = "\\{" ++ intercalate "," (map tex ps) ++ "\\}"

simplify :: Form -> Form
simplify f = if simStep f == f then f else simplify (simStep f)

simStep :: Form -> Form
simStep Top           = Top
simStep Bot           = Bot
simStep (PrpF p)      = PrpF p
simStep (Neg Top)     = Bot
simStep (Neg Bot)     = Top
simStep (Neg (Neg f)) = simStep f
simStep (Neg f)       = Neg $ simStep f
simStep (Conj [])     = Top
simStep (Conj [f])    = simStep f
simStep (Conj fs)     | Bot `elem` fs = Bot
                      | or [ Neg f `elem` fs | f <- fs ] = Bot
                      | otherwise     = Conj (nub $ concatMap unpack fs) where
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
simStep (Disj [])     = Bot
simStep (Disj [f])    = simStep f
simStep (Disj fs)     | Top `elem` fs = Top
                      | or [ Neg f `elem` fs | f <- fs ] = Top
                      | otherwise     = Disj (nub $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Xor  [])     = Bot
simStep (Xor  [Bot])  = Bot
simStep (Xor  [f])    = simStep f
simStep (Xor  fs)     = Xor (map simStep $ filter (Bot /=) fs)
simStep (Impl Bot _)  = Top
simStep (Impl _ Top)  = Top
simStep (Impl Top f)  = simStep f
simStep (Impl f Bot)  = Neg (simStep f)
simStep (Impl f g)    | f==g      = Top
                      | otherwise = Impl (simStep f) (simStep g)
simStep (Equi Top f)  = simStep f
simStep (Equi Bot f)  = Neg (simStep f)
simStep (Equi f Top)  = simStep f
simStep (Equi f Bot)  = Neg (simStep f)
simStep (Equi f g)    | f==g      = Top
                      | otherwise = Equi (simStep f) (simStep g)
simStep (Forall ps f) = Forall ps (simStep f)
simStep (Exists ps f) = Exists ps (simStep f)
simStep (K a f)       = K a (simStep f)
simStep (Kw a f)      = Kw a (simStep f)
simStep (Ck _   Top)  = Top
simStep (Ck _   Bot)  = Bot
simStep (Ck ags f)    = Ck ags (simStep f)
simStep (Ckw _   Top) = Top
simStep (Ckw _   Bot) = Top
simStep (Ckw ags f)   = Ckw ags (simStep f)
simStep (PubAnnounce Top f) = simStep f
simStep (PubAnnounce Bot _) = Top
simStep (PubAnnounce  f g)  = PubAnnounce  (simStep f) (simStep g)
simStep (PubAnnounceW f g)  = PubAnnounceW (simStep f) (simStep g)
simStep (Announce  ags f g) = Announce  ags (simStep f) (simStep g)
simStep (AnnounceW ags f g) = AnnounceW ags (simStep f) (simStep g)
simStep (SabotageALE i f g) = SabotageALE i (simStep f) (simStep g)
simStep (SabotageOLE i f g) = SabotageOLE i (simStep f) (simStep g)
simStep (SabotageAGE i f g) = SabotageAGE i (simStep f) (simStep g)
simStep (SabotageOGE i f g) = SabotageOGE i (simStep f) (simStep g)
simStep (SabotageALV i f g) = SabotageALV i (simStep f) (simStep g)
simStep (SabotageOLV i f g) = SabotageOLV i (simStep f) (simStep g)
simStep (SabotageOGV i f g) = SabotageOGV i (simStep f) (simStep g)

texForm :: Form -> String
texForm Top           = "\\top "
texForm Bot           = "\\bot "
texForm (PrpF p)      = tex p
texForm (Neg (PubAnnounce f (Neg g))) = "\\langle !" ++ texForm f ++ " \\rangle " ++ texForm g
texForm (Neg f)       = "\\lnot " ++ texForm f
texForm (Conj [])     = "\\top "
texForm (Conj [f])    = texForm f
texForm (Conj [f,g])  = " ( " ++ texForm f ++ " \\land " ++ texForm g ++" ) "
texForm (Conj fs)     = "\\bigwedge \\{\n" ++ intercalate "," (map texForm fs) ++" \\} "
texForm (Disj [])     = "\\bot "
texForm (Disj [f])    = texForm f
texForm (Disj [f,g])  = " ( " ++ texForm f ++ " \\lor "++ texForm g ++ " ) "
texForm (Disj fs)     = "\\bigvee \\{\n " ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Xor [])      = "\\bot "
texForm (Xor [f])     = texForm f
texForm (Xor [f,g])   = " ( " ++ texForm f  ++ " \\oplus " ++ texForm g ++ " ) "
texForm (Xor fs)      = "\\bigoplus \\{\n" ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Equi f g)    = " ( "++ texForm f ++" \\leftrightarrow "++ texForm g ++" ) "
texForm (Impl f g)    = " ( "++ texForm f ++" \\rightarrow "++ texForm g ++" ) "
texForm (Forall ps f) = " \\forall " ++ tex ps ++ " " ++ texForm f
texForm (Exists ps f) = " \\exists " ++ tex ps ++ " " ++ texForm f
texForm (K i f)       = "K_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Kw i f)      = "K^?_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Ck ags f)    = "Ck_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (Ckw ags f)   = "Ck^?_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (PubAnnounce f g)   = "[!" ++ texForm f ++ "] " ++ texForm g
texForm (PubAnnounceW f g)  = "[?!" ++ texForm f ++ "] " ++ texForm g
texForm (Announce ags f g)  = "[" ++ intercalate "," ags ++ "!" ++ texForm f ++ "] " ++ texForm g
texForm (AnnounceW ags f g) = "[" ++ intercalate "," ags ++ "?!" ++ texForm f ++ "] " ++ texForm g
texForm (SabotageALE i f g) = "["  ++ texForm f ++ "]_{ALE}^" ++ i ++ " " ++ texForm g
texForm (SabotageOLE i f g) = "["  ++ texForm f ++ "]_{OLE}^" ++ i ++ " " ++ texForm g
texForm (SabotageAGE i f g) = "["  ++ texForm f ++ "]_{AGE}^" ++ i ++ " " ++ texForm g
texForm (SabotageOGE i f g) = "["  ++ texForm f ++ "]_{OGE}^" ++ i ++ " " ++ texForm g
texForm (SabotageALV i f g) = "["  ++ texForm f ++ "]_{ALV}^" ++ i ++ " " ++ texForm g
texForm (SabotageOLV i f g) = "["  ++ texForm f ++ "]_{OLV}^" ++ i ++ " " ++ texForm g
texForm (SabotageOGV i f g) = "["  ++ texForm f ++ "]_{OGV}^" ++ i ++ " " ++ texForm g

instance TexAble Form where
  tex = removeDoubleSpaces . texForm

testForm :: Form
testForm = Forall [P 3] $
  Equi
    (Disj [ Bot, PrpF $ P 3, Bot ])
    (Conj [ Top
          , Xor [Top,Kw alice (PrpF (P 4))]
          , AnnounceW [alice,bob] (PrpF (P 5)) (Kw bob $ PrpF (P 5)) ])

newtype BF = BF Form deriving (Eq,Ord,Show)

instance Arbitrary BF where
  arbitrary = sized $ randomboolformWith [P 1 .. P 100]
  shrink (BF f) = map BF $ shrinkform f

randomboolformWith :: [Prp] -> Int -> Gen BF
randomboolformWith allprops sz = BF <$> bf' sz where
  bf' 0 = PrpF <$> elements allprops
  bf' n = oneof [ pure SMCDEL.Language.Top
                , pure SMCDEL.Language.Bot
                , PrpF <$> elements allprops
                , Neg <$> st
                , (\x y -> Conj [x,y]) <$> st <*> st
                , (\x y z -> Conj [x,y,z]) <$> st <*> st <*> st
                , (\x y -> Disj [x,y]) <$> st <*> st
                , (\x y z -> Disj [x,y,z]) <$> st <*> st <*> st
                , Impl <$> st <*> st
                , Equi <$> st <*> st
                , (\x -> Xor [x]) <$> st
                , (\x y -> Xor [x,y]) <$> st <*> st
                , (\x y z -> Xor [x,y,z]) <$> st <*> st <*> st
                -- , (\p f -> Exists [p] f) <$> elements allprops <*> st
                -- , (\p f -> Forall [p] f) <$> elements allprops <*> st
                ]
    where
      st = bf' (n `div` 3)

instance Arbitrary Form where
  arbitrary = sized form where
    form 0 = oneof [ pure Top
                   , pure Bot
                   , PrpF <$> arbitrary ]
    form n = oneof [ pure SMCDEL.Language.Top
                   , pure SMCDEL.Language.Bot
                   , PrpF <$> arbitrary
                   , Neg <$> form n'
                   , Conj <$> listOf (form n')
                   , Disj <$> listOf (form n')
                   , Xor  <$> listOf (form n')
                   , Impl <$> form n' <*> form n'
                   , Equi <$> form n' <*> form n'
                   , K   <$> arbitraryAg <*> form n'
                   , Ck  <$> arbitraryAgs <*> form n'
                   , Kw  <$> arbitraryAg <*> form n'
                   , Ckw <$> arbitraryAgs <*> form n'
                   , PubAnnounce  <$> form n' <*> form n'
                   , PubAnnounceW <$> form n' <*> form n'
                   , Announce  <$> arbitraryAgs <*> form n' <*> form n'
                   , AnnounceW <$> arbitraryAgs <*> form n' <*> form n' ]
      where
        n' = n `div` 5
        arbitraryAg = (\(Ag i) -> i) <$> arbitrary
        arbitraryAgs = sublistOf (map show [1..(5::Integer)]) `suchThat` (not . null)
  shrink = shrinkform

newtype SimplifiedForm = SF Form deriving (Eq,Ord,Show)

instance Arbitrary SimplifiedForm where
  arbitrary = SF . simplify <$> arbitrary
  shrink (SF f) = nub $ map (SF . simplify) (shrinkform f)