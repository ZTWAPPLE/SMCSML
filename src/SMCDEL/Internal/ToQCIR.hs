{-# LANGUAGE ViewPatterns #-}
module SMCDEL.ToQCIR where

import qualified SMCDEL.Language as L
import SMCDEL.Symbolic.K
import SMCDEL.Other.BDD2Form
import qualified Data.Map.Strict as M

newtype PrpN = PN Int Int
newtype PrpS = PrpS String

--The letter z is reserved for gate labels in QCIRs
num2string :: Int -> String
num2string 0 = "a"
num2string 1 = "b"
num2string 2 = "c"
num2string 3 = "d"
num2string 4 = "e"
num2string 5 = "f"
num2string 6 = "g"
num2string 7 = "h"
num2string 8 = "i"
num2string 9 = "j"
num2string 10 = "k"
num2string 11 = "l"
num2string 12 = "m"
num2string 13 = "n"
num2string 14 = "o"
num2string 15 = "p"
num2string 16 = "q"
num2string 17 = "r"
num2string 18 = "s"
num2string 19 = "t"
num2string 20 = "u"
num2string 21 = "v"
num2string 22 = "w"
num2string 23 = "x"
num2string 24 = "y"
num2string n = num2string (n div 25) ++ num2string (n mod 25)

--propName :: Prp -> PrpS
--propName (P n) = PrpS (num2string n)

prpSub :: Int -> Prp -> PrpN
prpSub n (P m) = PN m n

pn2string :: PrpN -> String
pn2string (PN n m) = (num2string n) ++ (show m)

data BForm
  = Top
  | Bot
  | PrpF PrpN
  | Neg BForm
  | Conj BForm BForm
  | Disj BForm BForm
  | Xor BForm BForm
  | Impl BForm BForm
  | Equi BForm BForm
  | Forall [PrpN] BForm
  | Exists [PrpN] BForm
  deriving (Eq,Ord,Show)

moveOutQuantifier :: BForm -> BForm
moveOutQuantifier Top = Top
moveOutQuantifier Bot = Bot
moveOutQuantifier (PrpF p) = PrpF p
moveOutQuantifier (Neg (Forall set formula)) = Exists set (moveOutQuantifier (Neg formula))
moveOutQuantifier (Neg (Exists set formula)) = Forall set (moveOutQuantifier (Neg formula))
moveOutQuantifier (Neg formula) = Neg (moveOutQuantifier formula)

moveOutQuantifier (Conj (Forall set1 f1) f2) = Forall set1 (moveOutQuantifier (Conj f1 f2))
moveOutQuantifier (Conj (Exists set1 f1) f2) = Exists set1 (moveOutQuantifier (Conj f1 f2))
moveOutQuantifier (Conj f1 (Forall set2 f2)) = Forall set2 (moveOutQuantifier (Conj f1 f2))
moveOutQuantifier (Conj f1 (Exists set2 f2)) = Exists set2 (moveOutQuantifier (Conj f1 f2))
moveOutQuantifier (Conj f1 f2) = Conj (moveOutQuantifier f1) (moveOutQuantifier f2)

moveOutQuantifier (Disj (Forall set1 f1) f2) = Forall set1 (moveOutQuantifier (Disj f1 f2))
moveOutQuantifier (Disj (Exists set1 f1) f2) = Exists set1 (moveOutQuantifier (Disj f1 f2))
moveOutQuantifier (Disj f1 (Forall set2 f2)) = Forall set2 (moveOutQuantifier (Disj f1 f2))
moveOutQuantifier (Disj f1 (Exists set2 f2)) = Exists set2 (moveOutQuantifier (Disj f1 f2))
moveOutQuantifier (Disj f1 f2) = Disj (moveOutQuantifier f1) (moveOutQuantifier f2)

moveOutQuantifier (Xor (Forall set1 f1) f2) = Forall set1 (moveOutQuantifier (Xor f1 f2))
moveOutQuantifier (Xor (Exists set1 f1) f2) = Exists set1 (moveOutQuantifier (Xor f1 f2))
moveOutQuantifier (Xor f1 (Forall set2 f2)) = Forall set2 (moveOutQuantifier (Xor f1 f2))
moveOutQuantifier (Xor f1 (Exists set2 f2)) = Exists set2 (moveOutQuantifier (Xor f1 f2))
moveOutQuantifier (Xor f1 f2) = Xor (moveOutQuantifier f1) (moveOutQuantifier f2) 

moveOutQuantifier (Impl (Forall set1 f1) f2) = Forall set1 (moveOutQuantifier (Impl f1 f2))
moveOutQuantifier (Impl (Exists set1 f1) f2) = Exists set1 (moveOutQuantifier (Impl f1 f2))
moveOutQuantifier (Impl f1 (Forall set2 f2)) = Forall set2 (moveOutQuantifier (Impl f1 f2))
moveOutQuantifier (Impl f1 (Exists set2 f2)) = Exists set2 (moveOutQuantifier (Impl f1 f2))
moveOutQuantifier (Impl f1 f2) = Impl (moveOutQuantifier f1) (moveOutQuantifier f2) 

moveOutQuantifier (Equi (Forall set1 f1) f2) = Forall set1 (moveOutQuantifier (Equi f1 f2))
moveOutQuantifier (Equi (Exists set1 f1) f2) = Exists set1 (moveOutQuantifier (Equi f1 f2))
moveOutQuantifier (Equi f1 (Forall set2 f2)) = Forall set2 (moveOutQuantifier (Equi f1 f2))
moveOutQuantifier (Equi f1 (Exists set2 f2)) = Exists set2 (moveOutQuantifier (Equi f1 f2))
moveOutQuantifier (Equi f1 f2) = Equi (moveOutQuantifier f1) (moveOutQuantifier f2) 

moveOutQuantifier (Forall set f) = Forall set (moveOutQuantifier f)
moveOutQuantifier (Exists set f) = Exists set (moveOutQuantifier f)

moveInNegation :: BForm -> BForm
moveInNegation

bform2QCIR :: BForm -> Int -> [String]
bform2QCIR Top _ = ["and()"]
bform2QCIR Bot _ = ["or()"]
bform2QCIR (PrpF p) = [("and(" ++ (pn2string n) ++ ")")]
bform2QCIR 

type Step = Int

data ChangeLog
  = LPP Int Int Agent
  | LD  BForm Agent
  | LPD Int BForm Agent
  | VP  Int
  | VD  BForm
  deriving (Eq,Ord,Show)

changePrp :: Int -> Int -> PrpN -> PrpN
changePrp n m (PN a n) = (PN a m)

changeSubscript :: Int -> Int -> BForm -> BForm
changeSubscript _ _ Top = Top
changeSubscript _ _ Bot = Bot
changeSubscript n m (PrpF a) = changePrp n m a
changeSubscript n m (Neg f)  = Neg (changeSubscript0 n m f)
changeSubscript n m (Conj f g) = Conj (changeSubscript0 n m f) (changeSubscript0 n m g)
changeSubscript n m (Disj f g) = Disj (changeSubscript0 n m f) (changeSubscript0 n m g)
changeSubscript n m (Xor f g) = Xor (changeSubscript0 n m f) (changeSubscript0 n m g)
changeSubscript n m (Impl f g) = Impl (changeSubscript0 n m f) (changeSubscript0 n m g)
changeSubscript n m (Equi f g) = Equi (changeSubscript0 n m f) (changeSubscript0 n m g)
changeSubscript n m (Forall set f) = Forall (map (changePrp n m) set) (changeSubscript0 n m f)
changeSubscript n m (Exists set f) = Exists (map (changePrp n m) set) (changeSubscript0 n m f)

showSL :: Bdd -> [ChangeLog] -> [Prp] -> Int -> BForm
showSL bdd log prps n = Conj (showSLhelp (formOf bdd) n) (siftStates prps log n)

showAR :: RelBDD -> [ChangeLog] -> [Prp] -> Int -> Int -> Agent -> BForm 
showAR rbdd log prps n next ag = Conj (showARhelp (formOf rbdd) n next) (siftRelations prps log n next ag)

showARS :: RelBDD -> [ChangeLog] -> [Prp] -> Int -> Int -> Agent -> BForm
showARS rbdd log prps next spare ag =  
	Exists (map (prpSub spare) prps) (Conj (showARhelp (formOf rbdd) spare next) (siftRelations prps log spare next ag))

unEqual :: [Prp] -> Int -> Int -> BForm
unEqual [(P i)] n m = Neg (Equi (PrpF (PN i n)) (PN i m))
unEqual a:rest n m = Disj (unEqual [a] n m) (unEqual rest n m)
unEqual [] n m = Bot

siftStates :: [Prp] -> [ChangeLog] -> Int -> BForm
siftStates prps [(VP m)] n = unEqual prps m n
siftStates prps [(VD f)] n = Neg (changeSubscript 0 n f)
siftStates prps (VP m):rest n = Conj (siftStates prps (VP m) n) (siftStates prps rest n)
siftStates prps (VD m):rest n = Conj (siftStates prps (VD f) n) (siftStates prps rest n)
siftStates prps a:rest = siftStates prps rest
siftStates _ [] = Top

siftRelations :: [Prp] -> [ChangeLog] -> Int -> Int -> Agent -> BForm
siftRelations prps [(LD f ag)] n next ag  = 
	Neg (changeSubscript 0 next f)
siftRelations prps [(LPD m f ag)] n next ag = 
	Disj(unEqual m n) (Neg (changeSubscript 0 next f))
siftRelations prps [(LPP m mext ag)] n next ag = 
	Disj (unEqual m n) (unEqual mext next)
siftRelations prps (LD f ag):rest n next ag = 
	Conj (siftRelations prps [(LD f ag)] n next ag) (siftRelations prps rest n next ag)
siftRelations prps (LPD m f ag):rest n next ag = 
	Conj (siftRelations prps [(LPD m f ag)] n next ag) (siftRelations prps rest n next ag)
siftRelations prps (LPP m mext ag):rest n next ag = 
	Conj (siftRelations prps [(LPP m mext ag)] n next ag) (siftRelations prps rest n next ag)
siftRelations prps a:rest = siftRelations prps rest
siftRelations _ [] _ _ _ = Top
 
showSLhelp :: Form -> Int -> BForm
showSLhelp L.Top _ = Top
showSLhelp L.Bot _ = Bot
showSLhelp (L.PrpF m) n = PrpF m n
showSLhelp (L.Neg f) n = Neg (showSLhelp f n)
showSLhelp (L.Conj []) n = Top
showSLhelp (L.Conj [a]) n = showSLhelp a n
showSLhelp (L.Conj a:rest) n = Conj (showSLhelp a n) (showSLhelp rest n)
showSLhelp (L.Disj []) n = Bot
showSLhelp (L.Disj [a]) n = showSLhelp a n
showSLhelp (L.Disj a:rest) n = Disj (showSLhelp a n) (showSLhelp rest n)

showARhelp :: Form -> Int -> Int-> BForm
showARhelp L.Top _ _ = Top
showARhelp L.Bot _ _ = Bot
showARhelp (L.PrpF m) n next | even m = PrpF (m `div` 2) n
							 | otherwise = PrpF ((m - 1) `div` 2) next
showARhelp (L.Neg f) n next = Neg (showARhelp f n next)
showARhelp (L.Conj []) _ _ = Top
showARhelp (L.Conj [a]) n next = showARhelp a n next
showARhelp (L.Conj a:rest) n next = Conj (showARhelp a n next) (showARhelp rest n next)
showARhelp (L.Disj []) _ _ = Bot
showARhelp (L.Disj [a]) n next = showARhelp a n next
showARhelp (L.Disj a:rest) n next = Disj (showARhelp a n next) (showARhelp rest n next)

form2bform :: Form -> BelStruct -> [ChangeLog] -> Int -> Int -> Step -> BForm
form2bform L.Top _ _ _ _ _ = Top
form2bform L.Bot _ _ _ _ _ = Bot
form2bform (L.PrpF p) _ _ i _ _ = fmap (++ i) (propName p) 
form2bform (L.Neg f) bls log i next step = Neg (form2bform f bls log i next step)
form2bform (L.Conj []) _ _ _ _ _ = Top
form2bform (L.Conj [a]) bls log i next step = form2bform a bls log i next step
form2bform (L.Conj a:rest) bls log i next step = 
	Conj (form2bform bls log i next (step + step) a) (form2bform bls log i (next + step) (step + step) rest)
form2bform (L.Disj []) _ _ _ _ _ = Bot
form2bform (L.Disj [a]) bls log i next step = form2bform bls log i next step a
form2bform (L.Disj a:rest) bls log  i next step = 
	Disj (form2bform bls log i next (step + step) a) (form2bform bls log i (next + step) (step + step) rest)
form2bform (L.Xor []) _ _ _ _ _ = Bot
form2bform (L.Xor [a]) bls log i next step = form2bform bls log i next step a
form2bform (L.Xor a:rest) bls log i next step = 
	Xor (form2bform bls log i next (step + step) a) (form2bform bls log i (next + step) (step + step) rest)
form2bform (L.Impl a b) bls log i next step = 
	Impl (form2bform bls log i next (step + step) a) (form2bform bls log i (next + step) (step + step) b)
form2bform (L.Equi a b) bls log i next step = 
	Equi (form2bform bls log i next (step + step) a) (form2bform bls log i (next + step) (step + step) b)
--I cannot make sense of the appearance of quantifiers here...
--so I make these two lines as comments.
--form2bform (L.Forall set f) bls log i next step = Forall (map (fmap (++ i)).propName set) (form2bform bls log i next step f)
--form2bform (L.Exists set f) bls log i next step = Exists (map (fmap (++ i)).propName set) (form2bform bls log i next step f)
form2bform (L.SabotageALE ag cond assr) bls log i next step = 
	form2bform assr bls ((LPD next condition ag):log) i (next + step) (step + step)
			where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)

form2bform (L.SabotageOLE ag cond assr) bls@(BlS voc statelaw map) log i next step = 
	Forall (map (prpSub next) voc) (Impl (showSL statelaw log next) (Impl (showAR (M.findeWithDefault emptyRelBdd ag map) log i next ag) (Impl (condition) assertion)))
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)
			  assertion = form2bform assr bls ((LPP i next ag):log) i (next + step) (step + step)

form2bform (L.SabotageAGE ag cond assr) bls log i next step = 
	form2bform assr bls ((LD condition ag):log) i (next + step) (step + step)
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)

form2bform (L.SabotageOGE ag cond assr) bls@(BlS voc statelaw map) log i next step = 
	Forall (map (prpSub next) voc) (Impl (showSL statelaw log next) (Impl (showARS (M.findWithDefault emptyRelBdd ag map) log next (next + step + step) ag) (Impl (condition) assertion)))
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step + step + step) (step + step)
			  assertion = form2bform assr bls ((LPP i next ag):log) i (next + step) (step + step)
																				  
form2bform (L.SabotageALV ag cond assr) bls log i next step = 
	form2bform assr bls ((VD condition:log) i (next + step) (step + step)
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)

form2bform (L.SabotageOLV ag cond assr) bls@(BlS voc statelaw map) log i next step = 
	Forall (map (prpSub next) voc) (Impl (showSL statelaw log next) (Impl (showAR (M.findWithDefault emptyRelBdd ag map) log i next ag) (Impl (condition) assertion)))
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)
			  assertion = form2bform assr bls ((VP next):log) i (next + step) (step + step)

form2bform (L.SabotageOGV ag cond assr) bls@(BlS voc statelaw map) log i next step = 	
	Forall (map (prpSub next) voc) (Impl (showSL statelaw log next) (Impl (condition) assertion))
		where condition = changePrp next 0 $ form2bform cond bls log next (next + step + step) (step + step)
			  assertion = form2bform assr bls ((VP next):log) i (next + step) (step + step)

form2bform (L.K ag f) bls@(BlS voc statelaw map) log i next step = 
	Forall (map (prpSUb next) voc) (Impl (showSL statelaw log next) (Impl (showAR (M.findWithDefault emptyRelBdd ag map) log i next) assertion))
		where assertion = form2bform f bls log next (next + step) step