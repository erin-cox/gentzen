-- Gentzen-style sequent calculus for first-order logic.
import qualified Data.Sequence as S



-- Terms in first-order logic.
data Term
  = Const String [Term]
  | Var String
  deriving (Eq)

-- Formulas in first-order logic.
data Formula
  = Predicate String [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Impl Formula Formula
  | Equiv Formula Formula
  -- | ForAll (Term -> Formula)
  -- | Exists (Term -> Formula)
  deriving (Eq)

-- Gentzen-style sequents. The similarity of sequence the datatype and sequent in logic is regrettable.
type Sequent = (S.Seq Sequent, S.Seq Sequent)






test17b :: Sequent
test17b = (
  S.fromList [ForAll (\x -> And (Predicate "P" [x]) (Predicate "Q" [x]))],
  S.fromList [And (ForAll (\y -> Predicate "P" [y]) (ForAll (\y -> Predicate "Q" [y]))]
)




-- The proof tree.
data ProofTree
  = Unproved
  | Proved
  | SingleStep Sequent ProofTree
  | SplitStep Sequent ProofTree ProofTree


-- | i,j index the sequent. the result is either a single sequent or a pair. The use of "left/right" to mean both the left and right of a sequent and the constructors of either is unfortunate.
takeStep :: (Int, Int) -> Sequent -> Either Sequent (Sequent, Sequent)
takeStep (i,j) (leftS, rightS) =
  let f = S.index ([leftS, rightS] !! i) j in
    case i, f of
      -- not l
      0, Not f1 -> Left $ leftS', rightS S.|> f1
      -- not r
      1, Not f1 -> Left $ leftS S.<| f1, rightS'
      -- &l
      0, And f1 f2 -> Left $ (leftS' S.<| f2) S.<| f1, rightS
      -- &r
      1, And f1 f2 -> Right $
        (leftS, rightS' S.|> f1),
        (leftS, rightS' S.|> f2)
      -- |l
      0, Or f1 f2 -> Right $
        (leftS' S.<| f1, rightS),
        (leftS' S.<| f2, rightS)
      -- |r
      1, Or f1 f2 -> Left $ leftS, (rightS' S.<| f1) S.<| f2
      -- ->l
      0, Impl f1 f2 -> Right $
        (leftS', rightS S.|> f),
        (leftS' S.<| f2, rightS)
      -- ->r
      1, Impl f1 f2 -> Left $ leftS S.<| f1, rightS' S.|> f2
      -- think about how to handle quantifiers...
      where
        leftS' = S.deleteAt j leftS
        rightS' = S.deleteAt j rightS