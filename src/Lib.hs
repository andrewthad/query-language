{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib
  ( interactiveOptimize
  ) where

import Data.Map.Strict (Map)
import Data.Vector (Vector)
import Data.Text (Text)
import Data.Kind (Type)
import Data.Monoid
import Control.Monad
import Data.Witherable (wither,filterA)
import Text.Read (readMaybe)
import Data.Set (Set)
import Data.Maybe
import Data.Function ((&))
import qualified Data.IntDisjointSet as IDS
import qualified Data.Set as S
import qualified GHC.OldList as L
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as MM

interactiveOptimize :: IO ()
interactiveOptimize = do
  putStrLn "Enter query head (ex: 2,4)"
  qhead <- getQueryHead 
  putStrLn "Enter query body (ex: A(1,3,4); A(1,2,3); B(1,4))"
  qbody <- getQueryBody
  let qsize = M.mapMaybe (\(Body xs) -> case xs of
          [] -> Nothing
          (x : _) -> Just (V.length x)
        ) qbody
  putStrLn "Minimal Query:"
  case minimize (Query qhead qbody qsize) of
    Left err -> fail (show err)
    Right minQuery -> TIO.putStrLn (showQuery minQuery)
  return ()

getQueryHead :: IO (Vector Int)
getQueryHead = TIO.getLine >>= parseNumList

showQuery :: Query Text -> Text
showQuery (Query qhead qbody _) = T.concat
  [ T.intercalate "," (map (T.pack . show) (V.toList qhead))
  , " <- "
  , T.intercalate "; " (M.foldMapWithKey (\name (Body bods) -> map (\bod -> name <> showNumList bod) bods) qbody)
  ]

showNumList :: Vector Int -> Text
showNumList v = "(" <> T.intercalate "," (fmap (T.pack . show) (V.toList v)) <> ")"

parseNumList :: Text -> IO (Vector Int)
parseNumList cs = 
  V.forM (V.fromList (L.filter (not . T.null) (T.splitOn "," cs))) $ \t -> do
    case readMaybe (T.unpack t) of
      Nothing -> fail "could not parse query head"
      Just ixs -> return ixs

getQueryBody :: IO (Map Text Body)
getQueryBody = do
  cs <- TIO.getLine
  xs <- forM (L.filter (not . T.null) (T.splitOn ";" cs)) $ \t -> do
    case T.splitOn "(" t of
      [name,nums] -> do
        v <- parseNumList (T.init nums)
        return (name,Body [v])
      _ -> fail "could not parse query body"
  return (M.fromListWith (<>) xs)

data Nat = Zero | Succ Nat

data SNat :: Nat -> Type where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)

data Vec :: Nat -> a -> Type where
  VecNil :: Vec 'Zero a
  VecCons :: a -> Vec n a -> Vec ('Succ n) a

newtype Body = Body { getBody :: [Vector Int] }
  deriving (Show,Monoid)
newtype Row = Row { getRow :: Vector Int }
  deriving (Show)

normalizeSpc :: Spc a -> Either EvaluationException (NormalSpc a)
normalizeSpc = go
  where
  go :: Spc a -> Either EvaluationException (NormalSpc a)
  go (SpcTable table) = Right (NormalSpc (allUnnamedColumns table) mempty [table])
  go (SpcCross a b) = joinNormalSpc <$> go a <*> go b
  go (SpcProject cols a) = do
    NormalSpc proj sel tables <- go a
    newProj <- forM cols $ \col -> do
      maybe (Left InvalidNormalSpc) Right (proj V.!? col)
    Right (NormalSpc newProj sel tables)
  go (SpcSelect (UnnamedSelection x y) a) = do
    NormalSpc proj sels tables <- go a
    x' <- maybe (Left InvalidNormalSpc) Right (proj V.!? x)
    y' <- maybe (Left InvalidNormalSpc) Right (proj V.!? y)
    Right (NormalSpc proj (S.insert (UnnamedSelection x' y') sels) tables)

joinNormalSpc :: NormalSpc a -> NormalSpc a -> NormalSpc a
joinNormalSpc (NormalSpc proj1 selections1 tables1) (NormalSpc proj2 selections2 tables2) = NormalSpc
  (offsetProjection sz proj1 <> proj2)
  (S.map (offsetSelection sz) selections1 <> selections2)
  (tables1 ++ tables2)
  where
  sz = sum (map unnamedTableSize tables2)

offsetProjection :: Int -> Vector Int -> Vector Int
offsetProjection n v = fmap (+n) v

offsetSelection :: Int -> UnnamedSelection -> UnnamedSelection
offsetSelection n (UnnamedSelection a b) = UnnamedSelection (n + a) (n + b)

allUnnamedColumns :: UnnamedTable a -> Vector Int
allUnnamedColumns (UnnamedTable n _) = V.enumFromN 0 n

-- normalSpcBaseSize :: NormalSpc -> Int
-- normalSpcBaseSize (NormalSpc _ _ xs) = sum (map unnamedTableSize xs)

data UnnamedTable a = UnnamedTable
  { unnamedTableSize :: Int
  , unnamedTableValue :: a
  } deriving (Show)

data UnnamedSelection = UnnamedSelection Int Int
  deriving (Eq,Ord,Show)

-- | The way the column numbers work for this is a little weird.
--   Basically, the last table in the list gets the smallest column
--   numbers (starting at zero). So, the column numbers are assigned
--   right-to-left in this way, but inside of an individual table,
--   they are assigned from left to right.
data NormalSpc a = NormalSpc (Vector Int) (Set UnnamedSelection) [UnnamedTable a]
  deriving (Show)

data Spc a
  = SpcSelect UnnamedSelection (Spc a)
  | SpcProject (Vector Int) (Spc a)
  | SpcCross (Spc a) (Spc a)
  | SpcTable (UnnamedTable a)
  deriving (Show)

normalSpcToQuery :: Ord a => NormalSpc a -> Query a
normalSpcToQuery (NormalSpc proj sels tables) =
  let sizes = L.foldl' (\m (UnnamedTable sz t) -> M.insertWith max t sz m) M.empty tables
      -- we don't actually use the disjoint set in an efficient way,
      -- but whatever
      ids0 = buildDisjointSet sels
      (_,newBodies) = foldr (\(UnnamedTable sz t) (totalSz,bodies) ->
          (totalSz + sz, M.insertWith (\(Body x) (Body y) -> Body (x ++ y)) t (Body [fmap (\i -> fromMaybe i (fst (IDS.lookup i ids0))) $ V.enumFromN totalSz sz]) bodies)
        ) (0,M.empty) tables
      newProj = V.map (\i -> fromMaybe i (fst (IDS.lookup i ids0))) proj
   in Query newProj newBodies sizes

buildDisjointSet :: Set UnnamedSelection -> IDS.IntDisjointSet
buildDisjointSet = S.foldl' (\ids (UnnamedSelection x y) ->
    IDS.union x y (IDS.insert y (IDS.insert x ids))
  ) IDS.empty

data Spjr c a
  = SpjrSelect c c (Spjr c a)
  | SpjrProject (Set c) (Spjr c a)
  | SpjrJoin (Spjr c a) (Spjr c a)
  | SpjrRename c c (Spjr c a)
  | SpjrTable (NamedTable c a)
  deriving (Show)

data NamedTable c a = NamedTable a (Set c)
  deriving Show
data NamedSelection c = NamedSelection c c
  deriving Show
data Rename c = Rename c c
  deriving Show

data NormalSpjr c a = NormalSpjr
  { normalSpjrTables :: [(NamedTable c a, [Rename c])] -- tables with renames
  , normalSpjrSelections :: [NamedSelection c] -- selections
  , normalSpjrProjections :: Set c -- projections
  } deriving (Show)

spjrToNormalSpjr :: Ord c => Spjr c a -> NormalSpjr c a
spjrToNormalSpjr = go where
  go (SpjrJoin a b) = joinNormalSpjrs (go a) (go b)
  go (SpjrProject cols a) = (go a) {normalSpjrProjections = cols}
  go (SpjrSelect c1 c2 a) = let x = go a in x {normalSpjrSelections = NamedSelection c1 c2 : normalSpjrSelections x}
  go (SpjrTable t@(NamedTable _ cols)) = NormalSpjr [(t,[])] [] cols
  go (SpjrRename c1 c2 a) = renameNormalSpjr c1 c2 (go a)

renameNormalSpjr :: Ord c => c -> c -> NormalSpjr c a -> NormalSpjr c a
renameNormalSpjr c1 c2 (NormalSpjr tables sels proj) =
  NormalSpjr newTables newSels (S.insert c2 (S.delete c1 proj))
  where
  newSels = map (renameSelection c1 c2) sels
  newTables = map (renameTable c1 c2) tables

renameTable :: Ord c => c -> c -> (NamedTable c a, [Rename c]) -> (NamedTable c a, [Rename c])
renameTable c1 c2 (table@(NamedTable _ cols),renames) = case replaceRename c1 c2 renames of
  Nothing -> if S.member c1 cols
    then (table,Rename c1 c2 : renames)
    else (table,renames)
  Just newRenames -> (table,newRenames)

replaceRename :: Eq c => c -> c -> [Rename c] -> Maybe [Rename c]
replaceRename c1 c2 [] = Nothing
replaceRename c1 c2 (Rename old new : xs) = if new == c1
  then Just $ if old == c2
    then xs
    else Rename old c2 : xs
  else fmap (Rename old new :) (replaceRename c1 c2 xs)

renameSelection :: Eq c => c -> c -> NamedSelection c -> NamedSelection c
renameSelection c1 c2 (NamedSelection a b) = NamedSelection
  (if a == c1 then c2 else a)
  (if b == c1 then c2 else b)

joinNormalSpjrs :: Ord c => NormalSpjr c a -> NormalSpjr c a -> NormalSpjr c a
joinNormalSpjrs (NormalSpjr tables1 sels1 proj1) (NormalSpjr tables2 sels2 proj2) =
  NormalSpjr (tables1 ++ tables2) (sels1 ++ sels2) (S.union proj1 proj2)

-- | returns the SPC query and a mapping from the indices
--   in each table back to their column names.
normalSpjrToNormalSpc :: NormalSpjr c a -> (NormalSpc a, Map c Int)
normalSpjrToNormalSpc (NormalSpjr tables sels proj) =
  let 
   in NormalSpc _ _ _

-- | The type variable refers to the underlying table.
data Query a = Query
  (Vector Int) -- head
  (Map a Body) -- body
  (Map a Int) -- number of columns in each table
  deriving (Show)

data Valuation a = Valuation (Map a Body)
  deriving (Show)

data EvaluationException
  = EvaluationException
  | QueryHeadLookup (Map Int Int) (Vector Int)
  | InvalidNormalSpc
  deriving (Show)

data Assignment
  = AssignmentPossible (Map Int Int)
  | AssignmentImpossible 
  deriving (Show)

instance Monoid Assignment where
  mempty = AssignmentPossible M.empty
  mappend AssignmentImpossible x = AssignmentImpossible
  mappend (AssignmentPossible m1) a = 
    let mres = case a of
          AssignmentImpossible -> Nothing
          AssignmentPossible m2 -> MM.mergeA
            MM.preserveMissing
            MM.preserveMissing
            (MM.zipWithAMatched (\_ x y -> if x == y then Just x else Nothing))
            m1
            m2
     in case mres of
          Nothing -> AssignmentImpossible
          Just x -> AssignmentPossible x

removeOneRule :: Query a -> [Query a]
removeOneRule (Query qhead qbody qsize) = fmap (\x -> Query qhead x qsize) (removeOneRuleBodies qbody)

removeOneRuleBodies :: Map a Body -> [Map a Body]
removeOneRuleBodies = traverse removeOneRuleBody 

removeOneRuleBody :: Body -> [Body]
removeOneRuleBody (Body vs0) = case vs0 of
  [] -> []
  v : vs -> [Body vs] ++ fmap (\(Body ks) -> Body ([v] ++ ks)) (removeOneRuleBody (Body vs))

minimize :: Ord a => Query a -> Either EvaluationException (Query a)
minimize q = do
  equivalentSmallers <- filterA (\smaller -> contains q smaller) (removeOneRule q)
  minimizedSmallers <- mapM minimize equivalentSmallers
  return (head (minimizedSmallers ++ [q]))

minimizeMany :: Ord a => Query a -> Either EvaluationException [Query a]
minimizeMany q = do
  equivalentSmallers <- filterA (\smaller -> contains q smaller) (removeOneRule q)
  minimizedSmallers <- mapM minimize equivalentSmallers
  return (minimizedSmallers ++ [q])

-- | True if the first query contains the second one.
contains :: Ord a => Query a -> Query a -> Either EvaluationException Bool
contains a (Query bhead bbody _) = do
  rows <- evaluate a (Valuation bbody)
  return (L.elem bhead (map getRow rows))
  
canonicalize :: Query a -> Valuation a
canonicalize (Query _ b _) = Valuation b

evaluate :: Ord a => Query a -> Valuation a -> Either EvaluationException [Row]
evaluate (Query qhead qbody _) v = do
  let tuples = allTuples v
  flip wither tuples $ \tuple -> do
    assgn <- evaluateOne qbody tuple
    case assgn of
      AssignmentImpossible -> Right Nothing
      AssignmentPossible assgnMap -> do
        xs <- extractFromAssignment assgnMap qhead
        Right (Just (Row xs))

extractFromAssignment :: Map Int Int -> Vector Int -> Either EvaluationException (Vector Int)
extractFromAssignment m v = V.forM v $ \i -> case M.lookup i m of
  Nothing -> Left (QueryHeadLookup m v)
  Just j -> Right j

qtest1 = Query (V.singleton 0) (M.singleton 'x' (Body [V.fromList [0,1]]))
vtest1 = Valuation (M.singleton 'x' (Body [V.fromList [55,19], V.fromList [42,15]]))
qtest2 = Query (V.singleton 0) (M.singleton 'x' (Body [V.fromList [0,1],V.fromList [0,1]]))
    
evaluateOne :: Ord a => Map a Body -> Map a Row -> Either EvaluationException Assignment
evaluateOne qbody rows = 
  M.foldlWithKey (\m table (Body namings) -> do
    prevAssgn <- m
    assgns <- forM namings $ \naming -> do
      row <- case M.lookup table rows of
        Nothing -> Left EvaluationException
        Just row -> Right row
      assgnMap <- makeAssignment naming row
      Right (AssignmentPossible assgnMap)
    Right (mconcat assgns <> prevAssgn) 
  ) (return mempty) qbody

makeAssignment ::
     Vector Int -- ^ naming
  -> Row -- ^ row
  -> Either EvaluationException (Map Int Int)
makeAssignment naming (Row row) =
  if V.length naming == V.length row
    then Right (M.fromList (V.toList (V.zip naming row)))
    else Left EvaluationException
  
allTuples :: Valuation a -> [Map a Row]
allTuples (Valuation v) = (fmap.fmap) Row (rowsHelper (fmap getBody v))

rowsHelper :: Map k [a] -> [Map k a]
rowsHelper = sequenceA
  
-- contains :: Query a -> Query a -> Bool
-- contains 

exampleSpc :: Either EvaluationException (NormalSpc String)
exampleSpc = normalizeSpc $ SpcSelect (UnnamedSelection 0 1) $ SpcProject (V.fromList [3,0,2])
  ( SpcCross
    ( SpcSelect
      (UnnamedSelection 1 2)
      (SpcTable (UnnamedTable 3 "foo"))
    )
    ( SpcProject (V.fromList [0]) $ SpcProject (V.fromList [1,0])
      ( SpcTable (UnnamedTable 2 "bar") )
    )
  )

simpleSpc :: Either EvaluationException (NormalSpc String)
simpleSpc = normalizeSpc $ SpcCross
  (SpcTable (UnnamedTable 2 "foo"))
  (SpcTable (UnnamedTable 3 "bar"))

exampleSpjr :: Spjr String Int
exampleSpjr = SpjrTable people
  & SpjrRename "person_id" "owner_id"
  & SpjrJoin (SpjrTable dogs)
  & SpjrRename "owner_id" "master_id"


people :: NamedTable String Int
people = NamedTable 1001 (S.fromList ["person_id","person_name","person_age"])

dogs :: NamedTable String Int
dogs = NamedTable 1002 (S.fromList ["dog_name","owner_id"])


