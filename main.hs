{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

import Prelude hiding (sum,product)
import Data.List hiding (sum,product)
import Data.Char
import Data.Function
import Debug.Trace
import Control.Monad
import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Lens
import System.Random
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Maybe as L (mapMaybe,catMaybes)

newtype Parser a = Parser (String -> [(a,String)])

instance Functor Parser where
  fmap f (Parser g) = Parser $ fmap (first f) . g
instance Applicative Parser where
  pure x = Parser $ \s -> [(x,s)]
  Parser f <*> Parser x = Parser $ \s -> do
    (f',s') <- f s
    (x',s'') <- x s'
    return (f' x',s'')
instance Monad Parser where
  return = pure
  Parser x >>= f = Parser $ \s -> do
    (x',s') <- x s
    let Parser f' = f x'
    f' s'
instance Alternative Parser where
  empty = Parser $ const []
  Parser x <|> Parser y = Parser $ \s -> x s ++ y s

isChar :: (Char -> Bool) -> Parser Char
isChar f = Parser $ \case
  [] -> []
  (x:xs)
    | f x -> [(x,xs)]
    | otherwise -> []

char :: Char -> Parser Char
char x = isChar (==x)

inSet :: [Char] -> Parser Char
inSet xs = isChar (`elem`xs)

natural :: Parser Int
natural = do
  xs <- many $ isChar isDigit
  return $ read xs 

eps :: Parser ()
eps = Parser $ \xs -> [((),xs)]

parse :: Parser a -> String -> Maybe a
parse (Parser f) xs = safeHead $ filter (null.snd) $ f xs where
  safeHead [] = Nothing
  safeHead (x:xs) = Just $ fst x

data Reg = Chr Char
         | Any
         | Eps
         | Bot
         | Seq Reg Reg
         | Alt Reg Reg
         | And Reg Reg
         | Rep Reg
         | Not Reg
  deriving (Show)

readReg :: String -> Maybe Reg
readReg str = parse r1 $ filter (/=' ') str where
  lit x = isAlpha x || isDigit x
  r1 = (eps >> return Eps) <|> do
    l <- r2
    v <- optional $ char '-' >> r1
    return $ case v of
      Nothing -> l
      Just r -> And l (Not r)
  r2 = (eps >> return Eps) <|> do
    l <- r3
    v <- optional $ char '|' >> r2
    return $ case v of
      Nothing -> l
      Just r -> Alt l r
  r3 = do
    l <- r4
    v <- optional $ char '&' >> r3
    return $ case v of
      Nothing -> l
      Just r -> And l r
  r4 = do
    l <- r5
    v <- optional r4
    return $ case v of
      Nothing -> l
      Just r -> Seq l r
  r5 = do
    e <- elm
    v <- optional $ inSet "*+?{"
    case v of
      Nothing -> return e
      Just '*' -> return $ Rep e
      Just '+' -> return $ Seq e (Rep e)
      Just '?' -> return $ Alt e Eps
      Just '{' -> do
        m <- natural
        n <- optional $ do
          char ','
          natural
        char '}'
        let
          iterN 0 f x = x
          iterN n f x = f $ iterN (n-1) f x
        return $ case n of
          Nothing -> iterN m (Seq e) Eps
          Just p -> iterN (p-m) (\i -> Alt i (Seq e i)) $ iterN m (Seq e) Eps
  elm = chi <|> esc <|> any <|> bot <|> set <|> neg <|> do
    char '('
    e <- r1
    char ')'
    return e
  chi = Chr <$> isChar lit
  esc = char '\\' >> (Chr <$> isChar (const True))
  any = char '.' >> return Any
  bot = char '$' >> return Bot
  set = do
    char '['
    v <- optional $ char '^'
    xs <- many $ (return <$> isChar lit) <|> do
      a <- isChar lit
      char '-'
      b <- isChar lit
      return [a..b]
    char ']'
    let p = foldr (\c e -> Alt (Chr c) e) Bot $ concat xs
    return $ case v of
      Nothing -> p
      Just _ -> And Any (Not p) 
  neg = do
    char '!'
    e <- elm
    return $ Not e

data DFA = DFA {
  dLetter :: S.Set Char,
  dAccept :: S.Set Int,
  dTransit :: V.Vector (M.Map Char Int, Int)
} deriving (Show)
data NFA = NFA {
  nLetter :: S.Set Char,
  nAccept :: Int,
  nTransit :: V.Vector (M.Map Char [Int], [Int], [Int]) -- last is eps
} deriving (Show)

minify :: DFA -> DFA
minify = id

mapDFA :: (Int -> Int) -> DFA -> DFA
mapDFA f (DFA l a t) = DFA l (S.map f a) (fmap f' t) where
  f' (x,y) = (fmap f x, f y)

makeDFA :: Reg -> DFA
makeDFA (Chr c) = DFA (S.singleton c) (S.singleton 1) a where
  a = V.fromList [(M.singleton c 1,2),(M.empty,2),(M.empty,2)]
makeDFA Any = DFA S.empty (S.singleton 1) a where
  a = V.fromList [(M.empty,1),(M.empty,2),(M.empty,2)] 
makeDFA Eps = DFA S.empty (S.singleton 0) a where
  a = V.fromList [(M.empty,1),(M.empty,1)]
makeDFA Bot = DFA S.empty (S.singleton 1) a where
  a = V.fromList [(M.empty,0),(M.empty,1)]
makeDFA (Seq a b) = minify $ transDFA $ makeSeq (makeDFA a) (makeDFA b)
makeDFA (Alt a b) = minify $ DFA lett acc tra where
  a' = makeDFA a
  b' = makeDFA b
  lett = dLetter a' `S.union` dLetter b'
  sa = V.length $ dTransit a'
  sb = V.length $ dTransit b'
  memA = flip S.member $ dAccept a'
  memB = flip S.member $ dAccept b'
  traA i = dTransit a' V.! i
  traB i = dTransit b' V.! i
  po x y = x*sb+y
  lst = [ po x y | x <- [0..sa-1], y <- [0..sb-1] ]
  emb f = f.(`divMod`sb)
  acc = S.fromList $ filter (emb $ \(ix,iy) -> memA ix || memB iy) lst
  tra = V.fromList $ map (emb $ \(ix,iy) -> traA ix`meld`traB iy) lst
  meld (ma,fa) (mb,fb) = (M.fromList $ map con $ S.toList lett, po fa fb) where
    con c = (c,) $ case (M.lookup c ma, M.lookup c mb) of
      (Just ua, Just ub) -> po ua ub
      (Just ua, Nothing) -> po ua fb
      (Nothing, Just ub) -> po fa ub
      (Nothing, Nothing) -> po fa fb
makeDFA (And a b) = minify $ DFA lett acc tra where
  a' = makeDFA a
  b' = makeDFA b
  lett = dLetter a' `S.union` dLetter b'
  sa = V.length $ dTransit a'
  sb = V.length $ dTransit b'
  memA = flip S.member $ dAccept a'
  memB = flip S.member $ dAccept b'
  traA i = dTransit a' V.! i
  traB i = dTransit b' V.! i
  po x y = x*sb+y
  lst = [ po x y | x <- [0..sa-1], y <- [0..sb-1] ]
  emb f = f.(`divMod`sb)
  acc = S.fromList $ filter (emb $ \(ix,iy) -> memA ix && memB iy) lst
  tra = V.fromList $ map (emb $ \(ix,iy) -> traA ix`meld`traB iy) lst
  meld (ma,fa) (mb,fb) = (M.fromList $ map con $ S.toList lett, po fa fb) where
    con c = (c,) $ case (M.lookup c ma, M.lookup c mb) of
      (Just ua, Just ub) -> po ua ub
      (Just ua, Nothing) -> po ua fb
      (Nothing, Just ub) -> po fa ub
      (Nothing, Nothing) -> po fa fb
makeDFA (Rep e) = minify $ transDFA $ makeRep (makeDFA e)
makeDFA (Not e) = minify $ let
    e' = makeDFA e
    s = V.length $ dTransit e'
    acc = S.fromList [0..s-1] S.\\ dAccept e' 
  in DFA (dLetter e') acc (dTransit e')

mapNFA :: (Int -> Int) -> NFA -> NFA
mapNFA f (NFA l a t) = NFA l (f a) (fmap f' t) where
  f' (x,y,z) = (fmap (map f) x, map f y, map f z)

makeSeq :: DFA -> DFA -> NFA
makeSeq (DFA al aa at) (DFA bl ba bt) = NFA l (s-1) tra where
  l = al`S.union`bl
  sa = V.length at
  sb = V.length bt
  s = sa + sb + 1
  tra = V.fromList $ map con [0..s-1]
  con i
    | i == s-1 = (M.empty,[],[])
    | i < sa = let
        (m,e) = at V.! i
        isA = i`S.member`aa
      in (fmap return m,[e],if isA then [sa] else [])
    | otherwise = let
        (m',e') = bt V.! (i-sa)
        m = fmap (+sa) m'
        e = e'+sa
        isA = (i-sa)`S.member`ba
      in (fmap return m,[e],if isA then [s-1] else [])

makeRep :: DFA -> NFA
makeRep (DFA l a t) = NFA l (s-1) tra where
  s = V.length t + 2
  tra = V.fromList $ map con [0..s-1]
  con i
    | i == 0 = (M.empty,[],[1,s-1])
    | i == s-1 = (M.empty,[],[])
    | otherwise = let
        (m',e') = t V.! (i-1)
        m = fmap (+1) m'
        e = e'+1
        isA = (i-1)`S.member`a
      in (fmap return m,[e],if isA then [1,s-1] else [])

type Elem = (Int, Maybe (M.Map Char Int, Int))
type Env = (M.Map (S.Set Int) Elem, Int)

transDFA :: NFA -> DFA
transDFA (NFA l a t) = kon $ execState (act s0) (M.empty,0) where
  s0 :: S.Set Int
  s0 = S.singleton 0
  kon :: Env -> DFA
  kon (m,_) = DFA l acc tra where
    acc = S.fromList $ L.mapMaybe elimi $ M.assocs m
    elimi :: (S.Set Int, Elem) -> Maybe Int
    elimi (_,(_,Nothing)) = error "Incomplete traverse"
    elimi (s,(e,_)) = if a`S.member`s then Just e else Nothing
    tra = V.fromList $ L.catMaybes $ map snd $ sortBy (compare`on`fst) $ M.elems m
  epsilons :: S.Set Int -> S.Set Int
  epsilons s = let
      f i = let (_,_,ep) = t V.! i in ep
      s' = S.union s $ S.fromList $ S.toList s >>= f
    in if s == s'
      then s
      else epsilons s'
  done :: S.Set Int -> State Env Bool
  done s = do
    v <- preuse $ _1 . ix s . _2 . _Just
    return $ case v of
      Just _ -> True
      Nothing -> False
  obtain :: S.Set Int -> State Env Int
  obtain s = do
    v <- preuse $ _1 . ix s
    case v of
      Just (i,_) -> return i
      Nothing -> do
        i <- use _2
        _1 . at s .= Just (i,Nothing)
        _2 += 1
        return i
  ins :: S.Set Int -> Maybe Char -> Int -> State Env ()
  ins s (Just c) s' = _1 . ix s . _2 . _Just . _1 . at c .= Just s'
  ins s Nothing s'  = _1 . ix s . _2 . _Just . _2 .= s'
  make :: S.Set Int -> State Env ()
  make s = _1 . ix s . _2 .= Just (M.empty, error "Incomplete state set")
  act :: S.Set Int -> State Env ()
  act (epsilons -> s) = done s >>= \exist -> if exist then return () else do
    i <- obtain s
    make s
    s1 <- forM (S.toList l) $ \c -> do
      let
        st i = let (m,f,_) = t V.! i in case c`M.lookup`m of
          Just j -> j
          Nothing -> f
        sts = epsilons $ S.fromList $ S.toList s >>= st
      u <- obtain sts
      ins s (Just c) u
      return sts
    let s2 = epsilons $ S.fromList $ S.toList s >>= \i -> (t V.! i)^._2
    stf <- obtain s2
    ins s Nothing stf
    forM_ (s2:s1) act

match :: DFA -> String -> Bool
match (DFA _ a t) str = flip S.member a $ foldl ac 0 str where
  ac i c = let (m,f) = t V.! i in case c`M.lookup`m of
    Just j -> j
    Nothing -> f

test :: String -> String -> Maybe Bool
test reg str = flip match str . makeDFA <$> readReg reg

sampleString :: DFA -> IO (Maybe String)
sampleString (DFA l a t) = do
  let
    lett = S.toList l
    s = V.length t
    ini = V.fromList $ take s $ Just id : repeat Nothing
    nil = V.fromList $ replicate s []
    next i c = let (m,f) = t V.! i in case c`M.lookup`m of
      Just j -> j
      Nothing -> f
    allChars = S.fromList (['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9']) S.\\ l
    chooseChars = S.toList allChars
    randC = lift $ (chooseChars!!) <$> randomRIO (0,S.size allChars-1)
    proc :: Int -> StateT (V.Vector (Maybe (String -> String)), V.Vector [String -> String]) IO ()
    proc 0 = return ()
    proc d = do
      _2 .= nil
      ss <- use _1
      forM_ lett $ \c -> do
        iforM_ ss $ \i -> \case
          Just f -> _2 . ix (next i c) %= ((f.(c:)):)
          Nothing -> return ()
      do
        rC <- randC
        iforM_ ss $ \i -> \case
          Just f -> _2 . ix (next i rC) %= ((f.(rC:)):)
          Nothing -> return ()
      va <- forM [0..s-1] $ \i -> do
        u <- use $ _2 . ix i
        case length u of
          0 -> do
            _1 . ix i .= Nothing
            return False
          len -> do
            j <- lift $ randomRIO (0,len-1)
            _1 . ix i .= Just (u !! j)
            if i`S.member`a
              then return True
              else return False
      if or va
        then return ()
        else proc (d-1)
  if 0`S.member`a
    then return $ Just ""
    else do
      rev <- fmap fst $ execStateT ?? (ini,V.empty) $ proc s
      let
        alive (_,Nothing) = False
        alive (i,Just _) = i`S.member`a
        res = L.catMaybes $ map snd $ filter alive $ zip [0..] $ V.toList rev
      case res of
        [] -> return Nothing
        _ -> do
          i <- randomRIO (0,length res-1)
          return $ Just $ (res !! i) ""

sample :: String -> IO (Maybe String)
sample s = case readReg s of
  Nothing -> return Nothing
  Just p -> sampleString (makeDFA p)