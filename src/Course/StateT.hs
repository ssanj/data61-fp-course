{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}

module Course.StateT where

import Course.Core
import Course.ExactlyOne
import Course.Optional
import Course.List
import Course.Functor
import Course.Applicative
import Course.Monad
import Course.State
import qualified Data.Set as S
import qualified Prelude as P

-- $setup
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- | A `StateT` is a function from a state value `s` to a functor f of (a produced value `a`, and a resulting state `s`).
newtype StateT s f a =
  StateT {
    runStateT ::
      s
      -> f (a, s)
  }

-- | Implement the `Functor` instance for @StateT s f@ given a @Functor f@.
--
-- >>> runStateT ((+1) <$> (pure 2) :: StateT Int List Int) 0
-- [(3,0)]
instance Functor f => Functor (StateT s f) where
  (<$>) ::
    (a -> b)
    -> StateT s f a
    -> StateT s f b
  (<$>) f st1 = StateT (\s ->
                          let fas = runStateT st1 s in
                           (\(a, s1) -> (f a, s1)) <$> fas
                )


-- | Implement the `Applicative` instance for @StateT s f@ given a @Monad f@.
--
-- >>> runStateT (pure 2) 0
-- (2,0)
--
-- >>> runStateT ((pure 2) :: StateT Int List Int) 0
-- [(2,0)]
--
-- >>> runStateT (pure (+2) <*> ((pure 2) :: StateT Int List Int)) 0
-- [(4,0)]
--
-- >>> import qualified Prelude as P
-- >>> runStateT (StateT (\s -> Full ((+2), s P.++ [1])) <*> (StateT (\s -> Full (2, s P.++ [2])))) [0]
-- Full (4,[0,1,2])
--
-- >>> runStateT (StateT (\s -> ((+2), s P.++ [1]) :. ((+3), s P.++ [1]) :. Nil) <*> (StateT (\s -> (2, s P.++ [2]) :. Nil))) [0]
-- [(4,[0,1,2]),(5,[0,1,2])]
instance Monad f => Applicative (StateT s f) where
  pure ::
    a
    -> StateT s f a
  pure a = StateT(\s -> return (a, s))

  (<*>) ::
   StateT s f (a -> b)
    -> StateT s f a
    -> StateT s f b
  (<*>) sfab sfa = StateT(\s ->
                       do (fab, sx) <- runStateT sfab s
                          (a, sy)   <- runStateT sfa sx
                          return (fab a, sy)
                  )

-- | Implement the `Monad` instance for @StateT s f@ given a @Monad f@.
-- Make sure the state value is passed through in `bind`.
--
-- >>> runStateT ((const $ putT 2) =<< putT 1) 0
-- ((),2)
--
-- >>> let modify f = StateT (\s -> pure ((), f s)) in runStateT (modify (+1) >>= \() -> modify (*2)) 7
-- ((),16)
instance Monad f => Monad (StateT s f) where
  (=<<) ::
    (a -> StateT s f b)
    -> StateT s f a
    -> StateT s f b
  (=<<) asfb sfa = StateT(\s ->
                    do (a, s1) <- runStateT sfa s
                       (b, s2) <- runStateT (asfb a) s1
                       return (b, s2)
                   )

-- | A `State'` is `StateT` specialised to the `ExactlyOne` functor.
type State' s a =
  StateT s ExactlyOne a

-- | Provide a constructor for `State'` values
--
-- >>> runStateT (state' $ runState $ put 1) 0
-- ExactlyOne  ((),1)
state' ::
  (s -> (a, s))
  -> State' s a
state' f = StateT(\s -> ExactlyOne (f s))

-- | Provide an unwrapper for `State'` values.
--
-- >>> runState' (state' $ runState $ put 1) 0
-- ((),1)
runState' ::
  State' s a
  -> s
  -> (a, s)
runState' st = runExactlyOne . (runStateT st)

-- | Run the `StateT` seeded with `s` and retrieve the resulting state.
execT ::
  Functor f =>
  StateT s f a
  -> s
  -> f s
execT st s = snd <$> (runStateT st s)-- f (a, s)

-- | Run the `State` seeded with `s` and retrieve the resulting state.
exec' ::
  State' s a
  -> s
  -> s
exec' st s = runExactlyOne $ execT st s -- f (a, s)

-- | Run the `StateT` seeded with `s` and retrieve the resulting value.
evalT ::
  Functor f =>
  StateT s f a
  -> s
  -> f a
evalT st s = fst <$> (runStateT st s)

-- | Run the `State` seeded with `s` and retrieve the resulting value.
eval' ::
  State' s a
  -> s
  -> a
eval' st s = runExactlyOne $ evalT st s

-- | A `StateT` where the state also distributes into the produced value.
--
-- >>> (runStateT (getT :: StateT Int List Int) 3)
-- [(3,3)]
getT ::
  Applicative f =>
  StateT s f s
getT = StateT(\s -> pure (s, s)) -- f (a, s)

-- | A `StateT` where the resulting state is seeded with the given value.
--
-- >>> runStateT (putT 2) 0
-- ((),2)
--
-- >>> runStateT (putT 2 :: StateT Int List ()) 0
-- [((),2)]
putT ::
  Applicative f =>
  s
  -> StateT s f ()
putT s = StateT (\_ -> pure ((), s))

-- | Remove all duplicate elements in a `List`.
--
-- /Tip:/ Use `filtering` and `State'` with a @Data.Set#Set@.
--
-- prop> distinct' xs == distinct' (flatMap (\x -> x :. x :. Nil) xs)
distinct' ::
  (Ord a, Num a) =>
  List a
  -> List a
distinct' xs =  let result = filtering (\a -> state' (\s -> (a `S.notMember` s, a `S.insert` s))) xs
                    (_, matches) = runState' result S.empty
                in
                    listh $ S.elems matches
-- filtering :: Applicative f => (a -> f Bool) -> List a -> f (List a)

-- | Remove all duplicate elements in a `List`.
-- However, if you see a value greater than `100` in the list,
-- abort the computation by producing `Empty`.
--
-- /Tip:/ Use `filtering` and `StateT` over `Optional` with a @Data.Set#Set@.
--
-- >>> distinctF $ listh [1,2,3,2,1]
-- Full [1,2,3]
--
-- >>> distinctF $ listh [1,2,3,2,1,101]
-- Empty
distinctF ::
  (Ord a, Num a) =>
  List a
  -> Optional (List a)
distinctF xs = let unique = distinct' xs
               in
                  if  (any ( > 100)) unique then Empty else Full (unique)

-- | An `OptionalT` is a functor of an `Optional` value.
data OptionalT f a =
  OptionalT {
    runOptionalT ::
      f (Optional a)
  }

-- | Implement the `Functor` instance for `OptionalT f` given a Functor f.
--
-- >>> runOptionalT $ (+1) <$> OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Empty]
--  Functor (<$>) :: (a -> b) -> f a -> f b
instance Functor f => Functor (OptionalT f) where
  (<$>) ab fa = OptionalT ((ab <$>) <$> (runOptionalT fa))

-- | Implement the `Applicative` instance for `OptionalT f` given a Applicative f.
--
-- >>> runOptionalT $ OptionalT (Full (+1) :. Full (+2) :. Nil) <*> OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Empty,Full 3,Empty]
instance Applicative f => Applicative (OptionalT f) where
  pure a = OptionalT (pure $ pure a)
  -- (<*>) f (a -> b) -> f a -> f b
  (<*>) ofab ofa = OptionalT(
                      lift2 (<*>) (runOptionalT ofab) (runOptionalT ofa)
                    )

-- | Implement the `Monad` instance for `OptionalT f` given a Monad f.
--
-- >>> runOptionalT $ (\a -> OptionalT (Full (a+1) :. Full (a+2) :. Nil)) =<< OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Full 3,Empty]
instance Monad f => Monad (OptionalT f) where
  --     (a -> f b) -> f a -> f b
  (=<<) aotfb otfa = OptionalT (
                      do oa <- runOptionalT otfa
                         let result = case oa of
                                        (Full a) -> aotfb a
                                        Empty -> OptionalT (pure Empty)
                         runOptionalT result
                     )


-- | A `Logger` is a pair of a list of log values (`[l]`) and an arbitrary value (`a`).
data Logger l a =
  Logger (List l) a
  deriving (Eq, Show)

-- | Implement the `Functor` instance for `Logger
--
-- >>> (+3) <$> Logger (listh [1,2]) 3
-- Logger [1,2] 6
instance Functor (Logger l) where
  (<$>) ab (Logger log a) = Logger log (ab a)

-- | Implement the `Applicative` instance for `Logger`.
--
-- >>> pure "table" :: Logger Int P.String
-- Logger [] "table"
--
-- >>> Logger (listh [1,2]) (+7) <*> Logger (listh [3,4]) 3
-- Logger [1,2,3,4] 10
instance Applicative (Logger l) where
  pure = Logger Nil
  (<*>) (Logger log1 ab) (Logger log2 a) = Logger (log1 ++ log2) (ab a)

-- | Implement the `Monad` instance for `Logger`.
-- The `bind` implementation must append log values to maintain associativity.
--
-- >>> (\a -> Logger (listh [4,5]) (a+3)) =<< Logger (listh [1,2]) 3
-- Logger [1,2,4,5] 6
instance Monad (Logger l) where
-- (=<<) (a -> Logger l b) -> Logger l a -> Logger l b
  (=<<) afb (Logger log1 a) = let (Logger log2 b) = afb a in
                              Logger (log1 ++ log2) b

-- | A utility function for producing a `Logger` with one log value.
--
-- >>> log1 1 2
-- Logger [1] 2
log1 ::
  l
  -> a
  -> Logger l a
log1 l = Logger (l :. Nil)


-- | Remove all duplicate integers from a list. Produce a log as you go.
-- If there is an element above 100, then abort the entire computation and produce no result.
-- However, always keep a log. If you abort the computation, produce a log with the value,
-- "aborting > 100: " followed by the value that caused it.
-- If you see an even number, produce a log message, "even number: " followed by the even number.
-- Other numbers produce no log message.
--
-- /Tip:/ Use `filtering` and `StateT` over (`OptionalT` over `Logger` with a @Data.Set#Set@).
--
-- >>> distinctG $ listh [1,2,3,2,6]
-- Logger ["even number: 2","even number: 2","even number: 6"] (Full [1,2,3,6])
--
-- >>> distinctG $ listh [1,2,3,2,6,106]
-- Logger ["even number: 2","even number: 2","even number: 6","aborting > 100: 106"] Empty
distinctG ::
  (Integral a, Show a) =>
  List a
  -> Logger Chars (Optional (List a)) -- StateT Set (OptionalT (Logger Chars)) a, Logger Chars (Optional)
  -- filtering :: Applicative f => (a -> f Bool) -> List a -> f (List a)
  -- f == State Set (OptionalT (Logger Chars))
  -- filtering :: Applicative f => (a -> f Bool) -> List a -> f (List a)
distinctG xs =
  let filtered =
        filtering (\a ->
          if isOverHundred a then logOverHundred a
          else if isEven a then logEven a
          else logOthers a
        ) xs

      result =  runOptionalT $ evalT filtered S.empty
  in result

                                -- s -> m (a, s)
                                -- s -> (Logger Chars Maybe (a, s))
                                -- s -> Logger Char (Optional (Bool, S.Set a))

isEven :: Integral a => a -> Bool
isEven a =  (a `mod` 2 == 0)

isOverHundred :: Integral a => a -> Bool
isOverHundred a = (a > 100)

-- blah :: Logger Chars Int
-- blah  = log1 (listh ("even number: " P.++ (show 2))) 2

-- blah2 :: OptionalT (Logger Chars) Int
-- blah2  = OptionalT (log1 (listh ("even number: " P.++ (show 2))) (Full 2))

-- blah3 :: StateT (S.Set Int) (OptionalT (Logger Chars)) Int
-- blah3  = StateT(\s -> OptionalT (log1 (listh ("even number: " P.++ (show 2))) (Full (2, 2 `S.insert` s))))

logEven :: (Ord a, Num a, Show a) => a -> StateT (S.Set a) (OptionalT (Logger Chars)) Bool
logEven a = StateT (\s -> OptionalT (log1
                                      (listh ("even number: " P.++ (show a)))
                                      (Full (a `S.notMember` s, a `S.insert` s))
                          )
            )

logOverHundred :: (Ord a, Num a, Show a) => a -> StateT (S.Set a) (OptionalT (Logger Chars)) Bool
logOverHundred a = StateT(\s -> OptionalT (log1
                                            (listh ("aborting > 100: " P.++ (show a)))
                                            Empty
                                )
                   )

logOthers :: (Ord a, Num a, Show a) => a -> StateT (S.Set a) (OptionalT (Logger Chars)) Bool
logOthers a = StateT(\s -> OptionalT (pure
                                        (Full (a `S.notMember` s, a `S.insert` s))
                           )
              )
