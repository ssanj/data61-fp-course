{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Course.Compose where

import Course.Core
import Course.Functor
import Course.Applicative
import Course.Monad

-- Exactly one of these exercises will not be possible to achieve. Determine which.

newtype Compose f g a =
  Compose (f (g a))

-- Implement a Functor instance for Compose
instance (Functor f, Functor g) =>
    Functor (Compose f g) where
-- (<$>) :: (a -> b) -> f a -> f b
-- (<$>) :: (a -> b) -> f (g a) -> f (g b)
  (<$>) fab (Compose st) = Compose ((fab <$>) <$> st)

instance (Applicative f, Applicative g) =>
  Applicative (Compose f g) where
-- Implement the pure function for an Applicative instance for Compose
-- pure :: a -> f (g a)
  pure a = Compose (pure $ pure a)

-- Implement the (<*>) function for an Applicative instance for Compose
-- (<*>) :: f (a -> b) -> f a -> f b
-- (<*>) :: f (g (a -> b)) -> f (g a) -> f (g b)
  (<*>) (Compose fgab) (Compose fga) = Compose (lift2 (<*>) fgab fga)


instance (Monad f, Monad g) =>
  Monad (Compose f g) where
-- Implement the (=<<) function for a Monad instance for Compose
-- (=<<) :: (a -> f b) -> f a -> f b
-- (=<<) :: (a -> f (g b)) -> f (g a) -> f (g b)
  (=<<) fafb (Compose fga) = fafb <$> fga
-- f (g (f (g b))) //no way to join
    -- error "todo: Course.Compose (<<=)#instance (Compose f g)"
