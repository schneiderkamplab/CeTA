-- Shared input conversion only. No XML normalization or certificate rewriting.
module Ceta.Input.Characters (cachedCharacters) where
import Data.Array (listArray, (!))
import Data.Char (ord, chr)

-- The supplied generated decoder maps characters independently. Cache its exact
-- singleton result for ASCII, retaining its own error behavior for other input.
-- Cache lists, rather than taking head, so this helper introduces no partiality.
cachedCharacters :: (String -> [a]) -> String -> [a]
cachedCharacters decode = concatMap character
  where
    table = listArray (0 :: Int,127) [decode [chr i] | i <- [0..127]]
    character c | ord c < 128 = table ! ord c
                | otherwise = decode [c]

