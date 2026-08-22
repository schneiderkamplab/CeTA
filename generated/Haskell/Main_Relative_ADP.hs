module Main (main) where

import Ceta_Relative
import System.Environment (getArgs)
import System.Exit (ExitCode(..), exitWith)
import System.IO (hPutStrLn, stderr)
import Text.Read (readMaybe)

mapMaybe :: (a -> b) -> Maybe a -> Maybe b
mapMaybe _ Nothing = Nothing
mapMaybe f (Just value) = Just (f value)

noWhite :: String -> String
noWhite = filter (`notElem` " \t\n\r")

replace :: (String -> Maybe String) -> String -> String
replace f value = case f (noWhite value) of
  Nothing -> value
  Just replacement -> replacement

xml :: String -> String -> String
xml tag body = "<" ++ tag ++ ">" ++ body ++ "</" ++ tag ++ ">"

xmlLeaf :: String -> String
xmlLeaf tag = "<" ++ tag ++ "/>"

complexityStart, complexityEnd :: String
complexityStart = "WORST_CASE(?,O(n^"
complexityEnd = "))"

shortAnswer :: String -> Maybe String
shortAnswer "YES" = Just (xml "answer" (xmlLeaf "yes"))
shortAnswer "NO" = Just (xml "answer" (xmlLeaf "no"))
shortAnswer value =
  let (start, remainder) = splitAt (length complexityStart) value
  in if start == complexityStart
     then
       let (ending, reversedDegree) = splitAt (length complexityEnd) (reverse remainder)
       in if ending == complexityEnd
          then mapMaybe
            (\degree -> xml "answer" (xml "upperBound" (xml "polynomial" (show degree))))
            (readMaybe reversedDegree :: Maybe Integer)
          else Nothing
     else Nothing

shortProperty :: String -> Maybe String
shortProperty "SN" = Just (xml "property" (xmlLeaf "termination"))
shortProperty "CR" = Just (xml "property" (xmlLeaf "confluence"))
shortProperty "COM" = Just (xml "property" (xmlLeaf "commutation"))
shortProperty "DC" = Just (xml "property" (xml "complexity" (xmlLeaf "derivationalComplexity")))
shortProperty "RC" = Just (xml "property" (xml "complexity" (xmlLeaf "runtimeComplexity")))
shortProperty "INF" = Just (xml "property" (xmlLeaf "infeasibility"))
shortProperty _ = Nothing

main :: IO ()
main = getArgs >>= parse False Nothing Nothing Nothing

parse :: Bool -> Maybe String -> Maybe String -> Maybe String -> [String] -> IO ()
parse _ _ _ _ ("--version" : _) = putStrLn "3.9-relative-adp"
parse _ input property answer ("--allow-assumptions" : args) =
  parse True input property answer args
parse assumptions _ property answer ("--inputf" : path : args) = do
  input <- readFile path
  parse assumptions (Just input) property answer args
parse assumptions input _ answer ("--propertyf" : path : args) = do
  property <- readFile path
  parse assumptions input (Just property) answer args
parse assumptions input _ answer ("--property" : property : args) =
  parse assumptions input (Just property) answer args
parse assumptions input property _ ("--answerf" : path : args) = do
  answer <- readFile path
  parse assumptions input property (Just answer) args
parse assumptions input property _ ("--answer" : answer : args) =
  parse assumptions input property (Just answer) args
parse assumptions input property answer [path] = do
  proof <- readFile path
  start assumptions
    (mapMaybe explode input)
    (mapMaybe (explode . replace shortProperty) property)
    (mapMaybe (explode . replace shortAnswer) answer)
    (explode proof)
parse _ _ _ _ _ = do
  hPutStrLn stderr usage
  exitWith (ExitFailure 4)

start assumptions input property answer proof =
  case certify_proof_integrated assumptions input property answer proof of
    Certified -> do
      putStrLn "CERTIFIED"
      exitWith ExitSuccess
    Error message -> do
      putStrLn "REJECTED"
      hPutStrLn stderr message
      exitWith (ExitFailure 1)
    Unsupported message -> do
      putStrLn "UNSUPPORTED"
      hPutStrLn stderr message
      exitWith (ExitFailure 2)

usage :: String
usage = "usage: ceta [(parameters) certificate | --version]\n\
        \  \n\
        \  A \"certificate\" is an XML file in CPF 3.x or CPF 4.0.\n\
        \  \n\
        \  --allow-assumptions    Allow axiomatic assumptions.\n\
        \  --inputf fname         Read input from a separate file.\n\
        \  --propertyf fname      Read property from a separate file.\n\
        \  --property p           Read property from a string.\n\
        \  --answerf fname        Read answer from a separate file.\n\
        \  --answer a             Read answer from a string.\n\
        \  --version              Print the version."
