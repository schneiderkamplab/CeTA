{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Map_Choice(ceta_map_of, ceta_set_of, ceta_list_diff, fun_of_map_fun,
              precompute_fun, fun_of_map_funa)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Uint;
import qualified Array;
import qualified IArray;
import qualified Uint32;
import qualified Uint64;
import qualified Data_Bits;
import qualified Bit_Shifts;
import qualified Str_Literal;
import qualified Arith;
import qualified RBTSetImpl;
import qualified HOL;
import qualified RBTMapImpl;
import qualified RBT;
import qualified Compare;

ceta_map_of ::
  forall a b. (Compare.Compare_order a) => [(a, b)] -> a -> Maybe b;
ceta_map_of ps = RBT.lookup (RBTMapImpl.g_list_to_map_rm_basic_ops ps);

ceta_set_of :: forall a. (Compare.Compare_order a) => [a] -> a -> Bool;
ceta_set_of ps =
  let {
    tree = RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops ps;
  } in (\ a -> RBTSetImpl.memb_rm_basic_ops a tree);

ceta_list_diff :: forall a. (Compare.Compare_order a) => [a] -> [a] -> [a];
ceta_list_diff xs ys =
  RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
    (Arith.foldl (\ a b -> RBTSetImpl.delete_rm_basic_ops b a)
      (RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops xs) ys);

fun_of_map_fun :: forall a b. (a -> Maybe b) -> (a -> b) -> a -> b;
fun_of_map_fun m d a = (case m a of {
                         Nothing -> d a;
                         Just b -> b;
                       });

precompute_fun ::
  forall a b. (Compare.Compare_order a) => (a -> b) -> [a] -> a -> b;
precompute_fun f asa =
  fun_of_map_fun (ceta_map_of (map (\ a -> (a, f a)) asa)) f;

fun_of_map_funa ::
  forall a b c. (a -> Maybe b) -> (a -> c) -> (b -> c) -> a -> c;
fun_of_map_funa m d f a = (case m a of {
                            Nothing -> d a;
                            Just aa -> f aa;
                          });

}
