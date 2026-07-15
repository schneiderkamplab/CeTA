{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Status_Impl(X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option, status_of)
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
import qualified Option;
import qualified Product_Type;
import qualified Map_Choice;
import qualified Map;
import qualified List;
import qualified Status;
import qualified Arith;

newtype X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a =
  Abs_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option
  (Maybe ((a, Arith.Nat) -> [Arith.Nat]));

rep_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option ::
  forall a.
    X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a ->
      Maybe ((a, Arith.Nat) -> [Arith.Nat]);
rep_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option
  (Abs_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option x) = x;

sel21 ::
  forall a.
    X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a -> Status.Status a;
sel21 xa =
  Status.Abs_status
    (case rep_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option xa of {
      Nothing -> Status.status (error "undefined");
      Just x2 -> x2;
    });

dis1 ::
  forall a. X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a -> Bool;
dis1 xa =
  (case rep_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option xa of {
    Nothing -> True;
    Just _ -> False;
  });

rep_isom ::
  forall a.
    X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a ->
      Maybe (Status.Status a);
rep_isom x = (if dis1 x then Nothing else Just (sel21 x));

status_of_aux ::
  forall a.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                X_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option a;
status_of_aux xa =
  Abs_x_f_status_option_x_x_nat_list_nat_x_f_prod_fun_option
    (if all (\ fidx ->
              all (\ i -> Arith.less_nat i (snd (fst fidx))) (snd fidx))
          xa
      then Just (Map_Choice.fun_of_map_fun (Map.map_of xa)
                  (\ (_, a) -> List.upt Arith.zero_nat a))
      else Nothing);

status_of ::
  forall a.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] -> Maybe (Status.Status a);
status_of x = rep_isom (status_of_aux x);

}
