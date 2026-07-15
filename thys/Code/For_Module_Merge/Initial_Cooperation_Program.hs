{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Initial_Cooperation_Program(create_initial_cp_prog) where {

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
import qualified Cut_Points;
import qualified List;
import qualified Set;
import qualified Collection_Order;
import qualified Compare;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified HOL;
import qualified Product_Type;
import qualified Cooperation_Program;
import qualified Formula;
import qualified LTS;
import qualified Term;

make_copy_prog ::
  forall a b c d e.
    LTS.Lts_impl a b c d e ->
      [(Cooperation_Program.Sharp e,
         LTS.Transition_rule a b c (Cooperation_Program.Sharp d))] ->
        LTS.Lts_impl a b c (Cooperation_Program.Sharp d)
          (Cooperation_Program.Sharp e);
make_copy_prog (LTS.Lts_Impl init tau_s lc) cutpoints =
  LTS.Lts_Impl (map Cooperation_Program.Flat init)
    (map (\ (tr, tau) ->
           (Cooperation_Program.Flat tr,
             Cooperation_Program.flat_transition tau))
       tau_s ++
      cutpoints ++
        map (\ (tr, tau) ->
              (Cooperation_Program.Sharp tr,
                Cooperation_Program.sharp_transition tau))
          tau_s)
    (map (\ (tr, a) -> (Cooperation_Program.Flat tr, a)) lc ++
      map (\ (tr, a) -> (Cooperation_Program.Sharp tr, a)) lc);

check_exists_cut ::
  forall a b c d e.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d, Eq e,
      Shows_Literal.Showl e) => (Term.Term a (b, c) -> String -> String) ->
                                  (d -> Formula.Formula (Term.Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term.Term a (b, c) ->
Formula.Formula (Term.Term a (b, c))) ->
                                      [LTS.Transition_rule a b c
 (Cooperation_Program.Sharp e)] ->
e -> Sum_Type.Sum (String -> String) ();
check_exists_cut showsl_atom logic_checker normalize_lit taus n =
  Check_Monad.check
    (any (\ tau ->
           Cooperation_Program.equal_sharp (LTS.source tau)
             (Cooperation_Program.Flat n) &&
             Cooperation_Program.equal_sharp (LTS.target tau)
               (Cooperation_Program.Sharp n) &&
               Error_Monad.isOK
                 (Cooperation_Program.check_skip_transition showsl_atom
                   logic_checker normalize_lit tau))
      taus)
    (Shows_Literal.showsl_lit "missing skip transition for " .
      Shows_Literal.showsl n);

create_initial_cp_prog ::
  forall a b c d e f.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Eq.Ceq e, Collection_Order.Ccompare e, Compare.Compare_order e,
      Eq e, Set_Impl.Set_impl e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (c, b) -> String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (c, b)) -> Sum_Type.Sum (String -> String) ()) ->
(Bool -> Term.Term a (c, b) -> Formula.Formula (Term.Term a (c, b))) ->
  LTS.Lts_impl a c b e f ->
    [[(Cooperation_Program.Sharp f,
        LTS.Transition_rule a c b (Cooperation_Program.Sharp e))]] ->
      Sum_Type.Sum (String -> String)
        [LTS.Lts_impl a c b (Cooperation_Program.Sharp e)
           (Cooperation_Program.Sharp f)];
create_initial_cp_prog type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p cp_trans_list =
  (case let {
          cp_trans = concat cp_trans_list;
          cut_points =
            List.remdups
              (map (\ (_, tau) -> Cooperation_Program.natural (LTS.source tau))
                cp_trans);
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (Cut_Points.check_cut_points
                   (Cooperation_Program.call_graph_impl p)
                   (List.set cut_points))
                 (\ x ->
                   Sum_Type.Inl
                     (Shows_Literal.showsl_lit
                        "problem in ensuring validity of cutpoints\n" .
                       x)))
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (n, cp) ->
                         Check_Monad.check
                           (LTS.transition_rule type_of_fun bool_types cp)
                           (Cooperation_Program.showsl_sharp n .
                             Shows_Literal.showsl_lit
                               " is non valid transition rule"))
                       cp_trans)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.catch_error
                       (Error_Monad.forallM
                         (check_exists_cut showsl_atom logic_checker
                           normalize_lit (map snd cp_trans))
                         cut_points)
                       (\ x -> Sum_Type.Inl (snd x))))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ -> Sum_Type.Inr (map (make_copy_prog p) cp_trans_list);
  });

}
