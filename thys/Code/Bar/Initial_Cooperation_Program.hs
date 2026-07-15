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
import qualified Compare;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified HOL;
import qualified Arith;
import qualified Term_Rewriting;

make_copy_prog ::
  forall a b c d e.
    Term_Rewriting.Lts_impl a b c d e ->
      [(Term_Rewriting.Sharp e,
         Term_Rewriting.Transition_rule a b c (Term_Rewriting.Sharp d))] ->
        Term_Rewriting.Lts_impl a b c (Term_Rewriting.Sharp d)
          (Term_Rewriting.Sharp e);
make_copy_prog (Term_Rewriting.Lts_Impl init tau_s lc) cutpoints =
  Term_Rewriting.Lts_Impl (map Term_Rewriting.Flat init)
    (map (\ (tr, tau) ->
           (Term_Rewriting.Flat tr, Term_Rewriting.flat_transition tau))
       tau_s ++
      cutpoints ++
        map (\ (tr, tau) ->
              (Term_Rewriting.Sharp tr, Term_Rewriting.sharp_transition tau))
          tau_s)
    (map (\ (tr, a) -> (Term_Rewriting.Flat tr, a)) lc ++
      map (\ (tr, a) -> (Term_Rewriting.Sharp tr, a)) lc);

check_exists_cut ::
  forall a b c d e.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d, Eq e,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a (b, c) ->
                                  String -> String) ->
                                  (d -> Term_Rewriting.Formula
  (Term_Rewriting.Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term_Rewriting.Term a (b, c) ->
Term_Rewriting.Formula (Term_Rewriting.Term a (b, c))) ->
                                      [Term_Rewriting.Transition_rule a b c
 (Term_Rewriting.Sharp e)] ->
e -> Sum_Type.Sum (String -> String) ();
check_exists_cut showsl_atom logic_checker normalize_lit taus n =
  Check_Monad.check
    (any (\ tau ->
           Term_Rewriting.equal_sharp (Term_Rewriting.source tau)
             (Term_Rewriting.Flat n) &&
             Term_Rewriting.equal_sharp (Term_Rewriting.target tau)
               (Term_Rewriting.Sharp n) &&
               Error_Monad.isOK
                 (Term_Rewriting.check_skip_transition showsl_atom logic_checker
                   normalize_lit tau))
      taus)
    (Shows_Literal.showsl_lit "missing skip transition for " .
      Shows_Literal.showsl n);

create_initial_cp_prog ::
  forall a b c d e f.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b, Eq c, Shows_Literal.Showl c,
      HOL.Default d, Shows_Literal.Showl d, Arith.Ceq e, Arith.Ccompare e,
      Compare.Compare_order e, Eq e, Arith.Set_impl e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (Term_Rewriting.Term a (c, b) ->
                                      String -> String) ->
                                      (d ->
Term_Rewriting.Formula (Term_Rewriting.Term a (c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term_Rewriting.Term a (c, b) ->
    Term_Rewriting.Formula (Term_Rewriting.Term a (c, b))) ->
  Term_Rewriting.Lts_impl a c b e f ->
    [[(Term_Rewriting.Sharp f,
        Term_Rewriting.Transition_rule a c b (Term_Rewriting.Sharp e))]] ->
      Sum_Type.Sum (String -> String)
        [Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e)
           (Term_Rewriting.Sharp f)];
create_initial_cp_prog type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p cp_trans_list =
  (case let {
          cp_trans = concat cp_trans_list;
          cut_points =
            Arith.remdups
              (map (\ (_, tau) ->
                     Term_Rewriting.natural (Term_Rewriting.source tau))
                cp_trans);
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (Cut_Points.check_cut_points (Term_Rewriting.call_graph_impl p)
                   (Arith.set cut_points))
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
                           (Term_Rewriting.transition_rule type_of_fun
                             bool_types cp)
                           (Term_Rewriting.showsl_sharp n .
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
