{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Forbidden_Pattern_Loops_Impl(Fp_loop_prf(..), check_fploop) where {

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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Outermost_Loops;
import qualified Forbidden_Pattern_Loops;
import qualified Innermost_Loops_Impl;
import qualified Context_Substitution;
import qualified Sublist;
import qualified HOL;
import qualified Phantom_Type;
import qualified Position;
import qualified Forbidden_Patterns;
import qualified Innermost_Loops;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

data Fp_loop_prf a b =
  FP_loop_prf (Term_Rewriting.Actxt a (Term_Rewriting.Term a b))
    [(b, Term_Rewriting.Term a b)] (Term_Rewriting.Term a b)
    [([Arith.Nat],
       ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         Term_Rewriting.Term a b))];

fp_valid ::
  forall a b c.
    (Compare.Compare a, Eq a, Compare.Compare b, Eq b, Arith.Ceq c,
      Arith.Ccompare c) => Arith.Set
                             (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                               (Term_Rewriting.Term a b, c)) ->
                             Bool;
fp_valid p =
  Arith.ball p
    (\ (l, (la, _)) ->
      not (Term_Rewriting.is_Var
            (Term_Rewriting.intp_actxt Term_Rewriting.Fun l la)));

fp_R_decide ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 Term_Rewriting.Term a b ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
                         Term_Rewriting.Term a b -> Bool;
fp_R_decide mu l oo q c t =
  not (Arith.bex
        (let {
           h = Term_Rewriting.hole_pos c;
           q_s = filter (\ qa -> Position.is_left_of qa q)
                   (Term_Rewriting.poss_list t);
           m1 = map (\ qa -> (Term_Rewriting.subt_at t qa, l)) q_s;
           sterms =
             Arith.remdups
               (map (Innermost_Loops.si_subst mu)
                 (Arith.remdups
                   (concatMap
                     (\ qa ->
                       Innermost_Loops.si_W mu (Term_Rewriting.subt_at t qa))
                     q_s)));
           uterms = concatMap Term_Rewriting.supteq_list sterms;
           m2 = map (\ u -> (u, l)) (Arith.remdups uterms);
           p_s = filter (\ qa -> Position.is_left_of qa h)
                   (Term_Rewriting.poss_list
                     (Term_Rewriting.intp_actxt Term_Rewriting.Fun c t));
           m3 = map (\ p ->
                      (Term_Rewriting.subt_at
                         (Term_Rewriting.intp_actxt Term_Rewriting.Fun c t) p,
                        l))
                  p_s;
           stermsa =
             Arith.remdups
               (map (Innermost_Loops.si_subst mu)
                 (Arith.remdups
                   (concatMap
                     (\ p ->
                       Innermost_Loops.si_W mu
                         (Term_Rewriting.subt_at
                           (Term_Rewriting.intp_actxt Term_Rewriting.Fun c t)
                           p))
                     p_s)));
           utermsa = concatMap Term_Rewriting.supteq_list stermsa;
           m4 = map (\ u -> (u, l)) (Arith.remdups utermsa);
         } in Arith.set (m1 ++ m2 ++ m3 ++ m4))
        (Innermost_Loops_Impl.match_decision mu));

fp_H_decide ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 Term_Rewriting.Term a b ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
                         Term_Rewriting.Term a b -> Bool;
fp_H_decide mu l oo q c t =
  not (Arith.bex
        (Forbidden_Pattern_Loops.h_match_probs (Innermost_Loops.si_subst mu) l
          oo q c t)
        (Innermost_Loops_Impl.match_decision mu));

decompositions :: [Arith.Nat] -> [([Arith.Nat], [Arith.Nat])];
decompositions p =
  map (\ pa -> (pa, Arith.the (Position.remove_prefix pa p)))
    (Position.prefix_list p);

fp_B_decide ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 Term_Rewriting.Term a b ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
                         Term_Rewriting.Term a b -> Bool;
fp_B_decide mu l oo q c t =
  not (Arith.bex
        (Arith.foldr
          (Arith.sup_set .
            (\ qa ->
              Forbidden_Pattern_Loops.h_match_probs
                (Innermost_Loops.si_subst mu) l oo qa c t))
          (Position.proper_prefix_list q)
          (Arith.set_empty
            (Phantom_Type.of_phantom
              (Arith.set_impl_prod ::
                Phantom_Type.Phantom
                  (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
                  Arith.Set_impla))))
        (Innermost_Loops_Impl.match_decision mu)) &&
    not (Arith.bex
          (let {
             p = Term_Rewriting.hole_pos c;
             n = (\ pa -> Forbidden_Pattern_Loops.n0b p pa oo);
             ps = filter
                    (\ (pa, pb) ->
                      Sublist.strict_prefix oo (pb ++ Arith.power p (n pb)) &&
                        Sublist.strict_prefix pa p)
                    (Arith.remdups (decompositions p));
           } in Arith.set
                  (map (\ (pb, pa) ->
                         (Term_Rewriting.subt_at_ctxt c pb,
                           (l, (Term_Rewriting.map_actxt (\ x -> x)
                                  (\ ta ->
                                    Term_Rewriting.eval_term Term_Rewriting.Fun
                                      ta (Innermost_Loops.si_subst mu))
                                  c,
                                 Term_Rewriting.eval_term Term_Rewriting.Fun
                                   (Context_Substitution.ctxt_subst c
                                     (Innermost_Loops.si_subst mu) (n pa) t)
                                   (Innermost_Loops.si_subst mu)))))
                    (Arith.remdups ps)))
          (\ ep ->
            Arith.bex
              (Arith.set_option (Outermost_Loops.ident_prob_of_emp mu ep))
              (all (Innermost_Loops_Impl.ident_decision mu))));

fp_A_decide ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 Term_Rewriting.Term a b ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
                         Term_Rewriting.Term a b -> Bool;
fp_A_decide mu l oo q c t =
  not (Arith.bex
        (case Term_Rewriting.subt_at t q of {
          Term_Rewriting.Var _ ->
            Arith.set_empty
              (Phantom_Type.of_phantom
                (Arith.set_impl_prod ::
                  Phantom_Type.Phantom
                    (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
                    Arith.Set_impla));
          Term_Rewriting.Fun _ _ ->
            let {
              h = Term_Rewriting.hole_pos c;
              n = Forbidden_Pattern_Loops.n0 h q oo;
              hn = Arith.power h n;
              cs = Context_Substitution.ctxt_subst c
                     (Innermost_Loops.si_subst mu) n t;
              q_s = Position.bounded_postfixes q (Term_Rewriting.poss_list t);
              qoo_s =
                concatMap
                  (\ qa ->
                    map (\ a -> (qa, a)) (Position.prefix_list (hn ++ q ++ qa)))
                  q_s;
              qoo_sf =
                filter
                  (\ qoo -> Sublist.strict_prefix (hn ++ q) (snd qoo ++ oo))
                  qoo_s;
              m1 = map (\ qoo -> (Term_Rewriting.subt_at cs (snd qoo), l))
                     qoo_sf;
              sterms =
                Arith.remdups
                  (map (Innermost_Loops.si_subst mu)
                    (Innermost_Loops.si_W mu (Term_Rewriting.subt_at t q)));
              uterms =
                concatMap
                  (filter (\ ta -> not (Term_Rewriting.is_Var ta)) .
                    Term_Rewriting.supteq_list)
                  sterms;
              m2 = map (\ u -> (u, l)) (Arith.remdups uterms);
            } in Arith.set (m1 ++ m2);
        })
        (Innermost_Loops_Impl.match_decision mu));

fp_decide ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 ([Arith.Nat],
                   (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                     Term_Rewriting.Term a b)) ->
                   (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                     (Term_Rewriting.Term a b, Forbidden_Patterns.Location)) ->
                     Bool;
fp_decide mu =
  (\ (q, (c, t)) (l, (la, loc)) ->
    (if Forbidden_Patterns.equal_location loc Forbidden_Patterns.H
      then fp_H_decide mu (Term_Rewriting.intp_actxt Term_Rewriting.Fun l la)
             (Term_Rewriting.hole_pos l) q c t
      else True) &&
      (if Forbidden_Patterns.equal_location loc Forbidden_Patterns.A
        then fp_A_decide mu (Term_Rewriting.intp_actxt Term_Rewriting.Fun l la)
               (Term_Rewriting.hole_pos l) q c t
        else True) &&
        (if Forbidden_Patterns.equal_location loc Forbidden_Patterns.B
          then fp_B_decide mu
                 (Term_Rewriting.intp_actxt Term_Rewriting.Fun l la)
                 (Term_Rewriting.hole_pos l) q c t
          else True) &&
          (if Forbidden_Patterns.equal_location loc Forbidden_Patterns.R
            then fp_R_decide mu
                   (Term_Rewriting.intp_actxt Term_Rewriting.Fun l la)
                   (Term_Rewriting.hole_pos l) q c t
            else True));

showsl_pattern ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term_Rewriting.Actxt a
                                   (Term_Rewriting.Term a b),
                                  (Term_Rewriting.Term a b,
                                    Forbidden_Patterns.Location)) ->
                                  String -> String;
showsl_pattern (c, (s, p)) =
  (((((Shows_Literal.showsl_lit "(" .
        Term_Rewriting.showsl_terma
          (Term_Rewriting.intp_actxt Term_Rewriting.Fun c s)) .
       Shows_Literal.showsl_lit ", ") .
      Position.showsl_pos (Term_Rewriting.hole_pos c)) .
     Shows_Literal.showsl_lit ", ") .
    Forbidden_Patterns.showsl_location p) .
    Shows_Literal.showsl_lit ")";

check_fploop ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Actxt a
                                      (Term_Rewriting.Term a b),
                                     (Term_Rewriting.Term a b,
                                       Forbidden_Patterns.Location))] ->
                                    Fp_loop_prf a b ->
                                      Sum_Type.Sum (String -> String) ();
check_fploop r p (FP_loop_prf c sigma t seq) =
  let {
    mu = Innermost_Loops_Impl.subst_incr sigma;
    mua = Innermost_Loops.si_subst mu;
  } in Error_Monad.bind
         (Check_Monad.check (not (null seq))
           (Shows_Literal.showsl_lit "looping reduction must not be empty"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check
               (Term_Rewriting.equal_term (case Arith.last seq of {
    (_, (_, ta)) -> ta;
  })
                 (Term_Rewriting.intp_actxt Term_Rewriting.Fun c
                   (Term_Rewriting.eval_term Term_Rewriting.Fun t mua)))
               (Shows_Literal.showsl_lit
                 "last term in sequence is not C[t sigma]"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check (fp_valid (Arith.set p))
                   (Shows_Literal.showsl_lit
                     "lhss in forbidden patterns must not be variables"))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ (l, _) ->
                           Check_Monad.check (not (Term_Rewriting.is_Var l))
                             (Shows_Literal.showsl_lit
                               "lhss of TRS must not be variables"))
                         r)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       let {
                         seqa = zip (t : map (\ (_, (_, ta)) -> ta) seq) seq;
                       } in Error_Monad.catch_error
                              (Error_Monad.forallM
                                (\ (ta, (q, (ra, s))) ->
                                  Error_Monad.bind
                                    (Q_Restricted_Rewriting_Impl.check_rstep r q
                                      ra ta s)
                                    (\ _ ->
                                      let {
check_fpstep = fp_decide mu (q, (c, ta));
                                      } in
Error_Monad.catch_error
  (Error_Monad.forallM
    (\ pt ->
      Check_Monad.check (check_fpstep pt)
        (((((((Shows_Literal.showsl_lit "iterating reduction " .
                Term_Rewriting.showsl_terma ta) .
               Shows_Literal.showsl_lit " -->") .
              Position.showsl_pos q) .
             Shows_Literal.showsl_lit " ") .
            Term_Rewriting.showsl_terma s) .
           Shows_Literal.showsl_lit " does not respect forbidden pattern ") .
          showsl_pattern pt))
    p)
  (\ x -> Sum_Type.Inl (snd x))))
                                seqa)
                              (\ x -> Sum_Type.Inl (snd x))))));

}
