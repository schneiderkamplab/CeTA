{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Joins(Crit_pair_info(..), Cp_join_hints(..), cp_peak, cpPeak,
               is_mstep_join, is_par_rsteps_join, cp_right, cp_left, cp_join,
               is_rsteps_join_one, is_rsteps_join_two, is_rsteps_conversion,
               is_rsteps_conversiona, cp_poss, cp_labels,
               is_toyama_par_rstep_join, check_conversion_sequence,
               check_generic_decreasing_sequence, check_rl_decreasing_sequence,
               check_par_rsteps_join_sequence, check_toyama_pcp_join_sequence,
               check_rl_par_decreasing_sequence)
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
import qualified Error_Monad;
import qualified Check_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Rewrite_Relations_Impl;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

data Crit_pair_info a b =
  Crit_Pair_Info (Term_Rewriting.Term a b) (Maybe (Term_Rewriting.Term a b))
    (Term_Rewriting.Term a b) [Term_Rewriting.Term a b] (Maybe [[Arith.Nat]])
    (Maybe (Arith.Nat, Arith.Nat));

data Cp_join_hints a b = CP_Auto Arith.Nat | CP_Sequences [Crit_pair_info a b];

cp_peak :: forall a b. Crit_pair_info a b -> Maybe (Term_Rewriting.Term a b);
cp_peak (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x2;

cpPeak :: forall a b. Crit_pair_info a b -> Term_Rewriting.Term a b;
cpPeak = Arith.the . cp_peak;

check_steps ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                 Term_Rewriting.Term a b ->
                   [Term_Rewriting.Term a b] ->
                     Term_Rewriting.Term a b ->
                       (Term_Rewriting.Term a b, [Term_Rewriting.Term a b]);
check_steps f s [] u = (if f s u then (u, []) else (s, []));
check_steps f s (t : ts) u =
  (if Term_Rewriting.equal_term s t || f s t then check_steps f t ts u
    else (s, t : ts));

is_mstep_join ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Maybe Arith.Nat ->
                                      Term_Rewriting.Term a b ->
Term_Rewriting.Term a b -> Bool;
is_mstep_join r sa (Just n) s t =
  not (Arith.is_none
        (Arith.find (Rewrite_Relations_Impl.is_mstep r s)
          (Term_Rewriting.reachable_terms sa t n)));
is_mstep_join r sa Nothing s t =
  not (Arith.is_none
        (Arith.find (Rewrite_Relations_Impl.is_mstep r s)
          (Rewrite_Relations_Impl.mstep_rewrite sa t)));

finalize_steps ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => a -> [a] ->
                                       a -> Sum_Type.Sum (String -> String) ();
finalize_steps x xs y =
  Check_Monad.check (x == y)
    (let {
       z = (case xs of {
             [] -> y;
             z : _ -> z;
           });
     } in (((Shows_Literal.showsl_lit "got stuck at step from " .
              Shows_Literal.showsl x) .
             Shows_Literal.showsl_lit " to ") .
            Shows_Literal.showsl z) .
            Shows_Literal.showsl_literal "\n");

is_rsteps_join ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Arith.Nat ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Bool;
is_rsteps_join r sa n s t =
  let {
    ss = Term_Rewriting.reachable_terms sa t n;
  } in any (Arith.membera ss) (Term_Rewriting.reachable_terms r s n);

is_par_rsteps_join ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Maybe Arith.Nat ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Bool;
is_par_rsteps_join r sa (Just n) s t =
  not (Arith.is_none
        (Arith.find (Rewrite_Relations_Impl.is_par_rstep r s)
          (Term_Rewriting.reachable_terms sa t n)));
is_par_rsteps_join r sa Nothing s t =
  not (Arith.is_none
        (Arith.find (Rewrite_Relations_Impl.is_par_rstep r s)
          (Rewrite_Relations_Impl.parallel_rewrite sa t)));

cp_right :: forall a b. Crit_pair_info a b -> Term_Rewriting.Term a b;
cp_right (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x3;

cp_left :: forall a b. Crit_pair_info a b -> Term_Rewriting.Term a b;
cp_left (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x1;

cp_join :: forall a b. Crit_pair_info a b -> [Term_Rewriting.Term a b];
cp_join (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x4;

check_join_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Term_Rewriting.Term a b ->
                                      Term_Rewriting.Term a b ->
[Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_join_sequence r sa s t terms =
  (case check_steps (Rewrite_Relations_Impl.is_par_rstep r) s terms t of {
    (x, xs) ->
      (case check_steps
              (\ sb ta -> Rewrite_Relations_Impl.is_par_rstep sa ta sb) x xs t
        of {
        (y, ys) ->
          Error_Monad.catch_error (finalize_steps y ys t)
            (\ xa ->
              Sum_Type.Inl
                (((((Shows_Literal.showsl_lit "could not ensure " .
                      Term_Rewriting.showsl_terma s) .
                     Shows_Literal.showsl_lit " ->* . *<- ") .
                    Term_Rewriting.showsl_terma t) .
                   Shows_Literal.showsl_literal "\n") .
                  xa));
      });
  });

is_rsteps_join_one ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Cp_join_hints a b ->
                                    Sum_Type.Sum (String -> String)
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
Sum_Type.Sum (String -> String) ());
is_rsteps_join_one r (CP_Auto n) =
  Sum_Type.Inr
    (\ (s, t) ->
      Check_Monad.check (is_rsteps_join r r n s t)
        (((((Shows_Literal.showsl_nat n .
              Shows_Literal.showsl_lit
                " steps do not suffice to show joinability of ") .
             Term_Rewriting.showsl_terma s) .
            Shows_Literal.showsl_lit " and ") .
           Term_Rewriting.showsl_terma t) .
          Shows_Literal.showsl_literal "\n"));
is_rsteps_join_one r (CP_Sequences cp_infos) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ cp ->
            check_join_sequence r r (cp_left cp) (cp_right cp) (cp_join cp))
          cp_infos)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ x ->
        Sum_Type.Inl
          ((x . Shows_Literal.showsl_lit "\nunderlying TRS:\n") .
            Term_Rewriting.showsl_rules r)))
    (\ _ ->
      Sum_Type.Inr
        (\ (s, t) ->
          Check_Monad.check
            (Term_Rewriting.equal_term s t ||
              any (\ cp ->
                    Term_Rewriting.instance_rule (s, t)
                      (cp_left cp, cp_right cp) ||
                      Term_Rewriting.instance_rule (s, t)
                        (cp_right cp, cp_left cp))
                cp_infos)
            ((((Shows_Literal.showsl_literal
                  " could not find joining sequence for " .
                 Term_Rewriting.showsl_terma s) .
                Shows_Literal.showsl_lit " and ") .
               Term_Rewriting.showsl_terma t) .
              Shows_Literal.showsl_literal "\n")));

is_rsteps_join_two ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Cp_join_hints a b ->
                                      Sum_Type.Sum (String -> String)
((Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
  Sum_Type.Sum (String -> String) ());
is_rsteps_join_two r s (CP_Auto n) =
  Sum_Type.Inr
    (\ (sa, t) ->
      Check_Monad.check (is_rsteps_join r s n sa t)
        (((((Shows_Literal.showsl_nat n .
              Shows_Literal.showsl_lit
                " steps do not suffice to show joinability of ") .
             Term_Rewriting.showsl_terma sa) .
            Shows_Literal.showsl_lit " and ") .
           Term_Rewriting.showsl_terma t) .
          Shows_Literal.showsl_literal "\n"));
is_rsteps_join_two r s (CP_Sequences cp_infos) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ cp ->
            check_join_sequence r s (cp_left cp) (cp_right cp) (cp_join cp))
          cp_infos)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ x ->
        Sum_Type.Inl
          (((((x . Shows_Literal.showsl_lit "\nunderlying TRSs:\n") .
               Term_Rewriting.showsl_rules r) .
              Shows_Literal.showsl_literal "\n") .
             Shows_Literal.showsl_literal "\n") .
            Term_Rewriting.showsl_rules s)))
    (\ _ ->
      Sum_Type.Inr
        (\ (sa, t) ->
          Check_Monad.check
            (Term_Rewriting.equal_term sa t ||
              any (\ cp ->
                    Term_Rewriting.instance_rule (sa, t)
                      (cp_left cp, cp_right cp))
                cp_infos)
            ((((Shows_Literal.showsl_literal
                  " could not find joining sequence for " .
                 Term_Rewriting.showsl_terma sa) .
                Shows_Literal.showsl_lit " and ") .
               Term_Rewriting.showsl_terma t) .
              Shows_Literal.showsl_literal "\n")));

check_optional_step ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                 Term_Rewriting.Term a b ->
                   [Term_Rewriting.Term a b] ->
                     Term_Rewriting.Term a b ->
                       (Term_Rewriting.Term a b, [Term_Rewriting.Term a b]);
check_optional_step f s [] u = (if f s u then (u, []) else (s, []));
check_optional_step f s (t : ts) u =
  (if Term_Rewriting.equal_term s t then check_optional_step f s ts u
    else (if f s t then (t, ts) else (s, t : ts)));

is_rsteps_conversion ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Arith.Nat ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Bool;
is_rsteps_conversion r s = is_rsteps_join r s;

check_rewrite_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Term_Rewriting.Term a b ->
                                    Term_Rewriting.Term a b ->
                                      [Term_Rewriting.Term a b] ->
Sum_Type.Sum (String -> String) ();
check_rewrite_sequence r s t terms =
  (case check_steps (Rewrite_Relations_Impl.is_par_rstep r) s terms t of {
    (y, ys) ->
      Error_Monad.catch_error (finalize_steps y ys t)
        (\ x ->
          Sum_Type.Inl
            (((((Shows_Literal.showsl_lit "could not ensure " .
                  Term_Rewriting.showsl_terma s) .
                 Shows_Literal.showsl_lit " ->* ") .
                Term_Rewriting.showsl_terma t) .
               Shows_Literal.showsl_literal "\n") .
              x));
  });

is_rsteps_conversiona ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Cp_join_hints a b ->
                                      Sum_Type.Sum (String -> String)
(Term_Rewriting.Term a b ->
  Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ());
is_rsteps_conversiona r s (CP_Auto n) =
  Sum_Type.Inr
    (\ sa t ->
      Check_Monad.check (is_rsteps_conversion r s n sa t)
        (((((Shows_Literal.showsl_nat n .
              Shows_Literal.showsl_lit
                " steps do not suffice to show convertibility of ") .
             Term_Rewriting.showsl_terma sa) .
            Shows_Literal.showsl_lit " and ") .
           Term_Rewriting.showsl_terma t) .
          Shows_Literal.showsl_literal "\n"));
is_rsteps_conversiona r s (CP_Sequences cp_infos) =
  let {
    rs = r ++ map Arith.swap s;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.catch_error
             (Error_Monad.forallM
               (\ cp ->
                 check_rewrite_sequence rs (cp_left cp) (cp_right cp)
                   (cp_join cp))
               cp_infos)
             (\ x -> Sum_Type.Inl (snd x)))
           (\ x ->
             Sum_Type.Inl
               ((x . Shows_Literal.showsl_lit "\nunderlying TRS:\n") .
                 Term_Rewriting.showsl_rules rs)))
         (\ _ ->
           Sum_Type.Inr
             (\ sa t ->
               Check_Monad.check
                 (Term_Rewriting.equal_term sa t ||
                   any (\ cp ->
                         Term_Rewriting.instance_rule (sa, t)
                           (cp_left cp, cp_right cp))
                     cp_infos)
                 ((((Shows_Literal.showsl_literal
                       " could not find conversion for " .
                      Term_Rewriting.showsl_terma sa) .
                     Shows_Literal.showsl_lit " and ") .
                    Term_Rewriting.showsl_terma t) .
                   Shows_Literal.showsl_literal "\n")));

cp_poss :: forall a b. Crit_pair_info a b -> Maybe [[Arith.Nat]];
cp_poss (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x5;

cp_labels :: forall a b. Crit_pair_info a b -> Maybe (Arith.Nat, Arith.Nat);
cp_labels (Crit_Pair_Info x1 x2 x3 x4 x5 x6) = x6;

is_toyama_par_rstep_join ::
  forall a b c d.
    (Compare.Compare a, Eq a, Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b, Compare.Compare c,
      Eq c) => Arith.Nat ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     Term_Rewriting.Mctxt c b ->
                       Term_Rewriting.Term a b ->
                         d -> Term_Rewriting.Term a b -> Bool;
is_toyama_par_rstep_join n r sa c s peak t =
  any (Rewrite_Relations_Impl.is_par_rstep_var_restr r
        (Term_Rewriting.vars_mctxt c) t)
    (Term_Rewriting.reachable_terms sa s n);

check_conversion_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Term_Rewriting.Term a b ->
                                    Term_Rewriting.Term a b ->
                                      [Term_Rewriting.Term a b] ->
Sum_Type.Sum (String -> String) ();
check_conversion_sequence r s t terms =
  let {
    c = r ++ map Arith.swap r;
  } in (case check_steps (Rewrite_Relations_Impl.is_par_rstep c) s terms t of {
         (y, ys) ->
           Error_Monad.catch_error (finalize_steps y ys t)
             (\ x ->
               Sum_Type.Inl
                 (((((Shows_Literal.showsl_lit "could not ensure " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " <->* ") .
                     Term_Rewriting.showsl_terma t) .
                    Shows_Literal.showsl_literal "\n") .
                   x));
       });

check_generic_decreasing_sequence ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                  Bool) ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Bool) ->
                                    ((Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                      Bool) ->
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
Bool) ->
((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool) ->
  ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool) ->
    String ->
      Term_Rewriting.Term a b ->
        Term_Rewriting.Term a b ->
          [Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_generic_decreasing_sequence rSk sm rSkma rSkm rk rSm rel_descr s t terms =
  (case check_steps (\ sa ta -> rSk (sa, ta)) s terms t of {
    (v, vs) ->
      (case check_optional_step (\ sa ta -> sm (sa, ta)) v vs t of {
        (w, ws) ->
          (case check_steps (\ sa ta -> rSkma (sa, ta)) w ws t of {
            (wa, wsa) ->
              (case check_steps (\ sa ta -> rSkm (sa, ta)) wa wsa t of {
                (u, us) ->
                  (case check_optional_step (\ sa ta -> rk (sa, ta)) u us t of {
                    (z, zs) ->
                      (case check_steps (\ sa ta -> rSm (sa, ta)) z zs t of {
                        (y, ys) ->
                          Error_Monad.catch_error (finalize_steps y ys t)
                            (\ x ->
                              Sum_Type.Inl
                                (((((Shows_Literal.showsl_lit
                                       "could not ensure " .
                                      Term_Rewriting.showsl_terma s) .
                                     Shows_Literal.showsl_lit rel_descr) .
                                    Term_Rewriting.showsl_terma t) .
                                   Shows_Literal.showsl_literal "\n") .
                                  x));
                      });
                  });
              });
          });
      });
  });

check_rl_decreasing_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)] ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  Term_Rewriting.Term a b ->
    Term_Rewriting.Term a b ->
      [Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_rl_decreasing_sequence rlk rm rkm rk rlm =
  check_generic_decreasing_sequence
    (\ (s, t) -> (case (s, t) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rlk) a b;
                 }))
    (\ (s, t) -> (case (s, t) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rm) a b;
                 }))
    (\ (s, t) -> (case (s, t) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rkm) a b;
                 }))
    (\ (s, t) -> (case (t, s) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rkm) a b;
                 }))
    (\ (s, t) -> (case (t, s) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rk) a b;
                 }))
    (\ (s, t) -> (case (t, s) of {
                   (a, b) -> Term_Rewriting.is_rstep (Arith.set rlm) a b;
                 }))
    " ->* . -> . ->* . *<- . <- . *<- ";

check_par_rsteps_join_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  String ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      String ->
Term_Rewriting.Term a b ->
  Term_Rewriting.Term a b ->
    [Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_par_rsteps_join_sequence ra r sb sa s t terms =
  (case check_optional_step (Rewrite_Relations_Impl.is_par_rstep ra) s terms t
    of {
    (v, vs) ->
      (case check_steps
              (\ sc ta ->
                (case (ta, sc) of {
                  (a, b) -> Term_Rewriting.is_rstep (Arith.set sb) a b;
                }))
              v vs t
        of {
        (w, ws) ->
          Error_Monad.catch_error (finalize_steps w ws t)
            (\ x ->
              Sum_Type.Inl
                (((((Shows_Literal.showsl_lit "could not ensure " .
                      Term_Rewriting.showsl_terma s) .
                     Shows_Literal.showsl_lit
                       ((((" -||," ++ r) ++ "-> . *<-") ++ sa) ++ "- ")) .
                    Term_Rewriting.showsl_terma t) .
                   Shows_Literal.showsl_literal "\n") .
                  x));
      });
  });

check_toyama_pcp_join_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Card_UNIV b,
      Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  String ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      String ->
Arith.Set b ->
  Term_Rewriting.Term a b ->
    Term_Rewriting.Term a b ->
      [Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_toyama_pcp_join_sequence ra r sb sa v s t terms =
  (case check_steps
          (\ sc ta -> (case (sc, ta) of {
                        (a, b) -> Term_Rewriting.is_rstep (Arith.set sb) a b;
                      }))
          s terms t
    of {
    (va, vs) ->
      (case check_optional_step
              (\ sc ta ->
                Rewrite_Relations_Impl.is_par_rstep_var_restr ra v ta sc)
              va vs t
        of {
        (w, ws) ->
          Error_Monad.catch_error (finalize_steps w ws t)
            (\ x ->
              Sum_Type.Inl
                ((((Shows_Literal.showsl_lit "could not ensure " .
                     Term_Rewriting.showsl_terma s) .
                    Shows_Literal.showsl_lit
                      ((((" -" ++ sa) ++ "->* . <-||,") ++ r) ++ "- ")) .
                   Term_Rewriting.showsl_terma t) .
                  x));
      });
  });

check_rl_par_decreasing_sequence ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Card_UNIV b,
      Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)] ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  Arith.Set b ->
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term a b ->
        [Term_Rewriting.Term a b] -> Sum_Type.Sum (String -> String) ();
check_rl_par_decreasing_sequence rSk sm rSkm rk rSm v =
  check_generic_decreasing_sequence
    (\ (a, b) -> Rewrite_Relations_Impl.is_par_rstep rSk a b)
    (\ (a, b) -> Rewrite_Relations_Impl.is_par_rstep sm a b)
    (\ (a, b) -> Rewrite_Relations_Impl.is_par_rstep rSkm a b) (\ _ -> False)
    (\ (s, t) -> Rewrite_Relations_Impl.is_par_rstep_var_restr rk v t s)
    (\ (a, b) -> Rewrite_Relations_Impl.is_par_rstep rSm a b)
    " <->* . -||-> . <->* . <-||- . <->* ";

}
