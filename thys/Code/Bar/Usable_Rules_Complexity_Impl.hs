{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Usable_Rules_Complexity_Impl(usable_rules_complexity,
                                smart_rule_shift_complexity)
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
import qualified Map_Choice;
import qualified Missing_List;
import qualified Icap_Impl;
import qualified Term_Order;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Compare_Order_Instances;
import qualified Innermost_Usable_Rules_Impl;
import qualified HOL;
import qualified Usable_Replacement_Map_Impl;
import qualified Termination_Problem_Spec;
import qualified Term_Rewriting;
import qualified Compare;
import qualified Shows_Literal;
import qualified Complexity;
import qualified Sum_Type;
import qualified Arith;

extract_rt_C_D ::
  forall a b.
    Complexity.Complexity_measure a b ->
      Sum_Type.Sum (String -> String) ([(a, Arith.Nat)], [(a, Arith.Nat)]);
extract_rt_C_D (Complexity.Runtime_Complexity c d) = Sum_Type.Inr (c, d);
extract_rt_C_D (Complexity.Derivational_Complexity v) =
  Sum_Type.Inl (Shows_Literal.showsl_lit "runtime complexity required");

usable_rules_complexity_innermost ::
  forall a b.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                  [Arith.Char] () ->
                                  [(Term_Rewriting.Term b [Arith.Char],
                                     Term_Rewriting.Term b [Arith.Char])] ->
                                    Complexity.Complexity_measure b
                                      [Arith.Char] ->
                                      Complexity.Complexity_class ->
a -> Sum_Type.Sum (String -> String) a;
usable_rules_complexity_innermost i nUr cm cc cp =
  Error_Monad.catch_error
    (let {
       s = Termination_Problem_Spec.r i cp;
       w = Termination_Problem_Spec.rw i cp;
       r = s ++ w;
     } in Error_Monad.bind
            (Check_Monad.check
              (Termination_Problem_Spec.nFQ_subset_NF_rules i cp)
              (Shows_Literal.showsl_lit "innermost required"))
            (\ _ ->
              Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                (\ _ ->
                  Error_Monad.bind (extract_rt_C_D cm)
                    (\ (cl, dl) ->
                      let {
                        c = Arith.set cl;
                        d = Arith.set dl;
                        isnf = Termination_Problem_Spec.is_QNF i cp;
                      } in Error_Monad.bind
                             (Check_Monad.check
                               (null (Arith.inter_list_set cl
                                       (Term_Rewriting.defined_list r)))
                               ((Shows_Literal.showsl_lit "constructors " .
                                  Shows_Literal.showsl_lista cl) .
                                 Shows_Literal.showsl_lit
                                   " must not be defined"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Check_Monad.check_subseteq nUr r)
                                   (\ _ ->
                                     Sum_Type.Inl
                                       ((Shows_Literal.showsl_lit "rule " .
  Term_Rewriting.showsl_rules nUr) .
 Shows_Literal.showsl_lit " does not occur in problem")))
                                 (\ _ ->
                                   let {
                                     ur = Missing_List.list_diff r nUr;
                                   } in Error_Monad.bind
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) ->
        Check_Monad.check
          (not (Arith.member (Arith.the (Term_Rewriting.root l)) d &&
                 Arith.less_eq_set
                   (Arith.foldr (Arith.sup_set . Term_Rewriting.funas_term)
                     (Term_Rewriting.args l) Arith.bot_set)
                   c))
          (Term_Rewriting.showsl_rule (l, ra) .
            Shows_Literal.showsl_lit " should be usable"))
      nUr)
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    (case Usable_Replacement_Map_Impl.get_fs_mu r (Icap_Impl.icap_impl isnf r)
            True cm
      of {
      (_, (mu, _)) ->
        let {
          is_urc =
            Innermost_Usable_Rules_Impl.is_ur_closed_af_impl_tp_mv i cp mu ur;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ (l, ra) ->
                     Check_Monad.check (is_urc (Term_Rewriting.args l) ra)
                       ((Shows_Literal.showsl_lit
                           "problem with closure properties of usable rule " .
                          Term_Rewriting.showsl_rule (l, ra)) .
                         Shows_Literal.showsl_lit
                           ": rhs is not closed under usable rules"))
                   ur)
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 Sum_Type.Inr
                   (Termination_Problem_Spec.mk i
                     (Termination_Problem_Spec.nfs i cp)
                     (Termination_Problem_Spec.q i cp)
                     (Missing_List.list_diff s nUr)
                     (Missing_List.list_diff w nUr)));
    }))))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "error when restricting to innermost usable rules\n" .
          x));

usable_rules_complexity_usymbols ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Set_impl b, Shows_Literal.Showl b, Compare.Compare c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  [(Term_Rewriting.Term b c,
                                     Term_Rewriting.Term b c)] ->
                                    Complexity.Complexity_measure b c ->
                                      Complexity.Complexity_class ->
a -> Sum_Type.Sum (String -> String) a;
usable_rules_complexity_usymbols i nUr cm cc cp =
  Error_Monad.catch_error
    (let {
       s = Termination_Problem_Spec.r i cp;
       w = Termination_Problem_Spec.rw i cp;
       r = s ++ w;
     } in Error_Monad.bind
            (Error_Monad.catch_error (Check_Monad.check_subseteq nUr r)
              (\ _ ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "rule " .
                     Term_Rewriting.showsl_rules nUr) .
                    Shows_Literal.showsl_lit " does not occur in problem")))
            (\ _ ->
              let {
                ur = Missing_List.list_diff r nUr;
                us = Arith.set
                       (concatMap (Term_Rewriting.funas_term_list . snd) ur ++
                         Complexity.get_signature_of_cm cm);
                urs = Arith.set ur;
              } in Error_Monad.bind (Term_Rewriting.check_varcond_subset ur)
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ lr ->
                               Check_Monad.check
                                 (if Arith.less_eq_set
                                       (Term_Rewriting.funas_term (fst lr)) us
                                   then Arith.member lr urs else True)
                                 ((Shows_Literal.showsl_lit "rule " .
                                    Term_Rewriting.showsl_rule lr) .
                                   Shows_Literal.showsl_lit
                                     " should be usable"))
                             r)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Sum_Type.Inr
                             (Termination_Problem_Spec.mk i
                               (Termination_Problem_Spec.nfs i cp)
                               (Termination_Problem_Spec.q i cp)
                               (Missing_List.list_diff s nUr)
                               (Missing_List.list_diff w nUr))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "error when restricting to usable rules w.r.t. usable symbols\n" .
          x));

usable_rules_complexity ::
  forall a b.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                  [Arith.Char] () ->
                                  [(Term_Rewriting.Term b [Arith.Char],
                                     Term_Rewriting.Term b [Arith.Char])] ->
                                    Complexity.Complexity_measure b
                                      [Arith.Char] ->
                                      Complexity.Complexity_class ->
a -> Sum_Type.Sum (String -> String) a;
usable_rules_complexity i nUr cm cc cp =
  (case usable_rules_complexity_usymbols i nUr cm cc cp of {
    Sum_Type.Inl e ->
      (case usable_rules_complexity_innermost i nUr cm cc cp of {
        Sum_Type.Inl ea ->
          Sum_Type.Inl
            ((((Shows_Literal.showsl_lit
                  "neither of the usable rules processors is applicable:\n" .
                 Shows_Literal.showsl_lit
                   "the one via usable symbols complains as follows\n") .
                e) .
               Shows_Literal.showsl_lit
                 "\n\nand the one via icap and innermost says\n") .
              ea);
        Sum_Type.Inr a -> Sum_Type.Inr a;
      });
    Sum_Type.Inr a -> Sum_Type.Inr a;
  });

is_ur_closed_af_impl_tp_mv_impl ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b,
      Arith.Ccompare b) => ([Term_Rewriting.Term a [Arith.Char]] ->
                             Term_Rewriting.Term a [Arith.Char] ->
                               Term_Rewriting.Term a
                                 (Sum_Type.Sum () [Arith.Char])) ->
                             (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                               [(Term_Rewriting.Term a [Arith.Char], b)] ->
                                 ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                   Arith.Set
                                     (Term_Rewriting.Term a [Arith.Char], b) ->
                                     [Term_Rewriting.Term a [Arith.Char]] ->
                                       Term_Rewriting.Term a [Arith.Char] ->
 Bool;
is_ur_closed_af_impl_tp_mv_impl ic qnf r pi =
  let {
    urc = (\ s ->
            Innermost_Usable_Rules_Impl.is_ur_closed_term_af_impl qnf (ic s) pi
              r);
  } in (\ u s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
         } in (\ t ->
                urc sa u sa
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

rule_shift_complexity_urm_ur_tt ::
  forall a b.
    (Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                  [Arith.Char] () ->
                                  Term_Rewriting.Rel_impl_ext b [Arith.Char]
                                    () ->
                                    [(Term_Rewriting.Term b [Arith.Char],
                                       Term_Rewriting.Term b [Arith.Char])] ->
                                      [(Term_Rewriting.Term b [Arith.Char],
 Term_Rewriting.Term b [Arith.Char])] ->
Complexity.Complexity_measure b [Arith.Char] ->
  Complexity.Complexity_class -> a -> Sum_Type.Sum (String -> String) a;
rule_shift_complexity_urm_ur_tt i rp rdelete ur cm cc tp =
  let {
    rb = Termination_Problem_Spec.rules i tp;
    r = Termination_Problem_Spec.r i tp;
    rw = Termination_Problem_Spec.rw i tp;
    r2 = Map_Choice.ceta_list_diff r rdelete;
    rremain = rw ++ r2;
    isnf = Termination_Problem_Spec.is_QNF i tp;
    inn = Termination_Problem_Spec.nFQ_subset_NF_rules i tp;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq rdelete rb)
                   (\ x ->
                     Sum_Type.Inl
                       ((Shows_Literal.showsl_lit "rule " .
                          Term_Rewriting.showsl_rule x) .
                         Shows_Literal.showsl_lit
                           " should be deleted, but does not occur in problem")))
                 (\ _ ->
                   Error_Monad.bind (Term_Rewriting.check_wf_trs rb)
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (Termination_Problem_Spec.nFQ_subset_NF_rules i tp)
                           (Shows_Literal.showsl_lit "innermost required"))
                         (\ _ ->
                           (case Usable_Replacement_Map_Impl.get_fs_mu_DP rb
                                   (Icap_Impl.icap_impl isnf rb) inn rdelete cm
                             of {
                             (fs, (mu, info)) ->
                               (case Usable_Replacement_Map_Impl.get_fs_mu_DP rb
                                       (Icap_Impl.icap_impl isnf rb) inn rremain
                                       cm
                                 of {
                                 (_, (pi, _)) ->
                                   Error_Monad.bind (extract_rt_C_D cm)
                                     (\ (cl, dl) ->
                                       let {
 c = Arith.set cl;
 d = Arith.set dl;
                                       } in
 Error_Monad.bind
   (Check_Monad.check
     (null (Arith.inter_list_set cl (Term_Rewriting.defined_list rb)))
     ((Shows_Literal.showsl_lit "constructors " .
        Shows_Literal.showsl_lista cl) .
       Shows_Literal.showsl_lit " must not be defined"))
   (\ _ ->
     Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
       (\ _ ->
         Error_Monad.bind
           (Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (l, ra) ->
                 Check_Monad.check
                   (not (Arith.member (Arith.the (Term_Rewriting.root l)) d &&
                          Arith.less_eq_set
                            (Arith.foldr
                              (Arith.sup_set . Term_Rewriting.funas_term)
                              (Term_Rewriting.args l) Arith.bot_set)
                            c))
                   (Term_Rewriting.showsl_rule (l, ra) .
                     Shows_Literal.showsl_lit " should be usable"))
               (Missing_List.list_diff rb ur))
             (\ x -> Sum_Type.Inl (snd x)))
           (\ _ ->
             let {
               ic = Icap_Impl.icap_impl_tp i tp;
               qnf = Termination_Problem_Spec.is_QNF i tp;
               ra = Termination_Problem_Spec.rules i tp;
               uu = Arith.set ur;
               is_urc = is_ur_closed_af_impl_tp_mv_impl ic qnf ra mu uu;
               pia = Term_Order.af_inter (Term_Rewriting.af rp) pi;
               is_urc_pi = is_ur_closed_af_impl_tp_mv_impl ic qnf ra pia uu;
             } in Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (l, rc) ->
                          Check_Monad.check
                            (is_urc (Term_Rewriting.args l) rc &&
                              is_urc_pi (Term_Rewriting.args l) rc)
                            ((Shows_Literal.showsl_lit
                                "problem with closure properties of usable rule " .
                               Term_Rewriting.showsl_rule (l, rc)) .
                              Shows_Literal.showsl_lit
                                ": rhs is not closed under usable rules"))
                        ur)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Error_Monad.catch_error
                            (Error_Monad.forallM
                              (\ f ->
                                Check_Monad.check
                                  (Arith.less_eq_set (mu f)
                                    (Term_Rewriting.mono_af rp f))
                                  (((((Shows_Literal.showsl_lit
 "error in monotonicity: strict order for " .
Shows_Literal.showsl_prod f) .
                                       Shows_Literal.showsl_lit
 " ensures monotonicity in positions ") .
                                      Usable_Replacement_Map_Impl.showsl_position_set
f (Term_Rewriting.mono_af rp f)) .
                                     Shows_Literal.showsl_lit
                                       "\nbut usable replacement map is ") .
                                    Usable_Replacement_Map_Impl.showsl_position_set
                                      f (mu f)))
                              fs)
                            (\ x -> Sum_Type.Inl (snd x)))
                          (\ x ->
                            Sum_Type.Inl
                              (((((x . Shows_Literal.showsl_lit
 "\nthe computed usable replacement map (") .
                                   Shows_Literal.showsl_literal info) .
                                  Shows_Literal.showsl_lit ") is\n") .
                                 Shows_Literal.showsl_sep
                                   (\ f ->
                                     ((Shows_Literal.showsl_lit "mu(" .
Shows_Literal.showsl_prod f) .
                                       Shows_Literal.showsl_lit ") = ") .
                                       Usable_Replacement_Map_Impl.showsl_position_set
 f (mu f))
                                   (Shows_Literal.showsl_literal "\n") fs) .
                                Shows_Literal.showsl_lit
                                  "\nand mu(f) = {} for all other symbols f")))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Term_Rewriting.rel_impl_s rp
                                (Arith.inter_list_set rdelete ur))
                              (\ x ->
                                Sum_Type.Inl
                                  (Shows_Literal.showsl_lit
                                     "problem when orienting strict TRS\n" .
                                    x)))
                            (\ _ ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Term_Rewriting.rel_impl_ns rp
                                    (Arith.inter_list_set rremain ur))
                                  (\ x ->
                                    Sum_Type.Inl
                                      (Shows_Literal.showsl_lit
 "problem when orienting non-strict TRS\n" .
x)))
                                (\ _ ->
                                  Error_Monad.catch_error
                                    (Term_Rewriting.cpx rp cm cc)
                                    (\ x ->
                                      Sum_Type.Inl
(Shows_Literal.showsl_lit "problem when ensuring complexity of order\n" .
  x))))))))));
                               });
                           })))))
               (\ x ->
                 Sum_Type.Inl
                   (((((((Shows_Literal.showsl_lit
                            "could not derive the intended complexity " .
                           Complexity.showsl_complexity_class cc) .
                          Shows_Literal.showsl_lit " from the following\n") .
                         Term_Rewriting.desc rp) .
                        Shows_Literal.showsl_literal "\n") .
                       x) .
                      Shows_Literal.showsl_lit "\nwith usable rules\n") .
                     Term_Rewriting.showsl_trs ur))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tp)
               (Termination_Problem_Spec.q i tp) r2
               (Missing_List.list_union rw rdelete));
       });

smart_rule_shift_complexity ::
  forall a b.
    (Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                  [Arith.Char] () ->
                                  Term_Rewriting.Rel_impl_ext b [Arith.Char]
                                    () ->
                                    [(Term_Rewriting.Term b [Arith.Char],
                                       Term_Rewriting.Term b [Arith.Char])] ->
                                      Maybe [(Term_Rewriting.Term b
        [Arith.Char],
       Term_Rewriting.Term b [Arith.Char])] ->
Complexity.Complexity_measure b [Arith.Char] ->
  Complexity.Complexity_class -> a -> Sum_Type.Sum (String -> String) a;
smart_rule_shift_complexity i rp rdelete (Just ur) cm cc tp =
  rule_shift_complexity_urm_ur_tt i rp rdelete ur cm cc tp;
smart_rule_shift_complexity i rp rdelete Nothing cm cc tp =
  Usable_Replacement_Map_Impl.rule_shift_complexity_urm_tt i rp rdelete cm cc
    tp;

}
