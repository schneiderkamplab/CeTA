{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Okui_Criterion_Impl(Ll_rule, check_sim_cps_closed, check_sim_cps_closed_comm)
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
import qualified Rewrite_Relations_Impl;
import qualified Check_Joins;
import qualified Compare;
import qualified Check_Monad;
import qualified Okui_Criterion;
import qualified Mgu_List;
import qualified Position;
import qualified Sublist;
import qualified Error_Monad;
import qualified Missing_List;
import qualified Mgu_generic;
import qualified HOL;
import qualified RenamingN;
import qualified Fresh;
import qualified Mapping;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

newtype Ll_rule b a = LL_Rule
  (Term_Rewriting.Term b a, (Term_Rewriting.Term b a, ([[Arith.Nat]], [a])));

ll_rule_tuple ::
  forall b a.
    Ll_rule b a ->
      (Term_Rewriting.Term b a,
        (Term_Rewriting.Term b a, ([[Arith.Nat]], [a])));
ll_rule_tuple (LL_Rule x) = x;

equal_ll_rule :: forall a b. (Eq a, Eq b) => Ll_rule a b -> Ll_rule a b -> Bool;
equal_ll_rule xa xc =
  (case ll_rule_tuple xa of {
    (l, (r, _)) ->
      (\ (la, (ra, _)) ->
        Term_Rewriting.equal_term l la && Term_Rewriting.equal_term r ra);
  })
    (ll_rule_tuple xc);

instance (Eq a, Eq b) => Eq (Ll_rule a b) where {
  a == b = equal_ll_rule a b;
};

newtype
  X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    a b
  = Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
  (Sum_Type.Sum String
    (Term_Rewriting.Term b a, (Term_Rewriting.Term b a, ([[Arith.Nat]], [a]))));

lhs :: forall a b. Ll_rule a b -> Term_Rewriting.Term a b;
lhs xa = fst (ll_rule_tuple xa);

rhs :: forall a b. Ll_rule a b -> Term_Rewriting.Term a b;
rhs xa = fst (snd (ll_rule_tuple xa));

var_rule_list :: forall a b. Ll_rule a b -> [b];
var_rule_list xa = snd (snd (snd (ll_rule_tuple xa)));

to_Pterm ::
  forall a b.
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term (Sum_Type.Sum (Ll_rule a b) a) b;
to_Pterm (Term_Rewriting.Var x) = Term_Rewriting.Var x;
to_Pterm (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun (Sum_Type.Inr f) (map to_Pterm ts);

join ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Term_Rewriting.Term
                                   (Sum_Type.Sum (Ll_rule a b) a) b ->
                                   Term_Rewriting.Term
                                     (Sum_Type.Sum (Ll_rule a b) a) b ->
                                     Maybe (Term_Rewriting.Term
     (Sum_Type.Sum (Ll_rule a b) a) b);
join (Term_Rewriting.Var x) (Term_Rewriting.Var y) =
  (if x == y then Just (Term_Rewriting.Var x) else Nothing);
join (Term_Rewriting.Fun (Sum_Type.Inr f) asa)
  (Term_Rewriting.Fun (Sum_Type.Inr g) bs) =
  (if f == g && Arith.equal_nat (Arith.size_list asa) (Arith.size_list bs)
    then (case Arith.those (map (\ (a, b) -> join a b) (zip asa bs)) of {
           Nothing -> Nothing;
           Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inr f) xs);
         })
    else Nothing);
join (Term_Rewriting.Fun (Sum_Type.Inl alpha) asa)
  (Term_Rewriting.Fun (Sum_Type.Inl beta) bs) =
  (if equal_ll_rule alpha beta
    then (case Arith.those (map (\ (a, b) -> join a b) (zip asa bs)) of {
           Nothing -> Nothing;
           Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inl alpha) xs);
         })
    else Nothing);
join (Term_Rewriting.Fun (Sum_Type.Inl alpha) asa) (Term_Rewriting.Var v) =
  (case Term_Rewriting.match (Term_Rewriting.Var v) (to_Pterm (lhs alpha)) of {
    Nothing -> Nothing;
    Just sigma ->
      (case Arith.those
              (map (\ (a, b) -> join a b)
                (zip asa (map sigma (var_rule_list alpha))))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term_Rewriting.Fun (Sum_Type.Inl alpha) asa)
  (Term_Rewriting.Fun (Sum_Type.Inr vb) va) =
  (case Term_Rewriting.match (Term_Rewriting.Fun (Sum_Type.Inr vb) va)
          (to_Pterm (lhs alpha))
    of {
    Nothing -> Nothing;
    Just sigma ->
      (case Arith.those
              (map (\ (a, b) -> join a b)
                (zip asa (map sigma (var_rule_list alpha))))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term_Rewriting.Var v) (Term_Rewriting.Fun (Sum_Type.Inl alpha) bs) =
  (case Term_Rewriting.match (Term_Rewriting.Var v) (to_Pterm (lhs alpha)) of {
    Nothing -> Nothing;
    Just sigma ->
      (case Arith.those
              (map (\ (a, b) -> join a b)
                (zip (map sigma (var_rule_list alpha)) bs))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term_Rewriting.Fun (Sum_Type.Inr vb) va)
  (Term_Rewriting.Fun (Sum_Type.Inl alpha) bs) =
  (case Term_Rewriting.match (Term_Rewriting.Fun (Sum_Type.Inr vb) va)
          (to_Pterm (lhs alpha))
    of {
    Nothing -> Nothing;
    Just sigma ->
      (case Arith.those
              (map (\ (a, b) -> join a b)
                (zip (map sigma (var_rule_list alpha)) bs))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term_Rewriting.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term_Rewriting.Fun (Sum_Type.Inr vc) va) (Term_Rewriting.Var vb) =
  Nothing;
join (Term_Rewriting.Var vb) (Term_Rewriting.Fun (Sum_Type.Inr vc) va) =
  Nothing;

target ::
  forall a b.
    (Eq b) => Term_Rewriting.Term (Sum_Type.Sum (Ll_rule a b) a) b ->
                Term_Rewriting.Term a b;
target (Term_Rewriting.Var x) = Term_Rewriting.Var x;
target (Term_Rewriting.Fun (Sum_Type.Inr f) asa) =
  Term_Rewriting.Fun f (map target asa);
target (Term_Rewriting.Fun (Sum_Type.Inl alpha) asa) =
  Term_Rewriting.eval_term Term_Rewriting.Fun (rhs alpha)
    (Term_Rewriting.mk_subst Term_Rewriting.Var
      (zip (var_rule_list alpha) (map target asa)));

join_opt ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Term_Rewriting.Term
                                   (Sum_Type.Sum (Ll_rule a b) a) b ->
                                   Maybe (Term_Rewriting.Term
   (Sum_Type.Sum (Ll_rule a b) a) b) ->
                                     Maybe (Term_Rewriting.Term
     (Sum_Type.Sum (Ll_rule a b) a) b);
join_opt a (Just b) = join a b;
join_opt uu Nothing = Nothing;

join_list ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [Term_Rewriting.Term
                                    (Sum_Type.Sum (Ll_rule a b) a) b] ->
                                   Maybe (Term_Rewriting.Term
   (Sum_Type.Sum (Ll_rule a b) a) b);
join_list [] = Nothing;
join_list [a] = Just a;
join_list (a : v : va) = join_opt a (join_list (v : va));

var_poss_list :: forall a b. Ll_rule a b -> [[Arith.Nat]];
var_poss_list xa = fst (snd (snd (ll_rule_tuple xa)));

in_funposs :: forall a b. [Arith.Nat] -> Term_Rewriting.Term a b -> Bool;
in_funposs (i : p) (Term_Rewriting.Fun f ts) =
  Arith.less_nat i (Arith.size_list ts) && in_funposs p (Arith.nth ts i);
in_funposs [] (Term_Rewriting.Fun uu uv) = True;
in_funposs p (Term_Rewriting.Var uw) = False;

compute_rp ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Term_Rewriting.Term b a -> [[(Ll_rule b a, [Arith.Nat])]];
compute_rp ren r (Term_Rewriting.Var x) = [[]];
compute_rp ren r (Term_Rewriting.Fun f ts) =
  (map concat . Missing_List.concat_lists)
    (map (\ (x, y) ->
           map (map (Arith.map_prod id (\ a -> x : a))) (compute_rp ren r y))
      (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts)) ++
    concatMap
      (\ rule ->
        let {
          ps = filter (\ y -> not (null y)) (var_poss_list rule);
          rec = map (\ p ->
                      (if in_funposs p (Term_Rewriting.Fun f ts)
                        then map (map (Arith.map_prod id (\ a -> p ++ a)))
                               (compute_rp ren r
                                 (Term_Rewriting.subt_at
                                   (Term_Rewriting.Fun f ts) p))
                        else [[]]))
                  ps;
        } in map (\ a -> (rule, []) : a)
               ((map concat . Missing_List.concat_lists) rec))
      (filter
        (\ rule ->
          not (Arith.is_none
                (Mgu_generic.mgu_vd_list ren
                  [(Term_Rewriting.Fun f ts, lhs rule)])))
        r);

rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                   a b ->
                                   Sum_Type.Sum String
                                     (Term_Rewriting.Term b a,
                                       (Term_Rewriting.Term b a,
 ([[Arith.Nat]], [a])));
rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
  (Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    x)
  = x;

sel21 ::
  forall b a.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl a) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                   b a ->
                                   Ll_rule a b;
sel21 xa =
  LL_Rule
    (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
            xa
      of {
      Sum_Type.Inl _ -> ll_rule_tuple (error "undefined");
      Sum_Type.Inr x2 -> x2;
    });

sel11 ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                   a b ->
                                   String;
sel11 xa =
  (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
          xa
    of {
    Sum_Type.Inl x1 -> x1;
  });

dis1 ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                   a b ->
                                   Bool;
dis1 xa =
  (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
          xa
    of {
    Sum_Type.Inl _ -> True;
    Sum_Type.Inr _ -> False;
  });

rep_isom ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                   a b ->
                                   Sum_Type.Sum String (Ll_rule b a);
rep_isom x =
  (if dis1 x then Sum_Type.Inl (sel11 x) else Sum_Type.Inr (sel21 x));

to_ll_rule_intern ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => (Term_Rewriting.Term a b, Term_Rewriting.Term c b) ->
                             Sum_Type.Sum String
                               (Term_Rewriting.Term a b,
                                 (Term_Rewriting.Term c b,
                                   ([[Arith.Nat]], [b])));
to_ll_rule_intern rule =
  let {
    xs = Term_Rewriting.vars_term_list (fst rule);
  } in Error_Monad.bind
         (Check_Monad.check (not (Term_Rewriting.is_Var (fst rule)))
           "variable left-hand side in rule")
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (Term_Rewriting.linear_term (fst rule))
               "left-hand side is not linear ")
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq
                     (Term_Rewriting.insert_vars_term (snd rule) []) xs)
                   (\ _ -> Sum_Type.Inl "free variable in right-hand side"))
                 (\ _ ->
                   Sum_Type.Inr
                     (fst rule,
                       (snd rule,
                         (Term_Rewriting.var_poss_list (fst rule), xs))))));

to_ll_rule_lift_aux ::
  forall a b.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                     b a;
to_ll_rule_lift_aux xa =
  Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    (to_ll_rule_intern xa);

to_ll_rule_lift ::
  forall a b.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   Sum_Type.Sum String (Ll_rule a b);
to_ll_rule_lift x = rep_isom (to_ll_rule_lift_aux x);

to_ll_rule ::
  forall a b.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   Sum_Type.Sum (String -> String)
                                     (Ll_rule a b);
to_ll_rule rule =
  Error_Monad.catch_error (to_ll_rule_lift rule)
    (\ x ->
      Sum_Type.Inl
        (((Term_Rewriting.showsl_lit "rule " .
            Term_Rewriting.showsl_rule rule) .
           Term_Rewriting.showsl_lit
             " is not a well-formed left-linear rule\n") .
          Term_Rewriting.showsl_lit x));

sim_cp_non_root_of ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 Ll_rule b a ->
                   [Arith.Nat] ->
                     Ll_rule b a ->
                       [(Ll_rule b a, [Arith.Nat])] ->
                         [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                            Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b)
                              a)];
sim_cp_non_root_of ren alpha q beta rdpA =
  let {
    rdp_A = (alpha, []) : rdpA;
    renamed_lhs_alpha_s =
      Okui_Criterion.rename_list ren (map (\ (alphaa, _) -> lhs alphaa) rdp_A);
    l = Term_Rewriting.intp_actxt Term_Rewriting.Fun
          (Term_Rewriting.ctxt_of_pos_term q (Arith.hda renamed_lhs_alpha_s))
          (Term_Rewriting.map_term (\ x -> x) (RenamingN.rename_single ren)
            (lhs beta));
  } in (case Mgu_List.mgu_list
               (map (\ (x, y) -> (x, Term_Rewriting.subt_at l y))
                 (zip renamed_lhs_alpha_s (map snd rdp_A)))
         of {
         Nothing -> [];
         Just tau ->
           let {
             asa = map (\ (a, b) ->
                         (case a of {
                           (alpha_i, pi) ->
                             (\ i ->
                               Term_Rewriting.intp_actxt Term_Rewriting.Fun
                                 (Term_Rewriting.ctxt_of_pos_term pi
                                   (to_Pterm
                                     (Term_Rewriting.eval_term
                                       Term_Rewriting.Fun l tau)))
                                 (Term_Rewriting.Fun (Sum_Type.Inl alpha_i)
                                   (map ((to_Pterm . tau) .
  Mgu_generic.rename_many ren i)
                                     (var_rule_list alpha_i))));
                         })
                           b)
                     (zip rdp_A
                       (Arith.upt Arith.zero_nat (Arith.size_list rdp_A)));
           } in (case join_list asa of {
                  Nothing -> [];
                  Just a ->
                    let {
                      b = Term_Rewriting.intp_actxt Term_Rewriting.Fun
                            (Term_Rewriting.ctxt_of_pos_term q
                              (to_Pterm
                                (Term_Rewriting.eval_term Term_Rewriting.Fun l
                                  tau)))
                            (Term_Rewriting.Fun (Sum_Type.Inl beta)
                              (map ((to_Pterm . tau) .
                                     RenamingN.rename_single ren)
                                (var_rule_list beta)));
                    } in [(a, b)];
                });
       });

non_root_rdps ::
  forall a b c d.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Ll_rule c d ->
                     [Arith.Nat] ->
                       Term_Rewriting.Term b a ->
                         [[(Ll_rule b a, [Arith.Nat])]];
non_root_rdps ren r alpha q ll =
  map concat
    (Missing_List.concat_lists
      (map (\ p ->
             (if Sublist.prefix q p && in_funposs (Position.pos_diff p q) ll
               then map (map (Arith.map_prod id (\ a -> p ++ a)))
                      (compute_rp ren r
                        (Term_Rewriting.subt_at ll (Position.pos_diff p q)))
               else [[]]))
        (var_poss_list alpha)));

non_root_sim_cps ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Ll_rule b a ->
                     [Arith.Nat] ->
                       Ll_rule b a ->
                         [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                            Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b)
                              a)];
non_root_sim_cps ren r alpha q beta =
  concatMap (sim_cp_non_root_of ren alpha q beta)
    (non_root_rdps ren r alpha q (lhs beta));

sim_cp_non_root_impl ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_non_root_impl ren r s =
  concatMap
    (\ alpha ->
      concatMap
        (\ q ->
          concatMap (non_root_sim_cps ren r alpha q)
            (filter
              (\ beta ->
                not (Arith.is_none
                      (Mgu_generic.mgu_vd_list ren
                        [(lhs beta, Term_Rewriting.subt_at (lhs alpha) q)])))
              s))
        (filter (\ y -> not (null y))
          (Term_Rewriting.fun_poss_list (lhs alpha))))
    r;

sim_cp_root_of ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 Ll_rule b a ->
                   [(Ll_rule b a, [Arith.Nat])] ->
                     [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_root_of ren rule rdp_A =
  let {
    l = Term_Rewriting.map_term (\ x -> x) (RenamingN.rename_single ren)
          (lhs rule);
    renamed_lhs_alpha_s =
      Okui_Criterion.rename_list ren (map (\ (alpha, _) -> lhs alpha) rdp_A);
  } in (case Mgu_List.mgu_list
               (map (\ (x, y) -> (x, Term_Rewriting.subt_at l y))
                 (zip renamed_lhs_alpha_s (map snd rdp_A)))
         of {
         Nothing -> [];
         Just tau ->
           let {
             asa = map (\ ((alpha_i, pi), y) ->
                         Term_Rewriting.intp_actxt Term_Rewriting.Fun
                           (Term_Rewriting.ctxt_of_pos_term pi
                             (to_Pterm
                               (Term_Rewriting.eval_term Term_Rewriting.Fun l
                                 tau)))
                           (Term_Rewriting.Fun (Sum_Type.Inl alpha_i)
                             (map ((to_Pterm . tau) .
                                    Mgu_generic.rename_many ren y)
                               (var_rule_list alpha_i))))
                     (zip rdp_A
                       (Arith.upt Arith.zero_nat (Arith.size_list rdp_A)));
           } in (case join_list asa of {
                  Nothing -> [];
                  Just a ->
                    let {
                      b = Term_Rewriting.Fun (Sum_Type.Inl rule)
                            (map ((to_Pterm . tau) .
                                   RenamingN.rename_single ren)
                              (var_rule_list rule));
                    } in [(a, b)];
                });
       });

sim_cp_root_impl ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_root_impl ren r s =
  concatMap
    (\ rule ->
      concatMap (sim_cp_root_of ren rule)
        (filter (\ y -> not (null y)) (compute_rp ren r (lhs rule))))
    s;

sim_cp_impl ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term_Rewriting.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_impl ren r s = sim_cp_root_impl ren r s ++ sim_cp_non_root_impl ren r s;

to_ll_rules ::
  forall a b.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Sum_Type.Sum (String -> String)
                                     [Ll_rule a b];
to_ll_rules = Error_Monad.mapM to_ll_rule;

sim_cps_impl ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
sim_cps_impl ren r s = map (Arith.map_prod target target) (sim_cp_impl ren r s);

check_sim_cps_equiv :: Bool;
check_sim_cps_equiv = False;

check_sim_cps_closed_joins ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       Check_Joins.Cp_join_hints a b ->
 Sum_Type.Sum (String -> String) ();
check_sim_cps_closed_joins r s scps (Check_Joins.CP_Auto n) =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (sa, t) ->
          Check_Monad.check
            (Check_Joins.is_mstep_join r s
              (if Arith.equal_nat n Arith.zero_nat then Nothing else Just n) t
              sa)
            (((((Term_Rewriting.showsl_lit "the simultaneous critical pair " .
                  Term_Rewriting.showsl_terma sa) .
                 Term_Rewriting.showsl_lit " <-o- . -> ") .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " is not almost closed within ") .
              (if Arith.equal_nat n Arith.zero_nat
                then Term_Rewriting.showsl_lit " one multistep"
                else Term_Rewriting.showsl_nat n .
                       Term_Rewriting.showsl_lit " steps.")))
        scps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (x . Term_Rewriting.showsl_lit
               "\nhence the it could not shown that the sim.-crit pairs are closed\n"));
check_sim_cps_closed_joins r s scps (Check_Joins.CP_Sequences cps) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ scp ->
          Check_Monad.check
            (Term_Rewriting.equal_term (fst scp) (snd scp) ||
              any (\ cp ->
                    Term_Rewriting.instance_rule scp
                      (Check_Joins.cp_left cp, Check_Joins.cp_right cp))
                cps)
            (Term_Rewriting.showsl_lit "could not find critical pair " .
              Term_Rewriting.showsl_prod scp))
        scps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ scp ->
              Check_Monad.check
                (if check_sim_cps_equiv
                  then (if not (Term_Rewriting.equal_term (fst scp) (snd scp))
                         then any (Term_Rewriting.instance_rule scp) scps
                         else True)
                  else True)
                ((Term_Rewriting.showsl_lit "pair " .
                   Term_Rewriting.showsl_prod scp) .
                  Term_Rewriting.showsl_lit
                    " is not a simultaneous critical pair"))
            (map (\ cp -> (Check_Joins.cp_left cp, Check_Joins.cp_right cp))
              cps))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ cp ->
                Error_Monad.catch_error
                  (Check_Joins.check_single_rsteps_join_sequence_gen
                    (Rewrite_Relations_Impl.is_mstep r) "" s ""
                    (Check_Joins.cp_right cp) (Check_Joins.cp_left cp)
                    (reverse (Check_Joins.cp_join cp)))
                  (\ x ->
                    Sum_Type.Inl
                      (((((Term_Rewriting.showsl_lit
                             "problem with sim. crit pair " .
                            Term_Rewriting.showsl_terma
                              (Check_Joins.cp_left cp)) .
                           Term_Rewriting.showsl_lit " <-o- . -> ") .
                          Term_Rewriting.showsl_terma
                            (Check_Joins.cp_right cp)) .
                         Term_Rewriting.showsl_literal "\n") .
                        x)))
              cps)
            (\ x -> Sum_Type.Inl (snd x))));

check_sim_cps_closed ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Compare.Compare b, Eq b,
      Term_Rewriting.Showl b) => RenamingN.RenamingN a ->
                                   [(Term_Rewriting.Term b a,
                                      Term_Rewriting.Term b a)] ->
                                     Check_Joins.Cp_join_hints b a ->
                                       Sum_Type.Sum (String -> String) ();
check_sim_cps_closed ren r infos =
  Error_Monad.catch_error
    (Error_Monad.bind (to_ll_rules r)
      (\ rules ->
        check_sim_cps_closed_joins r r (sim_cps_impl ren rules rules) infos))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "problem checking Okui\'s simultenous critical pair condition\n" .
          x));

check_sim_cps_closed_comm ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Compare.Compare b, Eq b,
      Term_Rewriting.Showl b) => RenamingN.RenamingN a ->
                                   [(Term_Rewriting.Term b a,
                                      Term_Rewriting.Term b a)] ->
                                     [(Term_Rewriting.Term b a,
Term_Rewriting.Term b a)] ->
                                       Check_Joins.Cp_join_hints b a ->
 Sum_Type.Sum (String -> String) ();
check_sim_cps_closed_comm ren r s infos =
  Error_Monad.catch_error
    (Error_Monad.bind (to_ll_rules r)
      (\ rules ->
        Error_Monad.bind (to_ll_rules s)
          (\ srules ->
            check_sim_cps_closed_joins r s (sim_cps_impl ren rules srules)
              infos)))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "problem checking Okui\'s simultenous critical pair condition\n" .
          x));

}
