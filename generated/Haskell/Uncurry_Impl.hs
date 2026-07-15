{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Uncurry_Impl(Uncurry_nt_proof(..), uncurry_tt, uncurry_proc_both,
                uncurry_nonterm_tt)
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
import qualified Map;
import qualified Tcap_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Uncurry;
import qualified Termination_Problem_Spec;
import qualified Mapping;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Utility;
import qualified HOL;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Uncurry_nt_proof a b c =
  Uncurry_nt_proof
    (Labelings.Lab a b,
      ([((Labelings.Lab a b, Arith.Nat), [Labelings.Lab a b])],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)])))
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)];

fmap ::
  forall a b.
    (Eq a,
      Eq b) => Labelings.Lab a b ->
                 Arith.Nat ->
                   [((Labelings.Lab a b, Arith.Nat), [Labelings.Lab a b])] ->
                     Labelings.Lab a b -> Arith.Nat -> Labelings.Lab a b;
fmap a nn sml =
  let {
    m = Arith.suc
          (Utility.max_list
            (map Labelings.label_depth (a : concatMap snd sml)));
  } in (\ f n -> (if (f, n) == (a, nn) then a else Labelings.gen_label f m));

check_partition :: forall a. (Eq a) => [[a]] -> Sum_Type.Sum a ();
check_partition xss = Check_Monad.check_pairwise Check_Monad.check_disjoint xss;

check_inj ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => Labelings.Lab a b ->
                                   Arith.Nat ->
                                     [((Labelings.Lab a b, Arith.Nat),
[Labelings.Lab a b])] ->
                                       Sum_Type.Sum (String -> String) ();
check_inj a nn sml =
  let {
    symbols =
      map (\ (aa, b) ->
            (case aa of {
              (_, n) ->
                (\ fs ->
                  map (\ (g, i) ->
                        (g, Arith.plus_nat n
                              (Arith.times_nat i
                                (Arith.minus_nat nn Arith.one_nat))))
                    (zip fs (Arith.upt Arith.zero_nat (Arith.size_list fs))));
            })
              b)
        sml;
    fsymbols = concat symbols;
  } in Error_Monad.bind
         (Error_Monad.catch_error (check_partition symbols)
           (\ x ->
             Sum_Type.Inl
               ((Term_Rewriting.showsl_lit "symbol " .
                  Term_Rewriting.showsl_prod x) .
                 Term_Rewriting.showsl_lit " occurs twice)")))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (not (Arith.membera fsymbols (a, nn)))
               ((Term_Rewriting.showsl_lit "application symbol" .
                  Term_Rewriting.showsl_lab a) .
                 Term_Rewriting.showsl_lit " must not occur as new symbol"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check (not (Arith.membera (map fst sml) (a, nn)))
                   ((Term_Rewriting.showsl_lit "application symbol" .
                      Term_Rewriting.showsl_lab a) .
                     Term_Rewriting.showsl_lit " must not be uncurried"))
                 (\ _ ->
                   (if Arith.less_eq_nat nn Arith.one_nat
                     then Error_Monad.catch_error
                            (Error_Monad.forallM
                              (Check_Monad.check_pairwise
                                (\ gn1 gn2 ->
                                  Check_Monad.check (not (gn1 == gn2))
                                    ((Term_Rewriting.showsl_lit "symbol " .
                                       Term_Rewriting.showsl_prod gn1) .
                                      Term_Rewriting.showsl_lit
" occurs twice")))
                              symbols)
                            (\ x -> Sum_Type.Inl (snd x))
                     else Sum_Type.Inr ()))));

uncurry_of_sig_list ::
  forall a.
    a -> [((a, Arith.Nat), [a])] ->
           (a -> Arith.Nat -> [a]) ->
             [(Term_Rewriting.Term a [Arith.Char],
                Term_Rewriting.Term a [Arith.Char])];
uncurry_of_sig_list a sml sm =
  concatMap
    (\ (b, c) ->
      (case b of {
        (f, n) ->
          (\ _ ->
            let {
              g = Uncurry.get_symbol sm f n;
            } in map (\ i ->
                       (Term_Rewriting.Fun a
                          [Uncurry.generate_f_xs (g i) (Arith.plus_nat n i),
                            Term_Rewriting.Var
                              (Uncurry.generate_var (Arith.plus_nat n i))],
                         Uncurry.generate_f_xs (g (Arith.suc i))
                           (Arith.plus_nat n (Arith.suc i))))
                   (Arith.upt Arith.zero_nat (Uncurry.aarity sm f n)));
      })
        c)
    sml;

sig_list_to_sig_map ::
  forall a.
    (Eq a) => a -> [((a, Arith.Nat), [a])] ->
                     ([((a, Arith.Nat), [a])] -> a -> Arith.Nat -> a) ->
                       a -> Arith.Nat -> [a];
sig_list_to_sig_map a sml fmap =
  let {
    fm = fmap sml;
  } in (\ f n -> (case Map.map_of sml (f, n) of {
                   Nothing -> [fm f n];
                   Just xs -> (if null xs then [fm f n] else xs);
                 }));

uncurry_eta_split ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     ([(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)],
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)]);
uncurry_eta_split eboth rtest =
  let {
    test =
      (\ (l, r) ->
        Arith.less_nat Arith.zero_nat
          (Arith.size_list (Term_Rewriting.args l)) &&
          Arith.less_nat Arith.zero_nat
            (Arith.size_list (Term_Rewriting.args r)) &&
            any (Term_Rewriting.eq_rule_mod_vars
                  (Arith.hda (Term_Rewriting.args l),
                    Arith.hda (Term_Rewriting.args r)))
              rtest);
  } in Arith.partition test eboth;

eta_closed_rules ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => a -> (a -> Arith.Nat -> [a]) ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    Sum_Type.Sum (String -> String) ();
eta_closed_rules a sm ra r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, raa) ->
        (case Uncurry.aarity_term a sm l of {
          Nothing -> Sum_Type.Inr ();
          Just ab ->
            (if Arith.equal_nat ab Arith.zero_nat then Sum_Type.Inr ()
              else Check_Monad.check
                     (any (\ (lll, rrr) ->
                            (case (lll, rrr) of {
                              (Term_Rewriting.Var _, _) -> False;
                              (Term_Rewriting.Fun _ [], _) -> False;
                              (Term_Rewriting.Fun _ [_], _) -> False;
                              (Term_Rewriting.Fun _ [_, Term_Rewriting.Var _],
                                Term_Rewriting.Var _)
                                -> False;
                              (Term_Rewriting.Fun _ [_, Term_Rewriting.Var _],
                                Term_Rewriting.Fun _ [])
                                -> False;
                              (Term_Rewriting.Fun _ [_, Term_Rewriting.Var _],
                                Term_Rewriting.Fun _ [_])
                                -> False;
                              (Term_Rewriting.Fun f [ll, Term_Rewriting.Var x],
                                Term_Rewriting.Fun g [rr, Term_Rewriting.Var y])
                                -> f == a &&
                                     g == a &&
                                       x == y &&
 not (Arith.membera (Term_Rewriting.insert_vars_rule (ll, rr) []) x) &&
   Term_Rewriting.instance_rule (l, raa) (ll, rr);
                              (Term_Rewriting.Fun _ [_, Term_Rewriting.Var _],
                                Term_Rewriting.Fun _
                                  (_ : Term_Rewriting.Var _ : _ : _))
                                -> False;
                              (Term_Rewriting.Fun _ [_, Term_Rewriting.Var _],
                                Term_Rewriting.Fun _
                                  (_ : Term_Rewriting.Fun _ _ : _))
                                -> False;
                              (Term_Rewriting.Fun _
                                 (_ : Term_Rewriting.Var _ : _ : _),
                                _)
                                -> False;
                              (Term_Rewriting.Fun _
                                 (_ : Term_Rewriting.Fun _ _ : _),
                                _)
                                -> False;
                            }))
                       r)
                     ((Term_Rewriting.showsl_lit "eta expansion of " .
                        Term_Rewriting.showsl_rule (l, raa)) .
                       Term_Rewriting.showsl_lit " missing"));
        }))
      ra)
    (\ x -> Sum_Type.Inl (snd x));

uncurry_rules ::
  forall a b.
    (Eq a) => a -> (a -> Arith.Nat -> [a]) ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
uncurry_rules a sm =
  map (\ (l, r) -> (Uncurry.uncurry_term a sm l, Uncurry.uncurry_term a sm r));

uncurry_tt ::
  forall a b.
    (Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   (b, ([((b, Arith.Nat), [b])],
 ([(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])],
   [(Term_Rewriting.Term b [Arith.Char],
      Term_Rewriting.Term b [Arith.Char])]))) ->
                                     [(Term_Rewriting.Term b [Arith.Char],
Term_Rewriting.Term b [Arith.Char])] ->
                                       a -> Sum_Type.Sum (String -> String) a;
uncurry_tt i info r tp =
  (case info of {
    (a, (sml, (u, eb))) ->
      let {
        ra = Termination_Problem_Spec.r i tp;
        rw = Termination_Problem_Spec.rw i tp;
      } in (case uncurry_eta_split eb ra of {
             (e, ew) ->
               let {
                 r_eta = e ++ ra;
                 rw_eta = ew ++ rw;
                 rb_eta = r_eta ++ rw_eta;
                 fmap = (\ _ f _ -> f);
                 sm = sig_list_to_sig_map a sml fmap;
                 uR = uncurry_rules a sm r_eta;
                 uRw = uncurry_rules a sm rw_eta;
               } in (case let {
                            s = uncurry_of_sig_list a sml sm;
                          } in Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ (l, _) ->
                                       Check_Monad.check (Uncurry.hvf_term a l)
 ((Term_Rewriting.showsl_lit "head variable in lhs " .
    Term_Rewriting.showsl_terma l) .
   Term_Rewriting.showsl_lit " not allowed"))
                                     r_eta)
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Error_Monad.catch_error
                                       (Error_Monad.forallM
 (\ (l, _) ->
   Check_Monad.check (Uncurry.hvf_term a l)
     ((Term_Rewriting.showsl_lit "head variable in lhs " .
        Term_Rewriting.showsl_terma l) .
       Term_Rewriting.showsl_lit " not allowed"))
 rw_eta)
                                       (\ x -> Sum_Type.Inl (snd x)))
                                     (\ _ ->
                                       Error_Monad.bind
 (eta_closed_rules a sm r_eta r_eta)
 (\ _ ->
   Error_Monad.bind (eta_closed_rules a sm rb_eta rb_eta)
     (\ _ ->
       Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ (l, rb) ->
               Check_Monad.check (not (Term_Rewriting.is_Var l))
                 (Term_Rewriting.showsl_lit
                    "lhs must not be a variable in rule " .
                   Term_Rewriting.showsl_rule (l, rb)))
             rw_eta)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error (Check_Monad.check_subseteq uR r)
               (\ x ->
                 Sum_Type.Inl
                   ((Term_Rewriting.showsl_lit "uncurried rule " .
                      Term_Rewriting.showsl_rule x) .
                     Term_Rewriting.showsl_lit " is missing")))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error (Check_Monad.check_subseteq uRw r)
                   (\ x ->
                     Sum_Type.Inl
                       ((Term_Rewriting.showsl_lit "uncurried rule " .
                          Term_Rewriting.showsl_rule x) .
                         Term_Rewriting.showsl_lit " is missing")))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Term_Rewriting.check_CS_subseteq s u)
                       (\ x ->
                         Sum_Type.Inl
                           ((Term_Rewriting.showsl_lit "uncurry rule " .
                              Term_Rewriting.showsl_rule x) .
                             Term_Rewriting.showsl_lit " is missing")))
                     (\ _ ->
                       Error_Monad.catch_error (Check_Monad.check_subseteq u r)
                         (\ x ->
                           Sum_Type.Inl
                             ((Term_Rewriting.showsl_lit "uncurry rule " .
                                Term_Rewriting.showsl_rule x) .
                               Term_Rewriting.showsl_lit
                                 " is missing in new TRS"))))))))))
                      of {
                      Sum_Type.Inl aa -> Sum_Type.Inl aa;
                      Sum_Type.Inr _ ->
                        Sum_Type.Inr
                          (Termination_Problem_Spec.mk i
                            (Termination_Problem_Spec.nfs i tp) [] uR
                            (uRw ++ u));
                    });
           });
  });

only_eta_rules ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Sum_Type.Sum (String -> String) ();
only_eta_rules e r_eta =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, r) ->
        Check_Monad.check
          (case (l, r) of {
            (Term_Rewriting.Var _, _) -> False;
            (Term_Rewriting.Fun _ _, Term_Rewriting.Var _) -> False;
            (Term_Rewriting.Fun f ls, Term_Rewriting.Fun g rs) ->
              f == g &&
                Arith.equal_nat (Arith.size_list ls)
                  (Arith.nat_of_integer (2 :: Integer)) &&
                  Arith.equal_nat (Arith.size_list rs)
                    (Arith.nat_of_integer (2 :: Integer)) &&
                    Term_Rewriting.equal_term (Arith.nth ls Arith.one_nat)
                      (Arith.nth rs Arith.one_nat) &&
                      any (\ (la, ra) ->
                            Term_Rewriting.instance_rule
                              (Arith.hda ls, Arith.hda rs) (la, ra))
                        r_eta;
          })
          ((Term_Rewriting.showsl_lit "rule " .
             Term_Rewriting.showsl_rule (l, r)) .
            Term_Rewriting.showsl_lit
              " is not an (eta-expanded) original rule"))
      e)
    (\ x -> Sum_Type.Inl (snd x));

uncurry_proc ::
  forall a b.
    (Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   (b, ([((b, Arith.Nat), [b])],
 ([(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])],
   [(Term_Rewriting.Term b [Arith.Char],
      Term_Rewriting.Term b [Arith.Char])]))) ->
                                     ([((b, Arith.Nat), [b])] ->
                                       b -> Arith.Nat -> b) ->
                                       (b ->
 Arith.Nat -> [((b, Arith.Nat), [b])] -> Sum_Type.Sum (String -> String) ()) ->
 [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
   [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
     a -> Sum_Type.Sum (String -> String) a;
uncurry_proc i info fmap check_inj p r dpp =
  (case info of {
    (a, (sml, (u, eb))) ->
      let {
        pa = Dependency_Pair_Problem_Spec.p i dpp;
        pw = Dependency_Pair_Problem_Spec.pw i dpp;
        ra = Dependency_Pair_Problem_Spec.r i dpp;
        rw = Dependency_Pair_Problem_Spec.rw i dpp;
        nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
        m = Dependency_Pair_Problem_Spec.minimal i dpp;
      } in (case uncurry_eta_split eb ra of {
             (e, ew) ->
               let {
                 sm = sig_list_to_sig_map a sml fmap;
                 uP = uncurry_rules a sm pa;
                 uPw = uncurry_rules a sm pw;
                 r_eta = e ++ ra;
                 rw_eta = ew ++ rw;
                 uR = uncurry_rules a sm r_eta;
                 uRw = uncurry_rules a sm rw_eta;
               } in (case let {
                            s = uncurry_of_sig_list a sml sm;
                          } in Error_Monad.bind
                                 (Check_Monad.check
                                   (null (Dependency_Pair_Problem_Spec.q i dpp))
                                   (Term_Rewriting.showsl_lit
                                     "strategy not supported for uncurrying"))
                                 (\ _ ->
                                   Error_Monad.bind (only_eta_rules e r_eta)
                                     (\ _ ->
                                       Error_Monad.bind
 (only_eta_rules ew rw_eta)
 (\ _ ->
   Error_Monad.bind (check_inj a (Arith.nat_of_integer (2 :: Integer)) sml)
     (\ _ ->
       Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ (l, _) ->
               Check_Monad.check (not (Term_Rewriting.is_Var l))
                 (Term_Rewriting.showsl_lit "lhs as variable is not allowed"))
             (ra ++ rw))
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ (l, _) ->
                   Check_Monad.check (Uncurry.hvf_term a l)
                     ((Term_Rewriting.showsl_lit "head variable in lhs " .
                        Term_Rewriting.showsl_terma l) .
                       Term_Rewriting.showsl_lit " not allowed"))
                 pa)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ (l, _) ->
                       Check_Monad.check (Uncurry.hvf_term a l)
                         ((Term_Rewriting.showsl_lit "head variable in lhs " .
                            Term_Rewriting.showsl_terma l) .
                           Term_Rewriting.showsl_lit " not allowed"))
                     pw)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ (l, _) ->
                           Check_Monad.check (Uncurry.hvf_term a l)
                             ((Term_Rewriting.showsl_lit
                                 "head variable in lhs " .
                                Term_Rewriting.showsl_terma l) .
                               Term_Rewriting.showsl_lit " not allowed"))
                         r_eta)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, _) ->
                               Check_Monad.check (Uncurry.hvf_term a l)
                                 ((Term_Rewriting.showsl_lit
                                     "head variable in lhs " .
                                    Term_Rewriting.showsl_terma l) .
                                   Term_Rewriting.showsl_lit " not allowed"))
                             rw_eta)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Error_Monad.bind (eta_closed_rules a sm r_eta r_eta)
                             (\ _ ->
                               Error_Monad.bind
                                 (eta_closed_rules a sm rw_eta rw_eta)
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Error_Monad.catch_error
                                       (Check_Monad.check_subseteq uP p)
                                       (\ x ->
 Sum_Type.Inl
   ((Term_Rewriting.showsl_lit "uncurried pair " .
      Term_Rewriting.showsl_rule x) .
     Term_Rewriting.showsl_lit " is missing")))
                                     (\ _ ->
                                       Error_Monad.bind
 (Error_Monad.catch_error (Check_Monad.check_subseteq uPw p)
   (\ x ->
     Sum_Type.Inl
       ((Term_Rewriting.showsl_lit "uncurried pair " .
          Term_Rewriting.showsl_rule x) .
         Term_Rewriting.showsl_lit " is missing")))
 (\ _ ->
   Error_Monad.bind
     (Error_Monad.catch_error (Check_Monad.check_subseteq uR r)
       (\ x ->
         Sum_Type.Inl
           ((Term_Rewriting.showsl_lit "uncurried rule " .
              Term_Rewriting.showsl_rule x) .
             Term_Rewriting.showsl_lit " is missing")))
     (\ _ ->
       Error_Monad.bind
         (Error_Monad.catch_error (Check_Monad.check_subseteq uRw r)
           (\ x ->
             Sum_Type.Inl
               ((Term_Rewriting.showsl_lit "uncurried rule " .
                  Term_Rewriting.showsl_rule x) .
                 Term_Rewriting.showsl_lit " is missing")))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error (Term_Rewriting.check_CS_subseteq s u)
               (\ x ->
                 Sum_Type.Inl
                   ((Term_Rewriting.showsl_lit "uncurry rule " .
                      Term_Rewriting.showsl_rule x) .
                     Term_Rewriting.showsl_lit " is missing")))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error (Term_Rewriting.check_CS_subseteq u s)
                   (\ x ->
                     Sum_Type.Inl
                       ((Term_Rewriting.showsl_lit "rule " .
                          Term_Rewriting.showsl_rule x) .
                         Term_Rewriting.showsl_lit " is not an uncurry rule")))
                 (\ _ ->
                   Error_Monad.catch_error (Check_Monad.check_subseteq u r)
                     (\ x ->
                       Sum_Type.Inl
                         ((Term_Rewriting.showsl_lit "uncurry rule " .
                            Term_Rewriting.showsl_rule x) .
                           Term_Rewriting.showsl_lit
                             " is missing in new TRS")))))))))))))))))))
                      of {
                      Sum_Type.Inl aa -> Sum_Type.Inl aa;
                      Sum_Type.Inr _ ->
                        Sum_Type.Inr
                          (Dependency_Pair_Problem_Spec.mk i nfs m uP uPw [] uR
                            (uRw ++ u));
                    });
           });
  });

uncurry_of_top_sig_list ::
  forall a.
    a -> Arith.Nat ->
           [((a, Arith.Nat), [a])] ->
             (a -> Arith.Nat -> [a]) ->
               [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])];
uncurry_of_top_sig_list a m sml sm =
  concatMap
    (\ (b, c) ->
      (case b of {
        (f, n) ->
          (\ _ ->
            let {
              g = Uncurry.get_symbol sm f n;
            } in map (\ i ->
                       (Term_Rewriting.Fun a
                          (Uncurry.generate_f_xs (g i) (Arith.plus_nat n i) :
                            map (\ ia ->
                                  Term_Rewriting.Var (Uncurry.generate_var ia))
                              (Arith.upt (Arith.plus_nat n i)
                                (Arith.plus_nat (Arith.plus_nat n i)
                                  (Arith.minus_nat m Arith.one_nat)))),
                         Uncurry.generate_f_xs (g (Arith.suc i))
                           (Arith.plus_nat (Arith.plus_nat n i)
                             (Arith.minus_nat m Arith.one_nat))))
                   (Arith.upt Arith.zero_nat (Uncurry.aarity sm f n)));
      })
        c)
    sml;

eta_closed_top_rules ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => a -> Arith.Nat ->
(a -> Arith.Nat -> [a]) ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Sum_Type.Sum (String -> String) ();
eta_closed_top_rules a n sm r p =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) ->
        (case l of {
          Term_Rewriting.Var _ -> Sum_Type.Inr ();
          Term_Rewriting.Fun ff ls ->
            Check_Monad.check
              (Arith.equal_nat (Uncurry.aarity sm ff (Arith.size_list ls))
                 Arith.zero_nat ||
                any (\ (lll, rrr) ->
                      (case (lll, rrr) of {
                        (Term_Rewriting.Var _, _) -> False;
                        (Term_Rewriting.Fun _ [], _) -> False;
                        (Term_Rewriting.Fun _ (_ : _), Term_Rewriting.Var _) ->
                          False;
                        (Term_Rewriting.Fun _ (_ : _), Term_Rewriting.Fun _ [])
                          -> False;
                        (Term_Rewriting.Fun f (ll : yy),
                          Term_Rewriting.Fun g (rr : zz))
                          -> f == a &&
                               g == a &&
                                 zz == yy &&
                                   Arith.equal_nat (Arith.size_list yy)
                                     (Arith.minus_nat n Arith.one_nat) &&
                                     Arith.distinct yy &&
                                       all Term_Rewriting.is_Var yy &&
 null (Arith.inter_list_set (map Term_Rewriting.the_Var yy)
        (Term_Rewriting.insert_vars_rule (ll, rr) [])) &&
   Term_Rewriting.instance_rule (l, ra) (ll, rr);
                      }))
                  p)
              ((Term_Rewriting.showsl_lit "eta expansion of " .
                 Term_Rewriting.showsl_rule (l, ra)) .
                Term_Rewriting.showsl_lit " missing");
        }))
      r)
    (\ x -> Sum_Type.Inl (snd x));

uncurry_top_rules ::
  forall a b.
    (Eq a) => a -> Arith.Nat ->
                     (a -> Arith.Nat -> [a]) ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
uncurry_top_rules a n sm =
  map (\ (l, r) ->
        (Uncurry.uncurry_top a n sm l, Uncurry.uncurry_top a n sm r));

uncurry_top_proc ::
  forall a b.
    (Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   (b, ([((b, Arith.Nat), [b])],
 ([(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])],
   [(Term_Rewriting.Term b [Arith.Char],
      Term_Rewriting.Term b [Arith.Char])]))) ->
                                     Arith.Nat ->
                                       ([((b, Arith.Nat), [b])] ->
 b -> Arith.Nat -> b) ->
 (b -> Arith.Nat ->
         [((b, Arith.Nat), [b])] -> Sum_Type.Sum (String -> String) ()) ->
   [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
     [(Term_Rewriting.Term b [Arith.Char],
        Term_Rewriting.Term b [Arith.Char])] ->
       a -> Sum_Type.Sum (String -> String) a;
uncurry_top_proc i info n fmap check_inj p r dpp =
  (case info of {
    (a, (sml, (u, eb))) ->
      let {
        pa = Dependency_Pair_Problem_Spec.p i dpp;
        pw = Dependency_Pair_Problem_Spec.pw i dpp;
        ra = Dependency_Pair_Problem_Spec.r i dpp;
        rw = Dependency_Pair_Problem_Spec.rw i dpp;
        nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
        m = Dependency_Pair_Problem_Spec.minimal i dpp;
      } in (case uncurry_eta_split eb ra of {
             (e, ew) ->
               let {
                 sm = sig_list_to_sig_map a sml fmap;
                 p_eta = e ++ pa;
                 pw_eta = ew ++ pw;
                 uP = uncurry_top_rules a n sm p_eta;
                 uPw = uncurry_top_rules a n sm pw_eta;
                 uR = Term_Rewriting.map_funs_rules_wa
                        (\ (f, na) -> Uncurry.get_symbol sm f na Arith.zero_nat)
                        ra;
                 uRw = Term_Rewriting.map_funs_rules_wa
                         (\ (f, na) ->
                           Uncurry.get_symbol sm f na Arith.zero_nat)
                         rw;
               } in (case Error_Monad.bind
                            (Check_Monad.check
                              (null (Dependency_Pair_Problem_Spec.q i dpp))
                              (Term_Rewriting.showsl_lit
                                "strategy currently unsupported"))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (not (Arith.equal_nat n Arith.zero_nat))
                                  (Term_Rewriting.showsl_lit
                                    "the arity of the uncurried symbol must be at least 1"))
                                (\ _ ->
                                  Error_Monad.bind (check_inj a n sml)
                                    (\ _ ->
                                      let {
pb = Dependency_Pair_Problem_Spec.pairs i dpp;
is_def = (\ fn -> not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn)));
rm = Dependency_Pair_Problem_Spec.rules_map i dpp;
                                      } in
Error_Monad.bind
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, _) ->
        Check_Monad.check (not (Term_Rewriting.is_Var l))
          (Term_Rewriting.showsl_lit "lhs as variable is not allowed"))
      (ra ++ rw))
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (l, rb) ->
            Error_Monad.bind
              (Check_Monad.check (Uncurry.hvf_top a n l)
                ((Term_Rewriting.showsl_lit "head variable in lhs " .
                   Term_Rewriting.showsl_terma l) .
                  Term_Rewriting.showsl_lit " not allowed"))
              (\ _ -> Term_Rewriting.check_no_var rb))
          (pw_eta ++ p_eta))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (_, rb) ->
                Check_Monad.check
                  (not (is_def (Arith.the (Term_Rewriting.root rb))))
                  ((Term_Rewriting.showsl_lit "root of " .
                     Term_Rewriting.showsl_terma rb) .
                    Term_Rewriting.showsl_lit " must not be defined"))
              pb)
            (\ x -> Sum_Type.Inl (snd x)))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (not (is_def (a, n)))
                ((Term_Rewriting.showsl_lit "application symbol " .
                   Term_Rewriting.showsl a) .
                  Term_Rewriting.showsl_lit " must not be defined in R"))
              (\ _ ->
                Error_Monad.bind
                  (if any (\ (_, rb) ->
                            Arith.the (Term_Rewriting.root rb) == (a, n) &&
                              Term_Rewriting.equal_gctxt
                                (Tcap_Impl.tcapRM2 rm
                                  (Arith.hda (Term_Rewriting.args rb)))
                                Term_Rewriting.GCHole)
                        pb
                    then Error_Monad.bind
                           (Error_Monad.catch_error
                             (Term_Rewriting.check_CS_subseteq
                               (uncurry_of_top_sig_list a n sml sm) u)
                             (\ x ->
                               Sum_Type.Inl
                                 (((Term_Rewriting.showsl_lit
                                      "uncurrying pair " .
                                     Term_Rewriting.showsl_rule x) .
                                    Term_Rewriting.showsl_lit
                                      " is missing in\n") .
                                   Term_Rewriting.showsl_rules u)))
                           (\ _ ->
                             Error_Monad.bind
                               (eta_closed_top_rules a n sm ra p_eta)
                               (\ _ -> eta_closed_top_rules a n sm rw pw_eta))
                    else Sum_Type.Inr ())
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error (Check_Monad.check_subseteq uP p)
                        (\ x ->
                          Sum_Type.Inl
                            ((Term_Rewriting.showsl_lit "uncurried pair " .
                               Term_Rewriting.showsl_rule x) .
                              Term_Rewriting.showsl_lit " is missing")))
                      (\ _ ->
                        Error_Monad.bind
                          (Error_Monad.catch_error
                            (Check_Monad.check_subseteq uPw p)
                            (\ x ->
                              Sum_Type.Inl
                                ((Term_Rewriting.showsl_lit "uncurried pair " .
                                   Term_Rewriting.showsl_rule x) .
                                  Term_Rewriting.showsl_lit " is missing")))
                          (\ _ ->
                            Error_Monad.bind
                              (Error_Monad.catch_error
                                (Check_Monad.check_subseteq u p)
                                (\ x ->
                                  Sum_Type.Inl
                                    ((Term_Rewriting.showsl_lit
"uncurrying pair " .
                                       Term_Rewriting.showsl_rule x) .
                                      Term_Rewriting.showsl_lit
" is missing in new pairs")))
                              (\ _ ->
                                Error_Monad.bind
                                  (Error_Monad.catch_error
                                    (Check_Monad.check_subseteq uR r)
                                    (\ x ->
                                      Sum_Type.Inl
((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule x) .
  Term_Rewriting.showsl_lit " is missing in new rules")))
                                  (\ _ ->
                                    Error_Monad.catch_error
                                      (Check_Monad.check_subseteq uRw r)
                                      (\ x ->
Sum_Type.Inl
  ((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule x) .
    Term_Rewriting.showsl_lit " is missing in new rules"))))))))))))))
                      of {
                      Sum_Type.Inl aa -> Sum_Type.Inl aa;
                      Sum_Type.Inr _ ->
                        Sum_Type.Inr
                          (Dependency_Pair_Problem_Spec.mk i nfs m uP (uPw ++ u)
                            [] uR uRw);
                    });
           });
  });

uncurry_proc_both ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   Maybe Arith.Nat ->
                                     (Labelings.Lab b c,
                                       ([((Labelings.Lab b c, Arith.Nat),
   [Labelings.Lab b c])],
 ([(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
     Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
   [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])]))) ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
   a -> Sum_Type.Sum (String -> String) a;
uncurry_proc_both i Nothing (a, (sml, (u, eb))) =
  uncurry_proc i (a, (sml, (u, eb)))
    (fmap a (Arith.nat_of_integer (2 :: Integer))) check_inj;
uncurry_proc_both i (Just n) (a, (sml, (u, eb))) =
  uncurry_top_proc i (a, (sml, (u, eb))) n (fmap a n) check_inj;

uncurry_nonterm_tt_check ::
  forall a b.
    (Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   (b, ([((b, Arith.Nat), [b])],
 ([(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])],
   [(Term_Rewriting.Term b [Arith.Char],
      Term_Rewriting.Term b [Arith.Char])]))) ->
                                     ([((b, Arith.Nat), [b])] ->
                                       b -> Arith.Nat -> b) ->
                                       (b ->
 Arith.Nat -> [((b, Arith.Nat), [b])] -> Sum_Type.Sum (String -> String) ()) ->
 [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
   a -> Sum_Type.Sum (String -> String) a;
uncurry_nonterm_tt_check i info fmap check_inj r dpp =
  (case info of {
    (a, (sml, (u, e))) ->
      let {
        ra = Termination_Problem_Spec.rules i dpp;
        nfs = Termination_Problem_Spec.nfs i dpp;
        sm = sig_list_to_sig_map a sml fmap;
        r_eta = e ++ ra;
        uR = uncurry_rules a sm r_eta;
      } in (case Error_Monad.bind
                   (Check_Monad.check (null (Termination_Problem_Spec.q i dpp))
                     (Term_Rewriting.showsl_lit
                       "strategy not supported for uncurrying"))
                   (\ _ ->
                     let {
                       s = uncurry_of_sig_list a sml sm;
                     } in Error_Monad.bind (only_eta_rules e r_eta)
                            (\ _ ->
                              Error_Monad.bind
                                (check_inj a
                                   (Arith.nat_of_integer (2 :: Integer))
                                  sml)
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Term_Rewriting.check_CS_subseteq u s)
                                      (\ x ->
Sum_Type.Inl
  ((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule x) .
    Term_Rewriting.showsl_lit " is not an uncurry rule")))
                                    (\ _ ->
                                      Error_Monad.catch_error
(Check_Monad.check_subseteq r (u ++ uR))
(\ x ->
  Sum_Type.Inl
    ((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule x) .
      Term_Rewriting.showsl_lit
        " is neither uncurried rules nor uncurry rule"))))))
             of {
             Sum_Type.Inl aa -> Sum_Type.Inl aa;
             Sum_Type.Inr _ ->
               Sum_Type.Inr (Termination_Problem_Spec.mk i nfs [] r []);
           });
  });

uncurry_nonterm_tt ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   Uncurry_nt_proof b c [Arith.Char] ->
                                     a -> Sum_Type.Sum (String -> String) a;
uncurry_nonterm_tt i (Uncurry_nt_proof (a, (sml, (u, e))) r) tp =
  uncurry_nonterm_tt_check i (a, (sml, (u, e)))
    (fmap a (Arith.nat_of_integer (2 :: Integer))) check_inj r tp;

}
