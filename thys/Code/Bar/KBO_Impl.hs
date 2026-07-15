{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  KBO_Impl(prec_weight_repr_to_prec_weight, create_KBO_redord,
            create_KBO_rel_impl)
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
import qualified Compare_Order_Instances;
import qualified Lexicographic_Extension;
import qualified KBO;
import qualified Multiset;
import qualified Term_Order;
import qualified Complexity;
import qualified HOL;
import qualified Reduction_Order_Impl;
import qualified Compare;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified Arith;

prec_ext ::
  forall a b. (Eq a) => (a -> Maybe (Arith.Nat, b)) -> a -> a -> (Bool, Bool);
prec_ext prwm =
  (\ f g ->
    (case prwm f of {
      Nothing -> (False, f == g);
      Just pf ->
        (case prwm g of {
          Nothing -> (True, True);
          Just pg ->
            (Arith.less_nat (fst pg) (fst pf),
              Arith.less_eq_nat (fst pg) (fst pf));
        });
    }));

kbo_impl ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> Arith.Nat) ->
                Arith.Nat ->
                  ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                    (a -> Bool) ->
                      ((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
                        Term_Rewriting.Term a b ->
                          Term_Rewriting.Term a b -> (Bool, Bool);
kbo_impl w w0 prc least scf s t =
  let {
    wt = KBO.weight w w0 scf t;
    ws = KBO.weight w w0 scf s;
  } in (if Multiset.subseteq_mset
             (Term_Rewriting.vars_term_ms (KBO.scf_term scf t))
             (Term_Rewriting.vars_term_ms (KBO.scf_term scf s)) &&
             Arith.less_eq_nat wt ws
         then (if Arith.less_nat wt ws then (True, True)
                else (case s of {
                       Term_Rewriting.Var _ ->
                         (False,
                           (case t of {
                             Term_Rewriting.Var _ -> True;
                             Term_Rewriting.Fun g ts -> null ts && least g;
                           }));
                       Term_Rewriting.Fun f ss ->
                         (case t of {
                           Term_Rewriting.Var _ -> (True, True);
                           Term_Rewriting.Fun g ts ->
                             let {
                               p = prc (f, Arith.size_list ss)
                                     (g, Arith.size_list ts);
                             } in (if fst p then (True, True)
                                    else (if snd p
   then Lexicographic_Extension.lex_ext_unbounded (kbo_impl w w0 prc least scf)
          ss ts
   else (False, False)));
                         });
                     }))
         else (False, False));

kbo_strict ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) ->
                                  (a, Arith.Nat) -> (Bool, Bool)) ->
                                  ((a, Arith.Nat) -> Arith.Nat) ->
                                    Arith.Nat ->
                                      (a -> Bool) ->
((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
  (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
    Sum_Type.Sum (String -> String) ();
kbo_strict pr w w0 least scf =
  (\ (s, t) ->
    Check_Monad.check (fst (kbo_impl w w0 pr least scf s t))
      ((((Shows_Literal.showsl_literal "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_literal " >KBO ") .
         Term_Rewriting.showsl_terma t) .
        Shows_Literal.showsl_literal "\n"));

kbo_nstrict ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) ->
                                  (a, Arith.Nat) -> (Bool, Bool)) ->
                                  ((a, Arith.Nat) -> Arith.Nat) ->
                                    Arith.Nat ->
                                      (a -> Bool) ->
((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
  (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
    Sum_Type.Sum (String -> String) ();
kbo_nstrict pr w w0 least scf =
  (\ (s, t) ->
    Check_Monad.check (snd (kbo_impl w w0 pr least scf s t))
      ((((Shows_Literal.showsl_literal "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_literal " >=KBO ") .
         Term_Rewriting.showsl_terma t) .
        Shows_Literal.showsl_literal "\n"));

shows_kbo_repr ::
  forall a.
    (Shows_Literal.Showl a) => ([((a, Arith.Nat),
                                   (Arith.Nat,
                                     (Arith.Nat, Maybe [Arith.Nat])))],
                                 Arith.Nat) ->
                                 String -> String;
shows_kbo_repr (prs, w0) =
  (((((((((Shows_Literal.showsl_literal
             "KBO with the following precedence and weight function\n" .
            Arith.foldr
              (\ (a, b) ->
                (case a of {
                  (f, n) ->
                    (\ (pr, (_, _)) ->
                      (((((Shows_Literal.showsl_literal "precedence(" .
                            Shows_Literal.showsl f) .
                           Shows_Literal.showsl_literal "[") .
                          Shows_Literal.showsl_nat n) .
                         Shows_Literal.showsl_literal "]) = ") .
                        Shows_Literal.showsl_nat pr) .
                        Shows_Literal.showsl_literal "\n");
                })
                  b)
              prs) .
           Shows_Literal.showsl_literal
             "\nprecedence(_) = 0\nand the following weight\n") .
          Arith.foldr
            (\ (a, b) ->
              (case a of {
                (f, n) ->
                  (\ (_, (w, _)) ->
                    (((((Shows_Literal.showsl_literal "weight(" .
                          Shows_Literal.showsl f) .
                         Shows_Literal.showsl_literal "[") .
                        Shows_Literal.showsl_nat n) .
                       Shows_Literal.showsl_literal "]) = ") .
                      Shows_Literal.showsl_nat w) .
                      Shows_Literal.showsl_literal "\n");
              })
                b)
            prs) .
         Shows_Literal.showsl_literal "\nweight(_) = ") .
        Shows_Literal.showsl_nat (Arith.suc w0)) .
       Shows_Literal.showsl_literal "\nw0 = ") .
      Shows_Literal.showsl_nat w0) .
     Shows_Literal.showsl_literal
       "\nand the following subterm coefficient functions\n") .
    Arith.foldr
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ (_, (_, scf)) ->
              (((((Shows_Literal.showsl_literal "scf(" .
                    Shows_Literal.showsl f) .
                   Shows_Literal.showsl_literal "[") .
                  Shows_Literal.showsl_nat n) .
                 Shows_Literal.showsl_literal "]) = ") .
                (if Arith.is_none scf then Shows_Literal.showsl_literal "all 1"
                  else Shows_Literal.showsl_list_nat (Arith.the scf))) .
                Shows_Literal.showsl_literal "\n");
        })
          b)
      prs) .
    Shows_Literal.showsl_literal "\nscf(_) = all 1\n";

check_scf_entry ::
  forall a.
    (Shows_Literal.Showl a) => (a, Arith.Nat) ->
                                 Maybe [Arith.Nat] ->
                                   Sum_Type.Sum (String -> String) ();
check_scf_entry fn Nothing = Sum_Type.Inr ();
check_scf_entry (f, n) (Just es) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Arith.equal_nat (Arith.size_list es) n)
        (Shows_Literal.showsl_literal "nr of entries should be " .
          Shows_Literal.showsl_nat n))
      (\ _ ->
        Check_Monad.check (all (Arith.less_nat Arith.zero_nat) es)
          (Shows_Literal.showsl_literal "all entries must be non-zero")))
    (\ x ->
      Sum_Type.Inl
        ((((Shows_Literal.showsl_literal
              "problem with subterm coefficients for " .
             Shows_Literal.showsl_prod (f, n)) .
            Shows_Literal.showsl_literal ": ") .
           x) .
          Shows_Literal.showsl_literal "\n"));

scf_repr_to_scf ::
  forall a.
    ((a, Arith.Nat) -> Maybe [Arith.Nat]) ->
      (a, Arith.Nat) -> Arith.Nat -> Arith.Nat;
scf_repr_to_scf scf fn i = (case scf fn of {
                             Nothing -> Arith.one_nat;
                             Just xs -> Arith.nth xs i;
                           });

prec_weight_repr_to_prec_weight_funs ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
                 Arith.Nat) ->
                 ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool),
                   ((a, Arith.Nat) -> Arith.Nat,
                     (Arith.Nat, ([a], (a, Arith.Nat) -> Maybe [Arith.Nat]))));
prec_weight_repr_to_prec_weight_funs prw_w0 =
  (case prw_w0 of {
    (prw, w0) ->
      let {
        prwm = Map_Choice.ceta_map_of prw;
        w_fun =
          Map_Choice.fun_of_map_funa prwm (\ _ -> Arith.suc w0) (fst . snd);
        p_fun = prec_ext prwm;
        scf_fun = Map_Choice.fun_of_map_funa prwm (\ _ -> Nothing) (snd . snd);
        fs = map fst prw;
        cs = filter
               (\ fn ->
                 Arith.equal_nat (snd fn) Arith.zero_nat &&
                   Arith.equal_nat (w_fun fn) w0)
               fs;
        lcs = Arith.map_filter
                (\ x ->
                  (if all (\ c -> snd (p_fun c x)) cs then Just (fst x)
                    else Nothing))
                cs;
      } in (p_fun, (w_fun, (w0, (lcs, scf_fun))));
  });

prec_weight_repr_to_prec_weight ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => ([((a, Arith.Nat),
                                    (Arith.Nat,
                                      (Arith.Nat, Maybe [Arith.Nat])))],
                                  Arith.Nat) ->
                                  (Sum_Type.Sum (String -> String) (),
                                    ((a, Arith.Nat) ->
                                       (a, Arith.Nat) -> (Bool, Bool),
                                      ((a, Arith.Nat) -> Arith.Nat,
(Arith.Nat, ([a], (a, Arith.Nat) -> Arith.Nat -> Arith.Nat)))));
prec_weight_repr_to_prec_weight prw_w0 =
  (case prec_weight_repr_to_prec_weight_funs prw_w0 of {
    (p_fun, (w_fun, (_, (lcs, scf_fun)))) ->
      (case prw_w0 of {
        (prw, w0) ->
          let {
            fs = map fst prw;
            cw_okay =
              Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ fn ->
                    Check_Monad.check
                      (if Arith.equal_nat (snd fn) Arith.zero_nat
                        then Arith.less_eq_nat w0 (w_fun fn) else True)
                      ((Shows_Literal.showsl_literal "weight of constant " .
                         Shows_Literal.showsl (fst fn)) .
                        Shows_Literal.showsl_literal " must be at least w0"))
                  (map fst prw))
                (\ x -> Sum_Type.Inl (snd x));
            adm = Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ fn ->
                        Check_Monad.check
                          (if Arith.equal_nat (snd fn) Arith.one_nat
                            then (if Arith.equal_nat (w_fun fn) Arith.zero_nat
                                   then all (snd . p_fun fn) fs else True)
                            else True)
                          ((Shows_Literal.showsl_literal "unary symbol " .
                             Shows_Literal.showsl (fst fn)) .
                            Shows_Literal.showsl_literal
                              " with weight 0 does not have maximal precedence"))
                      (map fst prw))
                    (\ x -> Sum_Type.Inl (snd x));
            scf_ok =
              Error_Monad.catch_error
                (Error_Monad.forallM (\ fn -> check_scf_entry fn (scf_fun fn))
                  (map fst prw))
                (\ x -> Sum_Type.Inl (snd x));
            ok = Error_Monad.bind
                   (Check_Monad.check (Arith.less_nat Arith.zero_nat w0)
                     (Shows_Literal.showsl_literal "w0 must be larger than 0"))
                   (\ _ ->
                     Error_Monad.bind adm
                       (\ _ -> Error_Monad.bind cw_okay (\ _ -> scf_ok)));
          } in (ok, (p_fun, (w_fun, (w0, (lcs, scf_repr_to_scf scf_fun)))));
      });
  });

create_KBO_redord ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Eq b) => ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
                 Arith.Nat) ->
                 [(a, Arith.Nat)] -> Reduction_Order_Impl.Redord_ext a b ();
create_KBO_redord pr fs =
  (case prec_weight_repr_to_prec_weight pr of {
    (ch, (p, (w, (w0, (lcs, scf))))) ->
      let {
        valid =
          Error_Monad.bind ch
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Check_Monad.check_same_set fs (map fst (fst pr)))
                  (\ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_literal
                        " signature does not match ")))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (Arith.less_nat Arith.zero_nat (Arith.size_list lcs))
                      (Shows_Literal.showsl_literal
                        "there must be a minimal constant with weight w0"))
                    (\ _ ->
                      Check_Monad.check
                        (Arith.distinct (map (fst . snd) (fst pr)))
                        (Shows_Literal.showsl_literal
                          "the given precedence is not injective"))));
      } in Reduction_Order_Impl.Redord_ext valid
             (\ s t -> fst (kbo_impl w w0 p (Arith.membera lcs) scf s t))
             (Arith.nth lcs Arith.zero_nat) ();
  });

create_KBO_rel_impl ::
  forall a b c.
    (Shows_Literal.Showl a, Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => (([((a, Arith.Nat),
                                     (Arith.Nat,
                                       (Arith.Nat, Maybe [Arith.Nat])))],
                                   Arith.Nat) ->
                                  ([((b, Arith.Nat),
                                      (Arith.Nat,
(Arith.Nat, Maybe [Arith.Nat])))],
                                    Arith.Nat)) ->
                                  ([((a, Arith.Nat),
                                      (Arith.Nat,
(Arith.Nat, Maybe [Arith.Nat])))],
                                    Arith.Nat) ->
                                    Term_Rewriting.Rel_impl_ext b c ();
create_KBO_rel_impl f_to_g pr =
  (case prec_weight_repr_to_prec_weight (f_to_g pr) of {
    (ch, (p, (w, (w0, (lcs, scf))))) ->
      let {
        ns = kbo_nstrict p w w0 (Arith.membera lcs) scf;
        s = kbo_strict p w w0 (Arith.membera lcs) scf;
      } in Term_Rewriting.Rel_impl_ext ch (Sum_Type.Inr ()) (shows_kbo_repr pr)
             s ns ns Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.full_af
             (\ _ -> Sum_Type.Inr ()) (Just []) (Just [])
             Term_Rewriting.no_complexity_check ();
  });

}
