{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Nonloop_SRS_Impl(Dp_proof_step(..), Non_loop_srs_proof(..), normalize_wp,
                    check_non_loop_srs_prf)
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
import qualified Orderings;
import qualified Phantom_Type;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified String_Reversal;
import qualified Nonloop_SRS;
import qualified Term;
import qualified Product_Type;
import qualified List;
import qualified Shows_Literal;
import qualified Arith;

data Dp_proof_step a = OC1 ([a], [a]) Bool
  | OC2 ([a], [a]) ([a], [a]) ([a], [a]) [a] [a] [a]
  | OC2p ([a], [a]) ([a], [a]) ([a], [a]) [a] [a] [a]
  | OC3 ([a], [a]) ([a], [a]) ([a], [a]) [a] [a]
  | OC3p ([a], [a]) ([a], [a]) ([a], [a]) [a] [a]
  | OCDP1 (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
            ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a])
  | OCDP2 (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
            ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a])
  | WPEQ (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
           ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
  | Lift (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
           ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
  | DPOC1_1
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a]) [a] [a]
  | DPOC1_2
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a]) [a] [a] [a]
  | DPOC2 (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
            ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a]) [a] [a]
  | DPOC3_1
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a]) [a] [a]
  | DPOC3_2
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      ([a], [a]) [a] [a] [a]
  | DPDP1_1
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      [a] [a]
  | DPDP1_2
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      [a] [a]
  | DPDP2_1
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      [a] [a]
  | DPDP2_2
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      [a] [a];

data Non_loop_srs_proof a = SE_OC ([a], [a]) [a] [a] [Dp_proof_step a]
  | SE_DP (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
            ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
      [a] [a] [Dp_proof_step a];

pat_of ::
  forall a.
    Dp_proof_step a ->
      (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
        ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])));
pat_of (OC1 rl uu) =
  (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
    ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)));
pat_of (OC2 rl uv uw ux uy uz) =
  (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
    ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)));
pat_of (OC2p rl va vb vc vd ve) =
  (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
    ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)));
pat_of (OC3 rl vf vg vh vi) =
  (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
    ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)));
pat_of (OC3p rl vj vk vl vm) =
  (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
    ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)));
pat_of (OCDP1 p vn) = p;
pat_of (OCDP2 p vo) = p;
pat_of (WPEQ p vp) = p;
pat_of (Lift p vq) = p;
pat_of (DPOC1_1 p vr vs vt vu) = p;
pat_of (DPOC1_2 p vv vw vx vy vz) = p;
pat_of (DPOC2 p wa wb wc wd) = p;
pat_of (DPOC3_1 p we wf wg wh) = p;
pat_of (DPOC3_2 p wi wj wk wl wm) = p;
pat_of (DPDP1_1 p wn wo wp wq) = p;
pat_of (DPDP1_2 p wr ws wt wu) = p;
pat_of (DPDP2_1 p wv ww wx wy) = p;
pat_of (DPDP2_2 p wz xa xb xc) = p;

prems_of ::
  forall a.
    Dp_proof_step a ->
      [(([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
         ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))];
prems_of step =
  (case step of {
    OC1 _ _ -> [];
    OC2 _ p pa _ _ _ ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p))),
        (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst pa)),
          ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd pa)))];
    OC2p _ p pa _ _ _ ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p))),
        (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst pa)),
          ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd pa)))];
    OC3 _ p pa _ _ ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p))),
        (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst pa)),
          ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd pa)))];
    OC3p _ p pa _ _ ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p))),
        (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst pa)),
          ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd pa)))];
    OCDP1 _ p ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p)))];
    OCDP2 _ p ->
      [(([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst p)),
         ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd p)))];
    WPEQ _ p -> [p];
    Lift _ p -> [p];
    DPOC1_1 _ p rl _ _ ->
      [p, (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
            ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)))];
    DPOC1_2 _ p rl _ _ _ ->
      [p, (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
            ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)))];
    DPOC2 _ p rl _ _ ->
      [p, (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
            ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)))];
    DPOC3_1 _ p rl _ _ ->
      [p, (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
            ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)))];
    DPOC3_2 _ p rl _ _ _ ->
      [p, (([], ((Arith.zero_nat, (Arith.zero_nat, [])), fst rl)),
            ([], ((Arith.zero_nat, (Arith.zero_nat, [])), snd rl)))];
    DPDP1_1 _ p1 p2 _ _ -> [p1, p2];
    DPDP1_2 _ p1 p2 _ _ -> [p1, p2];
    DPDP2_1 _ p1 p2 _ _ -> [p1, p2];
    DPDP2_2 _ p1 p2 _ _ -> [p1, p2];
  });

showsl_exp ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (a, b) -> String -> String;
showsl_exp (f, c) =
  (Shows_Literal.showsl f . Shows_Literal.showsl_lit "n+ ") .
    Shows_Literal.showsl c;

showsl_p ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d,
      Shows_Literal.Showl e) => (a, ((b, (c, d)), e)) -> String -> String;
showsl_p (b, ((f, (c, m)), a)) =
  ((((Shows_Literal.showsl b . Shows_Literal.showsl m) .
      Shows_Literal.showsl_lit " ^ (") .
     showsl_exp (f, c)) .
    Shows_Literal.showsl_lit ")") .
    Shows_Literal.showsl a;

showsl_oc ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (a, b) -> String -> String;
showsl_oc (l, r) =
  (Shows_Literal.showsl l . Shows_Literal.showsl_lit " ->+ ") .
    Shows_Literal.showsl r;

showsl_pat ::
  forall a b c d e f g h i j.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d, Shows_Literal.Showl e, Shows_Literal.Showl f,
      Shows_Literal.Showl g, Shows_Literal.Showl h, Shows_Literal.Showl i,
      Shows_Literal.Showl j) => ((a, ((b, (c, d)), e)),
                                  (f, ((g, (h, i)), j))) ->
                                  String -> String;
showsl_pat (p1, p2) =
  (showsl_p p1 . Shows_Literal.showsl_lit " ->+ ") . showsl_p p2;

normalize_wp ::
  forall a.
    (Eq a) => ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])) ->
                ([a], ((Arith.Nat, (Arith.Nat, [a])), [a]));
normalize_wp xa =
  (case xa of {
    (x5a, ((x4ba, a), x1ca)) ->
      (if Arith.equal_nat x4ba Arith.zero_nat
        then (case a of {
               (aa, x2ca) ->
                 (if Arith.equal_nat aa Arith.zero_nat
                   then ([], ((Arith.zero_nat, (Arith.zero_nat, [])),
                               x5a ++ x1ca))
                   else normalize_wp
                          (x5a ++
                             concat
                               (List.replicate
                                 (Arith.suc (Arith.minus_nat aa Arith.one_nat))
                                 x2ca),
                            ((Arith.zero_nat, (Arith.zero_nat, x2ca)), x1ca)));
             })
        else (if Arith.equal_nat (Arith.minus_nat x4ba Arith.one_nat)
                   Arith.zero_nat
               then (case a of {
                      (aa, x2ca) ->
                        (if Arith.equal_nat aa Arith.zero_nat
                          then (case x2ca of {
                                 [] -> ([],
 ((Arith.zero_nat, (Arith.zero_nat, [])), x5a ++ x1ca));
                                 x4a : x3a ->
                                   (case x1ca of {
                                     [] -> (x5a,
     ((Arith.suc Arith.zero_nat, (Arith.zero_nat, x4a : x3a)), []));
                                     x2a : x1a ->
                                       (if x4a == x2a
 then normalize_wp
        (x5a ++ [x2a],
          ((Arith.suc Arith.zero_nat, (Arith.zero_nat, x3a ++ [x2a])), x1a))
 else (x5a, ((Arith.suc Arith.zero_nat, (Arith.zero_nat, x4a : x3a)),
              x2a : x1a)));
                                   });
                               })
                          else normalize_wp
                                 (x5a ++
                                    concat
                                      (List.replicate
(Arith.suc (Arith.minus_nat aa Arith.one_nat)) x2ca),
                                   ((Arith.suc Arith.zero_nat,
                                      (Arith.zero_nat, x2ca)),
                                     x1ca)));
                    })
               else (case a of {
                      (aa, x2ca) ->
                        (if Arith.equal_nat aa Arith.zero_nat
                          then (case x2ca of {
                                 [] -> ([],
 ((Arith.zero_nat, (Arith.zero_nat, [])), x5a ++ x1ca));
                                 x3fa : x2fa ->
                                   normalize_wp
                                     (x5a, ((Arith.suc Arith.zero_nat,
      (Arith.zero_nat,
        concat
          (List.replicate
            (Arith.suc
              (Arith.suc
                (Arith.minus_nat (Arith.minus_nat x4ba Arith.one_nat)
                  Arith.one_nat)))
            (x3fa : x2fa)))),
     x1ca));
                               })
                          else normalize_wp
                                 (x5a ++
                                    concat
                                      (List.replicate
(Arith.suc (Arith.minus_nat aa Arith.one_nat)) x2ca),
                                   ((Arith.suc
                                       (Arith.suc
 (Arith.minus_nat (Arith.minus_nat x4ba Arith.one_nat) Arith.one_nat)),
                                      (Arith.zero_nat, x2ca)),
                                     x1ca)));
                    })));
  });

showsl_srs_rule ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (a, b) -> String -> String;
showsl_srs_rule (l, r) =
  (Shows_Literal.showsl l . Shows_Literal.showsl_lit " -> ") .
    Shows_Literal.showsl r;

srs_of_trs_impl :: forall a b. [(Term.Term a b, Term.Term a b)] -> [([a], [a])];
srs_of_trs_impl r =
  concatMap
    (\ (l, ra) ->
      (if String_Reversal.unary_term l
        then (if String_Reversal.unary_term ra
               then [(Nonloop_SRS.term_to_string l,
                       Nonloop_SRS.term_to_string ra)]
               else [])
        else []))
    r;

check_step ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Shows_Literal.Showl a) => Set.Set ([a], [a]) ->
                                  Dp_proof_step a ->
                                    Sum_Type.Sum (String -> String) ();
check_step r step =
  (case step of {
    OC1 uv _ ->
      Check_Monad.check (Set.member uv r)
        (showsl_srs_rule uv .
          Shows_Literal.showsl_lit " is not an original rule");
    OC2 oc_new oc1 oc2 t x l ->
      (case oc_new of {
        (wl, tr) ->
          (case oc1 of {
            (w, tx) ->
              (case oc2 of {
                (xl, ra) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (xl == x ++ l)
                        (Shows_Literal.showsl_lit "problem: xl != x l"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (tx == t ++ x)
                            (Shows_Literal.showsl_lit "problem: tx != t x"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check (wl == w ++ l)
                                (Shows_Literal.showsl_lit "problem: wl != w l"))
                              (\ _ ->
                                Check_Monad.check (tr == t ++ ra)
                                  (Shows_Literal.showsl_lit
                                    "problem: tr != t r")))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap OC2 of\n" .
                                showsl_oc oc1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc2) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_oc oc_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    OC2p oc_new oc1 oc2 x t l ->
      (case oc_new of {
        (lw, rt) ->
          (case oc1 of {
            (w, xt) ->
              (case oc2 of {
                (lx, ra) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (lx == l ++ x)
                        (Shows_Literal.showsl_lit "problem: lx != l x"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (lw == l ++ w)
                            (Shows_Literal.showsl_lit "problem: lw != l w"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check (rt == ra ++ t)
                                (Shows_Literal.showsl_lit "problem: rt != r t"))
                              (\ _ ->
                                Check_Monad.check (xt == x ++ t)
                                  (Shows_Literal.showsl_lit
                                    "problem: xt != x t")))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap OC2\' of\n" .
                                showsl_oc oc1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc2) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_oc oc_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    OC3 oc_new oc1 oc2 t1 t2 ->
      (case oc_new of {
        (w, t1rt2) ->
          (case oc1 of {
            (wa, t1xt2) ->
              (case oc2 of {
                (x, ra) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (t1rt2 == t1 ++ ra ++ t2)
                        (Shows_Literal.showsl_lit
                          "problem: t1_r_t2 != t1 r t2"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (t1xt2 == t1 ++ x ++ t2)
                            (Shows_Literal.showsl_lit
                              "problem: t1_x_t2 != t1 x t2"))
                          (\ _ ->
                            Check_Monad.check (w == wa)
                              (Shows_Literal.showsl_lit "problem: w differs"))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap OC3 of\n" .
                                showsl_oc oc1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc2) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_oc oc_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    OC3p oc_new oc1 oc2 t1 t2 ->
      (case oc_new of {
        (t1wt2, ra) ->
          (case oc1 of {
            (t1xt2, raa) ->
              (case oc2 of {
                (w, x) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (t1wt2 == t1 ++ w ++ t2)
                        (Shows_Literal.showsl_lit
                          "problem: t1_w_t2 != t1 w t2"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (t1xt2 == t1 ++ x ++ t2)
                            (Shows_Literal.showsl_lit
                              "problem: t1_x_t2 != t1 x t2"))
                          (\ _ ->
                            Check_Monad.check (ra == raa)
                              (Shows_Literal.showsl_lit "problem: r differs"))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap OC3\' of\n" .
                                showsl_oc oc1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc2) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_oc oc_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    OCDP1 p oc1 ->
      (case oc1 of {
        (lc, cr) ->
          (case p of {
            (a, b) ->
              (case a of {
                (e1, (aa, ba)) ->
                  (case aa of {
                    (f, (d, l)) ->
                      (\ c1 (c2, (ab, bb)) ->
                        (case ab of {
                          (fa, (da, ra)) ->
                            (\ e2 ->
                              Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check (null e1)
                                    (Shows_Literal.showsl_lit
                                      "problem: e1 not empty"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check (null e2)
(Shows_Literal.showsl_lit "problem: e2 not empty"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (c1 == c2)
    (Shows_Literal.showsl_lit "problem: c not equal"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check
        (Arith.equal_nat f Arith.one_nat &&
          Arith.equal_nat fa Arith.one_nat &&
            Arith.equal_nat d Arith.zero_nat &&
              Arith.equal_nat da Arith.zero_nat)
        (Shows_Literal.showsl_lit "problem: 0 and 1 conditions not met"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (lc == l ++ c1)
            (Shows_Literal.showsl_lit "problem: lc != l c"))
          (\ _ ->
            Check_Monad.check (cr == c1 ++ ra)
              (Shows_Literal.showsl_lit "problem: cr != c r")))))))
                                (\ x ->
                                  Sum_Type.Inl
                                    (((((Shows_Literal.showsl_lit
   "problem in checking overlap OCDP1 of\n" .
  showsl_oc oc1) .
 Shows_Literal.showsl_lit "\nto yield\n") .
showsl_pat p) .
                                       Shows_Literal.showsl_literal "\n") .
                                      x)));
                        })
                          bb);
                  })
                    ba;
              })
                b;
          });
      });
    OCDP2 p oc1 ->
      (case oc1 of {
        (cl, rc) ->
          (case p of {
            (a, b) ->
              (case a of {
                (c1, (aa, ba)) ->
                  (case aa of {
                    (f, (d, l)) ->
                      (\ e1 (e2, (ab, bb)) ->
                        (case ab of {
                          (fa, (da, ra)) ->
                            (\ c2 ->
                              Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check (null e1 && null e2)
                                    (Shows_Literal.showsl_lit
                                      "problem: e1 or e2 not empty"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check (c1 == c2)
(Shows_Literal.showsl_lit "problem: c not equal"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check
    (Arith.equal_nat f Arith.one_nat &&
      Arith.equal_nat fa Arith.one_nat &&
        Arith.equal_nat d Arith.zero_nat && Arith.equal_nat da Arith.zero_nat)
    (Shows_Literal.showsl_lit "problem: 0 and 1 conditions not met"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check (cl == c1 ++ l)
        (Shows_Literal.showsl_lit "problem: lc != l c"))
      (\ _ ->
        Check_Monad.check (rc == ra ++ c1)
          (Shows_Literal.showsl_lit "problem: cr != c r"))))))
                                (\ x ->
                                  Sum_Type.Inl
                                    (((((Shows_Literal.showsl_lit
   "problem in checking overlap OCDP1 of\n" .
  showsl_oc oc1) .
 Shows_Literal.showsl_lit "\nto yield\n") .
showsl_pat p) .
                                       Shows_Literal.showsl_literal "\n") .
                                      x)));
                        })
                          bb);
                  })
                    ba;
              })
                b;
          });
      });
    WPEQ p_new p ->
      (case p of {
        (left, right) ->
          (case p_new of {
            (lefta, righta) ->
              Error_Monad.catch_error
                (Error_Monad.bind
                  (Check_Monad.check (Nonloop_SRS.word_pat_equiv left lefta)
                    (Shows_Literal.showsl_lit
                      "problem: lhss are not equivalent"))
                  (\ _ ->
                    Check_Monad.check (Nonloop_SRS.word_pat_equiv right righta)
                      (Shows_Literal.showsl_lit
                        "problem: rhss are not equivalent")))
                (\ x ->
                  Sum_Type.Inl
                    (((((Shows_Literal.showsl_lit
                           "problem in checking equivalence of\n" .
                          showsl_pat p) .
                         Shows_Literal.showsl_lit "\nand\n") .
                        showsl_pat p_new) .
                       Shows_Literal.showsl_literal "\n") .
                      x));
          });
      });
    Lift p_new p ->
      (case p of {
        (a, b) ->
          (case a of {
            (l1, (aa, ba)) ->
              (case aa of {
                (f1, (c1, m1)) ->
                  (\ r1 (l2, (ab, bb)) ->
                    (case ab of {
                      (f2, (c2, m2)) ->
                        (\ r2 ->
                          (case p_new of {
                            (ac, bc) ->
                              (case ac of {
                                (l1a, (ad, bd)) ->
                                  (case ad of {
                                    (f1a, (c1a, m1a)) ->
                                      (\ r1a (l2a, (ae, be)) ->
(case ae of {
  (f2a, (c2a, m2a)) ->
    (\ r2a ->
      Error_Monad.catch_error
        (Error_Monad.bind
          (Check_Monad.check (l1 == l1a && l2 == l2a)
            (Shows_Literal.showsl_lit "problem: l and l\' do not match"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (r1 == r1a && r2 == r2a)
                (Shows_Literal.showsl_lit "problem: r and r\' do not match"))
              (\ _ ->
                Error_Monad.bind
                  (Check_Monad.check
                    (Arith.equal_nat f1 f1a && Arith.equal_nat f2 f2a)
                    (Shows_Literal.showsl_lit
                      "problem: f and f\' do not match"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check (m1 == m1a && m2 == m2a)
                        (Shows_Literal.showsl_lit
                          "problem: m and m\' do not match"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Arith.equal_nat c1a (Arith.plus_nat c1 f1))
                            (Shows_Literal.showsl_lit
                              "problem: constant factor on the left not properly increased"))
                          (\ _ ->
                            Check_Monad.check
                              (Arith.equal_nat c2a (Arith.plus_nat c2 f2))
                              (Shows_Literal.showsl_lit
                                "problem: constant factor on the right not properly increased")))))))
        (\ x ->
          Sum_Type.Inl
            (((((Shows_Literal.showsl_lit "problem in checking lifting of\n" .
                  showsl_pat p) .
                 Shows_Literal.showsl_lit "\nto yield\n") .
                showsl_pat p_new) .
               Shows_Literal.showsl_literal "\n") .
              x)));
})
  be);
                                  })
                                    bd;
                              })
                                bc;
                          }));
                    })
                      bb);
              })
                ba;
          })
            b;
      });
    DPOC1_1 p_new p1 oc1 l ra ->
      (case p1 of {
        (left, (lxr, (m2, r2))) ->
          (case oc1 of {
            (x, v) ->
              (case p_new of {
                (lefta, (lvr, (m2a, r2a))) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (left == lefta)
                        (Shows_Literal.showsl_lit
                          "problem: lhss are not equal"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (m2 == m2a)
                            (Shows_Literal.showsl_lit
                              "problem: m2 and m2\' do not match"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check (r2 == r2a)
                                (Shows_Literal.showsl_lit
                                  "problem: r2 and r2\' do not match"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check (lxr == l ++ x ++ ra)
                                    (Shows_Literal.showsl_lit
                                      "problem: l_x_r != l @ x @ r"))
                                  (\ _ ->
                                    Check_Monad.check (lvr == l ++ v ++ ra)
                                      (Shows_Literal.showsl_lit
"problem: l_v_r != l @ v @ r"))))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap DPOC1_1 of\n" .
                                showsl_pat p1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc1) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_pat p_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    DPOC1_2 p_new p1 oc1 l ra x ->
      (case p1 of {
        (a, b) ->
          (case a of {
            (l1, (m1, r1)) ->
              (\ (xr, (m2, r2)) ->
                (case oc1 of {
                  (lx, v) ->
                    (case p_new of {
                      (aa, ba) ->
                        (case aa of {
                          (ll1, (m1a, r1a)) ->
                            (\ (vr, (m2a, r2a)) ->
                              Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check (m1 == m1a && m2 == m2a)
                                    (Shows_Literal.showsl_lit
                                      "problem: m components modified"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(r1 == r1a && r2 == r2a)
(Shows_Literal.showsl_lit "problem: r components modified"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (ll1 == l ++ l1)
    (Shows_Literal.showsl_lit "problem: l_l1 != l @ ll1"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check (xr == x ++ ra)
        (Shows_Literal.showsl_lit "problem: x_r != x @ r"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (lx == l ++ x)
            (Shows_Literal.showsl_lit "problem: l_x != l @ x"))
          (\ _ ->
            Check_Monad.check (vr == v ++ ra)
              (Shows_Literal.showsl_lit "problem: v_r != v @ r")))))))
                                (\ xa ->
                                  Sum_Type.Inl
                                    (((((((Shows_Literal.showsl_lit
     "problem in checking overlap DPOC1_2 of\n" .
    showsl_pat p1) .
   Shows_Literal.showsl_literal "\n") .
  showsl_oc oc1) .
 Shows_Literal.showsl_lit "\nto yield\n") .
showsl_pat p_new) .
                                       Shows_Literal.showsl_literal "\n") .
                                      xa)));
                        })
                          ba;
                    });
                }));
          })
            b;
      });
    DPOC2 p_new p1 oc1 l ra ->
      (case p1 of {
        (left, (l2, (a, b))) ->
          (case a of {
            (f2, (c2, lxr)) ->
              (\ r2 ->
                (case oc1 of {
                  (x, v) ->
                    (case p_new of {
                      (lefta, (l2a, (aa, ba))) ->
                        (case aa of {
                          (f2a, (c2a, lvr)) ->
                            (\ r2a ->
                              Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check (left == lefta)
                                    (Shows_Literal.showsl_lit
                                      "problem: left components modified"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(Arith.equal_nat f2 f2a)
(Shows_Literal.showsl_lit "problem: f components modified"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (Arith.equal_nat c2 c2a)
    (Shows_Literal.showsl_lit "problem: c components modified"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check (l2 == l2a)
        (Shows_Literal.showsl_lit "problem: l components modified"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (r2 == r2a)
            (Shows_Literal.showsl_lit "problem: r components modified"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (lxr == l ++ x ++ ra)
                (Shows_Literal.showsl_lit "problem: l_x_r != l @ x @ r"))
              (\ _ ->
                Check_Monad.check (lvr == l ++ v ++ ra)
                  (Shows_Literal.showsl_lit
                    "problem: l_v_r != l @ v @ r"))))))))
                                (\ xa ->
                                  Sum_Type.Inl
                                    (((((((Shows_Literal.showsl_lit
     "problem in checking overlap DPOC2 of\n" .
    showsl_pat p1) .
   Shows_Literal.showsl_literal "\n") .
  showsl_oc oc1) .
 Shows_Literal.showsl_lit "\nto yield\n") .
showsl_pat p_new) .
                                       Shows_Literal.showsl_literal "\n") .
                                      xa)));
                        })
                          ba;
                    });
                }));
          })
            b;
      });
    DPOC3_1 p_new p1 oc1 l ra ->
      (case p1 of {
        (left, (l2, (m2, lxr))) ->
          (case oc1 of {
            (x, v) ->
              (case p_new of {
                (lefta, (l2a, (m2a, lvr))) ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (left == lefta)
                        (Shows_Literal.showsl_lit
                          "problem: left components modified"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (m2 == m2a)
                            (Shows_Literal.showsl_lit
                              "problem: m components modified"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check (l2 == l2a)
                                (Shows_Literal.showsl_lit
                                  "problem: l components modified"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check (lxr == l ++ x ++ ra)
                                    (Shows_Literal.showsl_lit
                                      "problem: l_x_r != l @ x @ r"))
                                  (\ _ ->
                                    Check_Monad.check (lvr == l ++ v ++ ra)
                                      (Shows_Literal.showsl_lit
"problem: l_v_r != l @ v @ r"))))))
                    (\ xa ->
                      Sum_Type.Inl
                        (((((((Shows_Literal.showsl_lit
                                 "problem in checking overlap DPOC3_1 of\n" .
                                showsl_pat p1) .
                               Shows_Literal.showsl_literal "\n") .
                              showsl_oc oc1) .
                             Shows_Literal.showsl_lit "\nto yield\n") .
                            showsl_pat p_new) .
                           Shows_Literal.showsl_literal "\n") .
                          xa));
              });
          });
      });
    DPOC3_2 p_new p1 oc1 l ra x ->
      (case p1 of {
        (a, b) ->
          (case a of {
            (l1, (m1, r1)) ->
              (\ (l2, (m2, lx)) ->
                (case oc1 of {
                  (xr, v) ->
                    (case p_new of {
                      (aa, ba) ->
                        (case aa of {
                          (l1a, (m1a, r1r)) ->
                            (\ (l2a, (m2a, lv)) ->
                              Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check (m2 == m2a && m1 == m1a)
                                    (Shows_Literal.showsl_lit
                                      "problem: m components modified"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check (l1 == l1a)
(Shows_Literal.showsl_lit "problem: l components modified"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (l2 == l2a)
    (Shows_Literal.showsl_lit "problem: l2 components modified"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check (lx == l ++ x)
        (Shows_Literal.showsl_lit "problem: l_x != l @ x"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (xr == x ++ ra)
            (Shows_Literal.showsl_lit "problem: x_r != x @ r"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (r1r == r1 ++ ra)
                (Shows_Literal.showsl_lit "problem: r1_r != r1 @ r"))
              (\ _ ->
                Check_Monad.check (lv == l ++ v)
                  (Shows_Literal.showsl_lit "problem: l_v != l @ v"))))))))
                                (\ xa ->
                                  Sum_Type.Inl
                                    (((((((Shows_Literal.showsl_lit
     "problem in checking overlap DPOC3_2 of\n" .
    showsl_pat p1) .
   Shows_Literal.showsl_literal "\n") .
  showsl_oc oc1) .
 Shows_Literal.showsl_lit "\nto yield\n") .
showsl_pat p_new) .
                                       Shows_Literal.showsl_literal "\n") .
                                      xa)));
                        })
                          ba;
                    });
                }));
          })
            b;
      });
    DPDP1_1 p_new p1 p2 l ra ->
      (case p1 of {
        (left, (ll2, (mm, r2r))) ->
          (case p2 of {
            (a, b) ->
              (case a of {
                (l2, (mma, r2)) ->
                  (\ (l2a, (mm2, r2a)) ->
                    (case p_new of {
                      (lefta, (ll2a, (mm2a, r2pr))) ->
                        Error_Monad.catch_error
                          (Error_Monad.bind
                            (Check_Monad.check (left == lefta)
                              (Shows_Literal.showsl_lit
                                "problem: left components modified"))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check (mm == mma)
                                  (Shows_Literal.showsl_lit
                                    "problem: mm components modified"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check (mm2 == mm2a)
                                      (Shows_Literal.showsl_lit
"problem: mm2 components modified"))
                                    (\ _ ->
                                      Error_Monad.bind
(Check_Monad.check (ll2 == l ++ l2)
  (Shows_Literal.showsl_lit "problem: l_l2 != l @ l2"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check (r2r == r2 ++ ra)
      (Shows_Literal.showsl_lit "problem: r2_r != r2 @ r"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (r2pr == r2a ++ ra)
          (Shows_Literal.showsl_lit "problem: r2pr != r2\' @ r"))
        (\ _ ->
          Check_Monad.check (ll2a == l ++ l2a)
            (Shows_Literal.showsl_lit "problem: l_l2 != l @ l2 "))))))))
                          (\ x ->
                            Sum_Type.Inl
                              (((((((Shows_Literal.showsl_lit
                                       "problem in checking overlap DPDP1_1 of\n" .
                                      showsl_pat p1) .
                                     Shows_Literal.showsl_literal "\n") .
                                    showsl_pat p2) .
                                   Shows_Literal.showsl_lit "\nto yield\n") .
                                  showsl_pat p_new) .
                                 Shows_Literal.showsl_literal "\n") .
                                x));
                    }));
              })
                b;
          });
      });
    DPDP1_2 p_new p1 p2 l ra ->
      (case p1 of {
        (a, b) ->
          (case a of {
            (l1, (mm1, r1)) ->
              (\ (ll2, (mm, r1a)) ->
                (case p2 of {
                  (aa, ba) ->
                    (case aa of {
                      (l2, (mm2, r1r)) ->
                        (\ (l2a, (mm2a, r2)) ->
                          (case p_new of {
                            (ab, bb) ->
                              (case ab of {
                                (l3, (mm3, r1pr)) ->
                                  (\ (ll2a, (mm3a, r3)) ->
                                    Error_Monad.catch_error
                                      (Error_Monad.bind
(Check_Monad.check (l1 == l3)
  (Shows_Literal.showsl_lit "problem: l1\' components modified"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check (mm1 == mm3)
      (Shows_Literal.showsl_lit "problem: mm1\' components modified"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (mm == mm2)
          (Shows_Literal.showsl_lit "problem: mm components modified"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (mm2a == mm3a)
              (Shows_Literal.showsl_lit "problem: mm2\' components modified"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (r2 == r3)
                  (Shows_Literal.showsl_lit
                    "problem: r2\' components modified"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (ll2 == l ++ l2)
                      (Shows_Literal.showsl_lit "problem: l_l2 != l @ l2"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check (r1pr == r1 ++ ra)
                          (Shows_Literal.showsl_lit
                            "problem: r1\'r != r1\' @ r"))
                        (\ _ ->
                          Error_Monad.bind
                            (Check_Monad.check (r1r == r1a ++ ra)
                              (Shows_Literal.showsl_lit
                                "problem: r1r != r1 @ r"))
                            (\ _ ->
                              Check_Monad.check (ll2a == l ++ l2a)
                                (Shows_Literal.showsl_lit
                                  "problem: l_l2 != l @ l2 "))))))))))
                                      (\ x ->
Sum_Type.Inl
  (((((((Shows_Literal.showsl_lit "problem in checking overlap DPDP1_2 of\n" .
          showsl_pat p1) .
         Shows_Literal.showsl_literal "\n") .
        showsl_pat p2) .
       Shows_Literal.showsl_lit "\nto yield\n") .
      showsl_pat p_new) .
     Shows_Literal.showsl_literal "\n") .
    x)));
                              })
                                bb;
                          }));
                    })
                      ba;
                }));
          })
            b;
      });
    DPDP2_1 p_new p1 p2 l ra ->
      (case p1 of {
        (a, b) ->
          (case a of {
            (l1, (mm1, r1)) ->
              (\ (l1a, (mm, r2r)) ->
                (case p2 of {
                  (aa, ba) ->
                    (case aa of {
                      (ll1, (mm2, r2)) ->
                        (\ (l2, (mm2a, r2a)) ->
                          (case p_new of {
                            (ab, bb) ->
                              (case ab of {
                                (ll1a, (mm3, r3)) ->
                                  (\ (l3, (mm3a, r2pr)) ->
                                    Error_Monad.catch_error
                                      (Error_Monad.bind
(Check_Monad.check (r2r == r2 ++ ra)
  (Shows_Literal.showsl_lit "problem: r2r != r2 @ r"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check (ll1 == l ++ l1a)
      (Shows_Literal.showsl_lit "problem: l_l1 != l @ l1"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (ll1a == l ++ l1)
          (Shows_Literal.showsl_lit "problem: l_l1\' != l @ l1\' "))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (mm1 == mm3)
              (Shows_Literal.showsl_lit "problem: mm1\' component modified"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (r1 == r3)
                  (Shows_Literal.showsl_lit "problem: r1\' component modified"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (l2 == l3)
                      (Shows_Literal.showsl_lit
                        "problem: l2\' component modified"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check (mm2a == mm3a)
                          (Shows_Literal.showsl_lit
                            "problem: mm2\' components modified"))
                        (\ _ ->
                          Error_Monad.bind
                            (Check_Monad.check (mm == mm2)
                              (Shows_Literal.showsl_lit
                                "problem: mm components modified"))
                            (\ _ ->
                              Check_Monad.check (r2pr == r2a ++ ra)
                                (Shows_Literal.showsl_lit
                                  "problem: r2\'r != r2\' @ r"))))))))))
                                      (\ x ->
Sum_Type.Inl
  (((((((Shows_Literal.showsl_lit "problem in checking overlap DPDP2_1 of\n" .
          showsl_pat p1) .
         Shows_Literal.showsl_literal "\n") .
        showsl_pat p2) .
       Shows_Literal.showsl_lit "\nto yield\n") .
      showsl_pat p_new) .
     Shows_Literal.showsl_literal "\n") .
    x)));
                              })
                                bb;
                          }));
                    })
                      ba;
                }));
          })
            b;
      });
    DPDP2_2 p_new p1 p2 l ra ->
      (case p1 of {
        (a, b) ->
          (case a of {
            (l1, (mm1, r1)) ->
              (\ (l1a, (mm1a, r1a)) ->
                (case p2 of {
                  (aa, ba) ->
                    (case aa of {
                      (ll1, (mm2, r1r)) ->
                        (\ right ->
                          (case p_new of {
                            (ab, bb) ->
                              (case ab of {
                                (ll1a, (mm3, r1pr)) ->
                                  (\ righta ->
                                    Error_Monad.catch_error
                                      (Error_Monad.bind
(Check_Monad.check (r1r == r1a ++ ra)
  (Shows_Literal.showsl_lit "problem: r1r != r1 @ r"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check (ll1 == l ++ l1a)
      (Shows_Literal.showsl_lit "problem: l_l1 != l @ l1"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (ll1a == l ++ l1)
          (Shows_Literal.showsl_lit "problem: l_l1\' != l @ l1\' "))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (r1pr == r1 ++ ra)
              (Shows_Literal.showsl_lit "problem: r1\'_r != r1\' @ r "))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (mm1 == mm3)
                  (Shows_Literal.showsl_lit
                    "problem: mm1\' component modified"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (mm1a == mm2)
                      (Shows_Literal.showsl_lit
                        "problem: mm components modified"))
                    (\ _ ->
                      Check_Monad.check (right == righta)
                        (Shows_Literal.showsl_lit
                          "problem: right components modified"))))))))
                                      (\ x ->
Sum_Type.Inl
  (((((((Shows_Literal.showsl_lit "problem in checking overlap DPDP2_ of\n" .
          showsl_pat p1) .
         Shows_Literal.showsl_literal "\n") .
        showsl_pat p2) .
       Shows_Literal.showsl_lit "\nto yield\n") .
      showsl_pat p_new) .
     Shows_Literal.showsl_literal "\n") .
    x)));
                              })
                                bb;
                          }));
                    })
                      ba;
                }));
          })
            b;
      });
  });

check_proof ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Shows_Literal.Showl a) => Set.Set ([a], [a]) ->
                                  Set.Set
                                    (([a], ((Arith.Nat, (Arith.Nat, [a])),
     [a])),
                                      ([a],
((Arith.Nat, (Arith.Nat, [a])), [a]))) ->
                                    [Dp_proof_step a] ->
                                      Sum_Type.Sum (String -> String) ();
check_proof r delta [] = Sum_Type.Inr ();
check_proof r delta (p : ps) =
  Error_Monad.bind (check_step r p)
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ pa ->
              Check_Monad.check (Set.member pa delta)
                (Shows_Literal.showsl_lit
                   "problem: nothing known about premise " .
                  showsl_pat pa))
            (prems_of p))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          check_proof r
            (Set.sup_set delta
              (Set.insert (pat_of p)
                (Set_Impl.set_empty
                  (Phantom_Type.of_phantom
                    (Set_Impl.set_impl_prod ::
                      Phantom_Type.Phantom
                        (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
                          ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
                        Set_Impl.Set_impla)))))
            ps));

check_non_loop_srs_proof ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Shows_Literal.Showl a) => Set.Set ([a], [a]) ->
                                  Non_loop_srs_proof a ->
                                    Sum_Type.Sum (String -> String) ();
check_non_loop_srs_proof ra (SE_OC (m, lmr) l r steps) =
  Error_Monad.bind
    (Check_Monad.check
      (List.member (map pat_of steps)
        (([], ((Arith.zero_nat, (Arith.zero_nat, [])), m)),
          ([], ((Arith.zero_nat, (Arith.zero_nat, [])), lmr))))
      (Shows_Literal.showsl_lit "overlap closure not derived within proof"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (lmr == l ++ m ++ r)
          (Shows_Literal.showsl_lit "no selfoverlap"))
        (\ _ ->
          check_proof ra
            (Set_Impl.set_empty
              (Phantom_Type.of_phantom
                (Set_Impl.set_impl_prod ::
                  Phantom_Type.Phantom
                    (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
                      ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
                    Set_Impl.Set_impla)))
            steps));
check_non_loop_srs_proof ra (SE_DP (left, right) l r steps) =
  Error_Monad.bind
    (Check_Monad.check (List.member (map pat_of steps) (left, right))
      (Shows_Literal.showsl_lit "overlap closure not derived within proof"))
    (\ _ ->
      (case left of {
        (l1, (a, b)) ->
          (case a of {
            (f1, (c1, m1)) ->
              (\ r1 ->
                (case right of {
                  (l2, (aa, ba)) ->
                    (case aa of {
                      (f2, (c2, m2)) ->
                        (\ r2 ->
                          Error_Monad.bind
                            (Check_Monad.check
                              (m1 == m2 && l2 == l ++ l1 && r2 == r1 ++ r)
                              (Shows_Literal.showsl_lit
                                "problem with selfoverlap"))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (Arith.less_eq_nat f1 f2 &&
                                    Arith.equal_nat
                                      (Arith.modulo_nat
(Orderings.max (Arith.minus_nat c2 c1) (Arith.minus_nat c1 c2)) f1)
                                      Arith.zero_nat &&
                                      (if Arith.less_nat f1 f2
then Arith.equal_nat (Arith.modulo_nat f2 f1) Arith.zero_nat else True) &&
(if Arith.equal_nat f1 f2 then Arith.less_eq_nat c1 c2 else True))
                                  (Shows_Literal.showsl_lit
                                    "could not ensure fitting condition for selfoverlap"))
                                (\ _ ->
                                  check_proof ra
                                    (Set_Impl.set_empty
                                      (Phantom_Type.of_phantom
(Set_Impl.set_impl_prod ::
  Phantom_Type.Phantom
    (([a], ((Arith.Nat, (Arith.Nat, [a])), [a])),
      ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])))
    Set_Impl.Set_impla)))
                                    steps)));
                    })
                      ba;
                }));
          })
            b;
      }));

check_non_loop_srs_prf ::
  forall a b c d.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                  a -> Non_loop_srs_proof b ->
 Sum_Type.Sum (String -> String) ();
check_non_loop_srs_prf i tp prf =
  let {
    r = Termination_Problem_Spec.rules i tp;
    s = List.set (srs_of_trs_impl r);
  } in Error_Monad.bind
         (Check_Monad.check (null (Termination_Problem_Spec.q i tp))
           (Shows_Literal.showsl_lit "strategy for non-loops unsupported"))
         (\ _ -> check_non_loop_srs_proof s prf);

}
