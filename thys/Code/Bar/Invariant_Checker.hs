{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Invariant_Checker(Art_edge, Art_ext, Art_edge_impl(..), Art_node_impl(..),
                     Hinter_ext, Art_impl_ext(..), art_of, showsl_art,
                     get_disj_invariant, check_unique_names,
                     check_art_invariants_impl)
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
import qualified Show_LTS;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Map;
import qualified Map_Of;
import qualified HOL;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;
import qualified Term_Rewriting;

data Art_edge a b c d e = Cover e
  | Children [(Term_Rewriting.Transition_rule a b c d, e)];

data Art_ext a b c d e f =
  Art_ext [e] [e] (e -> Art_edge a b c d e) (e -> d)
    (e -> Term_Rewriting.Formula (Term_Rewriting.Term a (b, c))) f;

data Art_edge_impl a b c = Cover_Edge a c | Children_Edge [(b, (a, c))];

data Art_node_impl a b c d e f g =
  Art_Node e (Term_Rewriting.Formula (Term_Rewriting.Term a (b, c))) d
    (Art_edge_impl e f g);

data Hinter_ext a b c d e =
  Hinter_ext [c] (b -> [d]) (c -> a) (c -> Maybe [a]) e;

data Art_impl_ext a b c d e f g h =
  Art_impl_ext [e] [Art_node_impl a b c d e f g] h;

invariant ::
  forall a b c d e f g.
    Art_node_impl a b c d e f g ->
      Term_Rewriting.Formula (Term_Rewriting.Term a (b, c));
invariant (Art_Node x1 x2 x3 x4) = x2;

location :: forall a b c d e f g. Art_node_impl a b c d e f g -> d;
location (Art_Node x1 x2 x3 x4) = x3;

initial_nodesa :: forall a b c d e f g h. Art_impl_ext a b c d e f g h -> [e];
initial_nodesa (Art_impl_ext initial_nodes nodes more) = initial_nodes;

name :: forall a b c d e f g. Art_node_impl a b c d e f g -> e;
name (Art_Node x1 x2 x3 x4) = x1;

edgea ::
  forall a b c d e f g. Art_node_impl a b c d e f g -> Art_edge_impl e f g;
edgea (Art_Node x1 x2 x3 x4) = x4;

nodesb ::
  forall a b c d e f g h.
    Art_impl_ext a b c d e f g h -> [Art_node_impl a b c d e f g];
nodesb (Art_impl_ext initial_nodes nodes more) = nodes;

art_edge_of ::
  forall a b c d e f g.
    (Arith.Ccompare e, Eq e, Mapping.Mapping_impl e,
      Shows_Literal.Showl e) => Term_Rewriting.Lts_impl a b c d e ->
                                  Art_edge_impl f e g -> Art_edge a b c d f;
art_edge_of pi (Cover_Edge an uu) = Cover an;
art_edge_of pi (Children_Edge ans) =
  Children (map (\ (t, (a, _)) -> (Term_Rewriting.transition_of pi t, a)) ans);

art_nodes :: forall a b c d e f g. Art_impl_ext a b c d e f g () -> [e];
art_nodes ai = map name (nodesb ai);

art_of ::
  forall a b c d e f g.
    (Arith.Ccompare e, Eq e, Mapping.Mapping_impl e, Shows_Literal.Showl e,
      Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Shows_Literal.Showl f) => Term_Rewriting.Lts_impl a b c d e ->
                                  Art_impl_ext a b c d f e g () ->
                                    Art_ext a b c d f ();
art_of pi ai =
  let {
    ans = nodesb ai;
  } in Art_ext (initial_nodesa ai) (art_nodes ai)
         (Map_Of.map_of_total
           (\ a ->
             Shows_Literal.showsl_lit "error in looking up art edge " .
               Shows_Literal.showsl a)
           (map (\ a -> (name a, art_edge_of pi (edgea a))) ans))
         (Map_Of.map_of_total
           (\ a ->
             Shows_Literal.showsl_lit "error in looking up node location " .
               Shows_Literal.showsl a)
           (map (\ a -> (name a, location a)) ans))
         (Map_Of.map_of_total
           (\ a ->
             Shows_Literal.showsl_lit "error in looking up node invariant " .
               Shows_Literal.showsl a)
           (map (\ a -> (name a, invariant a)) ans))
         ();

edge :: forall a b c d e f. Art_ext a b c d e f -> e -> Art_edge a b c d e;
edge (Art_ext initial_nodes nodes edge node_location node_invariant more) =
  edge;

nodes :: forall a b c d e f. Art_ext a b c d e f -> [e];
nodes (Art_ext initial_nodes nodes edge node_location node_invariant more) =
  nodes;

showsl_art_node ::
  forall a b c d e f g.
    (Shows_Literal.Showl d, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => Art_node_impl a b c d e f g -> String -> String;
showsl_art_node (Art_Node n uu l (Cover_Edge m uv)) =
  (((Shows_Literal.showsl n . Shows_Literal.showsl_lit "(@ ") .
     Shows_Literal.showsl l) .
    Shows_Literal.showsl_lit "): covered by ") .
    Shows_Literal.showsl m;
showsl_art_node (Art_Node n uw l (Children_Edge ls)) =
  (((Shows_Literal.showsl n . Shows_Literal.showsl_lit "(@ ") .
     Shows_Literal.showsl l) .
    Shows_Literal.showsl_lit "): goes to ") .
    Shows_Literal.default_showsl_list
      (\ (tr, (na, _)) ->
        ((Shows_Literal.showsl_lit "-" . Shows_Literal.showsl tr) .
          Shows_Literal.showsl_lit "->") .
          Shows_Literal.showsl na)
      ls;

showsl_art ::
  forall a b c d e f g.
    (Shows_Literal.Showl d, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => Art_impl_ext a b c d e f g () ->
                                  String -> String;
showsl_art a =
  (((Shows_Literal.showsl_lit "ART:\nInitial node: " .
      Shows_Literal.showsl_list (initial_nodesa a)) .
     Shows_Literal.showsl_lit "\nArcs\n") .
    Shows_Literal.showsl_sep showsl_art_node (Shows_Literal.showsl_literal "\n")
      (nodesb a)) .
    Shows_Literal.showsl_literal "\n";

is_cover_node :: forall a b c d e f g. Art_node_impl a b c d e f g -> Bool;
is_cover_node (Art_Node uu uv uw (Cover_Edge ux uy)) = True;
is_cover_node (Art_Node uz va vb (Children_Edge vc)) = False;

cover_hints ::
  forall a b c d e f g.
    (Arith.Ccompare e, Eq e, Mapping.Mapping_impl e,
      HOL.Default g) => Art_impl_ext a b c d e f g () -> e -> g;
cover_hints ai =
  Map_Of.map_of_default HOL.defaulta
    (Arith.map_filter
      (\ x ->
        (if is_cover_node x then Just (name x, (case edgea x of {
         Cover_Edge _ h -> h;
       }))
          else Nothing))
      (nodesb ai));

nodesa :: forall a b c d e. Hinter_ext a b c d e -> [c];
nodesa (Hinter_ext nodes succ_trans_list cover_hints transition_hints more) =
  nodes;

transition_hints ::
  forall a b c d e f g.
    (Eq e) => Art_impl_ext a b c d e f g () -> e -> Maybe [g];
transition_hints ai =
  Map.map_of
    (Arith.map_filter
      (\ x ->
        (if not (is_cover_node x)
          then Just (name x, (case edgea x of {
                               Children_Edge a -> map (\ (_, (_, h)) -> h) a;
                             }))
          else Nothing))
      (nodesb ai));

initial_nodes :: forall a b c d e f. Art_ext a b c d e f -> [e];
initial_nodes
  (Art_ext initial_nodes nodes edge node_location node_invariant more) =
  initial_nodes;

node_location :: forall a b c d e f. Art_ext a b c d e f -> e -> d;
node_location
  (Art_ext initial_nodes nodes edge node_location node_invariant more) =
  node_location;

node_invariant ::
  forall a b c d e f.
    Art_ext a b c d e f ->
      e -> Term_Rewriting.Formula (Term_Rewriting.Term a (b, c));
node_invariant
  (Art_ext initial_nodes nodes edge node_location node_invariant more) =
  node_invariant;

is_cover_nodea :: forall a b c d e. Art_edge a b c d e -> Bool;
is_cover_nodea (Cover x1) = True;
is_cover_nodea (Children x2) = False;

get_disj_invariant ::
  forall a b c d e.
    (Eq d) => Art_ext a b c d e () ->
                d -> Term_Rewriting.Formula (Term_Rewriting.Term a (b, c));
get_disj_invariant a l =
  Term_Rewriting.Disjunction
    (Arith.map_filter
      (\ x ->
        (if node_location a x == l && not (is_cover_nodea (edge a x))
          then Just (node_invariant a x) else Nothing))
      (nodes a));

cover_hintsa :: forall a b c d e. Hinter_ext a b c d e -> c -> a;
cover_hintsa
  (Hinter_ext nodes succ_trans_list cover_hints transition_hints more) =
  cover_hints;

art ::
  forall a b c d e f.
    (Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b) => (a -> ([b], b)) ->
                                  Arith.Set b -> Art_ext a c b d e f -> Bool;
art type_of_fun bool_types a =
  all (\ aa ->
        Term_Rewriting.formula (Term_Rewriting.is_bool type_of_fun bool_types)
          (node_invariant a aa))
    (nodes a);

succ_trans_list :: forall a b c d e. Hinter_ext a b c d e -> b -> [d];
succ_trans_list
  (Hinter_ext nodes succ_trans_list cover_hints transition_hints more) =
  succ_trans_list;

transition_hintsa :: forall a b c d e. Hinter_ext a b c d e -> c -> Maybe [a];
transition_hintsa
  (Hinter_ext nodes succ_trans_list cover_hints transition_hints more) =
  transition_hints;

check_art ::
  forall a b c d e f.
    (Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    Art_ext a c b d e f ->
                                      Sum_Type.Sum (String -> String) ();
check_art type_of_fun bool_types a =
  Check_Monad.check (art type_of_fun bool_types a)
    (Shows_Literal.showsl_lit "ill-formed invariant");

make_hinter ::
  forall a b c d e f g h i j k l.
    (Eq d, Arith.Ccompare j, Eq j, Mapping.Mapping_impl j,
      HOL.Default l) => Term_Rewriting.Lts_impl a b c d e ->
                          Art_impl_ext f g h i j k l () ->
                            Hinter_ext l d j
                              (Term_Rewriting.Transition_rule a b c d) ();
make_hinter pi ai =
  Hinter_ext (art_nodes ai) (Term_Rewriting.succ_transitions pi)
    (cover_hints ai) (transition_hints ai) ();

check_initial_cond ::
  forall a b c d e f.
    (Eq a, Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, Eq e,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a (b, c) ->
                                  String -> String) ->
                                  Art_ext a b c d e f ->
                                    Sum_Type.Sum (String -> String) ();
check_initial_cond sa a =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ init ->
        Error_Monad.bind
          (Check_Monad.check (Arith.membera (nodes a) init)
            ((Shows_Literal.showsl_lit "initial node of A (" .
               Shows_Literal.showsl init) .
              Shows_Literal.showsl_lit ") is not mentioned as node of ART"))
          (\ _ ->
            Check_Monad.check
              (Term_Rewriting.equal_formula (node_invariant a init)
                (Term_Rewriting.Conjunction []))
              (((Shows_Literal.showsl_lit
                   "the node invariant for the initial ART node (" .
                  Shows_Literal.showsl init) .
                 Shows_Literal.showsl_lit ") must be TRUE,  but it is ") .
                Term_Rewriting.showsl_formula sa (node_invariant a init))))
      (initial_nodes a))
    (\ x -> Sum_Type.Inl (snd x));

check_unique_names ::
  forall a b c d e f g h.
    (Eq e) => Art_impl_ext a b c d e f g h ->
                Sum_Type.Sum (String -> String) ();
check_unique_names ai =
  Check_Monad.check (Arith.distinct (map name (nodesb ai)))
    (Shows_Literal.showsl_lit "Nodes in art graph must have unique names");

check_children_edges_cond ::
  forall a b c d e f g h i j k.
    (HOL.Default a, Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, Eq d, Shows_Literal.Showl d, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> Term_Rewriting.Formula
(Term_Rewriting.Term b (Term_Rewriting.Trans_var c, d)) ->
Sum_Type.Sum (String -> String) ()) ->
                                  (Term_Rewriting.Term b
                                     (Term_Rewriting.Trans_var c, d) ->
                                    String -> String) ->
                                    (Bool ->
                                      Term_Rewriting.Term b
(Term_Rewriting.Trans_var c, d) ->
Term_Rewriting.Formula
  (Term_Rewriting.Term b (Term_Rewriting.Trans_var c, d))) ->
                                      Art_ext b c d e f g ->
Term_Rewriting.Lts_ext b c d e h ->
  Hinter_ext a i f j k -> Sum_Type.Sum (String -> String) ();
check_children_edges_cond tc2 sa2 ne2 a p h =
  let {
    lc = Term_Rewriting.assertion p;
  } in Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ aa ->
               (case edge a aa of {
                 Cover _ -> Sum_Type.Inr ();
                 Children children ->
                   (case transition_hintsa h aa of {
                     Nothing ->
                       Sum_Type.Inl (Shows_Literal.showsl_lit "not yet");
                     Just hints ->
                       Error_Monad.catch_error
                         (Error_Monad.bind
                           (Check_Monad.check
                             (Arith.equal_nat (Arith.size_list hints)
                               (Arith.size_list children))
                             (Shows_Literal.showsl_lit
                               "the number of hints differs from the number of children"))
                           (\ _ ->
                             Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (b, c) ->
                                   (case b of {
                                     (tau, ba) ->
                                       (\ ha ->
 (case tau of {
   Term_Rewriting.Transition l _ phi ->
     Error_Monad.catch_error
       (Term_Rewriting.check_valid_formula sa2 tc2 ne2 ha
         (Term_Rewriting.Disjunction
           [Term_Rewriting.map_formula
              (Term_Rewriting.rename_vars_exp Term_Rewriting.Post)
              (node_invariant a ba),
             Term_Rewriting.form_not
               (Term_Rewriting.map_formula
                 (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
                 (node_invariant a aa)),
             Term_Rewriting.form_not
               (Term_Rewriting.map_formula
                 (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre) (lc l)),
             Term_Rewriting.form_not phi]))
       (\ x ->
         Sum_Type.Inl
           (((((((Shows_Literal.showsl_lit "problem in checking edge " .
                   Shows_Literal.showsl aa) .
                  Shows_Literal.showsl_lit " --> ") .
                 Shows_Literal.showsl ba) .
                Shows_Literal.showsl_lit " for transition\n") .
               Show_LTS.showsl_transition sa2 tau) .
              Shows_Literal.showsl_literal "\n") .
             x));
 }));
                                   })
                                     c)
                                 (zip children hints))
                               (\ x -> Sum_Type.Inl (snd x))))
                         (\ x ->
                           Sum_Type.Inl
                             (((Shows_Literal.showsl_lit
                                  "problem in checking transitions of node " .
                                 Shows_Literal.showsl aa) .
                                Shows_Literal.showsl_literal "\n") .
                               x));
                   });
               }))
             (nodesa h))
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
                "could not ensure transition edge condition of ART\n" .
               x));

check_cover_edges_cond ::
  forall a b c d e f g h i j k l m n o.
    (HOL.Default a, Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, Eq d, Shows_Literal.Showl d, Eq e, Eq f,
      Shows_Literal.Showl f) => (a -> Term_Rewriting.Formula
(Term_Rewriting.Term b (c, d)) ->
Sum_Type.Sum (String -> String) ()) ->
                                  (Term_Rewriting.Term b (c, d) ->
                                    String -> String) ->
                                    (Bool ->
                                      Term_Rewriting.Term b (c, d) ->
Term_Rewriting.Formula (Term_Rewriting.Term b (c, d))) ->
                                      Art_ext b c d e f g ->
Term_Rewriting.Lts_ext h i j k l ->
  Hinter_ext a m f n o -> Sum_Type.Sum (String -> String) ();
check_cover_edges_cond tc sa ne a p h =
  let {
    _ = Term_Rewriting.assertion p;
  } in Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ aa ->
               (case edge a aa of {
                 Cover b ->
                   Error_Monad.catch_error
                     (Error_Monad.bind
                       (Check_Monad.check (Arith.membera (nodes a) b)
                         (Shows_Literal.showsl_lit
                           "target node is not listed as art-node"))
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check
                             (node_location a aa == node_location a b)
                             (Shows_Literal.showsl_lit "node-locations differ"))
                           (\ _ ->
                             Error_Monad.bind
                               (Check_Monad.check
                                 (not (is_cover_nodea (edge a b)))
                                 (Shows_Literal.showsl_lit
                                   "target node must not have cover edge"))
                               (\ _ ->
                                 Term_Rewriting.check_valid_formula sa tc ne
                                   (cover_hintsa h aa)
                                   (Term_Rewriting.Disjunction
                                     [node_invariant a b,
                                       Term_Rewriting.form_not
 (node_invariant a aa)])))))
                     (\ x ->
                       Sum_Type.Inl
                         (((Shows_Literal.showsl_lit
                              "problem in checking cover edge of node " .
                             Shows_Literal.showsl aa) .
                            Shows_Literal.showsl_literal "\n") .
                           x));
                 Children _ -> Sum_Type.Inr ();
               }))
             (nodesa h))
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
                "could not ensure cover edge condition of ART\n" .
               x));

check_simulation_cond ::
  forall a b c d e f g h i j k l m.
    (HOL.Default a, Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, Eq d, Shows_Literal.Showl d, Arith.Cenum e,
      Arith.Ceq e, Arith.Ccompare e, Eq e, Arith.Set_impl e,
      Shows_Literal.Showl e, Eq f,
      Shows_Literal.Showl f) => (a -> Term_Rewriting.Formula
(Term_Rewriting.Term b (c, d)) ->
Sum_Type.Sum (String -> String) ()) ->
                                  (Term_Rewriting.Term b (c, d) ->
                                    String -> String) ->
                                    (Bool ->
                                      Term_Rewriting.Term b (c, d) ->
Term_Rewriting.Formula (Term_Rewriting.Term b (c, d))) ->
                                      Art_ext b c d e f g ->
Term_Rewriting.Lts_ext h i j e k ->
  Hinter_ext l e f (Term_Rewriting.Transition_rule b c d e) m ->
    Sum_Type.Sum (String -> String) ();
check_simulation_cond tc sa ne a p h =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check
        (Arith.less_eq_set (Term_Rewriting.initial p)
          (Arith.set (map (node_location a) (initial_nodes a))))
        (Shows_Literal.showsl_lit
          "not all initial nodes of LTS are represented by initial nodes in ART"))
      (\ _ ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ aa ->
              (case edge a aa of {
                Cover _ -> Sum_Type.Inr ();
                Children children ->
                  let {
                    l = node_location a aa;
                  } in Error_Monad.catch_error
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ tau ->
                               Check_Monad.check
                                 (any (\ (taua, b) ->
Term_Rewriting.equal_transition_rule taua tau &&
  node_location a b == Term_Rewriting.target tau && Arith.membera (nodes a) b)
                                   children)
                                 (((((Shows_Literal.showsl_lit
"could not find matching transition in ART for node " .
                                       Shows_Literal.showsl aa) .
                                      Shows_Literal.showsl_lit
" and transition ") .
                                     Shows_Literal.showsl
                                       (Term_Rewriting.source tau)) .
                                    Shows_Literal.showsl_lit " --> ") .
                                   Shows_Literal.showsl
                                     (Term_Rewriting.target tau)))
                             (succ_trans_list h l))
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ e1 ->
                           Error_Monad.catch_error
                             (Term_Rewriting.check_valid_formula sa tc ne
                               HOL.defaulta
                               (Term_Rewriting.form_not (node_invariant a aa)))
                             (\ _ ->
                               Sum_Type.Inl
                                 (e1 . Shows_Literal.showsl_lit
 "\nand could not prove unsatisfiability of the node invariant")));
              }))
            (nodesa h))
          (\ x -> Sum_Type.Inl (snd x))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "could not ensure simulation condition of ART\n" .
          x));

check_art_invariants ::
  forall a b c d e f g h i.
    (Eq a, Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b, HOL.Default c, Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d, Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Eq e,
      Arith.Set_impl e, Shows_Literal.Showl e, Eq f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (c -> Term_Rewriting.Formula
    (Term_Rewriting.Term a (d, b)) ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (c ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a (d, b) -> String -> String) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) -> String -> String) ->
    (Bool ->
      Term_Rewriting.Term a (d, b) ->
        Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
      (Bool ->
        Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
          Term_Rewriting.Formula
            (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
        Art_ext a d b e f g ->
          Term_Rewriting.Lts_ext a d b e h ->
            Hinter_ext c e f (Term_Rewriting.Transition_rule a d b e) i ->
              Sum_Type.Sum (String -> String) ();
check_art_invariants type_of_fun bool_types tc tc2 sa sa2 ne ne2 a p h =
  Error_Monad.catch_error
    (Error_Monad.bind (check_art type_of_fun bool_types a)
      (\ _ ->
        Error_Monad.bind (check_initial_cond sa a)
          (\ _ ->
            Error_Monad.bind (check_simulation_cond tc sa ne a p h)
              (\ _ ->
                Error_Monad.bind (check_cover_edges_cond tc sa ne a p h)
                  (\ _ -> check_children_edges_cond tc2 sa2 ne2 a p h)))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "could not ensure validity of art-graph:\n" .
          x));

check_art_invariants_impl ::
  forall a b c d e f g.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Eq e,
      Mapping.Mapping_impl e, Arith.Set_impl e, Shows_Literal.Showl e,
      Arith.Ccompare f, Eq f, Mapping.Mapping_impl f, Shows_Literal.Showl f,
      Arith.Ceq g, Arith.Ccompare g, Eq g, Mapping.Mapping_impl g,
      Arith.Set_impl g,
      Shows_Literal.Showl g) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (c -> Term_Rewriting.Formula
    (Term_Rewriting.Term a (d, b)) ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (c ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a (d, b) -> String -> String) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) -> String -> String) ->
    (Bool ->
      Term_Rewriting.Term a (d, b) ->
        Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
      (Bool ->
        Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
          Term_Rewriting.Formula
            (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
        Art_impl_ext a d b e f g c () ->
          Term_Rewriting.Lts_impl a d b e g ->
            Sum_Type.Sum (String -> String) ();
check_art_invariants_impl type_of_fun bool_types tc tc2 sa sa2 ne ne2 ai pi =
  check_art_invariants type_of_fun bool_types tc tc2 sa sa2 ne ne2
    (art_of pi ai) (Term_Rewriting.lts_of pi) (make_hinter pi ai);

}
