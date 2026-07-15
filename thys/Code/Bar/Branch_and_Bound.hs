{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Branch_and_Bound(branch_and_bound_int) where {

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
import qualified Integral_Bounded_Vectors;
import qualified Archimedean_Field;
import qualified Is_Rat_To_Rat;
import qualified Simplex_Incremental;
import qualified Mapping;
import qualified QDelta;
import qualified Sum_Type;
import qualified Lattices_Big;
import qualified Phantom_Type;
import qualified HOL;
import qualified Farkas;
import qualified Term_Rewriting;
import qualified Rat;
import qualified Arith;

constraint_to_le_constraint ::
  Term_Rewriting.Constraint -> [Farkas.Le_constraint Rat.Rat];
constraint_to_le_constraint (Term_Rewriting.LEQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel l x];
constraint_to_le_constraint (Term_Rewriting.GEQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel (Term_Rewriting.uminus_linear_poly l)
     (Rat.uminus_rat x)];
constraint_to_le_constraint (Term_Rewriting.LT l x) =
  [Farkas.Le_Constraint Farkas.Lt_Rel l x];
constraint_to_le_constraint (Term_Rewriting.GT l x) =
  [Farkas.Le_Constraint Farkas.Lt_Rel (Term_Rewriting.uminus_linear_poly l)
     (Rat.uminus_rat x)];
constraint_to_le_constraint (Term_Rewriting.EQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel l x,
    Farkas.Le_Constraint Farkas.Leq_Rel (Term_Rewriting.uminus_linear_poly l)
      (Rat.uminus_rat x)];

var_list :: [Term_Rewriting.Constraint] -> [Arith.Nat];
var_list cs = let {
                lecs = concatMap constraint_to_le_constraint cs;
                polys = map Farkas.lec_poly lecs;
              } in Arith.remdups (concatMap Term_Rewriting.vars_list polys);

max_coeff :: Farkas.Le_constraint Rat.Rat -> Rat.Rat;
max_coeff (Farkas.Le_Constraint uu l c) =
  Lattices_Big.max
    (Arith.sup_set
      (Arith.insert (Rat.abs_rat c)
        (Arith.set_empty (Phantom_Type.of_phantom Term_Rewriting.set_impl_rat)))
      (Arith.image (\ x -> Rat.abs_rat (Term_Rewriting.coeff l x))
        (Term_Rewriting.vars l)));

normalize :: [Term_Rewriting.Constraint] -> [Farkas.Le_constraint Rat.Rat];
normalize cs = concatMap constraint_to_le_constraint cs;

sum_to_option :: forall a b. Sum_Type.Sum a b -> Maybe b;
sum_to_option (Sum_Type.Inr x) = Just x;
sum_to_option (Sum_Type.Inl uu) = Nothing;

atom_to_qdatom ::
  Term_Rewriting.Atom Rat.Rat -> Term_Rewriting.Atom QDelta.QDelta;
atom_to_qdatom atm =
  (case atm of {
    Term_Rewriting.Leq vr c ->
      Term_Rewriting.Leq vr (QDelta.QDelta c Rat.zero_rat);
    Term_Rewriting.Geq vr c ->
      Term_Rewriting.Geq vr (QDelta.QDelta c Rat.zero_rat);
  });

i_bounds_to_constraints ::
  forall a.
    [Arith.Nat] ->
      (Arith.Nat -> (a, Arith.Int)) ->
        (Arith.Nat -> (a, Arith.Int)) -> [(a, Term_Rewriting.Constraint)];
i_bounds_to_constraints is lb ub =
  map (\ x ->
        (fst (lb x),
          Term_Rewriting.GEQ (Term_Rewriting.var x) (Rat.of_int (snd (lb x)))))
    is ++
    map (\ x ->
          (fst (ub x),
            Term_Rewriting.LEQ (Term_Rewriting.var x)
              (Rat.of_int (snd (ub x)))))
      is;

bnb_state_init ::
  [Term_Rewriting.Constraint] ->
    [Arith.Nat] ->
      (Arith.Nat -> Arith.Int) ->
        (Arith.Nat -> Arith.Int) ->
          ([(Arith.Nat, Term_Rewriting.Constraint)],
            (Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int),
              (Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int),
                Sum_Type.Sum [Arith.Nat]
                  (Simplex_Incremental.Simplex_state Arith.Nat))));
bnb_state_init cs is lb ub =
  let {
    lba = zip is (Arith.upt Arith.zero_nat (Arith.size_list is));
    uba = zip is
            (Arith.upt (Arith.size_list is)
              (Arith.plus_nat (Arith.size_list is) (Arith.size_list is)));
    lbb = map (\ (x, y) -> (x, (y, lb x))) lba;
    ubb = map (\ (x, y) -> (x, (y, ub x))) uba;
    lb_m = Mapping.of_alist lbb;
    ub_m = Mapping.of_alist ubb;
    csa = zip (Arith.upt
                (Arith.plus_nat (Arith.size_list is) (Arith.size_list is))
                (Arith.plus_nat
                  (Arith.plus_nat (Arith.size_list is) (Arith.size_list is))
                  (Arith.size_list cs)))
            cs;
    bs = i_bounds_to_constraints is (Arith.the . Mapping.lookup lb_m)
           (Arith.the . Mapping.lookup ub_m) ++
           csa;
    s = Simplex_Incremental.assert_all_simplex (map fst bs)
          (Simplex_Incremental.init_simplex bs);
  } in (csa, (lb_m, (ub_m, s)));

mul_constraint ::
  Rat.Rat -> Farkas.Le_constraint Rat.Rat -> Farkas.Le_constraint Rat.Rat;
mul_constraint x (Farkas.Le_Constraint r l c) =
  Farkas.Le_Constraint r (Term_Rewriting.scaleRat_linear_poly x l)
    (Rat.times_rat x c);

atom_to_qdnsconstr ::
  Term_Rewriting.Atom Rat.Rat -> Term_Rewriting.Ns_constraint QDelta.QDelta;
atom_to_qdnsconstr atm =
  (case atm of {
    Term_Rewriting.Leq x qdcnst ->
      Term_Rewriting.LEQ_ns (Term_Rewriting.var x)
        (QDelta.QDelta qdcnst Rat.zero_rat);
    Term_Rewriting.Geq x qdcnst ->
      Term_Rewriting.GEQ_ns (Term_Rewriting.var x)
        (QDelta.QDelta qdcnst Rat.zero_rat);
  });

update_iatom_in_state ::
  Simplex_Incremental.Simplex_state Arith.Nat ->
    (Arith.Nat, Term_Rewriting.Atom Rat.Rat) ->
      Simplex_Incremental.Simplex_state Arith.Nat;
update_iatom_in_state s iatm =
  (case s of {
    Simplex_Incremental.Simplex_State (cs, ((asi, (tv, ui)), l3s)) ->
      let {
        csa = Arith.list_update cs (fst iatm) (atom_to_qdnsconstr (snd iatm));
        asia =
          Mapping.update (fst iatm) [(fst iatm, atom_to_qdatom (snd iatm))] asi;
      } in Simplex_Incremental.Simplex_State (csa, ((asia, (tv, ui)), l3s));
  });

del_atom_from_state ::
  Simplex_Incremental.Simplex_state Arith.Nat ->
    (Arith.Nat, Term_Rewriting.Atom Rat.Rat) ->
      Simplex_Incremental.Simplex_state Arith.Nat;
del_atom_from_state s iatm =
  (case s of {
    Simplex_Incremental.Simplex_State
      (l1, (l2, Term_Rewriting.State t bl bu v c uc))
      -> let {
           bua = Mapping.delete (Term_Rewriting.atom_var (snd iatm)) bu;
           bla = Mapping.delete (Term_Rewriting.atom_var (snd iatm)) bl;
         } in Simplex_Incremental.Simplex_State
                (l1, (l2, Term_Rewriting.State t bla bua v c uc));
  });

bnb_update_state ::
  [(Arith.Nat, Term_Rewriting.Constraint)] ->
    [Arith.Nat] ->
      (Arith.Nat -> (Arith.Nat, Arith.Int)) ->
        (Arith.Nat -> (Arith.Nat, Arith.Int)) ->
          Simplex_Incremental.Simplex_state Arith.Nat ->
            (Arith.Nat, Term_Rewriting.Atom Rat.Rat) ->
              Maybe (Simplex_Incremental.Simplex_state Arith.Nat);
bnb_update_state cs is lb ub s iatm =
  let {
    idx_list = map fst (i_bounds_to_constraints is lb ub ++ cs);
  } in (case Simplex_Incremental.assert_all_simplex
               (Arith.remove1 (fst iatm) idx_list) (del_atom_from_state s iatm)
         of {
         Sum_Type.Inl _ -> Nothing;
         Sum_Type.Inr sa ->
           sum_to_option
             (Simplex_Incremental.assert_simplex (fst iatm)
               (update_iatom_in_state sa iatm));
       });

bnb_state_core_p ::
  [(Arith.Nat, Term_Rewriting.Constraint)] ->
    [Arith.Nat] ->
      Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int) ->
        Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int) ->
          Simplex_Incremental.Simplex_state Arith.Nat ->
            Maybe (Maybe (Arith.Nat -> Rat.Rat));
bnb_state_core_p cs is lb ub s =
  (case Simplex_Incremental.check_simplex s of {
    (x, Nothing) ->
      let {
        v = Simplex_Incremental.solution_simplex x;
      } in (case Arith.find (\ xa -> not (Is_Rat_To_Rat.is_int_rat (v xa))) is
             of {
             Nothing -> Just (Just v);
             Just xa ->
               let {
                 new_leq =
                   (fst (Arith.the (Mapping.lookup ub xa)),
                     Term_Rewriting.Leq xa (Rat.of_int (Rat.floor_rat (v xa))));
                 new_geq =
                   (fst (Arith.the (Mapping.lookup lb xa)),
                     Term_Rewriting.Geq xa
                       (Rat.of_int (Archimedean_Field.ceiling (v xa))));
                 uba = Mapping.update xa
                         (fst (Arith.the (Mapping.lookup ub xa)),
                           Rat.floor_rat (v xa))
                         ub;
                 lba = Mapping.update xa
                         (fst (Arith.the (Mapping.lookup lb xa)),
                           Archimedean_Field.ceiling (v xa))
                         lb;
               } in Arith.bind
                      (case bnb_update_state cs is
                              (Arith.the . Mapping.lookup lb)
                              (Arith.the . Mapping.lookup uba) x new_leq
                        of {
                        Nothing -> Just Nothing;
                        Just a -> bnb_state_core_p cs is lb uba a;
                      })
                      (\ a ->
                        (case a of {
                          Nothing ->
                            (case bnb_update_state cs is
                                    (Arith.the . Mapping.lookup lba)
                                    (Arith.the . Mapping.lookup ub) x new_geq
                              of {
                              Nothing -> Just Nothing;
                              Just aa -> bnb_state_core_p cs is lba ub aa;
                            });
                          Just va -> Just (Just va);
                        }));
           });
    (_, Just _) -> Just Nothing;
  });

max_coeff_constraints :: [Farkas.Le_constraint Rat.Rat] -> Rat.Rat;
max_coeff_constraints cs =
  Lattices_Big.max (Arith.set (Rat.zero_rat : map max_coeff cs));

common_denominator :: Farkas.Le_constraint Rat.Rat -> Arith.Int;
common_denominator (Farkas.Le_Constraint uu l c) =
  let {
    coeffs_list = map (Term_Rewriting.coeff l) (Term_Rewriting.vars_list l);
    denominators = map (snd . Rat.quotient_of) (c : coeffs_list);
  } in Arith.fold Arith.lcm_int denominators Arith.one_int;

constraint_to_ints ::
  Farkas.Le_constraint Rat.Rat -> Farkas.Le_constraint Rat.Rat;
constraint_to_ints c = mul_constraint (Rat.of_int (common_denominator c)) c;

compute_bound_num_of_vars :: [Term_Rewriting.Constraint] -> Arith.Int;
compute_bound_num_of_vars cs =
  let {
    le_cs = normalize cs;
    le_csa = map constraint_to_ints le_cs;
    max_coeff = max_coeff_constraints le_csa;
    n = Arith.plus_nat Arith.one_nat (Arith.size_list (var_list cs));
  } in Arith.times_int (Arith.int_of_nat (Arith.plus_nat n Arith.one_nat))
         (Integral_Bounded_Vectors.det_bound_hadamard n
           (Rat.floor_rat max_coeff));

branch_and_bound ::
  [Term_Rewriting.Constraint] -> [Arith.Nat] -> Maybe (Arith.Nat -> Rat.Rat);
branch_and_bound cs is =
  let {
    bnd = compute_bound_num_of_vars cs;
  } in (case bnb_state_init cs is (\ _ -> Arith.uminus_int bnd) (\ _ -> bnd) of
         {
         (_, (_, (_, Sum_Type.Inl _))) -> Nothing;
         (csa, (lb_m, (ub_m, Sum_Type.Inr s))) ->
           Arith.the (bnb_state_core_p csa is lb_m ub_m s);
       });

vars_of_constraints :: [Term_Rewriting.Constraint] -> [Arith.Nat];
vars_of_constraints cs =
  Arith.remdups
    (concatMap (Term_Rewriting.vars_list . Farkas.lec_poly) (normalize cs));

branch_and_bound_int ::
  [Term_Rewriting.Constraint] -> Maybe (Arith.Nat -> Arith.Int);
branch_and_bound_int cs =
  let {
    vs = vars_of_constraints cs;
  } in (case branch_and_bound cs vs of {
         Nothing -> Nothing;
         Just v ->
           Just (\ x ->
                  (if Arith.membera vs x then Is_Rat_To_Rat.int_of_rat (v x)
                    else Arith.zero_int));
       });

}
