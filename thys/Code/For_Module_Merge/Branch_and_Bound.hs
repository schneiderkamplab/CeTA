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
import qualified GCD;
import qualified Archimedean_Field;
import qualified Is_Rat_To_Rat;
import qualified Product_Type;
import qualified Option;
import qualified Simplex_Incremental;
import qualified Mapping;
import qualified Mapping_Impl;
import qualified QDelta;
import qualified Sum_Type;
import qualified Lattices_Big;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Set;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified List;
import qualified HOL;
import qualified Abstract_Linear_Poly;
import qualified Farkas;
import qualified Simplex;
import qualified Rat;
import qualified Arith;

constraint_to_le_constraint ::
  Simplex.Constraint -> [Farkas.Le_constraint Rat.Rat];
constraint_to_le_constraint (Simplex.LEQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel l x];
constraint_to_le_constraint (Simplex.GEQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel
     (Abstract_Linear_Poly.uminus_linear_poly l) (Rat.uminus_rat x)];
constraint_to_le_constraint (Simplex.LT l x) =
  [Farkas.Le_Constraint Farkas.Lt_Rel l x];
constraint_to_le_constraint (Simplex.GT l x) =
  [Farkas.Le_Constraint Farkas.Lt_Rel
     (Abstract_Linear_Poly.uminus_linear_poly l) (Rat.uminus_rat x)];
constraint_to_le_constraint (Simplex.EQ l x) =
  [Farkas.Le_Constraint Farkas.Leq_Rel l x,
    Farkas.Le_Constraint Farkas.Leq_Rel
      (Abstract_Linear_Poly.uminus_linear_poly l) (Rat.uminus_rat x)];

var_list :: [Simplex.Constraint] -> [Arith.Nat];
var_list cs =
  let {
    lecs = concatMap constraint_to_le_constraint cs;
    polys = map Farkas.lec_poly lecs;
  } in List.remdups (concatMap Abstract_Linear_Poly.vars_list polys);

max_coeff :: Farkas.Le_constraint Rat.Rat -> Rat.Rat;
max_coeff (Farkas.Le_Constraint uu l c) =
  Lattices_Big.max
    (Set.sup_set
      (Set.insert (Rat.abs_rat c)
        (Set_Impl.set_empty
          (Phantom_Type.of_phantom Container_Setup.set_impl_rat)))
      (Set.image (\ x -> Rat.abs_rat (Abstract_Linear_Poly.coeff l x))
        (Abstract_Linear_Poly.vars l)));

normalize :: [Simplex.Constraint] -> [Farkas.Le_constraint Rat.Rat];
normalize cs = concatMap constraint_to_le_constraint cs;

sum_to_option :: forall a b. Sum_Type.Sum a b -> Maybe b;
sum_to_option (Sum_Type.Inr x) = Just x;
sum_to_option (Sum_Type.Inl uu) = Nothing;

atom_to_qdatom :: Simplex.Atom Rat.Rat -> Simplex.Atom QDelta.QDelta;
atom_to_qdatom atm =
  (case atm of {
    Simplex.Leq vr c -> Simplex.Leq vr (QDelta.QDelta c Rat.zero_rat);
    Simplex.Geq vr c -> Simplex.Geq vr (QDelta.QDelta c Rat.zero_rat);
  });

i_bounds_to_constraints ::
  forall a.
    [Arith.Nat] ->
      (Arith.Nat -> (a, Arith.Int)) ->
        (Arith.Nat -> (a, Arith.Int)) -> [(a, Simplex.Constraint)];
i_bounds_to_constraints is lb ub =
  map (\ x ->
        (fst (lb x),
          Simplex.GEQ (Abstract_Linear_Poly.var x) (Rat.of_int (snd (lb x)))))
    is ++
    map (\ x ->
          (fst (ub x),
            Simplex.LEQ (Abstract_Linear_Poly.var x) (Rat.of_int (snd (ub x)))))
      is;

bnb_state_init ::
  [Simplex.Constraint] ->
    [Arith.Nat] ->
      (Arith.Nat -> Arith.Int) ->
        (Arith.Nat -> Arith.Int) ->
          ([(Arith.Nat, Simplex.Constraint)],
            (Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int),
              (Mapping.Mapping Arith.Nat (Arith.Nat, Arith.Int),
                Sum_Type.Sum [Arith.Nat]
                  (Simplex_Incremental.Simplex_state Arith.Nat))));
bnb_state_init cs is lb ub =
  let {
    lba = zip is (List.upt Arith.zero_nat (List.size_list is));
    uba = zip is
            (List.upt (List.size_list is)
              (Arith.plus_nat (List.size_list is) (List.size_list is)));
    lbb = map (\ (x, y) -> (x, (y, lb x))) lba;
    ubb = map (\ (x, y) -> (x, (y, ub x))) uba;
    lb_m = Mapping.of_alist lbb;
    ub_m = Mapping.of_alist ubb;
    csa = zip (List.upt (Arith.plus_nat (List.size_list is) (List.size_list is))
                (Arith.plus_nat
                  (Arith.plus_nat (List.size_list is) (List.size_list is))
                  (List.size_list cs)))
            cs;
    bs = i_bounds_to_constraints is (Option.the . Mapping.lookup lb_m)
           (Option.the . Mapping.lookup ub_m) ++
           csa;
    s = Simplex_Incremental.assert_all_simplex (map fst bs)
          (Simplex_Incremental.init_simplex bs);
  } in (csa, (lb_m, (ub_m, s)));

mul_constraint ::
  Rat.Rat -> Farkas.Le_constraint Rat.Rat -> Farkas.Le_constraint Rat.Rat;
mul_constraint x (Farkas.Le_Constraint r l c) =
  Farkas.Le_Constraint r (Abstract_Linear_Poly.scaleRat_linear_poly x l)
    (Rat.times_rat x c);

atom_to_qdnsconstr ::
  Simplex.Atom Rat.Rat -> Simplex.Ns_constraint QDelta.QDelta;
atom_to_qdnsconstr atm =
  (case atm of {
    Simplex.Leq x qdcnst ->
      Simplex.LEQ_ns (Abstract_Linear_Poly.var x)
        (QDelta.QDelta qdcnst Rat.zero_rat);
    Simplex.Geq x qdcnst ->
      Simplex.GEQ_ns (Abstract_Linear_Poly.var x)
        (QDelta.QDelta qdcnst Rat.zero_rat);
  });

update_iatom_in_state ::
  Simplex_Incremental.Simplex_state Arith.Nat ->
    (Arith.Nat, Simplex.Atom Rat.Rat) ->
      Simplex_Incremental.Simplex_state Arith.Nat;
update_iatom_in_state s iatm =
  (case s of {
    Simplex_Incremental.Simplex_State (cs, ((asi, (tv, ui)), l3s)) ->
      let {
        csa = List.list_update cs (fst iatm) (atom_to_qdnsconstr (snd iatm));
        asia =
          Mapping.update (fst iatm) [(fst iatm, atom_to_qdatom (snd iatm))] asi;
      } in Simplex_Incremental.Simplex_State (csa, ((asia, (tv, ui)), l3s));
  });

del_atom_from_state ::
  Simplex_Incremental.Simplex_state Arith.Nat ->
    (Arith.Nat, Simplex.Atom Rat.Rat) ->
      Simplex_Incremental.Simplex_state Arith.Nat;
del_atom_from_state s iatm =
  (case s of {
    Simplex_Incremental.Simplex_State (l1, (l2, Simplex.State t bl bu v c uc))
      -> let {
           bua = Mapping.delete (Simplex.atom_var (snd iatm)) bu;
           bla = Mapping.delete (Simplex.atom_var (snd iatm)) bl;
         } in Simplex_Incremental.Simplex_State
                (l1, (l2, Simplex.State t bla bua v c uc));
  });

bnb_update_state ::
  [(Arith.Nat, Simplex.Constraint)] ->
    [Arith.Nat] ->
      (Arith.Nat -> (Arith.Nat, Arith.Int)) ->
        (Arith.Nat -> (Arith.Nat, Arith.Int)) ->
          Simplex_Incremental.Simplex_state Arith.Nat ->
            (Arith.Nat, Simplex.Atom Rat.Rat) ->
              Maybe (Simplex_Incremental.Simplex_state Arith.Nat);
bnb_update_state cs is lb ub s iatm =
  let {
    idx_list = map fst (i_bounds_to_constraints is lb ub ++ cs);
  } in (case Simplex_Incremental.assert_all_simplex
               (List.remove1 (fst iatm) idx_list) (del_atom_from_state s iatm)
         of {
         Sum_Type.Inl _ -> Nothing;
         Sum_Type.Inr sa ->
           sum_to_option
             (Simplex_Incremental.assert_simplex (fst iatm)
               (update_iatom_in_state sa iatm));
       });

bnb_state_core_p ::
  [(Arith.Nat, Simplex.Constraint)] ->
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
      } in (case List.find (\ xa -> not (Is_Rat_To_Rat.is_int_rat (v xa))) is of
             {
             Nothing -> Just (Just v);
             Just xa ->
               let {
                 new_leq =
                   (fst (Option.the (Mapping.lookup ub xa)),
                     Simplex.Leq xa (Rat.of_int (Rat.floor_rat (v xa))));
                 new_geq =
                   (fst (Option.the (Mapping.lookup lb xa)),
                     Simplex.Geq xa
                       (Rat.of_int (Archimedean_Field.ceiling (v xa))));
                 uba = Mapping.update xa
                         (fst (Option.the (Mapping.lookup ub xa)),
                           Rat.floor_rat (v xa))
                         ub;
                 lba = Mapping.update xa
                         (fst (Option.the (Mapping.lookup lb xa)),
                           Archimedean_Field.ceiling (v xa))
                         lb;
               } in Option.bind
                      (case bnb_update_state cs is
                              (Option.the . Mapping.lookup lb)
                              (Option.the . Mapping.lookup uba) x new_leq
                        of {
                        Nothing -> Just Nothing;
                        Just a -> bnb_state_core_p cs is lb uba a;
                      })
                      (\ a ->
                        (case a of {
                          Nothing ->
                            (case bnb_update_state cs is
                                    (Option.the . Mapping.lookup lba)
                                    (Option.the . Mapping.lookup ub) x new_geq
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
  Lattices_Big.max (List.set (Rat.zero_rat : map max_coeff cs));

common_denominator :: Farkas.Le_constraint Rat.Rat -> Arith.Int;
common_denominator (Farkas.Le_Constraint uu l c) =
  let {
    coeffs_list =
      map (Abstract_Linear_Poly.coeff l) (Abstract_Linear_Poly.vars_list l);
    denominators = map (snd . Rat.quotient_of) (c : coeffs_list);
  } in List.fold GCD.lcm_int denominators Arith.one_int;

constraint_to_ints ::
  Farkas.Le_constraint Rat.Rat -> Farkas.Le_constraint Rat.Rat;
constraint_to_ints c = mul_constraint (Rat.of_int (common_denominator c)) c;

compute_bound_num_of_vars :: [Simplex.Constraint] -> Arith.Int;
compute_bound_num_of_vars cs =
  let {
    le_cs = normalize cs;
    le_csa = map constraint_to_ints le_cs;
    max_coeff = max_coeff_constraints le_csa;
    n = Arith.plus_nat Arith.one_nat (List.size_list (var_list cs));
  } in Arith.times_int (Arith.int_of_nat (Arith.plus_nat n Arith.one_nat))
         (Integral_Bounded_Vectors.det_bound_hadamard n
           (Rat.floor_rat max_coeff));

branch_and_bound ::
  [Simplex.Constraint] -> [Arith.Nat] -> Maybe (Arith.Nat -> Rat.Rat);
branch_and_bound cs is =
  let {
    bnd = compute_bound_num_of_vars cs;
  } in (case bnb_state_init cs is (\ _ -> Arith.uminus_int bnd) (\ _ -> bnd) of
         {
         (_, (_, (_, Sum_Type.Inl _))) -> Nothing;
         (csa, (lb_m, (ub_m, Sum_Type.Inr s))) ->
           Option.the (bnb_state_core_p csa is lb_m ub_m s);
       });

vars_of_constraints :: [Simplex.Constraint] -> [Arith.Nat];
vars_of_constraints cs =
  List.remdups
    (concatMap (Abstract_Linear_Poly.vars_list . Farkas.lec_poly)
      (normalize cs));

branch_and_bound_int :: [Simplex.Constraint] -> Maybe (Arith.Nat -> Arith.Int);
branch_and_bound_int cs =
  let {
    vs = vars_of_constraints cs;
  } in (case branch_and_bound cs vs of {
         Nothing -> Nothing;
         Just v ->
           Just (\ x ->
                  (if List.member vs x then Is_Rat_To_Rat.int_of_rat (v x)
                    else Arith.zero_int));
       });

}
