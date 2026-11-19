:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 clause(numberargs([X],0,1),(Prefix,Rest)),
 Prefix=numvars(X,0,H),
 require(ground_caller_helper_is_free,var(H)),
 require(helper_separate_from_input,H \== X),
 require(ground_caller_tail_routing,Rest == numberargs([],H,1)),
 require(ground_caller_prefix_succeeds,call(Prefix)),
 require(ground_caller_parameter_result,H == 1),
 require(ground_caller_continuation_succeeds,call(Rest)),
 clause(numberargs([Y],0,Y),(SharedPrefix,SharedRest)),
 SharedPrefix=numvars(Y,0,H2),
 require(shared_caller_helper_is_free,var(H2)),
 require(shared_caller_distinct_helper,H2 \== Y),
 require(shared_caller_prefix_succeeds,call(SharedPrefix)),
 require(shared_caller_becomes_ground,(ground(Y),Y == var/0)),
 require(shared_caller_mismatch_rejected,\+ call(SharedRest)),
 require(nonnumeric_ground_parameter_supported,numberargs([a],f(seed),f(seed))),
 require(nonground_root_output_not_assumed_away,
  (numberargs([a],f(seed),f(Z)),Z == seed)),
 format('RECURSIVE_CALLER_SOURCE_CONTROLS_PASSED_FULL_FAMILY_OPEN~n').
