:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n', [Label]); throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(equal_scalar, numberargs([],1,1)),
 require(unequal_scalar_rejected, \+ numberargs([],1,2)),
 require(equal_compound_parameter, numberargs([],f(a),f(a))),
 require(unequal_compound_rejected, \+ numberargs([],f(a),f(b))),
 require(shared_bound_output_rejected, \+ numberargs([],1,var/0)),
 require(free_output_still_supported, (numberargs([],f(a),M), M == f(a))),
 require(bound_output_recursive_success, (numberargs([X],0,1), X == var/0)),
 require(bound_output_recursive_failure, \+ numberargs([_],0,2)),
 require(shared_root_still_fails, \+ numvars(f(Y),0,Y)),
 require(arbitrary_nonground_output_outside_mode, (numberargs([],f(a),f(Z)), Z == a)),
 format('GROUND_CALLER_SOURCE_CONTROLS_PASSED_M1_OPEN~n').
