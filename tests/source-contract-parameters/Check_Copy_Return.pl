% Operational controls for tracked compound copy returns and caller activation.
:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n', [Label]); throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(compound_parameter_reaches_caller,
   (numberargs([],f(a),N), N == f(a), N = f(A), A == a)),
 require(shared_caller_coordinates,
   (Pair = pair(X,X), numberargs([],f(a),X), Pair == pair(f(a),f(a)))),
 require(caller_list_spine_preserved,
   (List = [X,keep], numberargs([],f(a),X), List == [f(a),keep])),
 require(caller_failure_not_helper_success,
   \+ (numberargs([],f(a),N2), N2 = g(a))),
 require(helper_cut_preserves_caller_alternative,
   ((numberargs([],f(a),Y),fail);var(Y))),
 require(restored_caller_has_no_copy_binding, var(Y)),
 require(compound_copy_not_integer_only,
   (numberargs([],f(a),N3), \+ integer(N3))),
 format('COPY_RETURN_SOURCE_CONTROLS_PASSED_CALLER_CONTRACT_OPEN~n').
