:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n', [Label]); throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(free_output_copy, (numberargs([],f(a),M), M == f(a))),
 require(ground_output_copy, numberargs([],f(a),f(a))),
 require(ground_mismatch_fails, \+ numberargs([],1,var/0)),
 require(saved_alternative_restored,
   ((X=temporary,numberargs([],1,var/0));(var(X),X=restored))),
 require(saved_value_is_original_branch_value, X == restored),
 require(reject_active_binding_leak, X \== temporary),
 require(shared_helper_failure_restores_saved_output,
   ((numvars(f(Y),0,Y),fail);var(Y))),
 require(saved_success_after_shared_failure,
   ((numvars(f(Z),0,Z),fail);(numvars(f(Z),0,N),Z == var/0,N == 1))),
 require(cut_removes_later_clause_choice,
   (findall(O,numberargs([],1,O),Outputs),Outputs == [1])),
 require(nonground_output_outside_local_mode,
   (numberargs([],f(a),f(A)), A == a)),
 format('CALLER_COPY_NODE_SOURCE_CONTROLS_PASSED_FULL_FAMILY_OPEN~n').
