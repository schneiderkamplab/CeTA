% Execute the original clauses; do not replace their semantics with a model.
:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n', [Label]); throw(failed(Label))).
main :-
    consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
    clause(numberargs([X],0,X), (Prefix,Continuation)),
    require(shared_prefix_succeeds, call(Prefix)),
    require(shared_output_bound, X == var/0),
    require(actual_continuation, Continuation == numberargs([],1,var/0)),
    require(shared_output_not_free, nonvar(X)),
    require(shared_continuation_fails, \+ call(Continuation)),
    require(original_shared_query_fails, \+ numvars(f(Y),0,Y)),
    clause(numberargs([A],0,M), (GoodPrefix,GoodContinuation)),
    require(separate_prefix_succeeds, call(GoodPrefix)),
    require(separate_output_stays_free, var(M)),
    require(separate_continuation_succeeds, call(GoodContinuation)),
    require(separate_result, (A == var/0, M == 1)),
    require(original_separate_query_succeeds, (numvars(f(B),0,N), B == var/0, N == 1)),
    format('SHARED_CALLER_OBSTRUCTION_REPRODUCED_M1_OPEN~n').
