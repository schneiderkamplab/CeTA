:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Select the actual recursive clause, then try its head against the local call.
cons_choice(Input, N, M) :-
 clause(numberargs([Head|Tail], P, Out), Body),
 numberargs(Input,N,M) = numberargs([Head|Tail],P,Out),
 call(Body).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(compound_parameter_success,(cons_choice([a,b],outer(inner(z)),M),M==outer(inner(z)))),
 require(empty_input_fails_cons_choice,\+cons_choice([],outer(z),_)),
 require(failed_head_does_not_resume_caller,\+ ( (cons_choice([],outer(z),_),throw(unexpected_caller)) )),
 require(success_does_not_discharge_failing_continuation,\+ ( (cons_choice([a],outer(z),_),fail) )),
 require(partial_output_success,(cons_choice([a],outer(inner(z)),outer(X)),X==inner(z))),
 require(incompatible_output_fails,\+cons_choice([a],outer(z),other(z))),
 format('CONS_CONTRACT_SOURCE_CONTROLS_PASSED_FAMILY_OPEN~n').
