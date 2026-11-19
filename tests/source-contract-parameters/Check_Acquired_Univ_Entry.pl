:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Finite-term/continuation controls; not a source-to-residual simulation.
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 Term=f(X,g(X)),
 Univ=(Term=..[Name|Args]),
 clause(numvars(Term,0,M),(Univ,Next)),
 require(actual_body_shape,Univ=(Term=..[Name|Args])),
 require(finite_matched_body,acyclic_term((Univ,Next))),
 require(extraction,call(Univ)),
 require(finite_exact_tail,(Next==numberargs([X,g(X)],0,M),acyclic_term(Next),Name==f,Args==[X,g(X)])),
 require(sharing_preserved,var(X)),
 Cycle=[a|Cycle],
 require(negative_cyclic_saved,\+acyclic_term([saved(Cycle)])),
 require(negative_unrelated_pending,\+acyclic_term((Next,pending(Cycle)))),
 require(negative_wrong_tail,Next\==numberargs([],0,M)),
 format('ACQUIRED_UNIV_ENTRY_CONTROLS_PASSED_BLOCK_EXIT_OPEN~n').
