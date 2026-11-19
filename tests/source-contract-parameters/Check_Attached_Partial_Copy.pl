:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 P=outer(inner(z)), Caller=pair(X,Y),
 require(partial_output_copy,numberargs([],P,outer(X))),
 require(shared_caller_subterm,Caller=pair(inner(z),Y)),
 require(outside_output_remains_variable,var(Y)),
 require(repeated_output_compatible,numberargs([],pair(inner(z),inner(z)),pair(A,A))),
 require(repeated_output_incompatible,\+numberargs([],pair(a,b),pair(B,B))),
 require(saved_alternative_restored,((numberargs([],P,outer(Saved)),fail);var(Saved))),
 require(ground_parameter_not_integer,(ground(P),\+integer(P))),
 format('ATTACHED_PARTIAL_COPY_CONTROLS_PASSED_FAMILY_OPEN~n').
