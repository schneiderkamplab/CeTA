:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 require(partial_output_subterm,(Caller=box(X),outer(X)=outer(inner(z)),Caller=box(inner(z)))),
 require(shared_repeated_output,(pair(Y,Y)=pair(inner(z),inner(z)),Y=inner(z))),
 require(incompatible_repeated_output,\+(pair(Z,Z)=pair(a,b))),
 require(compound_scalar_mismatch,\+(box(_)=5)),
 require(saved_alias_restored,((outer(S)=outer(inner(z)),fail);var(S))),
 format('SUBTERM_GROUND_EQUALITY_CONTROLS_PASSED_ASSEMBLY_OPEN~n').
