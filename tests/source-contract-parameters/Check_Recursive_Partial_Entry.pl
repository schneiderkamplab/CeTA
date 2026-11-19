:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 P=outer(inner(z)), Out=outer(X),
 clause(numberargs([a,b],P,Out),(Prefix,Rest)),
 Prefix=numvars(a,P,H),
 require(compound_output_initially_nonground,(compound(Out),\+ground(Out))),
 require(helper_output_fresh,(var(H),H\==X)),
 require(negative_helper_alias,H\==X),
 require(proper_tail_routed,Rest==numberargs([b],H,Out)),
 require(prefix_copies_parameter,(call(Prefix),H==P)),
 require(prefix_keeps_caller_partial,var(X)),
 require(continuation_exposes_subterm,(call(Rest),X==inner(z))),
 require(repeated_output_mismatch,\+numberargs([a],pair(a,b),pair(Y,Y))),
 require(saved_output_restored,((numberargs([a],P,outer(S)),fail);var(S))),
 format('RECURSIVE_PARTIAL_ENTRY_CONTROLS_PASSED_FAMILY_OPEN~n').
