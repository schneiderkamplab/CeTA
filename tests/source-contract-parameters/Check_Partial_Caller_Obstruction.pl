:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
scalar(T) :- atomic(T).
old_replacement(P,T) :- T==P; T=var/Q,(Q==P;scalar(Q));scalar(T).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 P=outer(inner(z)), Output=outer(X),
 require(permitted_finite_ground_parameter,(ground(P),acyclic_term(P))),
 require(permitted_nonground_output,(compound(Output),\+ground(Output),acyclic_term(Output))),
 require(original_source_succeeds,numvars(a,P,Output)),
 require(exposed_strict_compound_subterm,X==inner(z)),
 require(old_replacement_set_rejects_image,\+old_replacement(P,X)),
 require(parameter_return_still_copies,Output==P),
 require(free_output_positive,(numvars(a,P,Free),Free==P)),
 require(ground_output_positive,numvars(a,P,P)),
 format('PARTIAL_CALLER_OBSTRUCTION_CONFIRMED_INVARIANT_REPAIR_REQUIRED~n').
