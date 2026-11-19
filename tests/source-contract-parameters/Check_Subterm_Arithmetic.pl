:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(scalar_success,(numvars(T,4,N),T=var/4,N=5)),
 require(shared_caller_scalar,(Caller=box(R),numvars(_,4,R),Caller=box(5))),
 require(compound_output_rejected,\+numvars(_,4,box(_))),
 require(saved_output_restored,((numvars(_,4,Saved),fail);var(Saved))),
 require(noninteger_parameter_not_assumed_success,
   catch((numvars(_,outer(inner(z)),_),fail),error(type_error(evaluable,_),_),true)),
 format('SUBTERM_ARITHMETIC_CONTROLS_PASSED_FAMILY_OPEN~n').
