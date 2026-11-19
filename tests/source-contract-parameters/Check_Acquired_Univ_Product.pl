:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Source sharing controls; not a proof of module representation or termination.
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 Input=f(X,g(X)), CallerTail=[X], CallerOutput=X, Parameter=counter(a),
 Univ=(Input=..[Name|Args]),
 clause(numvars(Input,Parameter,Out),(Univ,Next)),
 require(acquired_outputs_fresh,(var(Name),var(Args),Name\==Args,Name\==X,Args\==X)),
 require(ground_parameter_not_integer,(ground(Parameter),\+integer(Parameter))),
 require(acquired_normalization,(Input=Input,call(Univ))),
 require(caller_preserved,(var(X),CallerTail==[X],CallerOutput==X,var(Out))),
 require(exact_helper_tail,Next==numberargs([X,g(X)],Parameter,Out)),
 require(same_joint_execution,(Args=[a,g(a)],Input==f(a,g(a)),CallerTail==[a],CallerOutput==a)),
 Cycle=[a|Cycle],
 require(negative_saved_finiteness,\+acyclic_term(saved(Cycle))),
 require(saved_environment_restored,((Saved=temporary,f(Saved)=..[wrong|_]);var(Saved))),
 format('ACQUIRED_UNIV_PRODUCT_CONTROLS_PASSED_HELPER_REPRESENTATION_OPEN~n').
