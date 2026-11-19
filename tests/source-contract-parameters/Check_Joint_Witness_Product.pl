:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Executable controls for the actual builtin cases; not a source certificate.
main :-
 require(constructor_sharing,(T=f(X,X),T=..[f|Args],Args=[a,a],X==a)),
 require(variable_fresh_name_stops,catch((_V=..[_Name|_Args],fail),error(instantiation_error,_),true)),
 require(known_name_constructs_counterexample,(V=..[f,a],V==f(a))),
 require(wrong_name_fails,\+(f(a)=..[g|_])),
 require(saved_alternative_restores_sharing,((Saved=temporary,f(Saved)=..[g|_]);var(Saved))),
 format('JOINT_WITNESS_PRODUCT_CONTROLS_PASSED_ASSEMBLY_OPEN~n').
