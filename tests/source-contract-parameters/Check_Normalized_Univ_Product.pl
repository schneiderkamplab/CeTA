:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Executable sharing controls, not a formal residual simulation.
main :-
 Input=f(X), CallerTail=[X], CallerOut=X,
 require(reflexive_keeps_caller,(Input=Input,var(X),CallerTail==[X])),
 require(pair_keeps_shared_input,([Name|Args]=[f,X],Name==f,Args==[X],var(X),CallerOut==X)),
 require(same_execution,(Args=[a],Input==f(a),CallerTail==[a],CallerOut==a)),
 require(negative_independent_copy,(copy_term(f(Z)-[Z],F-T),F=f(b),T==[b],var(Z))),
 require(negative_forged_caller_protection,([_|ForgedCaller]=[f,w],ForgedCaller==[w])),
 require(saved_rollback,((Saved=temporary,[wrong|_]=[f,a]);var(Saved))),
 format('NORMALIZED_UNIV_PRODUCT_CONTROLS_PASSED_ASSEMBLY_OPEN~n').
