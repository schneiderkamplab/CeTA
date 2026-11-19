:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 Term=f(X,Y), CallerTail=[X,Y], CallerOutput=Y,
 clause(numvars(Term,0,HelperOut),(Univ,Next)),
 Univ=(Term=..[Name|Args]),
 require(extraction_outputs_fresh,(var(Name),var(Args),Name\==Args)),
 require(outputs_separate_from_caller,(Name\==X,Name\==Y,Args\==X,Args\==Y)),
 require(actual_source_extraction,call(Univ)),
 require(input_sharing_preserved,(var(X),var(Y),CallerTail==[X,Y],CallerOutput==Y)),
 require(argument_sharing_preserved,Args==[X,Y]),
 require(helper_output_stays_free,var(HelperOut)),
 require(actual_tail_call,Next==numberargs([X,Y],0,HelperOut)),
 require(arity_zero_preserved,(a=..[F0|A0],F0==a,A0==[])),
 require(nested_arity_three,(g(a,h(Z),Z)=..[_|A3],A3==[a,h(Z),Z],var(Z))),
 ForgedCaller=ForgedArgs,
 f(W)=..[_|ForgedArgs],
 require(negative_forged_freshness_binds_caller,(nonvar(ForgedCaller),ForgedCaller==[W])),
 require(saved_alternative_restores_caller,((Saved=temporary,f(Saved)=..[wrong|_]);var(Saved))),
 format('ACQUIRED_UNIV_CALLER_SOURCE_CONTROLS_PASSED_FULL_FAMILY_OPEN~n').
