:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
% Executable analogue of the two normalized equalities, not a source simulation.
normalized(Term, Name, Args) :- Term=Term, Term=..[F|Ts], [Name|Args]=[F|Ts].
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 Term=f(X,Y), Tail=[X,Y], Caller=Y,
 clause(numvars(Term,0,Helper),(Univ,Next)), Univ=(Term=..[Name|Args]),
 require(acquired_normalized_path,normalized(Term,Name,Args)),
 require(caller_sharing_preserved,(var(X),var(Y),Tail==[X,Y],Caller==Y)),
 require(extraction_and_tail,(Name==f,Args==[X,Y],Next==numberargs([X,Y],0,Helper),var(Helper))),
 require(zero_arity,normalized(a,a,[])),
 require(nested_sharing,(normalized(g(Z,h(Z),a),g,As),As==[Z,h(Z),a],var(Z))),
 require(negative_forged_freshness,(normalized(f(W),_,ForgedCaller),ForgedCaller==[W],nonvar(ForgedCaller))),
 require(negative_omitted_pair,(T=f(_),T=T,var(_MissingName),var(_MissingArgs))),
 require(saved_alternative,((normalized(f(Saved),wrong,_),fail);var(Saved))),
 format('ACQUIRED_UNIV_NORMALIZED_CONTROLS_PASSED_FULL_BLOCK_OPEN~n').
