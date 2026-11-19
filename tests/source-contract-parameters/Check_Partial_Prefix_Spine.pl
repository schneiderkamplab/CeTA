:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n',[Label]);throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 Tail=[X,b],length(Tail,Before),numvars(X,0,N),
 require(shared_element_instantiated,(X=var/0,N=1)),
 require(exact_tail_length,(length(Tail,After),Before=After,After=2)),
 require(open_spine_excluded,(Open=[a|_],\+is_list(Open))),
 require(cyclic_spine_excluded,(Cycle=[a|Cycle],\+is_list(Cycle))),
 require(saved_tail_restored,(Saved=[Y,b],((numvars(Y,0,_),fail);(var(Y),length(Saved,2))))),
 format('PARTIAL_PREFIX_SPINE_CONTROLS_PASSED_HELPER_CONTRACT_OPEN~n').
