% Source controls for the copy-successor payload proof.
:- initialization(main, main).
require(Label, Goal) :- (call(Goal) -> format('~w PASS~n', [Label]); throw(failed(Label))).
main :-
 consult('../TPDB-ARI/Prolog/prolog_mixed/numbervars.pl'),
 require(atomic_functor_compound_parameter,
   (T=atom, T=..[Name|Args], numberargs(Args,f(a),M),
    Name == atom, Args == [], T == atom, M == f(a))),
 require(original_atomic_return, (numvars(atom,f(a),M2), M2 == f(a))),
 require(nonempty_arguments_reject_copy_head,
   (T2=f(a), T2=..[_|As], \+ As=[])),
 require(mismatching_output_rejects_return, \+ numvars(atom,f(a),g(a))),
 require(simple_list_payload, (numberargs([],f(a),M3), M3 == f(a))),
 format('COPY_SUCCESSOR_CONTROLS_PASSED_FULL_CONTRACTS_OPEN~n').
