theory LP_TOCL09_Regression
  imports LP_TOCL09_Checker
begin

text \<open>A semantic regression, not a production processor: cyclic unification
  must not be excluded by the source relation. Here X = s(X) has a rational-tree
  solution, and the recursive clause returns to the same query in two steps.\<close>

primcorec lp_test_cycle :: "(nat,nat) lp_iterm" where
  "lp_test_cycle = LPIFun 2 [lp_test_cycle]"

definition lp_test_program :: "(nat,nat) lp_clause list" where
  "lp_test_program = [((0,[Var 0]),[(1,[Var 0,Fun 2 [Var 0]]),(0,[Var 0])]),
                      ((1,[Var 0,Var 0]),[])]"

lemma lp_test_cycle_resolution:
  "([(0,[lp_test_cycle])],[(0,[lp_test_cycle])]) \<in> (lp_ild lp_test_program)\<^sup>+"
proof -
  have unfold_cycle: "lp_test_cycle = LPIFun 2 [lp_test_cycle]"
    by (rule lp_test_cycle.code)
  have first: "([(0,[lp_test_cycle])],[(1,[lp_test_cycle,lp_test_cycle]),(0,[lp_test_cycle])])
    \<in> lp_ild lp_test_program"
    using lp_ild.resolve[where P=lp_test_program and c=0 and a="(0,[lp_test_cycle])"
      and gs="[]" and \<sigma>=LPIVar and \<rho>="\<lambda>_. lp_test_cycle"]
    by (simp add: lp_test_program_def lp_atom_eval_def flip: unfold_cycle)
  have second: "([(1,[lp_test_cycle,lp_test_cycle]),(0,[lp_test_cycle])],[(0,[lp_test_cycle])])
    \<in> lp_ild lp_test_program"
    using lp_ild.resolve[where P=lp_test_program and c=1 and a="(1,[lp_test_cycle,lp_test_cycle])"
      and gs="[(0,[lp_test_cycle])]" and \<sigma>=LPIVar and \<rho>="\<lambda>_. lp_test_cycle"]
    by (simp add: lp_test_program_def lp_atom_eval_def)
  show ?thesis using first second by (meson trancl.r_into_trancl trancl_trans)
qed

lemma lp_test_finite_query_reaches_cycle:
  "([(0,[LPIVar (0::nat)])],[(0,[lp_test_cycle])]) \<in> (lp_ild lp_test_program)\<^sup>+"
proof -
  have first: "([(0,[LPIVar (0::nat)])],[(1,[LPIVar (0::nat),LPIFun 2 [LPIVar (0::nat)]]),(0,[LPIVar (0::nat)])])
    \<in> lp_ild lp_test_program"
    using lp_ild.resolve[where P=lp_test_program and c=0 and a="(0,[LPIVar (0::nat)])"
      and gs="[]" and \<sigma>=LPIVar and \<rho>=LPIVar]
    by (simp add: lp_test_program_def lp_atom_eval_def)
  have second: "([(1,[LPIVar (0::nat),LPIFun 2 [LPIVar (0::nat)]]),(0,[LPIVar (0::nat)])],[(0,[lp_test_cycle])])
    \<in> lp_ild lp_test_program"
    using lp_ild.resolve[where P=lp_test_program and c=1 and a="(1,[LPIVar (0::nat),LPIFun 2 [LPIVar (0::nat)]])"
      and gs="[(0,[LPIVar (0::nat)])]" and \<sigma>="\<lambda>_. lp_test_cycle" and \<rho>="\<lambda>_. lp_test_cycle"]
    by (simp add: lp_test_program_def lp_atom_eval_def lp_iatom_subst_def flip: lp_test_cycle.code)
  show ?thesis using first second by (meson trancl.r_into_trancl trancl_trans)
qed

lemma lp_test_occurs_check_counterexample:
  "\<not> SN_on (lp_ild lp_test_program) {[(0,[LPIVar (0::nat)])]}"
proof
  assume sn: "SN_on (lp_ild lp_test_program) {[(0,[LPIVar (0::nat)])]}"
  have member: "[(0,[lp_test_cycle])] \<in> (lp_ild lp_test_program)\<^sup>* `` {[(0,[LPIVar (0::nat)])]}"
    using lp_test_finite_query_reaches_cycle by auto
  have "([(0,[lp_test_cycle])],[(0,[lp_test_cycle])]) \<notin> (lp_ild lp_test_program)\<^sup>+"
    using SN_on_irrefl[OF SN_on_trancl[OF SN_on_Image_rtrancl[OF sn]]] member by blast
  with lp_test_cycle_resolution show False by contradiction
qed

end
