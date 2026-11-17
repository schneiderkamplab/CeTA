theory LP_Prolog_Head_Constraints
 imports LP_Prolog_Finite_Is LP_Cut_Factored_Head_Resolution
begin

text \<open>Finite lists of nullary-constructor constraints use the existing
scalar unifier, which observes only the root of a possibly rational term.
The constructor names need not denote numbers. No occurs-check approximation
or finite-tree assumption is introduced.\<close>

definition lpp_head_constraints where
 "lpp_head_constraints cs sigma = list_all (\<lambda>(t,f).
    lp_isubst t sigma=LPIFun (LPCUser f) []) cs"

fun lpp_solve_head_constraints where
 "lpp_solve_head_constraints [] = Some LPIVar"
| "lpp_solve_head_constraints ((t,f)#cs) =
    (case lpp_scalar_unifier t f of None \<Rightarrow> None | Some mu \<Rightarrow>
     map_option (\<lambda>nu x. lp_isubst (mu x) nu)
       (lpp_solve_head_constraints (map (\<lambda>(u,g). (lp_isubst u mu,g)) cs)))"

lemma lpp_head_constraints_comp:
 "lpp_head_constraints (map (\<lambda>(u,g). (lp_isubst u mu,g)) cs) nu =
  lpp_head_constraints cs (\<lambda>x. lp_isubst (mu x) nu)"
 by (simp add: lpp_head_constraints_def list_all_iff lpc_isubst_comp split: prod.splits)

lemma lpp_solve_head_constraints_sound:
 "lpp_solve_head_constraints cs=Some mu \<Longrightarrow> lpp_head_constraints cs mu"
proof (induct cs arbitrary: mu rule: lpp_solve_head_constraints.induct)
 case 1 then show ?case by (simp add: lpp_head_constraints_def)
next
 case (2 t f cs)
 obtain first rest where first: "lpp_scalar_unifier t f=Some first"
   and rest: "lpp_solve_head_constraints (map (\<lambda>(u,g). (lp_isubst u first,g)) cs)=Some rest"
   and mu: "mu=(\<lambda>x. lp_isubst (first x) rest)"
   using "2.prems" by (auto split: option.splits)
 have head: "lp_isubst t first=LPIFun (LPCUser f) []"
   by (rule lpp_scalar_unifier_sound[OF first])
 have tail: "lpp_head_constraints cs mu"
   using "2.hyps"[OF first rest] by (simp add: lpp_head_constraints_comp mu)
 show ?case using head tail by (simp add: lpp_head_constraints_def mu lpc_isubst_comp[symmetric])
qed

lemma lpp_solve_head_constraints_preserves:
 fixes tau :: "'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm"
 assumes chosen: "lpp_solve_head_constraints cs=Some mu" and solution: "lpp_head_constraints cs tau"
 shows "lp_isubst (mu x) tau=tau x"
 using chosen solution
proof (induct cs arbitrary: mu x rule: lpp_solve_head_constraints.induct)
 case 1 then show ?case by simp
next
 case (2 t f cs)
 obtain first rest where first: "lpp_scalar_unifier t f=Some first"
   and rest: "lpp_solve_head_constraints (map (\<lambda>(u,g). (lp_isubst u first,g)) cs)=Some rest"
   and mu: "mu=(\<lambda>x. lp_isubst (first x) rest)"
   using "2.prems" by (auto split: option.splits)
 have head: "lp_isubst t tau=LPIFun (LPCUser f) []" and tail: "lpp_head_constraints cs tau"
   using "2.prems" by (auto simp: lpp_head_constraints_def)
 have first_factor: "lp_isubst (first x) tau=tau x" for x
   by (rule lpp_scalar_unifier_most_general[OF first head])
 have transformed: "lpp_head_constraints (map (\<lambda>(u,g). (lp_isubst u first,g)) cs) tau"
   using tail by (simp add: lpp_head_constraints_comp first_factor)
 have rest_factor: "lp_isubst (rest x) tau=tau x" for x
   by (rule "2.hyps"[OF first rest transformed])
 show ?case by (simp add: mu lpc_isubst_comp rest_factor first_factor)
qed

lemma lpp_solve_head_constraints_failure:
 fixes tau :: "'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm"
 shows "lpp_solve_head_constraints cs=None \<Longrightarrow> \<not> lpp_head_constraints cs tau"
proof (induct cs rule: lpp_solve_head_constraints.induct)
 case 1 then show ?case by simp
next
 case (2 t f cs)
 show ?case
 proof
  assume solution: "lpp_head_constraints ((t,f)#cs) tau"
  have head: "lp_isubst t tau=LPIFun (LPCUser f) []" and tail: "lpp_head_constraints cs tau"
    using solution by (auto simp: lpp_head_constraints_def)
  obtain first where first: "lpp_scalar_unifier t f=Some first"
    using head lpp_scalar_unifier_complete[of t f] by (cases "lpp_scalar_unifier t f") auto
  have factor: "lp_isubst (first x) tau=tau x" for x
    by (rule lpp_scalar_unifier_most_general[OF first head])
  have transformed: "lpp_head_constraints (map (\<lambda>(u,g). (lp_isubst u first,g)) cs) tau"
    using tail by (simp add: lpp_head_constraints_comp factor)
  have failed: "lpp_solve_head_constraints (map (\<lambda>(u,g). (lp_isubst u first,g)) cs)=None"
    using "2.prems" first by (auto split: option.splits)
  show False using "2.hyps"[OF first failed] transformed by contradiction
 qed
qed

ML \<open>
val checked = [@{thm lpp_solve_head_constraints_sound},
 @{thm lpp_solve_head_constraints_preserves}, @{thm lpp_solve_head_constraints_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite head constraints" else ();
\<close>
end
