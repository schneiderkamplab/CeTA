theory LP_Prolog_Constructor_Arguments
 imports LP_Prolog_List_Observation LP_Prolog_Finite_Term_Basis
begin

text \<open>Relational observations of actual constructor arguments. The label is
retained, and the list contains the actual children, including rational ones.
This is an observation relation, not a new operational semantics or an encoding
whose finite graph size can be used as a termination measure. Source univ steps
and the translation of their name argument still require separate checking.\<close>

fun lpp_argument_list :: "(string lp_cut_symbol,'v) lp_iterm list \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm" where
 "lpp_argument_list [] = LPIFun (LPCUser ''0:prolog_data_5b5d'') []"
| "lpp_argument_list (t#ts) = LPIFun (LPCUser ''2:prolog_data_2e'') [t,lpp_argument_list ts]"

lemma lpp_argument_list_subst:
 "lp_isubst (lpp_argument_list ts) sigma = lpp_argument_list (map (\<lambda>t. lp_isubst t sigma) ts)"
 by (induction ts) auto

lemma lpp_argument_list_injective:
 "lpp_argument_list xs = lpp_argument_list ys \<longleftrightarrow> xs=ys"
 by (induction xs arbitrary: ys) (case_tac ys; auto)+

lemma lpp_argument_list_length:
 "lpp_list_length (lpp_argument_list ts) (length ts)"
 by (induction ts) (auto intro: lpp_list_length.intros)

lemma lpp_argument_list_finite:
 "lpp_finite_term (lpp_argument_list ts) = list_all lpp_finite_term ts"
 by (induction ts) auto

definition lpp_constructor_arguments where
 "lpp_constructor_arguments t f arglist = (\<exists>ts. t=LPIFun f ts \<and> arglist=lpp_argument_list ts)"

lemma lpp_constructor_arguments_intro:
 "lpp_constructor_arguments (LPIFun f ts) f (lpp_argument_list ts)"
 by (auto simp: lpp_constructor_arguments_def)

lemma lpp_constructor_arguments_subst:
 "lpp_constructor_arguments t f arglist \<Longrightarrow>
  lpp_constructor_arguments (lp_isubst t sigma) f (lp_isubst arglist sigma)"
 by (auto simp: lpp_constructor_arguments_def lpp_argument_list_subst)

lemma lpp_constructor_arguments_exact:
 "lpp_constructor_arguments (LPIFun f ts) g arglist \<longleftrightarrow>
   f=g \<and> arglist=lpp_argument_list ts"
 by (auto simp: lpp_constructor_arguments_def)

lemma lpp_constructor_arguments_spine:
 "lpp_constructor_arguments t f arglist \<Longrightarrow> \<exists>n. lpp_list_length arglist n"
 by (auto simp: lpp_constructor_arguments_def intro: lpp_argument_list_length)

lemma lpp_constructor_arguments_finiteness:
 "lpp_constructor_arguments t f arglist \<Longrightarrow> lpp_finite_term arglist = lpp_finite_term t"
 by (auto simp: lpp_constructor_arguments_def lpp_argument_list_finite)

text \<open>An infinite child remains infinite despite the finite argument spine.
The constructor observation therefore cannot manufacture a finite tree fact.\<close>
lemma lpp_argument_list_infinite_child:
 "\<not> lpp_finite_term t \<Longrightarrow> \<not> lpp_finite_term (lpp_argument_list [t])"
 by (simp add: lpp_argument_list_finite)

lemma lpp_constructor_arguments_arity:
 assumes view: "lpp_constructor_arguments (LPIFun f ts) g arglist"
 and spine: "lpp_list_length arglist n"
 shows "n=length ts"
 using view spine lpp_argument_list_length[of ts]
 by (auto simp: lpp_constructor_arguments_exact intro: lpp_list_length_unique)

lemma lpp_constructor_arguments_variable_rejected:
 "\<not> lpp_constructor_arguments (LPIVar x) f arglist"
 by (simp add: lpp_constructor_arguments_def)

lemma lpp_finite_constructor_not_self_child:
 "lpp_finite_term t \<Longrightarrow> t \<noteq> LPIFun f [t]"
proof (induction rule: lpp_finite_term.induct)
 case (variable x) then show ?case by simp
next
 case (node ts g)
 show ?case
 proof
  assume eq: "LPIFun g ts = LPIFun f [LPIFun g ts]"
  have ts_eq: "ts = [LPIFun g ts]" by (rule conjunct2[OF iffD1[OF lp_iterm.inject(2) eq]])
  have member: "LPIFun g ts \<in> set ts" by (subst (2) ts_eq) simp
  have neq: "LPIFun g ts \<noteq> LPIFun f [LPIFun g ts]"
   using node.IH member by (auto simp: list_all_iff)
  show False using eq neq by contradiction
 qed
qed

lemma lpp_cyclic_child_finite_spine_only:
 assumes "t=LPIFun f [t]"
 shows "lpp_constructor_arguments t f (lpp_argument_list [t]) \<and>
   lpp_list_length (lpp_argument_list [t]) 1 \<and>
   \<not> lpp_finite_term (lpp_argument_list [t])"
 using assms lpp_finite_constructor_not_self_child[of t f]
 by (auto simp: lpp_constructor_arguments_def lpp_argument_list_finite
   intro: lpp_list_length.intros)

ML \<open>
val checked = [@{thm lpp_constructor_arguments_subst},
 @{thm lpp_constructor_arguments_exact}, @{thm lpp_constructor_arguments_finiteness},
 @{thm lpp_constructor_arguments_arity}, @{thm lpp_cyclic_child_finite_spine_only}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted constructor argument observation" else ();
\<close>
end
