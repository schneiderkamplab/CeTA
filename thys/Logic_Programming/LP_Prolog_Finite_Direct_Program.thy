theory LP_Prolog_Finite_Direct_Program
 imports LP_Prolog_Finite_Direct_Control
begin

lemma lpp_static_template_atom_code[code]:
 "lpp_static_template A (LPCAtom t) =
   (case t of Fun (LPCUser f) ts \<Rightarrow> (f,length ts)\<in>A | _ \<Rightarrow> False)"
 by (cases t) (auto split: lp_cut_symbol.splits)

fun lpp_check_direct_head where
 "lpp_check_direct_head (Var x)=False"
| "lpp_check_direct_head (Fun f ts)=(list_all is_Var ts \<and> distinct ts)"

lemma lpp_check_direct_head_sound:
 assumes checked: "lpp_check_direct_head h"
 shows "\<exists>f H. h=Fun f (map Var H) \<and> distinct H"
 using checked
proof (cases h)
 case (Var x) then show ?thesis using checked by simp
next
 case (Fun f ts)
 have vars: "list_all is_Var ts" and distinct: "distinct ts"
   using checked by (simp_all add: Fun)
 have mapped: "map Var (map the_Var ts)=ts"
   using vars by (induct ts) (auto split: term.splits)
 have "distinct (map the_Var ts)" using distinct mapped distinct_map by metis
 then show ?thesis using Fun mapped by (intro exI[of _ f] exI[of _ "map the_Var ts"]) auto
qed

definition lpp_check_finite_direct_program where
 "lpp_check_finite_direct_program P signatures =
   (list_all (\<lambda>(h,bs). lpp_check_direct_head h \<and> list_all lpp_direct_source_goal bs) P \<and>
    lpp_static_program (set signatures) P \<and>
    list_all (\<lambda>(f,n). (f,n)\<in>lpp_builtin_signature \<longrightarrow> lpp_direct_arithmetic_name f) signatures)"

lemma lpp_check_finite_direct_program_sound:
 assumes "lpp_check_finite_direct_program P signatures"
 shows "lpp_finite_direct_program P" "lpp_static_program (set signatures) P"
   "\<And>f n. (f,n)\<in>set signatures \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
proof -
 have clause: "\<exists>f H. h=Fun f (map Var H) \<and> distinct H \<and> list_all lpp_direct_source_goal bs"
   if member: "(h,bs)\<in>set P" for h bs
 proof -
  have checked: "lpp_check_direct_head h" and body: "list_all lpp_direct_source_goal bs"
    using assms member by (auto simp: lpp_check_finite_direct_program_def list_all_iff)
  obtain f H where head: "h=Fun f (map Var H)" "distinct H"
    using lpp_check_direct_head_sound[OF checked] by blast
  show ?thesis by (intro exI[of _ f] exI[of _ H]) (use head body in auto)
 qed
 show "lpp_finite_direct_program P"
   unfolding lpp_finite_direct_program_def list_all_iff
   by (intro ballI) (use clause[unfolded list_all_iff] in \<open>auto split: prod.splits\<close>)
 show "lpp_static_program (set signatures) P"
   using assms by (simp add: lpp_check_finite_direct_program_def)
 show "lpp_direct_arithmetic_name f" if "(f,n)\<in>set signatures" "(f,n)\<in>lpp_builtin_signature" for f n
   using assms that by (auto simp: lpp_check_finite_direct_program_def list_all_iff)
qed

lemma lpp_finite_direct_closed_control_SN:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_finite_direct_control_contexts fuel P Q nds states contexts contexts Fs T returned arity actions"
   and ranked: "lpc_seg_ranked_control rank_of Q"
   and transfer: "lpp_check_transfer_program T SP receipts"
   and source: "lp_cut_source_program P"
   and program: "lpp_check_finite_direct_program P signatures"
   and initial: "lpp_finite_direct_invariant (set signatures) ss"
   and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
   and closed: "list_all (\<lambda>x. x\<noteq>None) actions"
 shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {map fst ss}"
proof -
 have stable: "lpp_finite_direct_invariant (set signatures) ys"
   if "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys"
     "lpp_finite_direct_invariant (set signatures) xs" for xs and ev :: "(nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and ys
   by (rule lpp_finite_direct_arithmetic_stable[OF lpp_check_finite_direct_program_sound[OF program] that])
 have contract: "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ss (UNIV::unit rel) () (\<lambda>_. ())"
   apply (rule lpp_finite_direct_control_contract_contexts[where A="set signatures"])
   apply (fact compatible)
   apply (fact checked)
   apply assumption
   apply (fact ranked)
   apply (fact transfer)
   apply (fact source)
   apply (fact initial)
   apply (fact stable)
   apply (fact represented)
   using closed checked
   apply (auto simp: lpp_check_finite_direct_control_contexts_def list_all_iff; metis nth_mem option.distinct(1))
   by (rule rtrancl_refl)

 show ?thesis by (rule lpp_domain_instrumentation_SN)
   (use contract in \<open>simp add: lp_answer_contract_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_check_finite_direct_program_sound(1)}, @{thm lpp_finite_direct_closed_control_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct program" else ();
\<close>
end
