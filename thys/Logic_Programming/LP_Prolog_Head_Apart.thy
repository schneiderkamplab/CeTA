theory LP_Prolog_Head_Apart
 imports LP_Prolog_Scalar_Recurrence_Interface
begin

fun lpp_same_head_variable where
 "lpp_same_head_variable (Var x) (Var y) = (x=y)"
| "lpp_same_head_variable _ _ = False"

lemma lpp_same_head_variable_iff:
 "lpp_same_head_variable a b \<longleftrightarrow> (\<exists>x. a=Var x \<and> b=Var x)"
 by (cases a; cases b) auto

definition lpp_head_apart_args where
 "lpp_head_apart_args hs observations i j =
   (length hs=length observations \<and> i<length hs \<and> j<length hs \<and>
    lpp_same_head_variable (hs!i) (hs!j) \<and>
    (case (observations!i,observations!j) of (Some v,Some w) \<Rightarrow>
       lpp_machine_valid v \<and> lpp_machine_valid w \<and> v\<noteq>w | _ \<Rightarrow> False))"

definition lpp_head_apart_check where
 "lpp_head_apart_check P q observations d i j =
   (d<length P \<and> (case fst (P!d) of Fun (LPCUser f) hs \<Rightarrow>
     f=q \<and> lpp_head_apart_args hs observations i j | _ \<Rightarrow> False))"

lemma lpp_head_apart_no_unifier:
 fixes sigma rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_head_apart_args hs observations i j"
   and observed: "lpp_scalar_observations operation observations actuals"
 shows "lp_isubst (LPIFun (LPCUser q) actuals) sigma \<noteq>
    lp_ieval (Fun (LPCUser q) hs) rho"
proof -
 obtain x v w where heads: "hs!i=Var x" "hs!j=Var x"
   and obs_values: "observations!i=Some v" "observations!j=Some w"
   and valid: "lpp_machine_valid v" "lpp_machine_valid w" and different: "v\<noteq>w"
   using checked by (auto simp: lpp_head_apart_args_def lpp_same_head_variable_iff
     split: term.splits option.splits prod.splits)
 have lengths: "length hs=length observations" "length actuals=length observations"
   and bounds: "i<length hs" "j<length hs"
   using checked observed by (auto simp: lpp_head_apart_args_def lpp_scalar_observations_def)
 have all: "\<forall>k\<in>set [0..<length observations]. case observations!k of None \<Rightarrow> True | Some z \<Rightarrow>
   lpp_stable_scalar_evaluation operation (actuals!k) (lpp_machine_value z)"
   using observed by (simp add: lpp_scalar_observations_def list_all_iff)
 have im: "i\<in>set [0..<length observations]" and jm: "j\<in>set [0..<length observations]"
   using bounds lengths by simp_all
 have left: "lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value v)"
   using bspec[OF all im] obs_values by simp
 have right: "lpp_stable_scalar_evaluation operation (actuals!j) (lpp_machine_value w)"
   using bspec[OF all jm] obs_values by simp
 have left_subst: "lpp_stable_scalar_evaluation operation (lp_isubst (actuals!i) sigma) (lpp_machine_value v)"
   using lpp_stable_scalar_evaluation_subst[OF left, of sigma] by (simp add: lpp_machine_value_named)
 have right_subst: "lpp_stable_scalar_evaluation operation (lp_isubst (actuals!j) sigma) (lpp_machine_value w)"
   using lpp_stable_scalar_evaluation_subst[OF right, of sigma] by (simp add: lpp_machine_value_named)
 show ?thesis
 proof
  assume unifies: "lp_isubst (LPIFun (LPCUser q) actuals) sigma=lp_ieval (Fun (LPCUser q) hs) rho"
  have maps: "map (\<lambda>t. lp_isubst t sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
    using unifies by simp
  have li: "lp_isubst (actuals!i) sigma=rho x"
    using arg_cong[OF maps, of "\<lambda>ts. ts!i"] bounds lengths heads by simp
  have rj: "lp_isubst (actuals!j) sigma=rho x"
    using arg_cong[OF maps, of "\<lambda>ts. ts!j"] bounds lengths heads by simp
  have same: "(lpp_machine_value v :: (string lp_cut_symbol,string) lp_iterm)=lpp_machine_value w"
    by (rule lpp_stable_scalar_evaluation_unique[OF left_subst]) (use right_subst li rj in simp)
  show False using lpp_machine_value_injective[OF valid same] different by contradiction
 qed
qed

lemma lpp_head_apart_failure:
 assumes checked: "lpp_head_apart_check P q observations d i j"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain hs where head: "fst (P!d)=Fun (LPCUser q) hs"
   and args: "lpp_head_apart_args hs observations i j" and index: "d<length P"
   using checked by (auto simp: lpp_head_apart_check_def split: term.splits lp_cut_symbol.splits)
 have impossible: "\<not>(\<exists>sigma rho :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm.
     lp_isubst (LPIFun (LPCUser q) actuals) sigma=lp_ieval (fst (P!d)) rho)"
   unfolding head by (metis lpp_head_apart_no_unifier[OF args observed])
 have step: "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>lp_cut_mgu_source P"
   by (rule lp_cut_mgu_source.backtrack[OF index impossible])
 show ?thesis by (rule r_into_trancl)
   (use step in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_head_apart_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted repeated-head exclusion" else ();
\<close>
end
