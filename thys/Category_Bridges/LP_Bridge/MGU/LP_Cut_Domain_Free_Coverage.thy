theory LP_Cut_Domain_Free_Coverage
  imports LP_Cut_Domain_MGU_Properties
begin

text \<open>A distinct-variable call has a unifier in each selected domain:
instantiate its variables with finite clause-head terms and leave clause
variables free. Unrestricted unifiability alone would not establish this fact.\<close>

context cut_runtime_domain
begin

lemma distinct_variable_call_unifies:
  fixes hs :: "('f lp_cut_symbol,string) term list" and xs :: "string list"
  assumes distinct: "distinct xs" and lengths: "length xs=length hs"
  shows "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
    lp_isubst (LPIFun f (map LPIVar xs)) \<sigma> = lp_ieval (Fun f hs) \<rho>"
proof -
  let ?values = "map (\<lambda>t. lp_ieval t LPIVar) hs"
  let ?s = "\<lambda>x. case map_of (zip xs ?values) x of None \<Rightarrow> LPIVar x | Some t \<Rightarrow> t"
  have maps: "map ?s xs = ?values"
  proof (rule nth_equalityI)
    show "length (map ?s xs)=length ?values" using lengths by simp
    fix i assume i: "i<length (map ?s xs)"
    have lookup: "map_of (zip xs ?values) (xs!i) = Some (?values!i)"
      by (rule map_of_zip_nth) (use distinct lengths i in auto)
    show "map ?s xs ! i = ?values ! i" using lookup i by simp
  qed
  have ds: "\<forall>x. D (?s x)"
  proof (intro allI)
    fix x
    have "D (lp_cut_query_env xs ?values x)"
      by (rule query_env_domain) (auto intro: cut_domain_eval[OF variables constructors])
    then show "D (?s x)" by (simp add: lp_cut_query_env_def)
  qed
  show ?thesis
    by (rule exI[of _ ?s], rule exI[of _ LPIVar])
      (simp add: ds variables map_map o_def maps)
qed

theorem check_free_call_sound:
  fixes a h :: "('f lp_cut_symbol,string) term" and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_free_call F a h"
    and known: "lpc_free_knowledge (set F) \<eta>"
  shows "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
proof -
  obtain f ts hs where shape: "a=Fun f ts" "h=Fun f hs"
    and len: "length ts=length hs" and vars: "list_all is_Var ts"
    and distinct: "distinct ts" and subset: "\<Union>(vars_term ` set ts) \<subseteq> set F"
    using checked by (auto simp: lpc_check_free_call_def split: term.splits)
  have "\<exists>xs. ts=map Var xs"
    using vars
  proof (induct ts)
    case Nil then show ?case by simp
  next
    case (Cons t ts)
    then obtain x where t: "t=Var x" by (cases t) auto
    from Cons obtain xs where rest: "ts=map Var xs" by auto
    show ?case by (rule exI[of _ "x#xs"]) (simp add: t rest)
  qed
  then obtain xs where ts: "ts=map Var xs" by blast
  obtain r where injective: "inj_on r (set F)" and env: "\<forall>x\<in>set F. \<eta> x=LPIVar (r x)"
    using lpc_free_knowledge_representation[OF known] by blast
  have xs: "distinct xs" "set xs \<subseteq> set F" "length xs = length hs"
    using distinct subset len ts by (auto simp: distinct_map)
  have ds: "distinct (map r xs)"
    using xs injective by (auto simp: distinct_map inj_on_def)
  have call_value: "lp_ieval a \<eta> = LPIFun f (map LPIVar (map r xs))"
    using env xs(2) by (auto simp: shape ts map_map intro!: map_cong)
  have length_map: "length (map r xs) = length hs" using xs(3) by simp
  show ?thesis unfolding call_value shape(2)
    by (rule distinct_variable_call_unifies[OF ds length_map])
qed


end
end
