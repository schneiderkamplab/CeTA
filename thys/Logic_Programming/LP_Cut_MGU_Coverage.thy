theory LP_Cut_MGU_Coverage
  imports LP_Cut_MGU_Variants
begin

lemma lpc_distinct_variable_call_unifies:
  fixes hs :: "('f,string) term list" and xs :: "string list"
  assumes distinct: "distinct xs" and lengths: "length xs=length hs"
  shows "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f,string) lp_iterm.
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
  show ?thesis
    by (rule exI[of _ ?s], rule exI[of _ LPIVar]) (simp add: map_map o_def maps)
qed

lemma lpc_free_knowledge_representation:
  assumes "lpc_free_knowledge F \<eta>"
  shows "\<exists>r. inj_on r F \<and> (\<forall>x\<in>F. \<eta> x=LPIVar (r x))"
proof -
  let ?r = "\<lambda>x. case \<eta> x of LPIVar y \<Rightarrow> y | LPIFun f ts \<Rightarrow> undefined"
  have variable: "\<And>x. x\<in>F \<Longrightarrow> \<eta> x=LPIVar (?r x)"
    using assms by (auto simp: lpc_free_knowledge_def)
  have injective: "inj_on ?r F"
    using assms variable by (auto simp: lpc_free_knowledge_def inj_on_def)
  show ?thesis by (rule exI[of _ ?r], rule conjI[OF injective]) (auto intro: variable)
qed

definition lpc_check_free_call where
  "lpc_check_free_call F a h = (case (a,h) of
    (Fun f ts, Fun g us) \<Rightarrow>
      f=g \<and> length ts=length us \<and>
      list_all is_Var ts \<and> distinct ts \<and>
      (\<Union>(vars_term ` set ts)) \<subseteq> set F
    | _ \<Rightarrow> False)"

theorem lpc_check_free_call_sound:
  fixes a h :: "('f,string) term" and \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lpc_check_free_call F a h"
    and known: "lpc_free_knowledge (set F) \<eta>"
  shows "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f,string) lp_iterm.
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
    by (rule lpc_distinct_variable_call_unifies[OF ds length_map])
qed

lemma lpc_free_call_positive:
  "x\<noteq>y \<Longrightarrow> lpc_check_free_call [x,y] (Fun f [Var x,Var y]) (Fun f [s,t])"
  by (simp add: lpc_check_free_call_def)

lemma lpc_free_call_rejects_alias:
  "\<not>lpc_check_free_call F (Fun f [Var x,Var x]) (Fun f [s,t])"
  by (simp add: lpc_check_free_call_def)

lemma lpc_free_call_requires_knowledge:
  "\<not>lpc_check_free_call [] (Fun f [Var x]) (Fun f [t])"
  by (simp add: lpc_check_free_call_def)

end
