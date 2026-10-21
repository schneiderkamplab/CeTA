theory LP_Infinite_Machine
  imports LP_Continuation_Machine LP_Infinite_Narrowing
begin

type_synonym ('f,'w) lp_iatom = "'f \<times> ('f,'w) lp_iterm list"

definition lp_atom_eval where
  "lp_atom_eval a \<rho> = (fst a, map (\<lambda>t. lp_ieval t \<rho>) (snd a))"

definition lp_iatom_subst where
  "lp_iatom_subst a \<sigma> = (fst a, map (\<lambda>t. lp_isubst t \<sigma>) (snd a))"

definition lp_itag where
  "lp_itag tag a = LPIFun (tag (fst a)) (snd a)"

lemma lp_itag_eval:
  "lp_itag tag (lp_atom_eval a \<rho>) = lp_ieval (lp_tag tag a) \<rho>"
  by (simp add: lp_itag_def lp_atom_eval_def lp_tag_def)

lemma lp_itag_subst[simp]:
  "lp_itag tag (lp_iatom_subst a \<sigma>) = lp_isubst (lp_itag tag a) \<sigma>"
  by (simp add: lp_itag_def lp_iatom_subst_def)

datatype ('f,'v,'w) lp_iconfig =
    LPICall "('f,'w) lp_iatom"
  | LPIDone "('f,'w) lp_iatom"
  | LPIWait nat nat "'v \<Rightarrow> ('f,'w) lp_iterm" "('f,'v,'w) lp_iconfig"

fun lp_iconfig_subst where
  "lp_iconfig_subst (LPICall a) \<sigma> = LPICall (lp_iatom_subst a \<sigma>)"
| "lp_iconfig_subst (LPIDone a) \<sigma> = LPIDone (lp_iatom_subst a \<sigma>)"
| "lp_iconfig_subst (LPIWait c i \<rho> k) \<sigma> =
    LPIWait c i (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) (lp_iconfig_subst k \<sigma>)"

inductive_set lp_ilocal :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v,'w) lp_iconfig rel"
  for P where
  fact: "c < length P \<Longrightarrow> snd (P!c) = [] \<Longrightarrow>
    (LPICall (lp_atom_eval (fst (P!c)) \<rho>),
     LPIDone (lp_atom_eval (fst (P!c)) \<rho>)) \<in> lp_ilocal P"
| enter: "c < length P \<Longrightarrow> snd (P!c) \<noteq> [] \<Longrightarrow>
    (LPICall (lp_atom_eval (fst (P!c)) \<rho>),
     LPIWait c 0 \<rho> (LPICall (lp_atom_eval (snd (P!c)!0) \<rho>))) \<in> lp_ilocal P"
| advance: "c < length P \<Longrightarrow> Suc i < length (snd (P!c)) \<Longrightarrow>
    (LPIWait c i \<rho> (LPIDone (lp_atom_eval (snd (P!c)!i) \<rho>)),
     LPIWait c (Suc i) \<rho> (LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>))) \<in> lp_ilocal P"
| leave: "c < length P \<Longrightarrow> i < length (snd (P!c)) \<Longrightarrow>
    Suc i = length (snd (P!c)) \<Longrightarrow>
    (LPIWait c i \<rho> (LPIDone (lp_atom_eval (snd (P!c)!i) \<rho>)),
     LPIDone (lp_atom_eval (fst (P!c)) \<rho>)) \<in> lp_ilocal P"
| frame: "(s,t) \<in> lp_ilocal P \<Longrightarrow>
    (LPIWait c i \<rho> s, LPIWait c i \<rho> t) \<in> lp_ilocal P"

definition lp_imachine :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v,'w) lp_iconfig rel" where
  "lp_imachine P = {(s,t). \<exists>\<sigma>. (lp_iconfig_subst s \<sigma>,t) \<in> lp_ilocal P}"


context lp_translation
begin

fun iencode where
  "iencode (LPICall a) = lp_itag inp a"
| "iencode (LPIDone a) = lp_itag out a"
| "iencode (LPIWait c i \<rho> k) = LPIFun (u c i) (iencode k # map \<rho> (lp_saved_vars (P!c) i))"

lemma iencode_subst:
  "iencode (lp_iconfig_subst s \<sigma>) = lp_isubst (iencode s) \<sigma>"
  by (induct s) (simp_all add: o_def)

lemma ilocal_simulation:
  assumes "(s,t) \<in> lp_ilocal P"
  shows "(iencode s,iencode t) \<in> lp_iactive (set translated) (range (\<lambda>(c,i). u c i))"
  using assms
proof (induct rule: lp_ilocal.induct)
  case (fact c \<rho>)
  have r: "(lp_tag inp (fst (P!c)),lp_tag out (fst (P!c))) \<in> set translated"
    using entry_member[OF fact(1)] fact(2) by (simp add: entry_rule_def)
  show ?case by (simp only: iencode.simps lp_itag_eval, rule lp_iactive.root[OF r])
next
  case (enter c \<rho>)
  have r: "(lp_tag inp (fst (P!c)), wrap c 0 (lp_tag inp (snd (P!c)!0))) \<in> set translated"
    using entry_member[OF enter(1)] enter(2) by (simp add: entry_rule_def)
  show ?case using lp_iactive.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (advance c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),
      wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))) \<in> set translated"
    using return_member[OF advance(1), of i] advance(2)
    by (simp add: return_rule_def)
  show ?case using lp_iactive.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (leave c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),lp_tag out (fst (P!c))) \<in> set translated"
    using return_member[OF leave(1,2)] leave(3) by (simp add: return_rule_def)
  show ?case using lp_iactive.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (frame s t c i \<rho>)
  have member: "u c i \<in> range (\<lambda>(c,i). u c i)"
    by (rule image_eqI[where x="(c,i)"], simp, rule UNIV_I)
  show ?case by (simp only: iencode.simps, rule lp_iactive.frame[OF member frame(2)])
qed

lemma imachine_simulation:
  assumes "(s,t) \<in> lp_imachine P"
  shows "(iencode s,iencode t) \<in> lp_inarrow (set translated) (range (\<lambda>(c,i). u c i))"
proof -
  obtain \<sigma> where st: "(lp_iconfig_subst s \<sigma>,t) \<in> lp_ilocal P"
    using assms unfolding lp_imachine_def by blast
  have "(lp_isubst (iencode s) \<sigma>,iencode t) \<in> lp_iactive (set translated) (range (\<lambda>(c,i). u c i))"
    using ilocal_simulation[OF st] by (simp add: iencode_subst)
  then show ?thesis unfolding lp_inarrow_def by blast
qed


theorem infinite_source_machine_terminates:
  fixes a :: "('f,'v) term"
  assumes filter: "lp_filter \<pi> (range (\<lambda>(c,i). u c i))"
    and sn: "SN (rstep (af_rule \<pi> ` set translated))"
    and vars: "\<And>l r. (l,r) \<in> af_rule \<pi> ` set translated \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and gr: "lp_iproject \<pi> (iencode s) a"
  shows "SN_on (lp_imachine P) {s}"
proof -
  interpret lp_filter \<pi> "range (\<lambda>(c,i). u c i)" by (rule filter)
  have iencoded: "SN_on (lp_inarrow (set translated) (range (\<lambda>(c,i). u c i))) {iencode s}"
    proof (rule infinite_narrowing_terminates[OF sn _ gr])
    fix l r assume lr: "(l,r) \<in> set translated"
    have "(af_term \<pi> l,af_term \<pi> r) \<in> af_rule \<pi> ` set translated"
      using imageI[OF lr, of "af_rule \<pi>"] by (simp add: af_rule_alt_def)
    then show "vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)" by (rule vars)
  qed
  show ?thesis
  proof (rule SN_onI)
    fix f assume start: "f 0 \<in> {s}" and ch: "chain (lp_imachine P) f"
    have projected: "chain (lp_inarrow (set translated) (range (\<lambda>(c,i). u c i))) (\<lambda>n. iencode (f n))"
      unfolding chain_def
      by (intro allI, rule imachine_simulation, use ch in \<open>simp add: chain_def\<close>)
    have witness: "\<exists>g. g 0 \<in> {iencode s} \<and> chain (lp_inarrow (set translated) (range (\<lambda>(c,i). u c i))) g"
      by (rule exI[where x="\<lambda>n. iencode (f n)"], rule conjI, use start in simp, rule projected)
    from iencoded witness show False unfolding SN_on_def by contradiction
  qed
qed

end
end
