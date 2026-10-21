theory LP_Continuation_Machine
  imports LP_Filtered_Narrowing
begin

type_synonym ('f,'v) lp_atom = "'f \<times> ('f,'v) term list"
type_synonym ('f,'v) lp_clause = "('f,'v) lp_atom \<times> ('f,'v) lp_atom list"

definition lp_atom_subst where
  "lp_atom_subst a \<sigma> = (fst a, map (\<lambda>t. t \<cdot> \<sigma>) (snd a))"

definition lp_tag where
  "lp_tag tag a = Fun (tag (fst a)) (snd a)"

lemma lp_tag_subst[simp]:
  "lp_tag tag (lp_atom_subst a \<sigma>) = lp_tag tag a \<cdot> \<sigma>"
  by (simp add: lp_tag_def lp_atom_subst_def)

definition lp_atom_vars where
  "lp_atom_vars a = rev (remdups (rev (concat (map vars_term_list (snd a)))))"

definition lp_saved_vars where
  "lp_saved_vars c i = rev (remdups (rev (lp_atom_vars (fst c) @
    concat (map lp_atom_vars (take i (snd c))))))"

datatype ('f,'v) lp_config =
    LPCall "('f,'v) lp_atom"
  | LPDone "('f,'v) lp_atom"
  | LPWait nat nat "'v \<Rightarrow> ('f,'v) term" "('f,'v) lp_config"

fun lp_config_subst where
  "lp_config_subst (LPCall a) \<sigma> = LPCall (lp_atom_subst a \<sigma>)"
| "lp_config_subst (LPDone a) \<sigma> = LPDone (lp_atom_subst a \<sigma>)"
| "lp_config_subst (LPWait c i \<rho> k) \<sigma> =
    LPWait c i (\<lambda>x. \<rho> x \<cdot> \<sigma>) (lp_config_subst k \<sigma>)"

text \<open>Source-level call/return semantics. Clause instances are arbitrary,
  so most-general unification and standardization apart are included rather than
  trusted as restrictions of the checker. This theory uses finite substitutions;
  it does not yet claim the paper's rational-tree/no-occurs-check semantics.\<close>

inductive_set lp_local :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v) lp_config rel"
  for P where
  fact: "c < length P \<Longrightarrow> snd (P!c) = [] \<Longrightarrow>
    (LPCall (lp_atom_subst (fst (P!c)) \<rho>),
     LPDone (lp_atom_subst (fst (P!c)) \<rho>)) \<in> lp_local P"
| enter: "c < length P \<Longrightarrow> snd (P!c) \<noteq> [] \<Longrightarrow>
    (LPCall (lp_atom_subst (fst (P!c)) \<rho>),
     LPWait c 0 \<rho> (LPCall (lp_atom_subst (snd (P!c)!0) \<rho>))) \<in> lp_local P"
| advance: "c < length P \<Longrightarrow> Suc i < length (snd (P!c)) \<Longrightarrow>
    (LPWait c i \<rho> (LPDone (lp_atom_subst (snd (P!c)!i) \<rho>)),
     LPWait c (Suc i) \<rho> (LPCall (lp_atom_subst (snd (P!c)!Suc i) \<rho>))) \<in> lp_local P"
| leave: "c < length P \<Longrightarrow> i < length (snd (P!c)) \<Longrightarrow>
    Suc i = length (snd (P!c)) \<Longrightarrow>
    (LPWait c i \<rho> (LPDone (lp_atom_subst (snd (P!c)!i) \<rho>)),
     LPDone (lp_atom_subst (fst (P!c)) \<rho>)) \<in> lp_local P"
| frame: "(s,t) \<in> lp_local P \<Longrightarrow>
    (LPWait c i \<rho> s, LPWait c i \<rho> t) \<in> lp_local P"

definition lp_machine where
  "lp_machine P = {(s,t). \<exists>\<sigma>. (lp_config_subst s \<sigma>,t) \<in> lp_local P}"

locale lp_translation =
  fixes P :: "('f,'v) lp_clause list"
    and inp out :: "'f \<Rightarrow> 'f" and u :: "nat \<Rightarrow> nat \<Rightarrow> 'f"
begin

definition env where "env c i = map Var (lp_saved_vars (P!c) i)"
definition wrap where "wrap c i t = Fun (u c i) (t # env c i)"

definition entry_rule where
  "entry_rule c = (lp_tag inp (fst (P!c)),
    if snd (P!c) = [] then lp_tag out (fst (P!c))
    else wrap c 0 (lp_tag inp (snd (P!c)!0)))"

definition return_rule where
  "return_rule c i = (wrap c i (lp_tag out (snd (P!c)!i)),
    if Suc i < length (snd (P!c))
    then wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))
    else lp_tag out (fst (P!c)))"

definition translated where
  "translated = map entry_rule [0..<length P] @
    concat (map (\<lambda>c. map (return_rule c) [0..<length (snd (P!c))]) [0..<length P])"

lemma entry_member: "c < length P \<Longrightarrow> entry_rule c \<in> set translated"
  unfolding translated_def by force

lemma return_member: "c < length P \<Longrightarrow> i < length (snd (P!c)) \<Longrightarrow>
    return_rule c i \<in> set translated"
  unfolding translated_def by force

fun encode where
  "encode (LPCall a) = lp_tag inp a"
| "encode (LPDone a) = lp_tag out a"
| "encode (LPWait c i \<rho> k) = Fun (u c i) (encode k # map \<rho> (lp_saved_vars (P!c) i))"

lemma encode_subst:
  "encode (lp_config_subst s \<sigma>) = encode s \<cdot> \<sigma>"
  by (induct s) (simp_all add: o_def)

lemma local_simulation:
  assumes "(s,t) \<in> lp_local P"
  shows "(encode s,encode t) \<in> lp_active_step (set translated) (range (\<lambda>(c,i). u c i))"
  using assms
proof (induct rule: lp_local.induct)
  case (fact c \<rho>)
  have r: "(lp_tag inp (fst (P!c)),lp_tag out (fst (P!c))) \<in> set translated"
    using entry_member[OF fact(1)] fact(2) by (simp add: entry_rule_def)
  show ?case by (simp only: encode.simps lp_tag_subst, rule lp_active_step.root[OF r])
next
  case (enter c \<rho>)
  have r: "(lp_tag inp (fst (P!c)), wrap c 0 (lp_tag inp (snd (P!c)!0))) \<in> set translated"
    using entry_member[OF enter(1)] enter(2) by (simp add: entry_rule_def)
  show ?case using lp_active_step.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def)
next
  case (advance c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),
      wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))) \<in> set translated"
    using return_member[OF advance(1), of i] advance(2)
    by (simp add: return_rule_def)
  show ?case using lp_active_step.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def)
next
  case (leave c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),lp_tag out (fst (P!c))) \<in> set translated"
    using return_member[OF leave(1,2)] leave(3) by (simp add: return_rule_def)
  show ?case using lp_active_step.root[OF r, of \<rho>]
    by (simp add: wrap_def env_def o_def)
next
  case (frame s t c i \<rho>)
  have member: "u c i \<in> range (\<lambda>(c,i). u c i)"
    by (rule image_eqI[where x="(c,i)"], simp, rule UNIV_I)
  show ?case by (simp only: encode.simps, rule lp_active_step.frame[OF member frame(2)])
qed

lemma machine_simulation:
  assumes "(s,t) \<in> lp_machine P"
  shows "(encode s,encode t) \<in> lp_narrow_step (set translated) (range (\<lambda>(c,i). u c i))"
proof -
  obtain \<sigma> where st: "(lp_config_subst s \<sigma>,t) \<in> lp_local P"
    using assms unfolding lp_machine_def by blast
  have "(encode s \<cdot> \<sigma>,encode t) \<in> lp_active_step (set translated) (range (\<lambda>(c,i). u c i))"
    using local_simulation[OF st] by (simp add: encode_subst)
  then show ?thesis unfolding lp_narrow_step_def by blast
qed

theorem source_machine_terminates:
  assumes filter: "lp_filter \<pi> (range (\<lambda>(c,i). u c i))"
    and sn: "SN (rstep (af_rule \<pi> ` set translated))"
    and vars: "\<And>l r. (l,r) \<in> af_rule \<pi> ` set translated \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and gr: "ground (af_term \<pi> (encode s))"
  shows "SN_on (lp_machine P) {s}"
proof -
  interpret lp_filter \<pi> "range (\<lambda>(c,i). u c i)" by (rule filter)
  have encoded: "SN_on (lp_narrow_step (set translated) (range (\<lambda>(c,i). u c i))) {encode s}"
    by (rule filtered_narrowing_terminates[OF sn vars gr])
  show ?thesis
  proof (rule SN_onI)
    fix f assume start: "f 0 \<in> {s}" and ch: "chain (lp_machine P) f"
    have projected: "chain (lp_narrow_step (set translated) (range (\<lambda>(c,i). u c i))) (\<lambda>n. encode (f n))"
      unfolding chain_def
      by (intro allI, rule machine_simulation, use ch in \<open>simp add: chain_def\<close>)
    have witness: "\<exists>g. g 0 \<in> {encode s} \<and> chain (lp_narrow_step (set translated) (range (\<lambda>(c,i). u c i))) g"
      by (rule exI[where x="\<lambda>n. encode (f n)"], rule conjI, use start in simp, rule projected)
    from encoded witness show False unfolding SN_on_def by contradiction
  qed
qed

end

declare lp_translation.env_def[code]
declare lp_translation.wrap_def[code]
declare lp_translation.entry_rule_def[code]
declare lp_translation.return_rule_def[code]
declare lp_translation.translated_def[code]
end
