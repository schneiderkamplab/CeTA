theory Relative_ADP_Composition
  imports Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin

text \<open>Close ordinary recursive-checker obligations with independently checked
relative ADP proofs. No assumption is accepted merely because it occurs in the
certificate: every ordinary assumption must be an unconditional full-rewriting
termination obligation discharged by one of the checked ADP certificates.\<close>

type_synonym relative_adp_discharge =
  "(lsymbol,string) rules \<times> (lsymbol,string) rules \<times>
    lsymbol relative_adp_root_proof"

fun relative_adp_discharge_assumption ::
  "relative_adp_discharge \<Rightarrow> (string,label_type,string) assm" where
  "relative_adp_discharge_assumption (R,B,p) = SN_assm [] (False,[],R,B)"

fun check_relative_adp_discharge :: "relative_adp_discharge \<Rightarrow> showsl check" where
  "check_relative_adp_discharge (R,B,p) = check_relative_adp_root R B p"

lemma check_relative_adp_discharge_sound:
  assumes "isOK (check_relative_adp_discharge d)"
  shows "holds (relative_adp_discharge_assumption d)"
proof -
  obtain R B p where fields: "d = (R,B,p)" by (cases d) auto
  have "SN_rel (Trs.rstep (set R)) (Trs.rstep (set B))"
    using assms unfolding fields by (auto intro: check_relative_adp_root_sound)
  then show ?thesis unfolding fields
    by (simp add: SN_qrel_def)
qed

definition check_relative_adp_composition ::
  "(lsymbol,string) input \<Rightarrow> (lsymbol,string) property \<Rightarrow>
    (lsymbol,string) answer \<Rightarrow> (string,label_type,string) proof \<Rightarrow>
    relative_adp_discharge list \<Rightarrow> showsl check" where
  "check_relative_adp_composition inp prop ans prf discharges = do {
    check_allm check_relative_adp_discharge discharges;
    check (set (cert_assms True prf) \<subseteq>
      set (map relative_adp_discharge_assumption discharges))
      (showsl_lit (STR ''ordinary proof has an undischarged or incompatible assumption''));
    check_cert tp_impl dpp_impl ac_tp_impl ac_dpp_impl True inp prop ans prf
  }"

lemma check_relative_adp_composition_sound:
  assumes "isOK (check_relative_adp_composition inp prop ans prf discharges)"
  shows "desired_property inp prop ans"
proof -
  from assms have checked: "isOK
      (check_cert tp_impl dpp_impl ac_tp_impl ac_dpp_impl True inp prop ans prf)"
    and covered: "set (cert_assms True prf) \<subseteq>
      set (map relative_adp_discharge_assumption discharges)"
    and discharged: "\<forall>d\<in>set discharges. isOK (check_relative_adp_discharge d)"
    unfolding check_relative_adp_composition_def by (auto simp: isOK_check_allm)
  have closed: "\<forall>a\<in>set (cert_assms True prf). holds a"
  proof (intro ballI)
    fix a
    assume "a \<in> set (cert_assms True prf)"
    then obtain d where member: "d \<in> set discharges"
      and identity: "a = relative_adp_discharge_assumption d"
      using covered by auto
    have "isOK (check_relative_adp_discharge d)"
      using discharged member by blast
    then have "holds (relative_adp_discharge_assumption d)"
      by (rule check_relative_adp_discharge_sound)
    then show "holds a" unfolding identity .
  qed
  show ?thesis
    by (rule check_cert_with_assms_sound[OF tp_rbt_impl dpp_rbt_impl
      ac_tp_list_impl ac_dpp_rbt_impl checked closed])
qed

definition certify_relative_adp_composition where
  "certify_relative_adp_composition inp prop ans prf discharges =
    (case check_relative_adp_composition inp prop ans prf discharges of
      Inl err \<Rightarrow> Error (err (STR ''''))
    | Inr _ \<Rightarrow> Certified)"

lemma certify_relative_adp_composition_sound:
  assumes "certify_relative_adp_composition inp prop ans prf discharges = Certified"
  shows "desired_property inp prop ans"
  using assms unfolding certify_relative_adp_composition_def
  by (cases "check_relative_adp_composition inp prop ans prf discharges";
      auto intro: check_relative_adp_composition_sound)

lemma check_relative_adp_composition_rejects_uncovered:
  assumes "a \<in> set (cert_assms True prf)"
    and "a \<notin> set (map relative_adp_discharge_assumption discharges)"
  shows "\<not> isOK (check_relative_adp_composition inp prop ans prf discharges)"
  using assms unfolding check_relative_adp_composition_def by (auto simp: isOK_check_allm)

ML \<open>
val relative_adp_composition_soundness =
  [@{thm check_relative_adp_discharge_sound},
   @{thm check_relative_adp_composition_sound},
   @{thm certify_relative_adp_composition_sound},
   @{thm check_relative_adp_composition_rejects_uncovered}];
val relative_adp_composition_oracles =
  Thm_Deps.all_oracles relative_adp_composition_soundness;
val relative_adp_existing_oracles = Thm_Deps.all_oracles
  [@{thm check_relative_adp_root_sound}, @{thm check_cert_with_assms_sound}];
val _ = writeln ("ADP composition inherited oracle dependencies: " ^
  commas (map (fn ((name, _), _) => name) relative_adp_composition_oracles
    |> distinct (op =)));
val _ = if Thm_Deps.has_skip_proof relative_adp_composition_soundness
  orelse not (Ord_List.subset Proofterm.oracle_ord
    (relative_adp_composition_oracles, relative_adp_existing_oracles))
  then error "ADP composition introduces an admission or a new oracle dependency"
  else ();
\<close>

end
