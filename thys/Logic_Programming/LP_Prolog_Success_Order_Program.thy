theory LP_Prolog_Success_Order_Program
  imports LP_Prolog_Success_Order_Contracts
begin

fun lpp_check_order_facts where
  "lpp_check_order_facts summaries increasing bs gs known [] = True"
| "lpp_check_order_facts summaries increasing bs gs known (f#fs) =
    (lpp_check_order_fact summaries increasing bs gs known f \<and>
     lpp_check_order_facts summaries increasing bs gs (Var (lpp_order_fact_variable f)#known) fs)"

lemma lpp_check_order_facts_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_facts summaries increasing bs gs known fs"
    and known: "\<And>t. t\<in>set known \<Longrightarrow> lpp_order_bound_holds increasing eta n t"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_order_summaries_hold summaries (lpp_success_atom_eval b eta)) bs"
  shows "\<forall>f\<in>set fs. \<exists>m. eta (lpp_order_fact_variable f)=lpp_integer_value m \<and>
    lpp_order_relation increasing n m"
  using checked known
proof (induction fs arbitrary: known)
  case Nil then show ?case by simp
next
  case (Cons f fs)
  have check: "lpp_check_order_fact summaries increasing bs gs known f"
    and rest: "lpp_check_order_facts summaries increasing bs gs (Var (lpp_order_fact_variable f)#known) fs"
    using Cons.prems(1) by simp_all
  obtain m where returned_value: "eta (lpp_order_fact_variable f)=lpp_integer_value m"
    and order: "lpp_order_relation increasing n m"
    using lpp_check_order_fact_sound[OF compatible check Cons.prems(2) guards helpers] by blast
  have fresh: "lpp_order_bound_holds increasing eta n (Var (lpp_order_fact_variable f))"
    unfolding lpp_order_bound_holds_def
    by (rule exI[of _ m]) (simp add: returned_value order lpp_integer_evaluation.literal)
  have extended: "lpp_order_bound_holds increasing eta n t"
    if "t\<in>set (Var (lpp_order_fact_variable f)#known)" for t
    using that Cons.prems(2) fresh by auto
  show ?case using Cons.IH[OF rest extended] returned_value order by auto
qed

definition lpp_check_order_clause where
  "lpp_check_order_clause summaries c contract receipt = (case (c,contract,receipt) of
    ((h,bs,gs),(increasing,selector,j),(fs,k)) \<Rightarrow>
      j<length (snd h) \<and> k<length fs \<and>
      snd h!j=Var (lpp_order_fact_variable (fs!k)) \<and>
      (case lpp_order_base_select lpp_integer_term (snd h) selector of
        None \<Rightarrow> False | Some t \<Rightarrow>
          lpp_check_order_facts summaries increasing bs gs [t] fs))"

lemma lpp_check_order_clause_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_clause summaries (h,bs,gs) contract receipt"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_order_summaries_hold summaries (lpp_success_atom_eval b eta)) bs"
  shows "lpp_order_contract_holds (snd (lpp_success_atom_eval h eta)) contract"
proof -
  obtain increasing selector j fs k t where shape: "contract=(increasing,selector,j)" "receipt=(fs,k)"
    and outpos: "j<length (snd h)" "k<length fs" "snd h!j=Var (lpp_order_fact_variable (fs!k))"
    and selected: "lpp_order_base_select lpp_integer_term (snd h) selector=Some t"
    and facts: "lpp_check_order_facts summaries increasing bs gs [t] fs"
    using checked by (cases contract; cases receipt; auto simp: lpp_check_order_clause_def split: option.splits)
  have selection: "lpp_order_base_select lpp_integer_value (map (\<lambda>t. lp_ieval t eta) (snd h)) selector=Some (lp_ieval t eta)"
    using lpp_order_base_select_map[of "\<lambda>t. lp_ieval t eta" lpp_integer_term "snd h" selector] selected
    by (simp add: o_def)
  have result: "\<exists>m. lp_ieval (snd h!j) eta=lpp_integer_value m \<and>
      lpp_order_relation increasing n m"
    if evaluated: "lpp_integer_evaluation (lp_ieval t eta) n" for n
  proof -
    have seed: "lpp_order_bound_holds increasing eta n u" if "u\<in>set [t]" for u
      using that evaluated by (auto simp: lpp_order_bound_holds_def lpp_order_relation_def)
    have all: "\<forall>f\<in>set fs. \<exists>m. eta (lpp_order_fact_variable f)=lpp_integer_value m \<and>
        lpp_order_relation increasing n m"
      by (rule lpp_check_order_facts_sound[OF compatible facts seed guards helpers])
    show ?thesis using all outpos by (auto dest: bspec[OF _ nth_mem])
  qed
  show ?thesis using outpos selection result
    by (auto simp: shape lpp_order_contract_holds_def lpp_success_atom_eval_def)
qed

definition lpp_check_order_rows where
  "lpp_check_order_rows summaries c receipts = (case c of (h,bs,gs) \<Rightarrow>
    list_all2 (lpp_check_order_clause summaries c) (summaries (fst h,length (snd h))) receipts)"

definition lpp_check_order_program where
  "lpp_check_order_program summaries P receipts = list_all2 (lpp_check_order_rows summaries) P receipts"

theorem lpp_check_order_program_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_program summaries P receipts"
    and success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) a"
  shows "lpp_order_summaries_hold summaries a"
proof (rule lpp_magnitude_success_invariant[OF success])
  fix h bs gs eta
  assume member: "(h,bs,gs)\<in>set P"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_order_summaries_hold summaries (lpp_success_atom_eval b eta)) bs"
  obtain rows where row: "lpp_check_order_rows summaries (h,bs,gs) rows"
    using lpp_magnitude_list_all2_member[OF checked[unfolded lpp_check_order_program_def] member] by blast
  have result: "lpp_order_contract_holds (snd (lpp_success_atom_eval h eta)) contract"
    if selected: "contract\<in>set (summaries (fst h,length (snd h)))" for contract
  proof -
    obtain receipt where clause: "lpp_check_order_clause summaries (h,bs,gs) contract receipt"
      using lpp_magnitude_list_all2_member[OF row[unfolded lpp_check_order_rows_def, simplified] selected] by blast
    show ?thesis by (rule lpp_check_order_clause_sound[OF compatible clause guards helpers])
  qed
  show "lpp_order_summaries_hold summaries (lpp_success_atom_eval h eta)"
    using result by (auto simp: lpp_order_summaries_hold_def lpp_success_atom_eval_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_check_order_program_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted conditional order program dependency" else ();
\<close>
end
