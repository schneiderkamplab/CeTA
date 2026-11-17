theory LP_Prolog_Separation_Head_Check
 imports LP_Prolog_Separation_Finite_Unification
begin

text \<open>Finite-head evidence is bound to the actual selected call and source
clause. The alternatives reuse existing checks; no source name selects a rule.
The proper-spine case also requires finite execution in its node contract.\<close>

datatype lpp_separation_head =
   LPPSMatching "(string * string lpc_term) list"
 | LPPSAnchored "string lp_cut_symbol" "string lpc_term list" "string lpc_term list" "string list"
 | LPPSSpine "string lp_cut_symbol" "string lpc_term" "string lpc_term list" string string "string list"

fun lpp_check_separation_head where
 "lpp_check_separation_head P nd ctx a c (LPPSMatching bindings) =
   (c<length P \<and> lp_cut_check_match a (fst (P!c)) bindings)"
| "lpp_check_separation_head P nd ctx a c (LPPSAnchored f actuals hs G) =
   (c<length P \<and> a=Fun f actuals \<and> fst (P!c)=Fun f hs \<and>
    length actuals=length hs \<and> lpp_check_anchored_head G actuals hs \<and>
    set G\<subseteq> set (lpcn_ground nd)\<union>lpp_source_context_ground ctx)"
| "lpp_check_separation_head P nd ctx a c (LPPSSpine f arg actuals x y H) =
   (c<length P \<and> a=Fun f (arg#actuals) \<and>
    fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H) \<and>
    distinct (x#y#H) \<and> length H=length actuals \<and>
    LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd ctx)))"

theorem lpp_checked_separation_head_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c witness"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (cases witness)
 case (LPPSMatching bindings)
 have matching: "lp_cut_check_match a (fst (P!c)) bindings" using head LPPSMatching by simp
 show ?thesis by (rule lpp_finite_empty_separation_matching_node_contract[OF compatible transfer checked shape matching success_target failure_target])
next
 case (LPPSAnchored f actuals hs G)
 have call: "a=Fun f actuals" and source_head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs" and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G\<subseteq> set (lpcn_ground (nds!i))\<union>lpp_source_context_ground (contexts!i)"
  using head LPPSAnchored by auto
 show ?thesis by (rule lpp_finite_empty_separation_anchored_node_contract[OF compatible transfer checked[unfolded call]
   shape[unfolded call] source_head lengths anchored ground success_target failure_target])
next
 case (LPPSSpine f arg actuals x y H)
 have call: "a=Fun f (arg#actuals)"
 and source_head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)" and lengths: "length H=length actuals"
 and spine: "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd (contexts!i)))"
  using head LPPSSpine by auto
 show ?thesis by (rule lpp_finite_empty_separation_spine_head_node_contract[OF compatible transfer checked[unfolded call]
   shape[unfolded call] source_head distinct lengths spine success_target failure_target])
qed

lemma lpp_separation_head_missing_clause_rejected:
 "c\<ge>length P \<Longrightarrow> \<not>lpp_check_separation_head P nd ctx a c witness"
 by (cases witness) auto

lemma lpp_separation_head_missing_spine_rejected:
 "snd (snd ctx)=[] \<Longrightarrow>
  \<not>lpp_check_separation_head P nd ctx a c (LPPSSpine f arg actuals x y H)"
 by simp

lemma lpp_separation_head_repeated_spine_rejected:
 "\<not>lpp_check_separation_head P nd ctx a c (LPPSSpine f arg actuals x x H)"
 by simp

ML \<open>
val checked = @{thms lpp_checked_separation_head_node_contract
 lpp_separation_head_missing_clause_rejected lpp_separation_head_missing_spine_rejected
 lpp_separation_head_repeated_spine_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation head checker" else ();
\<close>
end
