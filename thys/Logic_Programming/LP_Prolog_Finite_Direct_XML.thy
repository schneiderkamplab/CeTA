theory LP_Prolog_Finite_Direct_XML
 imports LP_Prolog_Finite_Direct_Root LP_Prolog_Finite_Triple_XML LP_Prolog_Stable_Profile_Operations
begin

definition lpp_established_finite_direct_parser where
 "lpp_established_finite_direct_parser = XMLdo (STR ''prologEstablishedFiniteDirectProof'') {
   profile\<leftarrow>xml_text (STR ''profile'');
   P0\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
     h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
     bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
   q\<leftarrow>xml_text (STR ''predicate'');
   modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
   signatures\<leftarrow>xml_many (STR ''signatures'') (XMLdo (STR ''signature'') {
     f\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity''); xml_return (f,n)}) id;
   data\<leftarrow>lpp_established_finite_control_parser;
   Fs\<leftarrow>xml_many (STR ''freeKnowledge'') (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
   xml_return (profile,P0,q,modes,signatures,data,Fs)}"

definition check_lpp_established_finite_direct_xml where
 "check_lpp_established_finite_direct_xml xml = (case parse_xml_string lpp_established_finite_direct_parser xml of
   Right (profile,P0,q,modes,signatures,(P,fuel,r,(summaries,SP,receipts),region),Fs) \<Rightarrow>
     (let control=lppftr_control region in
      profile=''iso-rational-libraries-v1'' \<and> P0=P \<and> r=0 \<and>
      length (lppftr_typings region)=length (lpcsc_nodes control) \<and>
      list_all (\<lambda>fs. fs=[]) (lppftr_typings region) \<and>
      lpp_check_transfer_contract summaries SP receipts \<and>
      distinct (map fst (lpcsc_ranks control)) \<and>
      lpp_check_finite_direct_root fuel P (lpcsc_program control) (lpcsc_nodes control)
        (lpcsc_states control) (lppftr_contexts region) Fs (lpp_transfer_lookup summaries)
        (lpcsc_returned control) (lpcsc_arity control) (lppftr_actions region)
        (lpc_seg_control_rank control) signatures q modes)
   | _ \<Rightarrow> False)"

theorem check_lpp_established_finite_direct_xml_sound:
 fixes ts :: "(string lp_cut_symbol,string) term list"
 assumes parsed: "parse_xml_string lpp_established_finite_direct_parser xml =
   Right (profile,P0,q,modes,signatures,(P,fuel,r,(summaries,SP,receipts),region),Fs)"
   and ok: "check_lpp_established_finite_direct_xml xml"
   and len: "length ts=length modes"
   and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
 shows "SN_on (lpp_domain_source P lpp_builtin_signature
   (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain)
   {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
 let ?control = "lppftr_control region"
 have checked: "lpp_check_finite_direct_root fuel P (lpcsc_program ?control) (lpcsc_nodes ?control)
     (lpcsc_states ?control) (lppftr_contexts region) Fs (lpp_transfer_lookup summaries)
     (lpcsc_returned ?control) (lpcsc_arity ?control) (lppftr_actions region)
     (lpc_seg_control_rank ?control) signatures q modes"
   and transfer: "lpp_check_transfer_program (lpp_transfer_lookup summaries) SP receipts"
   using parsed ok by (auto simp: check_lpp_established_finite_direct_xml_def Let_def lpp_check_transfer_contract_def)
 show ?thesis
 proof (rule lpp_finite_direct_root_sound[OF lpp_stable_profile_integer_compatible checked transfer])
  show "length (map (\<lambda>t. lp_ieval t LPIVar) ts)=length modes" using len by simp
  show "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t LPIVar) ts)"
    by (simp add: list_all_iff lpp_finite_term_initial)
  show "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes). b \<longrightarrow> lp_seg_ground t"
    using ground len by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
 qed
qed

ML \<open>
val checked = [@{thm check_lpp_established_finite_direct_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct XML" else ();
\<close>
end
