theory Cons_Node_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Cons_Node"
   "../../thys/Logic_Programming/LP_Prolog_Cons_Successor_Facts"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_clause_coordinate :: "nat \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_clause_coordinate = lpp_check_clause_coordinate"
definition test_body_output :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_body_output = lpp_check_body_output"

definition test_cons_head :: "string lp_cut_symbol \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 nat \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> bool" where
 "test_cons_head p h arity x y H =
  (h=Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H) \<and>
   distinct (x#y#H) \<and> length H=arity)"

lemma test_cons_head_sound:
 "test_cons_head p h arity x y H \<Longrightarrow>
  h=Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H) \<and>
  distinct (x#y#H) \<and> length H=arity"
 by (simp add: test_cons_head_def)

definition test_leaf_slots :: "nat list \<Rightarrow> (string lp_cut_symbol,nat) term lp_cut_goal list \<Rightarrow> bool" where
 "test_leaf_slots = lpp_check_attached_leaf_slots"

ML \<open>
val checked = @{thms lpp_attached_cons_leaf_step lpp_cons_head_finite_instance
 lpp_attached_cons_finite_step lpp_cons_tail_successor lpp_cons_recursive_successor_facts
 lpp_checked_observer_cons_head lpp_checked_observer_cons_head_contract
 lpp_observer_cons_node_contract test_cons_head_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted head successor gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-cons-node";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Full family and Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_cons_head}, @{const_name test_leaf_slots}, @{const_name test_clause_coordinate}, @{const_name test_body_output},
  @{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
  @{const_name lpp_decode_separation_subject}, @{const_name lpp_check_functor_source_action},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Cons_Node_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Cons_Node_Check.ML") (snd(hd modules));
val _ = writeln "CONS_NODE_CONTRACT_CHECKED_AND_EXPORTED";
\<close>
end
