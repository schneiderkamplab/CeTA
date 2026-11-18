theory LP_Prolog_Observer_Family_Test
 imports LP_Prolog_Observer_Referenced_Link_Node
begin

lemma lpp_observer_empty_family_rejected:
 "\<not>lpp_observer_family_rep names operation SP {} family_nodes states contexts frees functors premises runtime subject"
 by (simp add: lpp_observer_family_rep_def)

lemma lpp_observer_missing_family_member_rejected:
 assumes missing: "\<And>m. m\<in>members \<Longrightarrow>
   \<not>lpp_premised_functor_module_rep names operation SP (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject"
 shows "\<not>lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises runtime subject"
 using missing by (auto simp: lpp_observer_family_rep_def)

lemma lpp_observer_local_family_node:
 assumes member: "m\<in>members"
 and local: "lpp_observer_node_contract names operation SP P B U D Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m) J rest returned i"
 shows "lpp_observer_referenced_node_contract names operation SP P B U D Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m)
   (lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises) J rest returned i"
 apply (rule lpp_observer_local_to_referenced_node[OF local])
 by (rule lpp_observer_family_member[OF member])

lemma lpp_observer_missing_node_premise_rejected:
 assumes missing: "\<And>m j eta. m\<in>members \<Longrightarrow> \<not>premises m j eta"
 shows "\<not>lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises runtime subject"
 using missing by (auto simp: lpp_observer_family_rep_def lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)

end
