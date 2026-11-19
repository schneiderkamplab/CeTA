theory DP_Checkpoint_Registry
 imports DP_Checkpoint_Certificate
begin

text \<open>Interfaces are projected from checked summary records. Merely listing
an input/output pair cannot authenticate a successful-return rule. Every record
checks the same complete support rule list used by the termination problem.\<close>

fun checkpoint_argument_interface where
 "checkpoint_argument_interface (f,g,resume,witnesses) = (f,g)"
fun check_checkpoint_argument_registration where
 "check_checkpoint_argument_registration C N Z S support (f,g,resume,witnesses) =
 check_checkpoint_argument_summary C N Z S f g resume support witnesses"

fun checkpoint_ground_interface where
 "checkpoint_ground_interface (f,g,spine_in,sout,resume,head,tail,witnesses) = (f,g)"
fun check_checkpoint_ground_registration where
 "check_checkpoint_ground_registration C N Z S support (f,g,spine_in,sout,resume,head,tail,witnesses) =
 check_checkpoint_ground_summary C N Z S f g spine_in sout resume head tail support witnesses"

fun checkpoint_list_interface where
 "checkpoint_list_interface (ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail,templates,witnesses,domain_witnesses) = (lin,lout)"
fun check_checkpoint_list_registration where
 "check_checkpoint_list_registration C L N Z S support (ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail,templates,witnesses,domain_witnesses) =
 (check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses \<and>
 check_checkpoint_list_domain C N Z S lin lout lhead ltail ein eout support domain_witnesses)"

lemma checkpoint_registered_argument_return:
 assumes checked: "list_all (check_checkpoint_argument_registration C N Z S support) registry"
 and leaf: "L\<notin>{N,Z,S}"
 and member: "(f,g)\<in>set (map checkpoint_argument_interface registry)"
 and step: "check_checkpoint_fact_arguments_return f g copied result src dst"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst"
proof -
 obtain resume witnesses where registered: "(f,g,resume,witnesses)\<in>set registry"
 using member by auto
 have summary: "check_checkpoint_argument_summary C N Z S f g resume support witnesses"
 using checked registered by (auto simp: list_all_iff)
 show ?thesis by (rule checked_checkpoint_fact_arguments_return[OF summary leaf step holds])
qed

lemma checkpoint_registered_ground_return:
 assumes checked: "list_all (check_checkpoint_ground_registration C N Z S support) registry"
 and leaf: "L\<notin>{N,Z,S}"
 and member: "(f,g)\<in>set (map checkpoint_ground_interface registry)"
 and step: "check_checkpoint_fact_ground_return f g copied param src dst"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst"
proof -
 obtain spine_in sout resume head tail witnesses where registered:
 "(f,g,spine_in,sout,resume,head,tail,witnesses)\<in>set registry"
 using member by auto
 have summary: "check_checkpoint_ground_summary C N Z S f g spine_in sout resume head tail support witnesses"
 using checked registered by (auto simp: list_all_iff)
 show ?thesis by (rule checked_checkpoint_fact_ground_return[OF summary leaf step holds])
qed

lemma checkpoint_registered_list_return:
 assumes checked: "list_all (check_checkpoint_list_registration C L N Z S support) registry"
 and member: "(f,g)\<in>set (map checkpoint_list_interface registry)"
 and step: "check_checkpoint_fact_list_return f g copied result param h src dst"
 and holds: "checkpoint_fact_holds C L N Z S (set support) old sigma src"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst"
proof -
 obtain ein eout spine_in sout resume head tail lhead ltail templates witnesses domain_witnesses where registered:
 "(ein,eout,spine_in,sout,resume,head,tail,f,g,lhead,ltail,templates,witnesses,domain_witnesses)\<in>set registry"
 using member by auto
 have summary: "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail f g lhead ltail templates support witnesses"
 and domain: "check_checkpoint_list_domain C N Z S f g lhead ltail ein eout support domain_witnesses"
 using checked registered by (auto simp: list_all_iff)
 show ?thesis by (rule checked_checkpoint_fact_list_return[OF summary domain step holds])
qed

lemma checked_checkpoint_registered_inference:
 assumes constructors: "{N,Z,S}\<subseteq>C" and leaf: "L\<notin>{N,Z,S}"
 and arguments: "list_all (check_checkpoint_argument_registration C N Z S support) argument_registry"
 and ground: "list_all (check_checkpoint_ground_registration C N Z S support) ground_registry"
 and lists: "list_all (check_checkpoint_list_registration C L N Z S support) list_registry"
 and step: "check_checkpoint_inference N Z S (map checkpoint_argument_interface argument_registry)
 (map checkpoint_ground_interface ground_registry) (map checkpoint_list_interface list_registry) known witness dst"
 and known: "list_all (checkpoint_fact_holds C L N Z S (set support) old sigma) known"
 shows "checkpoint_fact_holds C L N Z S (set support) old sigma dst"
 by (rule checked_checkpoint_inference[OF constructors _ _ _ step known])
 (blast intro: checkpoint_registered_argument_return[OF arguments leaf] checkpoint_registered_ground_return[OF ground leaf] checkpoint_registered_list_return[OF lists])+

ML \<open>
val thms = @{thms checkpoint_registered_argument_return checkpoint_registered_ground_return checkpoint_registered_list_return checked_checkpoint_registered_inference};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted checkpoint registry" else ();
\<close>
end
