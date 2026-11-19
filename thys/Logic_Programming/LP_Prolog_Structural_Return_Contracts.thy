theory LP_Prolog_Structural_Return_Contracts
 imports LP_Prolog_Runtime_Leaf_Invariant LP_Prolog_List_Leaf_Effect LP_Prolog_Structural_List_Observation
begin

text \<open>Coordinates distinguish the input and actual successful output.
These facts describe successful relations only; they assert no termination.
Finite trees and proper list spines are separate facts. Replacement conditions
are explicit premises, not implicit assumptions of an effect atom.\<close>

type_synonym lpp_return_coordinate = "bool * nat"
type_synonym lpp_return_replacements = nat

text \<open>Replacement identifiers refer to separately authenticated sets. This
also permits parameterized sets and all leaf-free values without imposing a
finite replacement-size bound. The registry and its proof dependencies belong
to the enclosing source or residual obligation.\<close>

datatype lpp_structural_return_atom =
 LPPRValueEq lpp_return_coordinate lpp_return_coordinate
 | LPPRTree lpp_return_coordinate
 | LPPRSpine lpp_return_coordinate
 | LPPRLeafFreeReplacements lpp_return_replacements
 | LPPRLeafEffect lpp_return_coordinate lpp_return_coordinate lpp_return_replacements
 | LPPRListEffect lpp_return_coordinate lpp_return_coordinate lpp_return_replacements
 | LPPRRigidity lpp_return_coordinate lpp_return_coordinate

definition lpp_return_value where
 "lpp_return_value before_env after_env coordinate =
 (if fst coordinate then before_env (snd coordinate) else after_env (snd coordinate))"

fun lpp_structural_return_holds where
 "lpp_structural_return_holds replacement_sets value (LPPRValueEq a b) = (value a=value b)"
| "lpp_structural_return_holds replacement_sets value (LPPRTree a) = lpp_finite_term (value a)"
| "lpp_structural_return_holds replacement_sets value (LPPRSpine a) = (\<exists>n. lpp_list_length (value a) n)"
| "lpp_structural_return_holds replacement_sets value (LPPRLeafFreeReplacements replacements) =
 (\<forall>t\<in>replacement_sets replacements. vars_term t={})"
| "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b replacements) =
 (\<exists>s. lpp_runtime_structure (value a) s \<and> lpp_runtime_leaf_effect (replacement_sets replacements) s (value b))"
| "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b replacements) =
 (\<exists>xs ys. lpp_runtime_structure (value a) (lpp_structural_argument_list xs) \<and>
 lpp_runtime_structure (value b) (lpp_structural_argument_list ys) \<and>
 list_all2 (lpp_leaf_effect (replacement_sets replacements)) xs ys)"
| "lpp_structural_return_holds replacement_sets value (LPPRRigidity a b) =
 (\<exists>s t. lpp_runtime_structure (value a) s \<and> lpp_runtime_structure (value b) t \<and>
 lpp_variable_leaf_count t \<le> lpp_variable_leaf_count s \<and>
 (lpp_variable_leaf_count t=lpp_variable_leaf_count s \<longrightarrow> s=t))"

lemma lpp_structural_leaf_return_rigid:
 assumes effect: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b replacements)"
 and leaf_free: "lpp_structural_return_holds replacement_sets value (LPPRLeafFreeReplacements replacements)"
 shows "lpp_structural_return_holds replacement_sets value (LPPRRigidity a b)"
proof -
 obtain s t where before: "lpp_runtime_structure (value a) s"
 and after: "lpp_runtime_structure (value b) t"
 and related: "lpp_leaf_effect (replacement_sets replacements) s t"
  using effect by (auto simp: lpp_runtime_leaf_effect_def)
 have ground: "vars_term u = {}" if "u\<in>replacement_sets replacements" for u
  using leaf_free that by simp
 have rank: "lpp_variable_leaf_count t \<le> lpp_variable_leaf_count s \<and>
  (lpp_variable_leaf_count t=lpp_variable_leaf_count s \<longrightarrow> s=t)"
  using lpp_ground_leaf_effect_rigidity[OF related ground] by blast
 show ?thesis using before after rank by auto
qed

lemma lpp_structural_list_return_leaf:
 assumes effect: "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b replacements)"
 shows "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b replacements)"
proof -
 obtain xs ys where before: "lpp_runtime_structure (value a) (lpp_structural_argument_list xs)"
 and after: "lpp_runtime_structure (value b) (lpp_structural_argument_list ys)"
 and pointwise: "list_all2 (lpp_leaf_effect (replacement_sets replacements)) xs ys"
  using effect by auto
 have related: "lpp_leaf_effect (replacement_sets replacements)
  (lpp_structural_argument_list xs) (lpp_structural_argument_list ys)"
  by (rule lpp_list_leaf_effect_exact[THEN iffD2])
     (rule exI[of _ ys], use pointwise in simp)
 show ?thesis unfolding lpp_structural_return_holds.simps lpp_runtime_leaf_effect_def
  by (rule exI[of _ "lpp_structural_argument_list xs"], rule conjI[OF before],
      rule exI[of _ "lpp_structural_argument_list ys"], rule conjI[OF after related])
qed

lemma lpp_structural_leaf_return_finite:
 assumes effect: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b replacements)"
 shows "lpp_structural_return_holds replacement_sets value (LPPRTree b)"
 using effect lpp_runtime_leaf_effect_finite by auto

lemma lpp_structural_leaf_return_list:
 assumes effect: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b replacements)"
 and spine: "lpp_structural_return_holds replacement_sets value (LPPRSpine a)"
 shows "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b replacements)"
proof -
 obtain s t where before: "lpp_runtime_structure (value a) s"
 and after: "lpp_runtime_structure (value b) t"
 and related: "lpp_leaf_effect (replacement_sets replacements) s t"
  using effect by (auto simp: lpp_runtime_leaf_effect_def)
 obtain n where length: "lpp_list_length (value a) n" using spine by auto
 have finite: "lpp_finite_term (value a)" by (rule lpp_runtime_structure_finite[OF before])
 obtain xs where list_before: "lpp_runtime_structure (value a) (lpp_structural_argument_list xs)"
  using lpp_finite_spine_structural_observation[OF length finite] by blast
 have shape: "s=lpp_structural_argument_list xs"
  by (rule lpp_runtime_structure_unique[OF before list_before])
 obtain ys where tail: "t=lpp_structural_argument_list ys"
 and pointwise: "list_all2 (lpp_leaf_effect (replacement_sets replacements)) xs ys"
  using related by (auto simp: shape lpp_list_leaf_effect_exact)
 show ?thesis using list_before after pointwise by (auto simp: tail)
qed

lemma lpp_structural_list_return_spines:
 assumes effect: "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b replacements)"
 shows "\<exists>n. lpp_list_length (value a) n \<and> lpp_list_length (value b) n"
proof -
 obtain xs ys where before: "lpp_runtime_structure (value a) (lpp_structural_argument_list xs)"
 and after: "lpp_runtime_structure (value b) (lpp_structural_argument_list ys)"
 and pointwise: "list_all2 (lpp_leaf_effect (replacement_sets replacements)) xs ys"
  using effect by auto
 show ?thesis using lpp_runtime_list_observation_length[OF before]
  lpp_runtime_list_observation_length[OF after] list_all2_lengthD[OF pointwise] by auto
qed

datatype lpp_structural_return_rule = LPPRKnown nat
 | LPPRDeriveRigidity nat nat | LPPRListAsLeaf nat | LPPRDeriveFinite nat
 | LPPRTransportTree nat nat | LPPRListSpine nat bool | LPPRLeafAsList nat nat

fun lpp_structural_return_infer where
 "lpp_structural_return_infer known (LPPRKnown i) =
 (if i<length known then Some (known!i) else None)"
| "lpp_structural_return_infer known (LPPRDeriveRigidity i j) =
 (if i<length known \<and> j<length known then
 (case known!i of LPPRLeafEffect a b replacements \<Rightarrow>
 if known!j=LPPRLeafFreeReplacements replacements then Some (LPPRRigidity a b) else None
 | _ \<Rightarrow> None) else None)"
| "lpp_structural_return_infer known (LPPRListAsLeaf i) =
 (if i<length known then (case known!i of LPPRListEffect a b replacements \<Rightarrow>
 Some (LPPRLeafEffect a b replacements) | _ \<Rightarrow> None) else None)"
| "lpp_structural_return_infer known (LPPRDeriveFinite i) =
 (if i<length known then (case known!i of LPPRLeafEffect a b replacements \<Rightarrow>
 Some (LPPRTree b) | _ \<Rightarrow> None) else None)"
| "lpp_structural_return_infer known (LPPRTransportTree i j) =
 (if i<length known \<and> j<length known then (case known!i of LPPRValueEq a b \<Rightarrow>
 if known!j=LPPRTree a then Some (LPPRTree b) else None | _ \<Rightarrow> None) else None)"
| "lpp_structural_return_infer known (LPPRListSpine i before) =
 (if i<length known then (case known!i of LPPRListEffect a b replacements \<Rightarrow>
 Some (LPPRSpine (if before then a else b)) | _ \<Rightarrow> None) else None)"
| "lpp_structural_return_infer known (LPPRLeafAsList i j) =
 (if i<length known \<and> j<length known then (case known!i of LPPRLeafEffect a b replacements \<Rightarrow>
 if known!j=LPPRSpine a then Some (LPPRListEffect a b replacements) else None
 | _ \<Rightarrow> None) else None)"

lemma lpp_structural_return_infer_sound:
 assumes known: "list_all (lpp_structural_return_holds replacement_sets value) facts"
 and checked: "lpp_structural_return_infer facts receipt=Some result_atom"
 shows "lpp_structural_return_holds replacement_sets value result_atom"
proof -
 have fact: "lpp_structural_return_holds replacement_sets value (facts!i)"
  if "i<length facts" for i
  using known that by (simp add: list_all_length)
 show ?thesis
 proof (cases receipt)
  case (LPPRKnown i)
  then show ?thesis using checked fact by (auto split: if_splits)
 next
  case (LPPRDeriveRigidity i j)
  then obtain a b r where bounds: "i<length facts" "j<length facts"
   and effect: "facts!i=LPPRLeafEffect a b r"
   and ground: "facts!j=LPPRLeafFreeReplacements r"
   and result: "result_atom=LPPRRigidity a b"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  have e: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b r)"
   using fact[OF bounds(1)] by (simp only: effect)
  have g: "lpp_structural_return_holds replacement_sets value (LPPRLeafFreeReplacements r)"
   using fact[OF bounds(2)] by (simp only: ground)
  show ?thesis unfolding result by (rule lpp_structural_leaf_return_rigid[OF e g])
 next
  case (LPPRListAsLeaf i)
  then obtain a b r where bound: "i<length facts"
   and effect: "facts!i=LPPRListEffect a b r"
   and result: "result_atom=LPPRLeafEffect a b r"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  have e: "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b r)"
   using fact[OF bound] by (simp only: effect)
  show ?thesis unfolding result by (rule lpp_structural_list_return_leaf[OF e])
 next
  case (LPPRDeriveFinite i)
  then obtain a b r where bound: "i<length facts"
   and effect: "facts!i=LPPRLeafEffect a b r"
   and result: "result_atom=LPPRTree b"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  have e: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b r)"
   using fact[OF bound] by (simp only: effect)
  show ?thesis unfolding result by (rule lpp_structural_leaf_return_finite[OF e])
 next
  case (LPPRTransportTree i j)
  then obtain a b where bounds: "i<length facts" "j<length facts"
   and equal: "facts!i=LPPRValueEq a b" and tree: "facts!j=LPPRTree a"
   and result: "result_atom=LPPRTree b"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  show ?thesis using fact[OF bounds(1)] fact[OF bounds(2)]
   by (simp add: equal tree result)
 next
  case (LPPRListSpine i before)
  then obtain a b r where bound: "i<length facts"
   and effect: "facts!i=LPPRListEffect a b r"
   and result: "result_atom=LPPRSpine (if before then a else b)"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  have e: "lpp_structural_return_holds replacement_sets value (LPPRListEffect a b r)"
   using fact[OF bound] by (simp only: effect)
  show ?thesis using lpp_structural_list_return_spines[OF e]
   by (auto simp: result split: if_splits)
 next
  case (LPPRLeafAsList i j)
  then obtain a b r where bounds: "i<length facts" "j<length facts"
   and effect: "facts!i=LPPRLeafEffect a b r"
   and spine: "facts!j=LPPRSpine a"
   and result: "result_atom=LPPRListEffect a b r"
   using checked by (auto split: if_splits lpp_structural_return_atom.splits)
  have e: "lpp_structural_return_holds replacement_sets value (LPPRLeafEffect a b r)"
   using fact[OF bounds(1)] by (simp only: effect)
  have s: "lpp_structural_return_holds replacement_sets value (LPPRSpine a)"
   using fact[OF bounds(2)] by (simp only: spine)
  show ?thesis unfolding result by (rule lpp_structural_leaf_return_list[OF e s])
 qed
qed

fun lpp_structural_return_map where
 "lpp_structural_return_map coordinate_map (LPPRValueEq a b) = LPPRValueEq (coordinate_map a) (coordinate_map b)"
| "lpp_structural_return_map coordinate_map (LPPRTree a) = LPPRTree (coordinate_map a)"
| "lpp_structural_return_map coordinate_map (LPPRSpine a) = LPPRSpine (coordinate_map a)"
| "lpp_structural_return_map coordinate_map (LPPRLeafFreeReplacements replacements) = LPPRLeafFreeReplacements replacements"
| "lpp_structural_return_map coordinate_map (LPPRLeafEffect a b replacements) = LPPRLeafEffect (coordinate_map a) (coordinate_map b) replacements"
| "lpp_structural_return_map coordinate_map (LPPRListEffect a b replacements) = LPPRListEffect (coordinate_map a) (coordinate_map b) replacements"
| "lpp_structural_return_map coordinate_map (LPPRRigidity a b) = LPPRRigidity (coordinate_map a) (coordinate_map b)"

lemma lpp_structural_return_map_sound:
 "lpp_structural_return_holds replacement_sets value (lpp_structural_return_map coordinate_map atom) =
 lpp_structural_return_holds replacement_sets (value \<circ> coordinate_map) atom"
 by (cases atom) auto

fun lpp_structural_return_coordinates where
 "lpp_structural_return_coordinates (LPPRValueEq a b) = [a,b]"
| "lpp_structural_return_coordinates (LPPRTree a) = [a]"
| "lpp_structural_return_coordinates (LPPRSpine a) = [a]"
| "lpp_structural_return_coordinates (LPPRLeafFreeReplacements r) = []"
| "lpp_structural_return_coordinates (LPPRLeafEffect a b r) = [a,b]"
| "lpp_structural_return_coordinates (LPPRListEffect a b r) = [a,b]"
| "lpp_structural_return_coordinates (LPPRRigidity a b) = [a,b]"

fun lpp_structural_return_registry_indices where
 "lpp_structural_return_registry_indices (LPPRLeafFreeReplacements r) = [r]"
| "lpp_structural_return_registry_indices (LPPRLeafEffect a b r) = [r]"
| "lpp_structural_return_registry_indices (LPPRListEffect a b r) = [r]"
| "lpp_structural_return_registry_indices _ = []"

definition lpp_structural_return_wellformed where
 "lpp_structural_return_wellformed input_arity output_arity registry_size atom =
 (list_all (\<lambda>coordinate. snd coordinate < (if fst coordinate then input_arity else output_arity))
 (lpp_structural_return_coordinates atom) \<and>
 list_all (\<lambda>i. i<registry_size) (lpp_structural_return_registry_indices atom))"

fun lpp_structural_return_derive where
 "lpp_structural_return_derive facts [] = Some facts"
| "lpp_structural_return_derive facts (receipt#receipts) =
 (case lpp_structural_return_infer facts receipt of None \<Rightarrow> None
 | Some atom \<Rightarrow> lpp_structural_return_derive (atom#facts) receipts)"

lemma lpp_structural_return_derive_sound:
 assumes known: "list_all (lpp_structural_return_holds replacement_sets value) facts"
 and checked: "lpp_structural_return_derive facts receipts=Some results"
 shows "list_all (lpp_structural_return_holds replacement_sets value) results"
 using known checked
proof (induct receipts arbitrary: facts)
 case Nil then show ?case by simp
next
 case (Cons receipt receipts)
 obtain atom where inferred: "lpp_structural_return_infer facts receipt=Some atom"
 and tail: "lpp_structural_return_derive (atom#facts) receipts=Some results"
  using Cons.prems(2) by (auto split: option.splits)
 have atom: "lpp_structural_return_holds replacement_sets value atom"
  by (rule lpp_structural_return_infer_sound[OF Cons.prems(1) inferred])
 have initialized: "list_all (lpp_structural_return_holds replacement_sets value) (atom#facts)"
  using atom Cons.prems(1) by simp
 show ?case by (rule Cons.hyps[OF initialized tail])
qed

datatype lpp_structural_return_contract = LPPRContract nat nat nat
 "lpp_structural_return_atom list" "lpp_structural_return_atom list"

fun lpp_structural_return_contract_holds where
 "lpp_structural_return_contract_holds replacement_sets value (LPPRContract input_arity output_arity registry_size return_conditions return_conclusions) =
 (list_all (lpp_structural_return_holds replacement_sets value) return_conditions \<longrightarrow>
 list_all (lpp_structural_return_holds replacement_sets value) return_conclusions)"

fun lpp_check_structural_return_contract where
 "lpp_check_structural_return_contract (LPPRContract input_arity output_arity registry_size return_conditions return_conclusions) receipts =
 (list_all (lpp_structural_return_wellformed input_arity output_arity registry_size) (return_conditions@return_conclusions) \<and>
 (case lpp_structural_return_derive return_conditions receipts of None \<Rightarrow> False
 | Some facts \<Rightarrow> list_all (\<lambda>atom. atom\<in>set facts) return_conclusions))"

lemma lpp_check_structural_return_contract_sound:
 assumes checked: "lpp_check_structural_return_contract contract_data receipts"
 shows "lpp_structural_return_contract_holds replacement_sets value contract_data"
proof (cases contract_data)
 case (LPPRContract input_arity output_arity registry_size return_conditions return_conclusions)
 obtain facts where derived: "lpp_structural_return_derive return_conditions receipts=Some facts"
 and selected: "list_all (\<lambda>atom. atom\<in>set facts) return_conclusions"
  using checked by (auto simp: LPPRContract split: option.splits)
 show ?thesis unfolding LPPRContract lpp_structural_return_contract_holds.simps
 proof
  assume initialized: "list_all (lpp_structural_return_holds replacement_sets value) return_conditions"
  have all: "list_all (lpp_structural_return_holds replacement_sets value) facts"
   by (rule lpp_structural_return_derive_sound[OF initialized derived])
  show "list_all (lpp_structural_return_holds replacement_sets value) return_conclusions"
   using selected all by (auto simp: list_all_iff)
 qed
qed

fun lpp_structural_return_contract_map where
 "lpp_structural_return_contract_map coordinate_map input_arity output_arity
 (LPPRContract old_input_arity old_output_arity registry_size return_conditions return_conclusions) =
 LPPRContract input_arity output_arity registry_size
 (map (lpp_structural_return_map coordinate_map) return_conditions)
 (map (lpp_structural_return_map coordinate_map) return_conclusions)"

text \<open>Transport moves every premise along with its conclusion. The
enclosing boundary checker must establish the coordinate correspondence;
choosing a map is not itself evidence about successful execution.\<close>

lemma lpp_structural_return_contract_map_sound:
 "lpp_structural_return_contract_holds replacement_sets value
 (lpp_structural_return_contract_map coordinate_map input_arity output_arity contract_data) =
 lpp_structural_return_contract_holds replacement_sets (value \<circ> coordinate_map) contract_data"
 by (cases contract_data)
    (simp add: list_all_iff lpp_structural_return_map_sound)

definition lpp_return_coordinate_map where
 "lpp_return_coordinate_map input_map output_map coordinate =
 (if fst coordinate then input_map else output_map)!snd coordinate"

fun lpp_check_structural_return_transport where
 "lpp_check_structural_return_transport
 (LPPRContract old_input old_output registry_size return_conditions return_conclusions)
 input_map output_map (LPPRContract new_input new_output new_registry new_conditions new_conclusions) =
 (length input_map = old_input \<and> length output_map = old_output \<and>
 list_all (\<lambda>c. snd c < (if fst c then new_input else new_output)) (input_map@output_map) \<and>
 list_all (lpp_structural_return_wellformed old_input old_output registry_size) (return_conditions@return_conclusions) \<and>
 LPPRContract new_input new_output new_registry new_conditions new_conclusions =
 lpp_structural_return_contract_map (lpp_return_coordinate_map input_map output_map) new_input new_output
 (LPPRContract old_input old_output registry_size return_conditions return_conclusions))"

lemma lpp_check_structural_return_transport_sound:
 assumes checked: "lpp_check_structural_return_transport source_contract input_map output_map target_contract"
 and valid_source: "lpp_structural_return_contract_holds replacement_sets
 (value \<circ> lpp_return_coordinate_map input_map output_map) source_contract"
 shows "lpp_structural_return_contract_holds replacement_sets value target_contract"
 using checked valid_source
 by (cases source_contract; cases target_contract)
    (auto simp: list_all_iff lpp_structural_return_map_sound)

text \<open>The caller supplies only facts checked for this frame. In particular,
a successful active frame cannot initialize a saved failure alternative.\<close>

ML \<open>
val checked = @{thms lpp_structural_return_infer_sound lpp_structural_return_map_sound
 lpp_structural_return_derive_sound lpp_check_structural_return_contract_sound
 lpp_structural_return_contract_map_sound lpp_check_structural_return_transport_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural return contracts" else ();
\<close>
end
