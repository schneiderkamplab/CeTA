theory DP_Checkpoint_Annotation_Syntax
 imports DP_Checkpoint_Transport DP_Checkpoint_Forest_Rank
begin

text \<open>Finite annotation syntax. Each clause is a separate alternative;
conjunction combines facts only within that alternative. Pending calls retain
an actual support derivation, never a promise of termination or success.\<close>
datatype 'f checkpoint_atom =
    CP_Exact nat
  | CP_Split nat nat
  | CP_Prefix nat
  | CP_Strict nat
  | CP_Guard nat
  | CP_Arguments 'f nat
  | CP_Ground 'f nat nat
  | CP_List 'f nat nat

primrec checkpoint_atom_coordinates where
 "checkpoint_atom_coordinates (CP_Exact i) = [i]"
| "checkpoint_atom_coordinates (CP_Split i j) = [i,j]"
| "checkpoint_atom_coordinates (CP_Prefix i) = [i]"
| "checkpoint_atom_coordinates (CP_Strict i) = [i]"
| "checkpoint_atom_coordinates (CP_Guard i) = [i]"
| "checkpoint_atom_coordinates (CP_Arguments f i) = [i]"
| "checkpoint_atom_coordinates (CP_Ground f i j) = [i,j]"
| "checkpoint_atom_coordinates (CP_List f i j) = [i,j]"

definition checkpoint_atom_bounded where
 "checkpoint_atom_bounded n a = list_all (\<lambda>i. i<n) (checkpoint_atom_coordinates a)"

definition checkpoint_guard where
 "checkpoint_guard C L p = (vars_term (checkpoint_skeleton C p)={} \<and>
 L\<notin>funs_term (checkpoint_skeleton C p))"

definition checkpoint_pending_arguments where
 "checkpoint_pending_arguments C N R f old call = (\<exists>children tail.
 old=Fun N [checkpoint_skeleton C children]#tail \<and>
 (Fun f [children],call)\<in>(Trs.rstep R)\<^sup>*)"

definition checkpoint_pending_ground where
 "checkpoint_pending_ground C R f call param = (\<exists>initial.
 checkpoint_skeleton C initial=checkpoint_skeleton C param \<and>
 (Fun f [initial],call)\<in>(Trs.rstep R)\<^sup>*)"

definition checkpoint_pending_list where
 "checkpoint_pending_list C L N Z S R f old call head = (\<exists>initial param.
 old=checkpoint_skeleton C head#checkpoint_forest N Z S (checkpoint_skeleton C initial) \<and>
 checkpoint_guard C L param \<and> (Fun f [initial,param],call)\<in>(Trs.rstep R)\<^sup>*)"

definition checkpoint_forest_less where
 "checkpoint_forest_less L xs old = (
 (((Inr (map (checkpoint_rank_view L) xs))::('f+unit,unit) term + ('f+unit,unit) term list),
 Inr (map (checkpoint_rank_view L) old))\<in>lpp_forest_call_order)"

primrec checkpoint_atom_holds where
 "checkpoint_atom_holds C L N Z S R old (CP_Exact i) ts =
 (old=checkpoint_forest N Z S (checkpoint_skeleton C (ts!i)))"
| "checkpoint_atom_holds C L N Z S R old (CP_Split i j) ts =
 (old=checkpoint_skeleton C (ts!i)#checkpoint_forest N Z S (checkpoint_skeleton C (ts!j)))"
| "checkpoint_atom_holds C L N Z S R old (CP_Prefix i) ts =
 (\<exists>tail. old=checkpoint_skeleton C (ts!i)#tail)"
| "checkpoint_atom_holds C L N Z S R old (CP_Strict i) ts =
 checkpoint_forest_less L (checkpoint_forest N Z S (checkpoint_skeleton C (ts!i))) old"
| "checkpoint_atom_holds C L N Z S R old (CP_Guard i) ts = checkpoint_guard C L (ts!i)"
| "checkpoint_atom_holds C L N Z S R old (CP_Arguments f i) ts =
 checkpoint_pending_arguments C N R f old (ts!i)"
| "checkpoint_atom_holds C L N Z S R old (CP_Ground f i j) ts =
 checkpoint_pending_ground C R f (ts!i) (ts!j)"
| "checkpoint_atom_holds C L N Z S R old (CP_List f i j) ts =
 checkpoint_pending_list C L N Z S R f old (ts!i) (ts!j)"

end
