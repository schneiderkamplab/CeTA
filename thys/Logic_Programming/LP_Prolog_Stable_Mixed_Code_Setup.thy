theory LP_Prolog_Stable_Mixed_Code_Setup
 imports LP_Cut_Projected_XML LP_Prolog_Stable_Numeric_Code_Setup LP_Prolog_Guarded_Triples
begin

derive (no) cenum lp_cut_symbol

lemma lpp_structural_erasure_list_code [code_unfold]:
  "lpp_erase_triples (fst ` set D) =
    set (map (\<lambda>((h,ps,b,gs),os). (lpp_lift_atom h,map lpp_lift_atom ps,lpp_lift_atom b)) D)"
  unfolding lpp_erase_triples_def set_map image_image
  apply (rule image_cong)
  apply (rule refl)
  by (auto split: prod.splits)

end
