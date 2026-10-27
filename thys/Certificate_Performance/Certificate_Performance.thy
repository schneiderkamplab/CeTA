theory Certificate_Performance
  imports XML_Performance Rule_Bucket_Performance
begin

ML \<open>
val certificate_performance_theorems =
 [@{thm xml_do_prepare}, @{thm xml_do_or_prepare}, @{thm xml_dispatch_two_eq},
  @{thm normalize_text_eq}, @{thm normalized_nodes_code(2)},
  @{thm normalized_node_code}, @{thm normalized_doc_code},
  @{thm parse_xml_string_fused_code}, @{thm insert_values_indexed_code},
  @{thm delete_values_batched_code}];
val _ = if Thm_Deps.has_skip_proof certificate_performance_theorems
  orelse not (null (Thm_Deps.all_oracles certificate_performance_theorems))
  then error "Certificate performance refinements must be kernel checked without oracles"
  else ();
\<close>

end
