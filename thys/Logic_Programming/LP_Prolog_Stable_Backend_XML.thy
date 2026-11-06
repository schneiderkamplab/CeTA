theory LP_Prolog_Stable_Backend_XML
 imports LP_Prolog_Stable_Relational_XML LP_Dependency_Triple_XML
begin

definition lpp_structural_backend_parser where
  "lpp_structural_backend_parser = XMLdo (STR ''structuralBackend'') {
    entries\<leftarrow>lpp_structural_entries_parser;
    coverage\<leftarrow>lpp_structural_coverage_parser;
    source_rows\<leftarrow>xml_many (STR ''triples'') (XMLdo (STR ''triple'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      ps\<leftarrow>xml_many (STR ''prefix'') lpc_atom_parser id;
      b\<leftarrow>xml_singleton (STR ''call'') lpc_atom_parser id;
      xml_return (h,ps,b)}) id;
    predicates\<leftarrow>lpc_seg_encoding_parser (STR ''predicates'');
    constructors\<leftarrow>lpc_seg_encoding_parser (STR ''constructors'');
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (entries,coverage,source_rows,predicates,constructors,child)}"

definition lpp_decode_structural_backend where
  "lpp_decode_structural_backend P data = (case data of
    (entries,coverage,source_rows,predicates,constructors,
      (D,Q,outs,fallback,dnames,pnames,marks,filters,(q,n,positions),labs,proofs)) \<Rightarrow>
    (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
      if D=lp_roles_triples p d source_rows \<and> Q=lp_roles_program p d (lpp_erase_success P) \<and>
        list_ex (\<lambda>(name,arity,ground). p (LPCUser name)=q \<and> arity=n \<and> ground = positions) entries
      then Some (entries,coverage,source_rows,predicates,constructors,outs,fallback,dnames,pnames,marks,filters,labs,proofs)
      else None))"

definition lpp_numeric_backend_parser where
  "lpp_numeric_backend_parser = XMLdo (STR ''numericBackend'') {
    projections\<leftarrow>xml_many (STR ''argumentProjection'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate'');
      positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
      xml_return (p,positions)}) id;
    child\<leftarrow>lpp_stable_numeric_component_parser;
    xml_return (projections,child)}"

definition lpp_decode_numeric_backend where
  "lpp_decode_numeric_backend transfer source_rows data = (case data of
    (projections,(child_transfer,coordinates,coordinate_modes,locations,child_rows,row_data,system,child_proof)) \<Rightarrow>
      (let positions=lpp_numeric_coordinate_lookup projections in
        if child_transfer=transfer \<and>
          distinct (map fst projections) \<and> distinct (map fst coordinates) \<and>
          distinct (map fst coordinate_modes) \<and> distinct (map fst locations) \<and>
          list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst projections) \<and>
            fst b\<in>set (map fst projections)) source_rows \<and>
          child_rows=map (lpp_project_observed_triple positions) source_rows
        then Some (positions,lpp_numeric_coordinate_lookup coordinates,
          lpp_numeric_coordinate_lookup coordinate_modes,lpp_numeric_location_lookup locations,system,row_data,child_proof)
        else None))"

text \<open>Decoding checks the parsed child subject and metadata. Only the
backend checker may establish termination, including all entry queries and
all numeric transition entries.\<close>
end
