theory LP_Prolog_Separation_Link_XML
 imports LP_Prolog_Separation_State_XML
begin

text \<open>Exact per-node outgoing links. Each uses the common link parser;
source actions, context transport and residual coverage must still be checked.\<close>

definition lpp_separation_links_parser where
 "lpp_separation_links_parser = xml_many (STR ''separationLinks'')
    (xml_many (STR ''links'') lpc_link_parser id) id"

definition lpp_decode_separation_links where
 "lpp_decode_separation_links xml = parse_xml_string lpp_separation_links_parser xml"

end
