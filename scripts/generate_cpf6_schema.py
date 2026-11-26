#!/usr/bin/env python3
"""Inherit all CPF5 constructs, then add the currently implemented CPF6 forms."""
from pathlib import Path
import json
from lxml import etree as E
root=Path(__file__).resolve().parents[1]
ns={'xs':'http://www.w3.org/2001/XMLSchema'}
tree=E.parse(str(root/'xml/cpf5.xsd'));schema=tree.getroot();schema.set('version','6.0')
schema.find('xs:annotation/xs:documentation',ns).text='CPF 6 inherits CPF 5 and adds LP, LP with cut and Prolog extensions. The grammar covers the exposed source and residual proof forms; schema validity is separate from mathematical certification.'
schema.insert(1,E.Element('{'+ns['xs']+'}include',schemaLocation='cpf6-logic-programming.xsd'))
schema.insert(2,E.Element('{'+ns['xs']+'}include',schemaLocation='cpf6-cut.xsd'))
schema.insert(3,E.Element('{'+ns['xs']+'}include',schemaLocation='cpf6-prolog.xsd'))
schema.insert(4,E.Element('{'+ns['xs']+'}include',schemaLocation='cpf6-prolog-source.xsd'))
for old,added in [('higherOrderInput',['prologInput','logicProgramInput','logicProgramWithCutInput','logicProgramTriplesInput']),('ho-plain-pump',['prologEstablishedStableSEGGuardedProof','prologEstablishedFiniteDirectProof','lpDependencyTriplesConstructorProof','prologEstablishedSEGConstructorTriplesProof','prologEstablishedFiniteSEGConstructorTriplesProof','prologEstablishedFiniteSEGDependencyTriplesProof','prologContextComposedDependencyTriplesProof','prologContextDependencyTriplesProof','prologEstablishedSEGDependencyTriplesProof','prologStaticSEGProof','prologStaticNonterminationProof','prologStaticUniformRecursionProof','prologUndefinedQueryProof','prologVarReturnDependencyTriplesProof','prologModularReturnDependencyTriplesProof','prologTestSourceNonterminationProof','prologRationalSourceNonterminationProof','prologIntegerSourceNonterminationProof','prologGroundIntegerSourceNonterminationProof','lpCutUniformRecursionProof','lpCutProjectedGraphTerminationProof','lpCutReturnDependencyTriplesProof','lpCutReturnModuleDependencyTriplesProof','lpCutReturnComposedDependencyTriplesProof','lpCutReturnNestedDependencyTriplesProof','lpCutReturnConstructorGraphTerminationProof','lpCutReturnModuleConstructorGraphTerminationProof','lpCutReturnComposedConstructorGraphTerminationProof','lpCutReturnNestedConstructorGraphTerminationProof','lpDependencyTriplesPiDpProof','lpCutSEGDependencyTriplesProof','lpCutSEGTerminationProof','lpCutSEGFreeTerminationProof','lpCutSEGProjectedTerminationProof','lpCutGraphTerminationProof','lpCutConstructorGraphTerminationProof','lpCutMguConstructorGraphTerminationProof','lpCutSourceNonterminationProof','lpSymbolicGraphTerminationProof','lpInitialDependencyTriplesProof','lpFiniteTerminationProof','lpTocl09TerminationProof','lpTocl09SourceLoopProof','lpTocl09SourceTraceProof','lpTocl09SourceUnifyProof','lpTocl09SourceNeutralProof','lpTocl09RecurrentPairProof','lpTocl09AffineLoopProof','lpTocl09PatternLoopProof','lpTocl09PiDpTerminationProof','lpTocl09PiDpModeTerminationProof','lpTocl09ModeTerminationProof','lpTocl09SimplificationProof','lpTocl09SourceGraphProof','lpAnswerGraphTerminationProof','lpConstructorQDpTerminationProof'])]:
 matches=schema.xpath('.//xs:element[@ref=$ref]',namespaces=ns,ref=old)
 assert len(matches)==1,(old,len(matches))
 parent=matches[0].getparent()
 if old=='ho-plain-pump':added += [s['root'] for s in json.loads((root/'xml/cpf6-prolog-source-forms.json').read_text())]
 for name in added:E.SubElement(parent,'{'+ns['xs']+'}element',ref=name)
(root/'xml/cpf6.xsd').write_bytes(E.tostring(tree,pretty_print=True,xml_declaration=True,encoding='UTF-8'))
