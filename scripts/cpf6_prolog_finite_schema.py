"""Explicit finite Prolog grammar from LP_Prolog_Evaluation_XML and
LP_Prolog_Finite_Triple_XML. Schema validity is not certification."""
from copy import deepcopy
from lxml import etree as E

def extend(root):
    ns='http://www.w3.org/2001/XMLSchema'
    q=lambda s:'{'+ns+'}'+s
    def node(tag,**kw):return E.Element(q(tag),**kw)
    def el(name,typ=None):return node('element',name=name,**({'type':typ} if typ else {}))
    def group(ref):return node('group',ref=ref)
    def wrap(name,children):
     e=el(name);c=E.SubElement(e,q('complexType'));s=E.SubElement(c,q('sequence'));s.extend(children);return e
    def many(name,child):
     child.set('minOccurs','0');child.set('maxOccurs','unbounded');return wrap(name,[child])
    def find(name):return next(x for x in root if x.get('name')==name)
    def clone(old,new):
     e=deepcopy(find(old));e.set('name',new);root.append(e);return e
    rows=[('cut', 'primitiveOrdinary', [('?', 'CutReturnSyntax.action'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('integerTest', 'primitive.integerTest', [('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('link', 'link'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('termTest', 'primitive.termTest', [('predicate', 'scalar'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('link', 'link'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('groundDisequality', 'primitive.groundDisequality', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('link', 'link'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('disjunction', 'primitive.choice', [('?', 'term'), ('?', 'term'), ('leftGoals', 'goals'), ('rightGoals', 'goals'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('conditionalBranch', 'primitive.branch', [('?', 'term'), ('?', 'term'), ('?', 'term'), ('conditionGoals', 'goals'), ('thenGoals', 'goals'), ('elseGoals', 'goals'), ('commitScope', 'natural'), ('localScope', 'natural'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('opaqueProbe', 'primitive.probe', [('predicate', 'scalar'), ('targetPredicate', 'scalar'), ('arguments', 'itemsTerm'), ('commitScope', 'natural'), ('localScope', 'natural'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('rationalDisequality', 'primitive.rationalDisequality', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('link', 'link'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('identityTest', 'primitive.identity', [('predicate', 'scalar'), ('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('link', 'link'), ('yesTypes', 'facts'), ('noTypes', 'facts')]), ('equationRewrite', 'equationRewrite', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('clauseEquationRewrite', 'clauseEquationRewrite', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('index', 'natural'), ('scope', 'natural'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('finiteEvaluationError', 'evaluationError', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState')]), ('finiteComparisonError', 'comparisonError', [('predicate', 'scalar'), ('?', 'prologNumericComparison'), ('reversed', 'boolean'), ('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState')]), ('checkedFiniteComparison', 'primitive.comparison', [('finiteComparison', 'prologFiniteComparisonReceipt'), ('yesTypes', 'facts'), ('noTypes', 'facts'), ('errorTypes', 'facts')]), ('normalizedFiniteEvaluation', 'finiteIs', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('resultVariable', 'scalar'), ('link', 'link'), ('types', 'facts')]), ('normalizedFiniteLength', 'finiteLength', [('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('resultVariable', 'scalar'), ('link', 'link'), ('types', 'facts')]), ('subtractLibrary', 'subtractLibrary', [('?', 'term'), ('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('normalizedConstantEvaluation', 'constantIs', [('?', 'integerExpression'), ('?', 'term'), ('?', 'term'), ('goals', 'goals'), ('active', 'itemsTerm'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('trimBarriers', 'trim', [('returnState', 'CutReturnSyntax.returnState'), ('returnState', 'CutReturnSyntax.returnState'), ('link', 'link'), ('types', 'facts')]), ('parallelAlternatives', 'parallel', [('links', 'itemsLink'), ('linkTypes', 'factLists')]), ('refutedContext', 'refuted', [('index', 'natural'), ('refresh', 'natural'), ('bindings', 'bindings')])]
    # Exact existing finiteComparison record, reused by the typed action.
    comparison=deepcopy(find('lp6PrologContextAction').find('.//'+q('element')+'[@name="finiteComparison"]'))
    assert comparison is not None
    act=node('group',name='lp6PrologEvaluationAction');choice=E.SubElement(act,q('choice'))
    for tag,ctor,fields in rows:
     children=[]
     for name,parser in fields:
      if parser in ['term','CutReturnSyntax.action','prologNumericComparison','integerExpression']:
       children.append(group({'term':'lp6CutTerm','CutReturnSyntax.action':'lp6CutReturnAction','prologNumericComparison':'lp6PrologComparison','integerExpression':'lp6IntegerExpression'}[parser]))
      elif parser=='prologFiniteComparisonReceipt':children.append(deepcopy(comparison))
      elif parser in ['natural','scalar','boolean']:children.append(el(name,{'natural':'xs:nonNegativeInteger','scalar':'xs:string','boolean':'lp6Boolean'}[parser]))
      elif parser in ['goals','itemsTerm','facts']:children.append(many(name,group({'goals':'lp6CutGoal','itemsTerm':'lp6CutTerm','facts':'lp6PrologTransferFact'}[parser])))
      elif parser in ['CutReturnSyntax.returnState','link']:children.append(el(name,{'CutReturnSyntax.returnState':'lp6CutReturnState','link':'lp6CutLink'}[parser]))
      elif parser=='bindings':children.append(many(name,el('binding','lp6CutBinding')))
      elif parser=='itemsLink':children.append(many(name,el('link','lp6CutLink')))
      elif parser=='factLists':children.append(many(name,el('types','lp6PrologTyping')))
      else:raise ValueError(parser)
     choice.append(wrap(tag,children))
    root.append(act)
    control=clone('lp6PrologEstablishedControl','lp6PrologFiniteControl')
    for x in control.iter():
     if x.get('ref')=='lp6PrologContextAction':x.set('ref','lp6PrologEvaluationAction')
    region=clone('lp6PrologTripleRegion','lp6PrologFiniteRegion')
    x=region.find('.//'+q('element')+'[@name="prologContextControl"]');x.set('name','prologEvaluationControl');x.set('type','lp6PrologFiniteControl')
    integer=clone('lp6PrologSourceIntegerReturn','lp6PrologFiniteIntegerReturn')
    integer.find('.//'+q('element')+'[@name="sourceReturnModel"]').set('name','sourceFiniteReturnModel')
    ground=clone('lp6PrologSourceGroundReturn','lp6PrologFiniteGroundReturn');seq=ground.find(q('sequence'));old=seq[0];seq.remove(old);opts=node('choice');opts.extend([el('sourceFiniteReturnModel','lp6PrologSourceReturnModel'),el('sourceControlReturnModel','lp6PrologSourceReturnModel')]);seq.insert(0,opts)
    shape=node('complexType',name='lp6PrologFiniteShapeReturn');seq=E.SubElement(shape,q('sequence'))
    seq.extend([el('sourceGroundReturn','lp6PrologFiniteGroundReturn'),el('integerFacts','lp6PrologTyping'),many('integers',el('var','xs:string')),el('shapeFuel','xs:nonNegativeInteger'),many('grammar',el('shapeNode','lp6PrologShapeNode'))])
    blocked=many('nonproductivePredicates',wrap('signature',[wrap('symbol',[group('lp6CutSymbol')]),el('arity','xs:nonNegativeInteger')]));blocked.set('minOccurs','0');seq.append(blocked)
    seq.append(many('shapeContracts',wrap('shapeContract',[wrap('symbol',[group('lp6CutSymbol')]),many('inputs',group('lp6PrologReturnShape')),many('outputs',group('lp6PrologReturnShape'))])))
    for name in ['seeds','outputs']:seq.append(many(name,wrap('shapeFact',[wrap('shape',[group('lp6PrologReturnShape')]),el('var','xs:string')])))
    root.append(shape)
    comp=node('group',name='lp6PrologFiniteTripleComponent');choice=E.SubElement(comp,q('choice'));choice.append(el('prologTripleRegion','lp6PrologFiniteRegion'))
    for kind in ['', 'Integer','Ground','Shape']:
     children=[el('tripleSplit','lp6TripleSplit')]
     if kind:children.append(el('source'+kind+'Return','lp6PrologFinite'+kind+'Return'))
     children.extend([el('firstTypes','lp6PrologTyping'),el('secondTypes','lp6PrologTyping')]);choice.append(wrap('prologTriple'+kind+'Split',children))
    root.append(comp)
    for name in ['Dependency','Constructor']:
     e=clone('prologEstablishedSEG'+name+'TriplesProof','prologEstablishedFiniteSEG'+name+'TriplesProof')
     for x in e.iter():
      if x.get('ref')=='lp6PrologTripleComponent':x.set('ref','lp6PrologFiniteTripleComponent')

    root.append(wrap('prologEstablishedFiniteDirectProof',[
      many('signatures',wrap('signature',[el('predicate','xs:string'),el('arity','xs:nonNegativeInteger')])),
      el('prologEvaluationControl','lp6PrologFiniteControl'),el('freeKnowledge','lp6SegFreeSets')]))
