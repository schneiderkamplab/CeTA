"""Explicit stable numeric/guarded CPF6 grammar; validity is not certification."""
from copy import deepcopy
from lxml import etree as E

def extend(root):
    q=lambda s:'{http://www.w3.org/2001/XMLSchema}'+s
    def node(t,**kw): return E.Element(q(t),**kw)
    def el(n,t=None): return node('element',name=n,**({'type':t} if t else {}))
    def group(r): return node('group',ref=r)
    def wrap(n,cs):
        e=el(n);c=E.SubElement(e,q('complexType'));E.SubElement(c,q('sequence')).extend(cs);return e
    def many(n,c): c.set('minOccurs','0');c.set('maxOccurs','unbounded');return wrap(n,[c])
    def choice(n,cs):
        g=node('group',name=n);E.SubElement(g,q('choice')).extend(cs);root.append(g)
    term=lambda:group('lp6CutTerm')
    expr=lambda:group('lp6IntegerExpression')
    choice('lp6StableCoordinate',[wrap(n+'Coordinate',[]) for n in ['integer','upperBound','scaledBound','magnitudeBound']])
    choice('lp6StableEndpointExpression',[wrap(n+'Endpoint',[expr() if n in ['integer','integerBound'] else term()]) for n in ['integer','integerBound','bound','scaled','magnitude']])
    endpoint=lambda:wrap('endpoint',[el('coordinate','xs:string'),term(),group('lp6StableEndpointExpression')])
    choice('lp6StableKey',[el('integerKey','xs:string')]+[wrap(n+'Key',[term()]) for n in ['bound','scaled','magnitude']])
    conditions=[wrap('ignoredCondition',[]),wrap('integerCondition',[group('lp6PrologComparison'),expr(),expr()]),
        wrap('evaluatedIntegerCondition',[many('leaves',wrap('leaf',[el('var','xs:string'),term()])),expr()])]
    for name in ['floorOrder','magnitudeLess','magnitudeLeq','scaledEquality','magnitudeEvaluation','scaledEvaluation','scaledLess','scaledLeq']:
        conditions.append(wrap(name+'Condition',[term(),term()]))
    for name in ['magnitudeModulo','scaledModulo','moduloDescent','quotientDescent']:
        conditions.append(wrap(name+'Condition',[term(),term(),term()]))
    for name in ['magnitudeQuotientModulo','scaledQuotientModulo']:
        conditions.append(wrap(name+'Condition',[term(),term(),term(),term()]))
    for name in ['magnitudeLiteralLess','magnitudeLiteralLeq']:
        conditions.append(wrap(name+'Condition',[el('integer','xs:integer'),term()]))
    for name in ['squareIntegerLess','squareIntegerLeq']:conditions.append(wrap(name+'Condition',[expr(),expr()]))
    for name in ['squareUpper','upper']:conditions.append(wrap(name+'Condition',[expr(),term()]))
    conditions.extend([wrap('quotientMagnitudeUpperCondition',[expr(),term(),term()]),
        wrap('quotientUpperCondition',[expr(),term(),el('divisor','xs:integer')]),
        wrap('quotientCondition',[term(),el('divisor','xs:integer'),term()])])
    choice('lp6StableCondition',conditions)
    triple=lambda:wrap('triple',[wrap('head',[el('atom','lp6PrologSuccessAtom')]),many('prefix',el('atom','lp6PrologSuccessAtom')),
        wrap('call',[el('atom','lp6PrologSuccessAtom')]),many('guards',group('lp6PrologSuccessGuard')),many('observations',group('lp6PrologObservation'))])
    row=wrap('row',[el('facts','lp6PrologTyping'),many('ground',el('var','xs:string')),many('inputs',endpoint()),many('outputs',endpoint()),
        many('tests',group('lp6StableCondition')),many('bindings',wrap('binding',[group('lp6StableKey'),group('variable')])),el('formula','formula')])
    root.append(wrap('prologStableNumericComponent',[el('prologSuccessTransferContract','lp6PrologTransferContract'),
        many('coordinates',wrap('entry',[el('predicate','xs:string'),many('names',el('coordinate','xs:string'))])),
        many('coordinateModes',wrap('entry',[el('predicate','xs:string'),many('modes',group('lp6StableCoordinate'))])),
        many('locations',wrap('entry',[el('predicate','xs:string'),el('locationId','xs:string')])),many('triples',triple()),many('rows',row),
        el('lts','lts'),wrap('ltsTerminationProof',[group('ltsTerminationProof')])]))
    base=next(x for x in root if x.get('name')=='prologEstablishedFiniteSEGDependencyTriplesProof')
    result=deepcopy(base);result.set('name','prologEstablishedStableSEGGuardedProof');seq=result.find(q('complexType')+'/'+q('sequence'))
    for child in list(seq)[8:]:seq.remove(child)
    choice('lp6GuardedDescent',[wrap('guardedRegion',[many('connections',el('tripleConnection','lp6TripleConnection'))]),
        wrap('guardedSplit',[wrap('firstCall',[el('clauseReceipt','lp6TripleReceipt')]),wrap('secondCall',[el('clauseReceipt','lp6TripleReceipt')])])])
    seq.extend([many('observedTriples',triple()),many('guardedDescents',group('lp6GuardedDescent')),
        many('argumentProjection',wrap('entry',[el('predicate','xs:string'),many('positions',el('position','xs:nonNegativeInteger'))])),
        node('element',ref='prologStableNumericComponent')])
    root.append(result)
