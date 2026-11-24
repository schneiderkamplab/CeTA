#!/usr/bin/env python3
"""Generate a data grammar for parser front ends, never mathematical checking code."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
g=json.loads((root/'src/Haskell/Ceta/Input/cpf4-native.json').read_text())
q=lambda x:json.dumps(x)
def fields(fs):return '['+','.join('('+q(n)+','+typ(t)+')' for n,t in fs)+']'
def typ(t):
 if isinstance(t,str):return {'natural':'Natural','boolean':'Boolean','string':'StringValue'}.get(t,'Ref '+q(t))
 if 'list' in t:return 'ListOf ('+typ(t['list'])+')'
 if 'tuple' in t:return 'TupleOf '+fields(t['tuple'])
 return 'Choice ['+','.join('('+q(k)+','+fields(v)+')' for k,v in t['sum'].items())+']'
out='''-- Generated from cpf4-native.json by scripts/generate_cpf4_native_grammar.py.
-- Data syntax only; acceptance remains in the Isabelle-generated checkers.
module Ceta.Input.Cpf4Grammar where

data Schema = Natural | Boolean | StringValue | Ref String | ListOf Schema
            | TupleOf [(String,Schema)] | Choice [(String,[(String,Schema)])]
data Root = Root { category :: String, wire :: String, fields :: [(String,Schema)], inputs :: [String], yes :: Bool }
types :: [(String,Schema)]
types = ['''+','.join('('+q(k)+','+typ(v)+')' for k,v in g['types'].items())+']\nroots :: [(String,Root)]\nroots = ['+','.join('('+q(k)+',Root '+q(v['category'])+' '+q(v['wire'])+' '+fields(v['fields'])+' '+q(v['inputs'])+' '+str(v['yes'])+')' for k,v in g['roots'].items())+']\n'
(root/'src/Haskell/Ceta/Input/Cpf4Grammar.hs').write_text(out)
