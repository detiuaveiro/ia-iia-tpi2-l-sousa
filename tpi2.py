# encoding: utf8

# Lucas Sousa
# 93019
# 93102 93248

from semantic_network import *
from bayes_net import *
from constraintsearch import *
from collections import OrderedDict
from functools import reduce
from collections import Counter
import json


class MyBN(BayesNet):

    # Conjuncoes
    def conjunctions(self, variaveis):
        """Código da aula prática do professor Diogo Gomes"""
        if len(variaveis) == 1:
            return [[(variaveis[0], True)], [(variaveis[0], False)]]

        l = []
        for c in self.conjunctions(variaveis[1:]):
            l.append([(variaveis[0], True)] + c)
            l.append([(variaveis[0], False)] + c)
        return l

    def individual_probabilities(self):
        """Código adaptado da aula prática do professor Diogo Gomes"""
        return {var: sum([self.jointProb([(var, True)] + c) for c in self.conjunctions([k for k in self.dependencies.keys() if k != var])]) for var in self.dependencies.keys()}


class MySemNet(SemanticNetwork):
    def __init__(self):
        SemanticNetwork.__init__(self)

    def translate_ontology(self):
        subs = {}
        
        # Gera o dicionário de tipo:entidades 
        for decl in self.declarations:
            if isinstance(decl.relation, Subtype):
                if decl.relation.entity2 not in subs:
                    subs[decl.relation.entity2] = set()
                subs[decl.relation.entity2].add(decl.relation.entity1)
                
        # gera a proposição lógica para os valores do dicionário
        return [f'Qx {"".join(map(lambda x: f"{x.capitalize()}(x) or ",sorted(vals)))[:-4]} => {key.capitalize()}(x)' for key, vals in sorted(subs.items())]

    def query_inherit(self, entity, assoc):
        is_member = lambda x: isinstance(x.relation, Member)
        is_assoc = lambda x: isinstance(x.relation, Association)
        is_subtype = lambda x: isinstance(x.relation, Subtype)
        member_or_sybtype = lambda x : is_member(x) or is_subtype(x)
        
        
        for inv in self.declarations:
            # se a assoc é uma associação inversa
            if is_assoc(inv) and inv.relation.entity2 == entity: 
                
                # Dá query local para sacar as associações locais da inversa 
                query_local = [decl for decl in self.query_local(
                    e2=entity, relname=inv.relation.name) if decl.relation.inverse]
                # Procura os pais 
                parents = [
                    decl.relation.entity1 for decl in self.declarations
                    if member_or_sybtype(decl)
                    and decl.relation.entity2 == entity]
                # chama resursivamente para os parents por causa da herança
                recursive = []
                for parent in parents:
                    recursive.extend(self.query_inherit(
                        parent, inv.relation.name))

                return query_local + recursive

        # caso não seja associação inversa
        # também saca as associações locais
        query_local = self.query_local(e1=entity, relname=assoc)
        
        # também calcula os pais
        parents = [decl.relation.entity2
                   for decl in self.declarations
                   if member_or_sybtype(decl)
                   and decl.relation.entity1 == entity]
        recursive = []
        # chama recursivamente para os pais da entity
        for p in parents:
            recursive.extend(self.query_inherit(p, assoc))

        return query_local + recursive

    def query(self, entity, relname):
        
        # lambdas auxiliares para não ter de estar sempre isinstance...
        is_member = lambda x: isinstance(x.relation, Member)
        is_assoc = lambda x: isinstance(x.relation, Association)
        is_subtype = lambda x: isinstance(x.relation, Subtype)
        member_or_sybtype = lambda x : is_member(x) or is_subtype(x)
        
        def filter_parents(query_local, parents):
            # Filtrar os parents
            for l in query_local:
                if is_assoc(l) and l.relation.cardinality == 'single' or member_or_sybtype(l):
                    parents = [
                        parent for parent in parents if parent.relation.name != l.relation.name]
            return parents
        
        def get_rels():
            # Sacar os singles
            singles = [l for l in query_local if is_assoc(l) and l.relation.cardinality == 'single']
            
            rels = [Counter([s.relation.entity2 for s in singles]).most_common(1)[0][0]] if len(singles) > 1 else []

            for parent in [p.relation.entity2 for p in parents]:
                rels.extend(self.query(parent, relname))
                
            return rels
        
        def most_common_properties():
            # sacar as properties mais comuns
            assoc_properties = [l.relation.assoc_properties() for l in self.query_local(relname=relname) if is_assoc(l)]
            counter = Counter(assoc_properties).most_common(1)
            return counter

        
        # assocciações locais
        query_local = [decl for decl in self.query_local(e1=entity, relname=relname)]

        # parents da entidade 
        parents = [decl for decl in self.declarations if member_or_sybtype(decl) and decl.relation.entity1 == entity]

        # filtrar os parents (cancelamento da herança) - basicamente cancela a herança para os parents que sejam single ou sejam membro ou subtipo
        parents = filter_parents(query_local, parents)
        
        # chama a função recursivamente para os parents que não foram cancelados
        rels = get_rels()
        
        # single mais comum
        most_common_properties = most_common_properties()
    
        return list(set(rels + [l.relation.entity2 for l in query_local if is_assoc(l) and l.relation.cardinality != 'single' and l.relation.assoc_properties() == most_common_properties[0][0] or member_or_sybtype(l)])) if len(most_common_properties) > 0 else list(set(rels + [l.relation.entity2 for l in query_local if is_assoc(l) and l.relation.cardinality != 'single' or member_or_sybtype(l)]))


class MyCS(ConstraintSearch):

    def search_all(self, domains=None, xpto=None):
        """Código adaptado do search do constraintseach.py """
        # Pode usar o argumento 'xpto' para passar mais
        # informação, caso precise
        #
        # IMPLEMENTAR AQUI
        if domains == None:
            domains = self.domains

        # se alguma variavel tiver lista de valores vazia, falha
        if any([lv == [] for lv in domains.values()]):
            return None

        # se nenhuma variavel tiver mais do que um valor possivel, sucesso
        if all([len(lv) == 1 for lv in list(domains.values())]):
            return {v: lv[0] for (v, lv) in domains.items()}

        solutions = []
        
        # continuação da pesquisa
        
        
        bt = xpto if xpto else set() # backtracking 

        for var in domains.keys():    
            if len(domains[var]) > 1:
                if var in bt:
                    continue
                bt.add(var)
                for val in domains[var]:

                    newdomains = dict(domains)
                    newdomains[var] = [val]

                    edges = [(v1, v2)
                             for (v1, v2) in self.constraints if v2 == var]

                    newdomains = self.propagate(newdomains, edges)
                    solution = self.search_all(newdomains, bt)
                    if solution and solution not in solutions:
                        solutions.append(solution)

        return solutions

    def propagate(self, domains, neighbours):
        """Código Aula prática do professor Diogo Gomes"""
        while neighbours != []:
            neighbour, var = neighbours.pop(0)
            values = []

            for val in domains[var]:
                constraint = self.constraints[neighbour, var]
                values = [x for x in domains[neighbour]
                          if constraint(neighbour, x, var, val)]
                if len(values) < len(domains[neighbour]):
                    domains[neighbour] = values

                    if not values:
                        return domains

                    # Extender nos abertos com neighbours dos neighbours
                    neighbours.extend(
                        [(nn, n) for nn, n in self.constraints if n == neighbour])

        return domains
