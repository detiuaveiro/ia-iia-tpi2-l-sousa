# encoding: utf8

from semantic_network import *
from bayes_net import *
from constraintsearch import *
from collections import OrderedDict
from functools import reduce
from collections import Counter
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
        for d in self.declarations:
            if isinstance(d.relation, Subtype):
                if d.relation.entity2 not in subs:
                    subs[d.relation.entity2] = set()
                subs[d.relation.entity2].add(d.relation.entity1)

        return [f'Qx {"".join(map(lambda x: f"{x.capitalize()}(x) or ",sorted(vals)))[:-4]} => {key.capitalize()}(x)' for key, vals in OrderedDict(sorted(subs.items())).items()]

    def query_inherit(self, entity, assoc):
        is_inv = [d for d in self.declarations if isinstance(
            d.relation, Association) if d.relation.entity2 == entity]
        if is_inv:
            for i in is_inv:
                local = [d for d in self.query_local(
                    e2=entity, relname=i.relation.name) if d.relation.inverse != None]
                pais = [d.relation.entity1 for d in self.declarations if isinstance(
                    d.relation, (Member, Subtype)) if d.relation.entity2 == entity]
                res = []
                for p in pais:
                    res += self.query_inherit(p, i.relation.name)
        else:
            local = self.query_local(e1=entity, relname=assoc)
            pais = [d.relation.entity2 for d in self.declarations if isinstance(
                d.relation, (Member, Subtype)) if d.relation.entity1 == entity]
            res = []
            for p in pais:
                res += self.query_inherit(p, assoc)
        return local + res

    def query(self, entity, relname):
        local = [d for d in self.query_local(e1=entity, relname=relname)]
        pais = [d for d in self.declarations if isinstance(
            d.relation, (Member, Subtype)) and d.relation.entity1 == entity]
        res = []
        for l in local:
            if isinstance(l.relation, Association) and l.relation.cardinality == 'single' or isinstance(l.relation, (Member, Subtype)):
                pais = [d for d in pais if d.relation.name != l.relation.name]
        singles = [l for l in local if isinstance(l.relation, Association) and l.relation.cardinality == 'single']
        assoc_properties = [l.relation.assoc_properties() for l in local if isinstance(l.relation, Association)]
        if len(singles) > 1:
            res += [Counter([s.relation.entity2 for s in singles]).most_common(1)[0][0]]
        for p in [d.relation.entity2 for d in pais]:
            res += self.query(p, relname)
        c = Counter(assoc_properties).most_common(1)
        if len(c) > 0:
            c = c[0][0]
            return list(set(res + [l.relation.entity2 for l in local if isinstance(l.relation, Association) and l.relation.cardinality != 'single' and l.relation.assoc_properties() == c or isinstance(l.relation, (Subtype, Member))]))
        else:
            return list(set(res + [l.relation.entity2 for l in local if isinstance(l.relation, Association) and l.relation.cardinality != 'single' or isinstance(l.relation, (Subtype, Member))]))


class MyCS(ConstraintSearch):

    def search_all(self, domains=None, xpto=None):
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

        for var in domains.keys():
            if len(domains[var]) > 1:

                for val in domains[var]:
                    newdomains = dict(domains)
                    newdomains[var] = [val]
                    edges = [(v1, v2) for (v1, v2) in self.constraints if v2 == var]
    
                    newdomains = self.propagate(newdomains, edges)
                    solution = self.search(newdomains)
                    if solution and solution not in solutions:
                        solutions.append(solution)

        return solutions

    def propagate(self, domains, neighbours):
        while neighbours != []:
            neighbour, var = neighbours.pop(0)
            values = []
            for val in domains[var]:
                constraint = self.constraints[neighbour, var]
                values = [x for x in domains[neighbour] if constraint(neighbour, x, var, val)]
                if len(values) < len(domains[neighbour]):
                    domains[neighbour] = values
                    
                    #EXTRA
                    if not values: return domains
                    
                    
                    # Extender nos abertos com neighbours dos neighbours
                    neighbours.extend(
                        [(nn, n) for nn, n in self.constraints if n == neighbour])

        return domains
