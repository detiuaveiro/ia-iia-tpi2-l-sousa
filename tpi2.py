#encoding: utf8

from semantic_network import *
from bayes_net import *
from constraintsearch import *


class MyBN(BayesNet):

    def individual_probabilities(self):
        # IMPLEMENTAR AQUI
        pass


class MySemNet(SemanticNetwork):
    def __init__(self):
        SemanticNetwork.__init__(self)

    def translate_ontology(self):
        #IMPLEMENTAR AQUI
        pass

    def query_inherit(self,entity,assoc):
        # IMPLEMENTAR AQUI
        pass

    def query(self,entity,relname):
        #IMPLEMENTAR AQUI
        pass

class MyCS(ConstraintSearch):

    def search_all(self,domains=None,xpto=None):
        # Pode usar o argumento 'xpto' para passar mais
        # informação, caso precise
        #
        # IMPLEMENTAR AQUI
        pass


