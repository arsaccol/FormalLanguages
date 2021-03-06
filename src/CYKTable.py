import src.Grammar
from src.ChomskyNormalForm import ChomskyNormalForm
from copy import deepcopy
from pprint import pprint


class CYKTable:
    def __init__(self, grammar, word):
        self.word = word
        self.grammar = grammar
        self.table = None
        self.accepts = self.build_table()

    def init_table(self):
        self.table = dict()
        for r in range(len(self.word)):
            for s in range(len(self.word) - r):
                self.table[(r, s)] = set()

    def print_table(self):
        rows = []
        for s in reversed(range(len(self.word))):
            rows.append([self.table[(r, s)] for r in range(len(self.word) - s)])
            # print('Row', s,':',row)

        for row in rows:
            print(row)

    def build_table(self):
        # Tokenization:
        #   If word has spaces within it, we consider it to be a "sentence".
        #   As such, we separate the sentence into a list of terminal "words"
        if ' ' in self.word:
            self.word = self.word.split(' ')

        self.init_table()

        # The algorithm works inductively on the table's len(self.word) rows
        # The table is a dict from pairs of integers to sets of variables
        # s is a row index in the table, starting at 0
        # r is a column index in the table, starting at 0
        # As such, any cell in the table may be addressed as self.table[(r, s)]

        # ------------ basis (s = 0) ------------
        for r in range(len(self.word)):
            self.table[(r, 0)] = {rule.head for rule in \
                                  self.grammar.rules if \
                                  len(rule.tail) == 1 and \
                                  self.word[r] in self.grammar.terminals and \
                                  self.word[r] in rule.tail}

        # ------------ induction (s > 0) ------------
        for s in range(1, len(self.word)):
            for r in range(len(self.word) - s):
                for k in range(s):
                    possible_Bs = {symbol for symbol in \
                                   self.table[(r, k)]}
                    possible_Cs = {symbol for symbol in \
                                   self.table[(r + k + 1, s - k - 1)]}

                    possible_tails = {(B, C) for B in possible_Bs for \
                                      C in possible_Cs}

                    self.table[(r, s)].update({rule.head for rule in \
                                               self.grammar.rules \
                                               for tail in possible_tails if \
                                               rule.tail == tail})


        if self.grammar.initial in self.table[(0, len(self.word) - 1)]:
            return True
        else:
            return False

    def gen_iterator(self, c, l):
        for i in range(0, l):
            yield ((c, i), (c+i+1, l-i-1))
        raise StopIteration

    def gen_tree(self, var, pos):
        if pos[1] == 0:
            return Node(var, Node(self.word[pos[0]]))
        else:
            var = Node(var)
            rules_tails = set(rule.tail for rule in self.grammar.rules if rule.head == var.value)
            for a, b in self.gen_iterator(pos[0], pos[1]):
                combs = self.combinations(self.table[a], self.table[b])
                for comb in combs:
                    if comb in rules_tails:
                        var.add(
                            self.gen_tree(comb[0], a),
                            self.gen_tree(comb[1], b)
                        )
            return var

    @staticmethod
    def combinations(iter1, iter2):
        acc = []
        for i in iter1:
            for j in iter2:
                acc.append((i, j))
        return acc

    # extract_all :: TreeNode -> [String]
    # if is a leaf, returns a list containing only the node value of the leaf.
    # else appends itself in front of every element in the list returned by calling this function recursively on its children
    @classmethod
    def extract_all(cls, node):
        acc = []
        for child in node.children:
            if type(child) is tuple:
                aux1 = cls.extract_all(child[0])
                aux2 = cls.extract_all(child[1])
                acc += [Node(node.value, x) for x in cls.combinations(aux1, aux2)]
            else:
                acc.append(Node(node.value, child))
        return acc

    def extract_all_parse_trees(self, pretty_print=False):
        tree = self.gen_tree(self.grammar.initial, (0, len(self.word)-1))
        data = self.extract_all(tree)

        return data  # return the tree


class Node:
    def __init__(self, value, generated=None):
        self.value = value  # str
        self.children = []  # [(Node, Node)] | [Node] if Node.value is terminal
        if generated is not None:
            self.children.append(generated)

    def __str__(self, deepness=0):
        padding = '    '
        s = deepness * padding + self.value + '\n'
        for c in self.children:
            if type(c) is tuple:
                s += c[0].__str__(deepness+1) + '\n' + c[1].__str__(deepness+1) + '\n'
            else:
                s += (deepness+1)* padding + c.value
        return s 
        #if self.children != []:
        #    return 'value = ' + str(self.value) + '\nchildren = ' + str([c[0].__str__() + '\n' + c[1].__str__() for c in self.children])
        #else:
        #    return 'value = ' + str(self.value)

    def add(self, var1, var2):
        self.children.append((var1, var2))

    def get_value(self):
        return self.value


class Parser:
    def __init__(self, grammar, log_grammar_preparation=False):
        self.grammar = grammar
        self.prepare_grammar_for_cyk(log_grammar_preparation)
        self.cyk_table = None

    def parse(self, word, print_parse_trees=True):
        # ------------------- Table construction -------------------
        self.cyk_table = CYKTable(self.grammar, word)
        self.table_construction_report(word)

        
        # ------------------- Parse tree extraction -------------------
        if self.cyk_table.accepts:
            print('Extracting parse trees...')
            parse_trees = self.cyk_table.extract_all_parse_trees(pretty_print=True)

            if print_parse_trees:
                self.print_parse_trees(parse_trees)


            return parse_trees

        else:
            print('Cannot extract parse trees.')
            return None

    def print_parse_trees(self, parse_trees):
        current_tree_count = 0
        if(len(parse_trees)) == 1:
            tree_plural_singular = 'tree'
        else:
            tree_plural_singular = 'trees'
        print('Printing ' + str(len(parse_trees)) + ' parse trees...')
        for tree in parse_trees:
            print('Parse tree ' + str(current_tree_count) +':')
            current_tree_count += 1
            print(tree)  # print each possible tree

    def table_construction_report(self, word):
        if ' ' in word:
            word_or_sentence = 'sentence'
        else:
            word_or_sentence = 'word'
        print('\nParsing', word_or_sentence, ':', word)

        print('Expected table size:', len(word.split(' ')) * (len(word.split(' ')) + 1) / 2)
        print('Actual table size:', len(self.cyk_table.table))
        print('Table state after parse:')
        self.cyk_table.print_table()

        if self.cyk_table.accepts:
            print('Grammar generates', word_or_sentence, '\"' + word + '\"' + '.\n')
        else:
            print('Grammar does not generate', word_or_sentence, '\"' + word + '\"' + '.\n')

    def prepare_grammar_for_cyk(self, log):
        '''
        Converts grammar to Chomsky normal form.
        '''
        grammar_copy = deepcopy(self.grammar)
        cnf_grammar = ChomskyNormalForm(grammar_copy, log)
        print('Grammar in Chomsky normal form')
        print(cnf_grammar)
        self.grammar = cnf_grammar
