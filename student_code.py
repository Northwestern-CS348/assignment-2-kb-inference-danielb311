import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if factq(fact_or_rule):
            if fact_or_rule.asserted:
                self.kb_remove(fact_or_rule)

    def kb_remove(self, fr):
        if factq(fr):
            fact = None
            for i in self.facts:
                if i == fr:
                    fact = i
                    break

            if fact.asserted:
                fact.asserted = False
                
            if fact.supported_by == []:
                self.facts.remove(fact)

                for i in fact.supports_facts:
                    for j in i.supported_by:
                        if j[0] == fact:
                            fact2 = None
                            for k in self.facts:
                                if k == i:
                                    fact2 = k
                                    break

                            fact2.supported_by.remove(j)
                            if fact2.supported_by == [] and fact2.asserted == False:
                                self.kb_remove(fact2)

                for i in fact.supports_rules:
                    for j in i.supported_by:
                        if j[0] == fact:
                            rule2 = None
                            for k in self.rules:
                                if k == i:
                                    rule2 = k
                                    break

                            rule2.supported_by.remove(j)
                            if rule2.supported_by == [] and rule2.asserted == False:
                                self.kb_remove(rule2)
        else:
            rule = None
            for i in self.rules:
                if i == fr:
                    rule = i
                    break

            if not rule.asserted:
                if rule.supported_by == []:
                    self.rules.remove(rule)
                    
                    for i in rule.supports_facts:
                        for j in i.supported_by:
                            if j[1] == rule:
                                fact2 = None
                                for k in self.facts:
                                    if k == i:
                                        fact2 = k
                                        break

                                fact2.supported_by.remove(j)
                                if fact2.supported_by == [] and fact2.asserted == False:
                                    self.kb_remove(fact2)

                for i in rule.supports_rules:
                    for j in i.supported_by:
                        if j[1] == rule:
                            rule2 = None
                            for k in self.rules:
                                if k == i:
                                    rule2 = k
                                    break

                            rule2.supported_by.remove(j)
                            if rule2.supported_by == [] and rule2.asserted == False:
                                self.kb_remove(rule2)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        binding = match(fact.statement, rule.lhs[0])

        if binding != False:
            #if there's only one part to the left hand side of the rule, then the rule entirely matches the fact, so we can create a new inferred fact
            if len(rule.lhs) == 1:
                # newFact = Fact(instantiate(rule.rhs, binding), [fact, rule]) #tried to pass suppported by into constructor but it didn't work
                newFact = Fact(instantiate(rule.rhs, binding))
                newFact.supported_by.append([fact, rule])

                #add supports
                rule.supports_facts.append(newFact)
                fact.supports_facts.append(newFact)

                newFact.asserted = False

                #add new fact to knowledge base
                kb.kb_add(newFact)
            
            #if there's more than one part to the lhs of the rule, we can't infer a new fact, but we can infer a new rule without the first element of the given rule
            else:
                lhsTerms = []

                #skip the first item on the lhs since that one already matches
                for i in range(1, len(rule.lhs)):
                    lhsTerms.append(instantiate(rule.lhs[i], binding))

                newRule = Rule([lhsTerms, instantiate(rule.rhs, binding)])

                #add supports
                newRule.supported_by.append([fact, rule])
                rule.supports_rules.append(newRule)
                fact.supports_rules.append(newRule)
                
                newRule.asserted = False

                #add new rule to the knowledge base
                kb.kb_add(newRule)