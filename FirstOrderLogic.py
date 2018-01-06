import itertools
import re
import sys
import collections

orderedDict = collections.OrderedDict()
from collections import OrderedDict

# Global Variables
global queries, knowledgeBase, queryCount, sentenceCount, true_values, false_values, queryList, split_sentence
global resultant_string


def getOutput():
    global resultant_string
    #print("resultant string is %s" %resultant_string)

    with open("output.txt", "w") as f1:
        f1.write(resultant_string)
        f1.close()

def getInput():
    global queries
    global knowledgeBase
    queries = []
    knowledgeBase = []
    with open('input.txt') as infile:
        # queries
        queryCount = int(infile.readline().strip())

        for line in range(0, queryCount):
            queries.append(infile.readline().strip().split(' '))

        # populating the knowledge base
        sentenceCount = int(infile.readline().strip())
        for line in range(queryCount, sentenceCount + queryCount):
            knowledgeBase.append(infile.readline().strip().split(' '))

        #print(knowledgeBase)
        knowledgeBase = [[''.join(''.join(sub).split())] for sub in knowledgeBase]
        #print(knowledgeBase)



# TODO: returns false if the unification involves 2 or more constants

def checkUnificationOfVariables(constant, variable):

    #print(constant)
    #print(variable)
    for c, v in zip(constant, variable):
        if (c[0].islower() and v[0].islower() and c != v):

            return False

    return True


def checkUnificationOfConstants(constant, variable):
    # cant unify 2 unequal constants.
    # can unify 2 equal constants.
    # cant unify a variable with more than one constant.
    dict = {}

    flag = 0
    const = []
    var = []
    for c, v in zip(constant, variable):
        if (c[0].isupper() and v[0].isupper() and c != v):
            return False
        else:
            if (c != v):
                if (c[0].isupper()):
                    const.append(c)
                if (c[0].islower()):
                    var.append(c)
                if (v[0].isupper()):
                    const.append(v)
                if (v[0].islower()):
                    var.append(v)

    dict = {}
    for c, v in zip(const, var):

        if (v in dict and c not in dict.values()):

            return False
        else:
            dict.update({v: c})

    return True


def checkMatching(predicate, sentence):
    # TODO : cannot unify 2 unequal constants.

    global sentence_partition
    global constant
    global variable
    total_sentences = sentence
    sentence_partition = []
    predicate_partition = []

    str_sentence = "".join(sentence)
    predicate_sentence = "".join(predicate)
    predicate_sentence = predicate_sentence.split("|")
    for p in predicate_sentence:
        predicate_partition.append(p.split("(", 1)[0])
    for s in sentence:
        sentence_partition.append(s.split("(", 1)[0])

    sentence_partition_str = "".join(sentence_partition)
    predicate_partition_str = "".join(predicate_partition)
    flagset = 0
    for subsentence in sentence_partition:
        for subpredicate in predicate_partition:
            if (("~" in subpredicate and "~" not in subsentence and subpredicate[1:] == subsentence) or (
                        "~" in subsentence and "~" not in subpredicate and subpredicate == subsentence[1:])):

                return True

    return False


# TODO: if the query can be matched to the sentence , make the unification.
def makeUnification(predicate, sentence):
    # make the unification by substituting variable for the given constant.
    # cannot unify 2 constants or 2 variables.
    total_sentences = sentence

    variable = []
    constant = []
    sentence_str = "".join(sentence)
    constant.append(predicate[predicate.index("(") + 1:predicate.index(")")])
    sentence_split = "".join(sentence).split("|")
    # secondvariable = []
    variables = []
    constants = []
    sentences_resolved = []
    count_false = 0
    variables_list = []
    constants_list = []
    count_so_far = 0
    predicate_split = "".join(predicate).split("|")
    constant_to_variable_mapping = {}
    for _sentence in sentence_split:
        for _predicate in predicate_split:

            if ("~" + _sentence.split("(", 1)[0] == _predicate.split("(", 1)[0] or "~" + _predicate.split("(", 1)[0] ==
                _sentence.split("(", 1)[0]):
                start_position = '('
                end_position = ')'
                start_predicate = '('
                end_predicate = ')'
                # constants and variables.
                count_so_far = count_so_far + 1

                constants = []
                variables = []
                temp_pred = _predicate[_predicate.index("(") + 1:_predicate.index(")")]

                temp_items = []
                for items in temp_pred.split():
                    temp_items.extend(items.split(","))


                temp_sent = _sentence[_sentence.index("(") + 1:_sentence.index(")")]
                sent_items = []
                for item in temp_sent.split():
                    sent_items.extend(item.split(","))
                flag = 0
                for temp_element, sent_element in zip(temp_items, sent_items):
                    if (temp_element != sent_element):

                        if (temp_element[0].isupper()):
                            constants.append(temp_element)
                        elif (not temp_element[0].isupper()):
                            variables.append(temp_element)
                        if (sent_element[0].isupper()):
                            constants.append(sent_element)
                        elif (not sent_element[0].isupper()):
                            variables.append(sent_element)

                constants_list = constants
                variables_list = variables
                if ("," in variables):
                    variables = "".join(variables).split(",")
                if ("," in constants):
                    constants = "".join(constants).split("")


                # if that particular predicate can be unified then ---->
                if (not checkUnificationOfConstants(temp_items, sent_items) or not checkUnificationOfVariables(
                        temp_items, sent_items)):

                    count_false = count_false + 1

                    continue


                if (checkUnificationOfConstants(temp_items, sent_items) and checkUnificationOfVariables(temp_items,
                                                                                                        sent_items)):
                    # if true, then append these constants and variables. else discard.
                    constants = "".join(constants).split(",")
                    new_constants_list = []
                    new_variables_list = []
                    for var in variables_list:
                        new_variables_list.extend(var.split(","))


                    for const in constants_list:
                        new_constants_list.extend(const.split(","))



                    s = "".join(sentence)

                    constant_to_variable_mapping = {}
                    for const, var in zip(new_constants_list, new_variables_list):
                        constant_to_variable_mapping.update({var: const})
                        # flipped = dict(zip(constant_to_variable_mapping.values(), constant_to_variable_mapping.keys()))


                    p = "".join(predicate)


                    # sentence
                    result1 = re.sub(r'\([^()]+\)', lambda m: '({})'.format(
                        ','.join(
                            constant_to_variable_mapping.get(k, '') or k for k in m.group().strip('()').split(','))),
                                     s)
                    s = result1

                    # predicate
                    result2 = re.sub(r'\([^()]+\)', lambda m: '({})'.format(','.join(
                        constant_to_variable_mapping.get(k, '') or k for k in m.group().strip('()').split(','))),
                                     p)


                    sentence = []
                    sentence.append(result1)
                    predicate = result2


                    # list of all sentences that can be resolved with the query
                    pred = "".join(predicate).split("|")
                    # sentence="".join(sentence).split("|")
                    # print("sentence %s" % sentence)

                    sentences_resolved = []
                    for subsentence in sentence:
                        subsentence = subsentence.split("|")
                        for subpredicate in pred:

                            for s in subsentence:
                                #print("s%s" % s)
                                if ("~" in s and "~" not in subpredicate and subpredicate == s[1:]):
                                    sentences_resolved.append(s)
                                elif ("~" not in s and "~" in subpredicate and subpredicate[1:] == s):
                                    sentences_resolved.append(s)

                    sent = "".join(sentence).split("|")


                    # TODO: replace other variables in the remaining sentences that match with the constant:

                    constant_list = []
                    variable_list = []

                    constant_list.append(constants)
                    variable_list.append(variables)

                    result_of_resolution_sentence = "".join(sent)

                    for resolved_sentence in sentences_resolved:
                        for subsentence in sent:  # to be changed.

                            if (resolved_sentence == subsentence):
                                # print("yes")
                                result_of_resolution_sentence = result_of_resolution_sentence.replace(resolved_sentence,
                                                                                                      "")

                               
                    result_of_resolution_query = pred

                    try:
                        for s in sentences_resolved:
                            if ("~" in s):
                                s = s.replace("~", "")
                                result_of_resolution_query = "".join(result_of_resolution_query).replace(s, "")

                            else:
                                s = "~" + s
                                result_of_resolution_query = "".join(result_of_resolution_query).replace(s, "")


                        if (not result_of_resolution_sentence):
                            result_of_resolution = result_of_resolution_query

                        if (not result_of_resolution_query):
                            result_of_resolution = result_of_resolution_sentence

                        if (result_of_resolution_query and result_of_resolution_sentence):

                            result_of_resolution = result_of_resolution_sentence + result_of_resolution_query

                    except AttributeError:

                        result_of_resolution = sent

                    result = []
                    result.append(result_of_resolution)

                    if (result_of_resolution):
                        results = (result_of_resolution.split(")", 1)[1])
                        if (not results):
                            # print("THE RESULT OF RESOLUTION!!!!!!! %s" % result_of_resolution)
                            res = []
                            res.append(result_of_resolution)
                            return res
                        else:
                            result = []
                            result.append(result_of_resolution)
                            s = ""
                            char = ''
                            for index in range(len(result_of_resolution) - 1):
                                if result_of_resolution[index] == ")":
                                    char = result_of_resolution[index + 1]
                                    s += result_of_resolution[index]
                                    continue
                                if result_of_resolution[index] == char:
                                    s += "|"
                                    char = []
                                s += result_of_resolution[index]
                                # print(s)
                            s = s + ")"
                            res = []
                            set_flag = 1
                            res.append(s)


                    elif (not result_of_resolution):

                        return []

    if (count_false == count_so_far):

        return sentence
    else:

        return res


def resolveSentencesInKnowledgeBase(updatedKnowledgeBase):
    sentence_split = []
    query_split = []
    for sentence_one in knowledgeBase:
        for sentence_two in updatedKnowledgeBase:
            if (checkMatching(sentence_one, sentence_two)):
                result = makeUnification("".join(sentence_one), sentence_two)
                # knowledgeBase.append(result)
                # updatedKnowledgeBase.append(result)
                if (not result):

                    return 0
                if (result):
                    knowledgeBase.append(result)
                    updatedKnowledgeBase.append(result)


def negateQuery(query):
    q_string = "".join(query)
    if ("~" in q_string):
        q_string = q_string.replace("~", "")
    elif ("~" not in q_string):
        q_string = "~" + q_string
    query = []
    query.append(q_string)
    return query


def resolveQuery(query):
    # print("Inside resolveQuery function")
    global queryList
    global split_sentence
    global knowledgeBase
    global resultant_string
    #print("resultant string is %s" %resultant_string)
    duplicateKnowledgeBase = knowledgeBase[:]
    #print("duplicate knowledge base is %s" % duplicateKnowledgeBase)
    queryList = []
    split_sentence = []
    query = negateQuery(query)  # resolution refutation
    # print("Negated the query!%s" % query)
    queue = [query]
    children = 5000
    while queue != [] and children:
        query = queue.pop(0)
        for predicate in query:
            for sentence in knowledgeBase:
                kbsentence = "".join(sentence)
                kbsentence = kbsentence.replace(" ", "")
                split_sentence.append(kbsentence.split("|"))
                # print("YAAY")
                for each_sentence in split_sentence:
                    if (checkMatching(query, each_sentence)):
                        resultOfUnification = makeUnification(predicate, sentence)
                        #print("result returned %s" % resultOfUnification)
                        if (not resultOfUnification):
                           # print("TRUE")
                            resultant_string+="TRUE\n"
                            #print("resultant string for true%s" %resultant_string)
                            knowledgeBase = duplicateKnowledgeBase
                            #print("duplicate knowledge base has %s" % duplicateKnowledgeBase)
                            #print("original has %s" % knowledgeBase)
                            return
                        else:
                            updatedKnowledgeBase.append(resultOfUnification)
                            if (resultOfUnification not in knowledgeBase):
                                knowledgeBase.append(resultOfUnification)
                                #print("knowledge base now has %s" % knowledgeBase)
                            if (resultOfUnification not in queue):
                                queue.append(resultOfUnification)
                           # print("queue contains %s" % queue)
                    children = children - 1
                    if(children==0):
                            resultant_string+="FALSE\n"
                            
                            return
                   # print("children! %s" %children)
                split_sentence = []
    resultant_string+="FALSE\n"
    return
        # resolveSentencesInKnowledgeBase(updatedKnowledgeBase)

def parseInput():
    global true_values
    global false_values
    true_values = []
    false_values = []
    global updatedKnowledgeBase
    for query in queries:
       # print("-----------resolving query %s--------------------" % query)
        updatedKnowledgeBase = []
        knowledgeBase = []
        resolveQuery(query)


# TODO: Main function
if __name__ == '__main__':
    global resultant_string
    getInput()
    resultant_string=""
    parseInput()
    getOutput()
