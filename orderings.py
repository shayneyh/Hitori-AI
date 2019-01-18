#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented.

import random
import itertools
import numpy as np

'''
This file will contain different variable ordering heuristics to be used within
bt_search.

var_ordering == a function with the following template
    ord_type(csp)
        ==> returns Variable 

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    ord_type returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.

val_ordering == a function with the following template
    val_ordering(csp,var)
        ==> returns [Value, Value, Value...]
    
    csp is a CSP object, var is a Variable object; the heuristic can use csp to access the constraints of the problem, and use var to access var's potential values. 

    val_ordering returns a list of all var's potential values, ordered from best value choice to worst value choice according to the heuristic.

'''


def ord_random(csp):
    '''
    ord_random(csp):
    A var_ordering function that takes a CSP object csp and returns a Variable object var at random.  var must be an unassigned variable.
    '''
    var = random.choice(csp.get_all_unasgn_vars())
    return var


def val_arbitrary(csp,var):
    '''
    val_arbitrary(csp,var):
    A val_ordering function that takes CSP object csp and Variable object var,
    and returns a value in var's current domain arbitrarily.
    '''
    return var.cur_domain()


def ord_mrv(csp):
    '''
    ord_mrv(csp):
    A var_ordering function that takes CSP object csp and returns Variable object var, 
    according to the Minimum Remaining Values (MRV) heuristic as covered in lecture.  
    MRV returns the variable with the most constrained current domain 
    (i.e., the variable with the fewest legal values).
    '''
#IMPLEMENT
    #if only one unassigned variable left then return that var
    num_unassigned = 0
    for var in csp.vars:
        if var.assignedValue is None:
            unassigned_var = var
            num_unassigned += 1
    if num_unassigned == 1:
        return unassigned_var

    mrv_var = float('inf')
    for var in csp.vars:
        if (var.assignedValue is None) & (len(var.cur_domain()) < mrv_var):
            mrv_var = len(var.cur_domain())
            final_var = var
    return final_var

def ord_dh(csp):
    '''
    ord_dh(csp):
    A var_ordering function that takes CSP object csp and returns Variable object var,
    according to the Degree Heuristic (DH), as covered in lecture.
    Given the constraint graph for the CSP, where each variable is a node, 
    and there exists an edge from two variable nodes v1, v2 iff there exists
    at least one constraint that includes both v1 and v2,
    DH returns the variable whose node has highest degree.
    '''    
#IMPLEMENT
    #if only one unassigned variable left then return that var
    num_unassigned = 0
    for var in csp.vars:
        if var.assignedValue is None:
            unassigned_var = var
            num_unassigned += 1
    if num_unassigned == 1:
        return unassigned_var

    deg_matrix = np.zeros((len(csp.vars),len(csp.vars)))
    for cons in csp.cons:
        cur_var_list = []
        for var in cons.scope:
            if var.assignedValue is None:
                cur_var_list.append(csp.vars.index(var))
        for pair in itertools.combinations(cur_var_list, 2):
            deg_matrix[pair] = 1
    deg_matrix += deg_matrix.T
    max_deg_var = np.argmax(np.sum(deg_matrix, axis = 0))
    #debug only (check if returned var is assigned already
    if csp.vars[max_deg_var].assignedValue is not None:
        a = 1
    return csp.vars[max_deg_var]

def val_lcv(csp,var):
    '''
    val_lcv(csp,var):
    A val_ordering function that takes CSP object csp and Variable object var,
    and returns a list of Values [val1,val2,val3,...]
    from var's current domain, ordered from best to worst, evaluated according to the 
    Least Constraining Value (LCV) heuristic.
    (In other words, the list will go from least constraining value in the 0th index, 
    to most constraining value in the $j-1$th index, if the variable has $j$ current domain values.) 
    The best value, according to LCV, is the one that rules out the fewest domain values in other 
    variables that share at least one constraint with var.
    '''    
#IMPLEMENT
    val_dict = {}#emtpy dict
    cur_val = var.cur_domain()

    for con in csp.cons:  # iterate through constraints
        if var in con.scope:  # only care about constraints involving var
            var_ind = con.scope.index(var)
            # go through each element in cur_val to make sure each val can satisfy this constraint for at least 1 tuple
            # if not, a DWO will occur and this val should be placed at the end of the LCV list
            bad_list = list()
            for val in cur_val:
                isFound = False
                for key in con.sat_tuples:
                    if key[var_ind] == val:
                        isFound = True
                        break
                if isFound == False:#val cannot satisfy this constraint at all no matter what other vars are
                    bad_list.append(val)
            #remove any bad values before going to next constraint
            for val in bad_list:
                cur_val.remove(val)
    #create empty dictionary for each valid val of var in cur_domain
    for val in cur_val:
        val_dict[val] = list()

    for con in csp.cons:#iterate through constraints
        if var in con.scope:#only care about constraints involving var
            var_ind = con.scope.index(var)
            for tuple in con.sat_tuples: #iterate through each satisfying tuples in current constraint
                key = tuple[var_ind] #value of var in current tuple
                #if val not in bad_list and is within current domain
                if key in cur_val:
                    #make sure all other assigned values correspond to this tuple
                    pass_this_tuple = False
                    for i in range(len(tuple)):
                        if (con.scope[i].assignedValue is not None) & (con.scope[i].assignedValue != tuple[i]):
                            #ignore this tuple and move on
                            pass_this_tuple = True
                            break
                    if pass_this_tuple:
                        continue
                    #loop through each element of tuple and add domain to each "connected" variable
                    for i in range(len(con.scope)):#len(con.scope) is the same as len(tuple)
                        if i != var_ind:#skip var
                            cur_var = con.scope[i]#find var corresponding to each index
                            #if cur_var is unassigned and
                            #if current value at current index of tuple is in the current domain of corresponding var
                            # and current domain is not in the dictionary yet
                            if (cur_var.assignedValue is None) & (tuple[i] in cur_var.cur_domain()) & ((cur_var, tuple[i]) not in val_dict[key]):
                                # add val in cur_var of cur_tuple to list of satisfying values
                                cur_item = val_dict[key]
                                cur_item.append((cur_var,tuple[i]))
                                val_dict[key] = cur_item

    val_summary_list = list()
    for key in var.cur_domain():
        if key in cur_val:
            val_summary_list.append((key,len(val_dict[key])))
        else:
            val_summary_list.append((key, 0))
    final_list = sorted(val_summary_list, key=lambda x: x[1], reverse=True)
    return [i[0] for i in final_list]


def ord_custom(csp):
    '''
    ord_custom(csp):
    A var_ordering function that takes CSP object csp and returns Variable object var,
    according to a Heuristic of your design.  This can be a combination of the ordering heuristics 
    that you have defined above.
    '''    
#IMPLEMENT
    # if only one unassigned variable left then return that var
    num_unassigned = 0
    for var in csp.vars:
        if var.assignedValue is None:
            unassigned_var = var
            num_unassigned += 1
    if num_unassigned == 1:
        return unassigned_var

    mrv_var = float('inf')
    final_vars = []
    for var in csp.vars:
        if (var.assignedValue is None): #only look at unassigned var
            #if mrv of var is smaller than current min, replace
            if (len(var.cur_domain()) < mrv_var):
                mrv_var = len(var.cur_domain())
                final_vars = []
                final_vars.append(var)
            #if mrv of var is equal to current min, append list to include possible candidates
            elif (len(var.cur_domain()) == mrv_var):
                final_vars.append(var)
    if (len(final_vars) == 1):
        return final_vars[0]
    else:#compute DH for all vars with mrv and return the one with highest DH
        if (len(final_vars) > 2):
            final_vars = final_vars[0:2]
        deg_matrix = [[] for i in range(len(final_vars))]
        for cons in csp.cons:
            cur_var_list = []  # get list of all unassigned vars
            for var in cons.scope:
                if var.assignedValue is None:
                    cur_var_list.append(var)
            for i in range(len(final_vars)):
                if final_vars[i] in cons.scope:
                    for cur_var in cur_var_list:
                        if cur_var not in deg_matrix[i]:
                            deg_matrix[i].append(cur_var)
        max_deg_var = 0
        for i in range(len(final_vars)):
            if len(deg_matrix[i]) > max_deg_var:
                max_deg_var = len(deg_matrix[i])
                final_ind = i
        return final_vars[final_ind]




