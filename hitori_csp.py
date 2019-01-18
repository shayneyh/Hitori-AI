#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the hitori models.  

'''
Construct and return hitori CSP models.
'''

from cspbase import *
from propagators import *
from orderings import *
import itertools
import string
from math import *


def adjacent_blocks(i,j, side_len):#check if two vars at index i and j are adjacent on the board
    i_row = floor(i/side_len)
    i_col = i % side_len
    j_row = floor(j / side_len)
    j_col = j % side_len
    return (abs(i_row - j_row) == 1) | (abs(i_col - j_col) == 1)

def solve_hitori(csp, propType, var_ord_type, val_ord_type, trace=False):
    solver = BT(csp)
    if trace:
        solver.trace_on()
    if propType == 'BT':
        solver.bt_search(prop_BT,var_ord_type,val_ord_type)
    return solver.csp.vars

def hitori_csp_model_1(initial_hitori_board):
    '''Return a CSP object representing a hitori CSP problem along 
       with an array of variables for the problem. That is return

       hitori_csp, variable_array

       where hitori_csp is a csp representing hitori using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the hitori board (indexed from (0,0) to (8,8))

       
       
       The input board is specified as a list of n lists. Each of the
       n lists represents a row of the board. Each item in the list 
       represents a cell, and will contain a number between 1--n.
       E.g., the board
    
       -------------------  
       |1|3|4|1|
       |3|1|2|4|
       |2|4|2|3|
       |1|2|3|2|
       -------------------
       would be represented by the list of lists
       
       [[1,3,4,1],
       [3,1,2,4],
       [2,4,2,3],
       [1,2,3,2]]
       
       This routine returns Model_1 which consists of a variable for
       each cell of the board, with domain equal to {0,i}, with i being
       the initial value of the cell in the board. 
       
       Model_1 also contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.)
       
       All of the constraints of Model_1 MUST BE binary constraints 
       (i.e., constraints whose scope includes exactly two variables).
    '''


##IMPLEMENT
    #add variables
    side_len = len(initial_hitori_board)
    vars = []
    for i in range(side_len):
        for j in range(side_len):
            var_name = string.ascii_lowercase[i] + string.ascii_lowercase[j]
            if initial_hitori_board[i][j] == 0:
                dom = [0]
            else:
                dom = [0,initial_hitori_board[i][j]]
            vars.append(Variable(var_name, dom))
    #constraint
    cons = []
    #no rows contain same number (include checking for adjacent black boxes (left-right))
    for row in range(side_len):
        for col in itertools.combinations(range(side_len), 2):
            ind1 = row*side_len+col[0]
            ind2 = row*side_len+col[1]
            con = Constraint("C({},{})".format(vars[ind1].name, vars[ind2].name), [vars[ind1], vars[ind2]])
            sat_tuples = []
            for t in itertools.product(vars[ind1].dom, vars[ind2].dom):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            if not adjacent_blocks(ind1, ind2, side_len):
                sat_tuples.append((0,0))
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)

    # no columns contain same number (include checking for adjacent black boxes (up-down))
    for col in range(side_len):
        for row in itertools.combinations(range(side_len), 2):
            ind1 = row[0] * side_len + col
            ind2 = row[1] * side_len + col
            con = Constraint("C({},{})".format(vars[ind1].name, vars[ind2].name), [vars[ind1], vars[ind2]])
            sat_tuples = []
            for t in itertools.product(vars[ind1].dom, vars[ind2].dom):
                if t[0] != t[1]:
                    sat_tuples.append(t)
            if not adjacent_blocks(ind1, ind2, side_len):
                sat_tuples.append((0, 0))
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)

    csp = CSP("{}-Hitori1".format(side_len), vars)
    for c in cons:
        csp.add_constraint(c)
    # #solve puzzle
    # trace = False
    # solve_hitori(csp, 'BT', ord_mrv, val_lcv, trace)
    var_array = [[Variable for i in range(side_len)] for j in range(side_len)]
    for i in range(side_len):
        for j in range(side_len):
            var_array[i][j] = vars[i*side_len + j]
    return csp, var_array



##############################

def check_row_or_col(tuple):
    #check if all values are unique
    new_list = []
    for i in range(len(tuple)):
        if tuple[i] not in new_list:#no repeated elements yet
            new_list.append(tuple[i])
        elif tuple[i] != 0:#repeat for non-zero value: not allowed
            return False
        elif tuple[i-1] == 0:#if previous element is also 0 (which would be adjacent to current one)
            return False
    return True

def hitori_csp_model_2(initial_hitori_board):
    '''Return a CSP object representing a hitori CSP problem along 
       with an array of variables for the problem. That is return

       hitori_csp, variable_array

       where hitori_csp is a csp representing hitori using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the hitori board (indexed from (0,0) to (8,8))

       
       
       The input board is specified as a list of n lists. Each of the
       n lists represents a row of the board. Each item in the list 
       represents a cell, and will contain a number between 1--n.
       E.g., the board
    
       -------------------  
       |1|3|4|1|
       |3|1|2|4|
       |2|4|2|3|
       |1|2|3|2|
       -------------------
       would be represented by the list of lists
       
       [[1,3,4,1],
       [3,1,2,4],
       [2,4,2,3],
       [1,2,3,2]]

       The input board takes the same input format (a list of n lists 
       specifying the board as hitori_csp_model_1).
   
       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0,i}, where i is
       the initial value of the cell.

       However, model_2 has different constraints.  In particular, instead
       of binary not-equals constraints, model_2 has 2n n-ary constraints
       that resemble a modified all-different constraint.  Each constraint
       is over n variables.  For any given row (resp. column), that 
       constraint will incorporate both the adjacent black squares and 
       no repeated numbers rules.
       
    '''

###IMPLEMENT 
    # add variables
    side_len = len(initial_hitori_board)
    vars = []
    for i in range(side_len):
        for j in range(side_len):
            var_name = string.ascii_lowercase[i] + string.ascii_lowercase[j]
            if initial_hitori_board[i][j] == 0:
                dom = [0]
            else:
                dom = [0, initial_hitori_board[i][j]]
            vars.append(Variable(var_name, dom))

    # constraint
    cons = []
    # no rows contain same number (include checking for adjacent black boxes (left-right))
    for row in range(side_len):
        cons_var = []
        constraint_name = ""
        cons_var_dom = []
        for col in range(side_len):
            ind = row * side_len + col
            constraint_name += (vars[ind].name + ",")
            cons_var.append(vars[ind])
            cons_var_dom.append(vars[ind].dom)
        constraint_name = constraint_name[:-1]
        con = Constraint("C({})".format(constraint_name), cons_var)

        sat_tuples = []
        for t in list(itertools.product(*cons_var_dom)):
            if check_row_or_col(t):
                sat_tuples.append(t)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)

    # no cols contain same number (include checking for adjacent black boxes (up-down))
    for col in range(side_len):
        cons_var = []
        constraint_name = ""
        cons_var_dom = []
        for row in range(side_len):
            ind = row * side_len + col
            constraint_name += (vars[ind].name + ",")
            cons_var.append(vars[ind])
            cons_var_dom.append(vars[ind].dom)
        constraint_name = constraint_name[:-1]
        con = Constraint("C({})".format(constraint_name), cons_var)

        sat_tuples = []
        for t in list(itertools.product(*cons_var_dom)):
            if check_row_or_col(t):
                sat_tuples.append(t)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)

    csp = CSP("{}-Hitori2".format(side_len), vars)
    for c in cons:
        csp.add_constraint(c)
    # #solve puzzle
    # trace = False
    # solve_hitori(csp, 'BT', ord_mrv, val_lcv, trace)
    var_array = [[Variable for i in range(side_len)] for j in range(side_len)]
    for i in range(side_len):
        for j in range(side_len):
            var_array[i][j] = vars[i * side_len + j]
    return csp, var_array