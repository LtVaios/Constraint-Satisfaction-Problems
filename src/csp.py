"""CSP (Constraint Satisfaction Problems) problems and solvers. (Chapter 6)"""

import itertools
import random
import re
import string
import time
from collections import defaultdict, Counter
from functools import reduce
from operator import eq, neg

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend

constr_counter=0 #This is a global variable used for measurements of the methods
constr_counter_limit=0 #This is a global variable used to limit the measurements of the methods
assignment_counter=0 #This is the global variable that measures how many nodes we visit in the search tree

class CSP(search.Problem):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b
    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases (for example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(n^4) for the
    explicit representation). In terms of describing the CSP as a
    problem, that's all there is.
    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP. Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation
    """

    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = domains
        self.nassigns = 0

    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""

        # Subclasses may implement this more efficiently
        def conflict(var2):
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):
        """Show a human-readable representation of the CSP."""
        # Subclasses can print in a prettier way, or display with a GUI
        print(assignment)

    # These methods are for the tree and graph-search interface:

    def actions(self, state):
        """Return a list of applicable actions: non conflicting
        assignments to an unassigned variable."""
        if len(state) == len(self.variables):
            return []
        else:
            assignment = dict(state)
            var = first([v for v in self.variables if v not in assignment])
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, action):
        """Perform an action and return the new state."""
        (var, val) = action
        return state + ((var, val),)

    def goal_test(self, state):
        """The goal is to assign all variables, with all constraints satisfied."""
        assignment = dict(state)
        return (len(assignment) == len(self.variables)
                and all(self.nconflicts(variables, assignment[variables], assignment) == 0
                        for variables in self.variables))

    # These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):
        """Start accumulating inferences from assuming var=value."""
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        """Rule out var=value."""
        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):
        """Return all values for var that aren't currently ruled out."""
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        """Return the partial assignment implied by the current inferences."""
        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):
        """Undo a supposition and all inferences from it."""
        for B, b in removals:
            self.curr_domains[B].append(b)

    # This is for min_conflicts search

    def conflicted_vars(self, current):
        """Return a list of variables in current assignment that are in conflict"""
        return [var for var in self.variables
                if self.nconflicts(var, current[var], current) > 0]

# ______________________________________________________________________________
# Constraint Propagation with AC3


def no_arc_heuristic(csp, queue):
    return queue


def dom_j_up(csp, queue):
    return SortedSet(queue, key=lambda t: neg(len(csp.curr_domains[t[1]])))


def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    """[Figure 6.3]"""
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    return True, checks  # CSP is satisfiable


def revise(csp, Xi, Xj, removals, checks=0):
    """Return true if we remove a value."""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        # if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            revised = True
    return revised, checks


# Constraint Propagation with AC3b: an improved version
# of AC3 with double-support domain-heuristic

def AC3b(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    global constr_counter
    global constr_counter_limit
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        if constr_counter > constr_counter_limit: #This is the limit of the method measurements
           return -1 
        (Xi, Xj) = queue.pop()
        # Si_p values are all known to be supported by Xj
        # Sj_p values are all known to be supported by Xi
        # Dj - Sj_p = Sj_u values are unknown, as yet, to be supported by Xi
        Si_p, Sj_p, Sj_u, checks = partition(csp, Xi, Xj, checks)
        if not Si_p:
            return False, checks  # CSP is inconsistent
        revised = False
        for x in set(csp.curr_domains[Xi]) - Si_p:
            csp.prune(Xi, x, removals)
            revised = True
        if revised:
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
        if (Xj, Xi) in queue:
            if isinstance(queue, set):
                # or queue -= {(Xj, Xi)} or queue.remove((Xj, Xi))
                queue.difference_update({(Xj, Xi)})
            else:
                queue.difference_update((Xj, Xi))
            # the elements in D_j which are supported by Xi are given by the union of Sj_p with the set of those
            # elements of Sj_u which further processing will show to be supported by some vi_p in Si_p
            for vj_p in Sj_u:
                for vi_p in Si_p:
                    conflict = True
                    constr_counter+=1 #This is the counter of the measurements
                    if csp.constraints(Xj, vj_p, Xi, vi_p):
                        conflict = False
                        Sj_p.add(vj_p)
                    checks += 1
                    if not conflict:
                        break
            revised = False
            for x in set(csp.curr_domains[Xj]) - Sj_p:
                csp.prune(Xj, x, removals)
                revised = True
            if revised:
                for Xk in csp.neighbors[Xj]:
                    if Xk != Xi:
                        queue.add((Xk, Xj))
    return True, checks  # CSP is satisfiable


def partition(csp, Xi, Xj, checks=0):
    Si_p = set()
    Sj_p = set()
    Sj_u = set(csp.curr_domains[Xj])
    for vi_u in csp.curr_domains[Xi]:
        conflict = True
        # now, in order to establish support for a value vi_u in Di it seems better to try to find a support among
        # the values in Sj_u first, because for each vj_u in Sj_u the check (vi_u, vj_u) is a double-support check
        # and it is just as likely that any vj_u in Sj_u supports vi_u than it is that any vj_p in Sj_p does...
        for vj_u in Sj_u - Sj_p:
            # double-support check
            if csp.constraints(Xi, vi_u, Xj, vj_u):
                conflict = False
                Si_p.add(vi_u)
                Sj_p.add(vj_u)
            checks += 1
            if not conflict:
                break
        # ... and only if no support can be found among the elements in Sj_u, should the elements vj_p in Sj_p be used
        # for single-support checks (vi_u, vj_p)
        if conflict:
            for vj_p in Sj_p:
                # single-support check
                if csp.constraints(Xi, vi_u, Xj, vj_p):
                    conflict = False
                    Si_p.add(vi_u)
                checks += 1
                if not conflict:
                    break
    return Si_p, Sj_p, Sj_u - Sj_p, checks


# Constraint Propagation with AC4

def AC4(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    support_counter = Counter()
    variable_value_pairs_supported = defaultdict(set)
    unsupported_variable_value_pairs = []
    checks = 0
    # construction and initialization of support sets
    while queue:
        (Xi, Xj) = queue.pop()
        revised = False
        for x in csp.curr_domains[Xi][:]:
            for y in csp.curr_domains[Xj]:
                if csp.constraints(Xi, x, Xj, y):
                    support_counter[(Xi, x, Xj)] += 1
                    variable_value_pairs_supported[(Xj, y)].add((Xi, x))
                checks += 1
            if support_counter[(Xi, x, Xj)] == 0:
                csp.prune(Xi, x, removals)
                revised = True
                unsupported_variable_value_pairs.append((Xi, x))
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
    # propagation of removed values
    while unsupported_variable_value_pairs:
        Xj, y = unsupported_variable_value_pairs.pop()
        for Xi, x in variable_value_pairs_supported[(Xj, y)]:
            revised = False
            if x in csp.curr_domains[Xi][:]:
                support_counter[(Xi, x, Xj)] -= 1
                if support_counter[(Xi, x, Xj)] == 0:
                    csp.prune(Xi, x, removals)
                    revised = True
                    unsupported_variable_value_pairs.append((Xi, x))
            if revised:
                if not csp.curr_domains[Xi]:
                    return False, checks  # CSP is inconsistent
    return True, checks  # CSP is satisfiable


# ______________________________________________________________________________
# CSP Backtracking Search

# Variable ordering 

def first_unassigned_variable(assignment, csp):
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])

def mrv(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))

def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])

# Value ordering 

def unordered_domain_values(var, assignment, csp):
    """The default value order."""
    return csp.choices(var)

def lcv(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted(csp.choices(var), key=lambda val: csp.nconflicts(var, val, assignment))

# Inference

def no_inference(csp, var, value, assignment, removals):
    return True

def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                global constr_counter 
                constr_counter+=1 #This is the counter of the measurements
                if not csp.constraints(var, value, B, b):
                    if var not in csp.conflicts[B]:
                        csp.conflicts[B].append(var) #adding var to the conflict set of B because it caused incosistency
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                for con in csp.conflicts[B]:
                    if con not in csp.conflicts[var] and con!=var:
                        csp.conflicts[var].append(con) #var occured domain annihilation to B so we add the conflict set of B to var
                return False
    return True

def mac(csp, var, value, assignment, removals, constraint_propagation=AC3b):
    """Maintain arc consistency."""
    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)

# The search, proper 

def backtracking_search(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):
    """[Figure 6.5]"""
    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            global assignment_counter
            assignment_counter+=1
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    if constr_counter > constr_counter_limit: #This is the limit of the method measurements
                        return -1
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack({})
    assert result is None or result == -1 or csp.goal_test(result)
    return result

# ______________________________________________________________________________
# Min-conflicts Hill Climbing search for CSPs

def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic Hill Climbing on the number of conflicts."""
    # Generate a complete assignment for all variables (probably with conflicts)
    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            print("MIN-CON steps: ",i)
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    return None

def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))

# ______________________________________________________________________________

def make_arc_consistent(Xj, Xk, csp):
    """Make arc between parent (Xj) and child (Xk) consistent under the csp's constraints,
    by removing the possible values of Xj that cause inconsistencies."""
    # csp.curr_domains[Xj] = []
    for val1 in csp.domains[Xj]:
        keep = False  # Keep or remove val1
        for val2 in csp.domains[Xk]:
            if csp.constraints(Xj, val1, Xk, val2):
                # Found a consistent assignment for val1, keep it
                keep = True
                break

        if not keep:
            # Remove val1
            csp.prune(Xj, val1, None)

    return csp.curr_domains[Xj]

def assign_value(Xj, Xk, csp, assignment):
    """Assign a value to Xk given Xj's (Xk's parent) assignment.
    Return the first value that satisfies the constraints."""
    parent_assignment = assignment[Xj]
    for val in csp.curr_domains[Xk]:
        if csp.constraints(Xj, parent_assignment, Xk, val):
            return val

    # No consistent assignment available
    return None 

def dom_wdeg(assignment,csp):
    min=999999
    min_var=0
    for var in csp.variables:
        count=1
        if var not in assignment:
            #calculating the weight of each var and for each of his neighbor that is not assigned yet and we sum them all together
            for n in csp.neighbors[var]:
                if n not in assignment:
                    temp=csp.constr_dict[str(var)+' '+str(n)][1]
                    temp=int(temp)
                    #the sum is here
                    count=count+temp
            #here we take the variable with the minimum current_domain_size/weight_count (which is basically the dom/wdeg heuristic)
            if len(csp.curr_domains[var])/count < min:
                min=len(csp.curr_domains[var])/count
                min_var=var
    return min_var

#This is implemented like the backtracking algorithm above but with adjustments so we can backtrack more than 1 nodes
def fc_cbj(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):

    def backjump(assignment):
        if csp.goal_test(assignment)==True: #Termination state
            print("FC-CBJ:",assignment)
            print("Constraint checks = ",constr_counter)
            return None
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            global assignment_counter
            assignment_counter+=1
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    if constr_counter > constr_counter_limit: #This is the limit of the method measurements
                        return -1
                    result = backjump(assignment)
                    if result==-1: #If result is -1 we exceeded the limit of constr_counter and the method didnt find a solution
                        return -1
                    if result is None: #If result is None we found a solution
                        return None
                    if result==-9999: #If result is -9999 that means the conflicts set of the previous variable was empty(see below) so we backjump only 1 node (this one)
                        csp.restore(removals)
                        continue
                    if result!=var:  #If the result is not the node we want to backtrack the we unassign,we remove the unassigned node from everywhere in the conflicts set,we restore 
                                        #and we backtrack more
                        csp.unassign(var, assignment)
                        for i in range(0,len(csp.conflicts)): #deleting the variable we unassigned from everywhere in the conflicts set
                            if var in csp.conflicts[i]:
                                csp.conflicts[i].remove(var)
                        csp.restore(removals)
                        return result #we backtrack more (until we find the node that we need which is stored in 'result' (see below))
                csp.restore(removals)
        csp.unassign(var, assignment) #if we run out of domains we unassign
        for i in range(0,len(csp.conflicts)): #deleting the variable we unassigned from everywhere in the conflicts set
            if var in csp.conflicts[i]:
                csp.conflicts[i].remove(var)
        if csp.conflicts[var]==[]:  #If the conflicts set is empty result becomes -Inf so we teel the function that we only need to backjump 1 node and no more
            return -9999
        h=csp.conflicts[var][len(csp.conflicts[var])-1]  #h becomes the deepest node in the conflicts set of var
        for con in csp.conflicts[var]: #in this loop we add all items from the conflicts set of 'var' to h (except h of course)
            if con not in csp.conflicts[h] and con!=h:
                csp.conflicts[h].append(con)
        return h #we return h and the algorithm will restore and backtrack until we reach node h (see above how it backjumps)

    result = backjump({})
    return result

class rlfa(CSP):
    def __init__(self,f_1,f_2,f_3):
        variables=[]
        domains={}
        neighbors={}
        self.constr_dict={} #This dictionary holds each constraint for all variables and we do that because the problem does not have a constant constraint for all variables
        self.conflicts={} #This is used by the fc-cbj algorithm
        flag=0
        #here we set up the domains temporary list
        doms={}
        for row in f_2:
            #skip 1st row
            if flag==0:
                flag=1
                continue
            temp_list=[]
            k=2
            q=row[k]
            b="empty"
            #read the whole line and put numbers in a list
            while q!='\n':
                while not q.isspace() and q!='\n':
                    if b!="empty":
                        b+=q
                    else:
                        b=q
                    k+=1
                    q=row[k]
                b=int(b)
                temp_list.append(b)
                b="empty"
                if q!='\n':
                    k+=1
                    q=row[k]
            #this is the domains list based on dom.txt files
            doms[int(row[0])]=temp_list
        #here we assign every variable to it's domain list (ex. in var2-f24 the variable 0 has the 0 list of domains assigne to it)
        flag=0
        for i in f_1:
            #skip 1st row
            if flag==0:
                flag=1
                continue
            j="empty"
            k=0
            sp=i[0]
            while not sp.isspace():
                if j!="empty":
                    j=j+sp
                else:
                    j=sp
                k+=1
                sp=i[k]
            j=int(j)  
            variables.append(j)
            self.conflicts[j]=[]
            #setting up the domains for each variable based on its index in the dom file
            k+=1
            domains[j]=doms[int(i[k])].copy()
        #setting up neighbours here
        flag=0
        for row in f_3:
            if flag==0:
                for i in range(0,len(variables)):
                    neighbors[i]=[]
                flag=1
                continue
            first_num=-99999
            sec_num=-99999
            x=row[0]
            j="empty"
            k=0
            while not x.isspace():
                if j!="empty":
                    j=j+x
                else:
                    j=x
                k+=1
                x=row[k]
            j=int(j)  
            first_num=j
            j="empty"
            k+=1
            x=row[k]
            while not x.isspace():
                if j!="empty":
                    j=j+x
                else:
                    j=x
                k+=1
                x=row[k]
            j=int(j)  
            sec_num=j
            #here we make a neighbor for each of the 2 variables
            neighbors[first_num].append(sec_num)
            neighbors[sec_num].append(first_num)
            #here we add the constraint beween the 2 variables to our dictionary
            k+=1
            x=row[k]
            j="empty"
            while x!='\n':
                if j!="empty":
                    j=j+x
                else:
                    j=x
                k+=1
                x=row[k]
            self.constr_dict[str(first_num)+' '+str(sec_num)]=(j,1) #1 is the weight of the dom/wdeg heuristic
            self.constr_dict[str(sec_num)+' '+str(first_num)]=(j,1) #THIS IS TO ADD NEIGHBOR TO BOTH VARS
        super().__init__(variables, domains, neighbors, self.constraint_func)

    def constraint_func(self,A,a,B,b):
        #nothing to explain here just a function that converts strings to integers and does the calculation between 2 variables based on the constraint dictionary (see rlfa.init())
        constraint=self.constr_dict[str(A)+' '+str(B)]
        operator=constraint[0][0]
        k=constraint[0][2]
        for i in range(3,len(constraint[0])):
            k+=constraint[0][i]
        k=int(k)
        if operator=='>':
            if abs(a-b) > k:
                return True
            else:
                if(len(self.curr_domains[B])==1):
                    #If the algorithm reaches here it means a domain wipeout will occur soon about variable B so this next 5 lines are used to increase the weight used by dom/wdeg algorithm
                    temp=self.constr_dict[str(A)+' '+str(B)]
                    temp_2=temp[1]
                    temp_2=int(temp_2)
                    temp_2+=1
                    self.constr_dict[str(A)+' '+str(B)]=(temp[0],temp_2)
                    self.constr_dict[str(B)+' '+str(A)]=(temp[0],temp_2)
                return False
        if operator=='=':
            if abs(a-b) == k:
                return True
            else:
                if(len(self.curr_domains[B])==1):
                    #same as above
                    temp=self.constr_dict[str(A)+' '+str(B)]
                    temp_2=temp[1]
                    temp_2=int(temp_2)
                    temp_2+=1
                    self.constr_dict[str(A)+' '+str(B)]=(temp[0],temp_2)
                    self.constr_dict[str(B)+' '+str(A)]=(temp[0],temp_2)
                return False


    
#-------------MAIN-------------
#Choose your files with the problems here
f_1 = open("../rlfap_dataset/var2-f24.txt", "r")
f_2 = open("../rlfap_dataset/dom2-f24.txt", "r")
f_3 = open("../rlfap_dataset/ctr2-f24.txt", "r") 


solution=rlfa(f_1,f_2,f_3)
start_time = time.time()

"""
#Uncomment this section for fc algorithm
constr_counter_limit=40000000
run=backtracking_search(solution, select_unassigned_variable=dom_wdeg, inference=forward_checking)
if run==None:
    print("FC: There is no solution!!\n","Constraint checks =",constr_counter)
elif run==-1:
    print("FC: ","Constraint checks >",constr_counter)
else:
    print("FC: ",run,"\nConstraint checks =",constr_counter)
"""


"""
#Uncomment this section for mac algorithm
constr_counter_limit=1000000
run=backtracking_search(solution, select_unassigned_variable=mrv, inference=mac)
if run==None:
    print("MAC: There is no solution!!\n",constr_counter)
elif run==-1:
    print("MAC: ","Constraint checks >",constr_counter)
else:
    print("MAC: ",run,"\nConstraint checks =",constr_counter)
"""


"""
#Uncomment this section for fc-cbj algorithm
constr_counter_limit=40000000
run=fc_cbj(solution, select_unassigned_variable=dom_wdeg, inference=forward_checking)
if run==-1:
    print("FC-CBJ: ","Constraint checks >",constr_counter)
elif run!=None:
    print("FC-CBJ: There is no solution!!","\nConstraint checks =",constr_counter)
"""


"""
#Uncomment this section for min-con algorithm
max_steps=1000000
run=min_conflicts(solution)
if run==None:
    print("MIN-CON: Solution not found after ",max_steps, " steps.")
else:
    print("MIN-CON: ",run)
"""

print("CPU time:",time.time()-start_time)
if (assignment_counter != 0):
    print("Assignments:",assignment_counter,"\n")
f_1.close()
f_2.close()
f_3.close()
#------------------------------
