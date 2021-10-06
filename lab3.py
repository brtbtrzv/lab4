# MIT 6.034 Lab 3: Constraint Satisfaction Problems
# Written by 6.034 staff
import copy

from constraint_api import *
import itertools
from test_problems import get_pokemon_problem


#### Part 1: Warmup ############################################################

def has_empty_domains(csp):
    """Returns True if the problem has one or more empty domains, otherwise False"""
    for variable in csp.variables:
        if not len(csp.get_domain(variable)):
            return True
    return False


def check_all_constraints(csp):
    """Return False if the problem's assigned values violate some constraint,
    otherwise True"""
    for constraint in csp.get_all_constraints():
        value1 = csp.assignments.get(constraint.var1, None)
        value2 = csp.assignments.get(constraint.var2, None)
        if value1 is not None and value2 is not None and not constraint.check(value1, value2):
            return False
    return True


#### Part 2: Depth-First Constraint Solver #####################################

def solve_constraint_dfs(problem):
    """
    Solves the problem using depth-first search.  Returns a tuple containing:
    1. the solution (a dictionary mapping variables to assigned values)
    2. the number of extensions made (the number of problems popped off the agenda).
    If no solution was found, return None as the first element of the tuple.
    """
    queue = [problem]
    extensions = 0
    while len(queue) != 0:
        extensions += 1
        problem = queue.pop(0)
        if not check_all_constraints(problem) or has_empty_domains(problem):
            continue
        if check_all_constraints(problem):
            if len(problem.unassigned_vars) == 0:
                return problem.assignments, extensions
            var = problem.pop_next_unassigned_var()
            problems_list = []
            for val in problem.get_domain(var):
                new_problem = copy.deepcopy(problem)
                new_problem.set_assignment(var, val)
                problems_list.append(new_problem)
            queue = problems_list + queue
    return None, extensions


# QUESTION 1: How many extensions does it take to solve the Pokemon problem
#    with DFS?
# Hint: Use get_pokemon_problem() to get a new copy of the Pokemon problem
#    each time you want to solve it with a different search method.
pokemon_problem = get_pokemon_problem()
print(solve_constraint_dfs(pokemon_problem))
ANSWER_1 = 20


#### Part 3: Forward Checking ##################################################

def eliminate_from_neighbors(csp, var):
    """
    Eliminates incompatible values from var's neighbors' domains, modifying
    the original csp.  Returns an alphabetically sorted list of the neighboring
    variables whose domains were reduced, with each variable appearing at most
    once.  If no domains were reduced, returns empty list.
    If a domain is reduced to size 0, quits immediately and returns None.
    """
    result = []
    for neighbor in csp.get_neighbors(var):
        current_list = []
        for domain_val in csp.get_domain(neighbor):
            r = 0
            for val in csp.get_domain(var):
                flag = 1
                for c in csp.constraints_between(var, neighbor):
                    flag *= c.check(val, domain_val)
                if flag:
                    r = 1
                    break
            if r == 0:
                current_list.append(domain_val)
        for elem in current_list:
            csp.eliminate(neighbor, elem)
            if neighbor not in result:
                result.append(neighbor)
        if len(csp.get_domain(neighbor)) == 0:
            return None
    result = sorted(result)
    return result


# Because names give us power over things (you're free to use this alias)
forward_check = eliminate_from_neighbors


def solve_constraint_forward_checking(problem):
    """
    Solves the problem using depth-first search with forward checking.
    Same return type as solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0
    while queue:
        extensions += 1
        problem = queue.pop(0)
        if not check_all_constraints(problem) or has_empty_domains(problem):
            continue
        if check_all_constraints(problem):
            if len(problem.unassigned_vars) == 0:
                return problem.assignments, extensions
            else:
                var = problem.pop_next_unassigned_var()
                new_problems = []
                for val in problem.get_domain(var):
                    new_problem = problem.copy()
                    new_problem.set_assignment(var, val)
                    forward_check(new_problem, var)
                    new_problems.append(new_problem)
                queue = new_problems + queue
    return None, extensions


# QUESTION 2: How many extensions does it take to solve the Pokemon problem
#    with DFS and forward checking?
pokemon_problem = get_pokemon_problem()
print(solve_constraint_forward_checking(pokemon_problem))
ANSWER_2 = 9


#### Part 4: Domain Reduction ##################################################

def domain_reduction(csp, queue=None):
    """
    Uses constraints to reduce domains, propagating the domain reduction
    to all neighbors whose domains are reduced during the process.
    If queue is None, initializes propagation queue by adding all variables in
    their default order. 
    Returns a list of all variables that were dequeued, in the order they
    were removed from the queue.  Variables may appear in the lists multiple times.
    If a domain is reduced to size 0, quits immediately and returns None.
    This function modifies the original csp.
    """
    answer = []
    q = copy.deepcopy(queue)
    if queue is None:
        q = csp.get_all_variables()
    while q:
        var = q.pop(0)
        answer.append(var)
        list = eliminate_from_neighbors(csp, var)
        if list:
            for neighbor in list:
                if neighbor not in q:
                    q.append(neighbor)
        if list is None:
            return list
    return answer


# QUESTION 3: How many extensions does it take to solve the Pokemon problem
#    with DFS (no forward checking) if you do domain reduction before solving it?
pokemon_problem = get_pokemon_problem()
domain_reduction(pokemon_problem)
print(solve_constraint_dfs(pokemon_problem))
ANSWER_3 = 6


def solve_constraint_propagate_reduced_domains(problem):
    """
    Solves the problem using depth-first search with forward checking and
    propagation through all reduced domains.  Same return type as
    solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0

    while queue:
        extensions += 1
        problem = queue.pop(0)
        if check_all_constraints(problem) or not has_empty_domains(problem):
            if check_all_constraints(problem):
                if len(problem.unassigned_vars) == 0:
                    return problem.assignments, extensions
                else:
                    var = problem.pop_next_unassigned_var()
                    problems_list = []

                    for val in problem.get_domain(var):
                        new_problem = copy.deepcopy(problem)
                        new_problem.set_assignment(var, val)
                        domain_reduction(new_problem, [var])
                        forward_check(new_problem, var)
                        problems_list.append(new_problem)
                    queue = problems_list + queue
    return None, extensions

# QUESTION 4: How many extensions does it take to solve the Pokemon problem
#    with forward checking and propagation through reduced domains?

pokemon_problem = get_pokemon_problem()
print(solve_constraint_propagate_reduced_domains(pokemon_problem))
ANSWER_4 = 7


#### Part 5A: Generic Domain Reduction #########################################

def propagate(enqueue_condition_fn, csp, queue=None):
    """
    Uses constraints to reduce domains, modifying the original csp.
    Uses enqueue_condition_fn to determine whether to enqueue a variable whose
    domain has been reduced. Same return type as domain_reduction.
    """
    answer = []
    if queue is None:
        queue = csp.get_all_variables()
    while queue:
        var = queue.pop(0)
        answer.append(var)
        eliminated_neighbors = forward_check(csp, var)
        if eliminated_neighbors is None:
            return None
        for eliminated_neighbor in eliminated_neighbors:
            if eliminated_neighbor not in queue and enqueue_condition_fn(csp, eliminated_neighbor):
                queue.append(eliminated_neighbor)
    return answer


def condition_domain_reduction(csp, var):
    """Returns True if var should be enqueued under the all-reduced-domains
    condition, otherwise False"""
    if not csp:
        return True
    return len(csp.get_domain(var)) == 0


def condition_singleton(csp, var):
    """Returns True if var should be enqueued under the singleton-domains
    condition, otherwise False"""
    if len(csp.get_domain(var)) == 1:
        return True
    return False


def condition_forward_checking(csp, var):
    """Returns True if var should be enqueued under the forward-checking
    condition, otherwise False"""
    return False


#### Part 5B: Generic Constraint Solver ########################################

def solve_constraint_generic(problem, enqueue_condition=None):
    """
    Solves the problem, calling propagate with the specified enqueue
    condition (a function). If enqueue_condition is None, uses DFS only.
    Same return type as solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0
    while queue:
        extensions += 1
        problem = queue.pop(0)
        if not check_all_constraints(problem) or has_empty_domains(problem):
            continue

        if check_all_constraints(problem):
            if len(problem.unassigned_vars) == 0:
                return problem.assignments, extensions
            var = problem.pop_next_unassigned_var()
            problems_list = []
            for val in problem.get_domain(var):
                new_problem = problem.copy()
                new_problem.set_assignment(var, val)
                if enqueue_condition is not None:
                    propagate(enqueue_condition, new_problem, [var])
                problems_list.append(new_problem)
            queue = problems_list + queue
    return None, extensions


# QUESTION 5: How many extensions does it take to solve the Pokemon problem
#    with forward checking and propagation through singleton domains? (Don't
#    use domain reduction before solving it.)

pokemon_problem = get_pokemon_problem()
print(solve_constraint_generic(pokemon_problem, condition_forward_checking))
ANSWER_5 = 8


#### Part 6: Defining Custom Constraints #######################################

def constraint_adjacent(m, n):
    """Returns True if m and n are adjacent, otherwise False.
    Assume m and n are ints."""
    return True if abs(m - n) == 1 else False


def constraint_not_adjacent(m, n):
    """Returns True if m and n are NOT adjacent, otherwise False.
    Assume m and n are ints."""
    return not constraint_adjacent(m, n)


def all_different(variables):
    """Returns a lists of constraints, with one difference constraint between
    each pair of variables."""
    combinations = list(set(itertools.combinations(variables, 2)))
    result = []
    for elem in combinations:
        result.append(Constraint(elem[0], elem[1], constraint_different))
    return result
