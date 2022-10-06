from typing import Set, List

import z3

# Process input and create handy arrays.
s = z3.Solver()
n, k = map(int, input().split())
relations = [tuple(map(int, input().split())) for _ in range(k)]
predicates = [z3.Bool(f"p{i}") for i in range(k)]
z3_ints = [z3.Int(str(i)) for i in range(n)]

# First we want to check if the given relations form a cycle.
for p, (x, y) in zip(predicates, relations):
    s.add(z3.Implies(p, z3_ints[x] < z3_ints[y]))

# z3.sat means the system of constraints is satisfiable.
is_partial_order = s.check(predicates) == z3.sat

# If a cycle is present, print the nodes forming the cycle.
if not is_partial_order:
    violations = set()
    for p in s.unsat_core():
        idx = int(str(p)[1:])
        x, y = relations[idx]
        violations.add(str(x))
        violations.add(str(y))
    print(' '.join(sorted(violations, key=lambda q: int(q))))
    exit(0)


def find_extremums(nodes: Set[int], find_minimums: bool = False) -> Set[int]:
    """
    Find all extremum(maximum or minimum based on `find_minimums` parameter) nodes in `nodes` and return them as a set.
    Ruins the solver context: to retain it, use s.push() and s.pop() before and after the function invocation.
    """
    result_extreme_nodes = set()

    # We will denote the extremum value as `x` and add corresponding constraints to the solver.
    extremum = z3.Int('x')
    for i in nodes:
        if find_minimums:
            s.add(extremum <= z3_ints[i])
        else:
            s.add(extremum >= z3_ints[i])

    while True:
        # Save the solver state and add a constraint meaning that an extremum must be one of the nodes.
        s.push()
        s.add(z3.Or([extremum == z3_ints[i] for i in nodes]))

        # If no more extremums were found, return.
        has_extremum = s.check() == z3.sat
        if not has_extremum:
            return result_extreme_nodes

        # Retrieve the extremum value as an int.
        model = s.model()
        extreme_value = model[extremum].as_long()

        # All the nodes with the same value are extremums.
        # Note that the loop continues because this is a sufficient but not a necessary condition.
        # Don't forget to remove the found extremum nodes from the current node list (`nodes`).
        extreme_nodes = [i for i in nodes if model[z3_ints[i]].as_long() == extreme_value]
        result_extreme_nodes.update(extreme_nodes)
        for extreme_node in extreme_nodes:
            nodes.remove(extreme_node)
        s.pop()


def find_levels(find_minimums: bool) -> List[List[int]]:
    """
    Returns a list of levels, where each level is a set of extremum nodes.
    1) Get all extremum nodes.
    2) Save them as a "level" in `ranged_nodes`.
    3) Remove them from `current_nodes`.
    4) If not over, go to 1).
    """
    ranged_nodes = []
    current_nodes = set(range(n))
    while len(current_nodes) > 0:
        s.reset()
        for x, y in relations:
            if x in current_nodes and y in current_nodes:
                s.add(z3_ints[x] < z3_ints[y])
        extremums = find_extremums(current_nodes, find_minimums=find_minimums)
        ranged_nodes.append(sorted(extremums))
    return ranged_nodes


maximum_levels = find_levels(find_minimums=False)
minimum_levels = find_levels(find_minimums=True)

# The first maximum "level" nodes are the maximums of the whole input.
maximums = maximum_levels[0]
if len(maximums) > 1:
    print("greatest not exist")  # aka greatest DOES not exist
else:
    print(maximums[0])

# The first minimum "level" nodes are the minimums of the whole input.
minimums = minimum_levels[0]
if len(minimums) > 1:
    print("least not exist")
else:
    print(minimums[0])

print(' '.join(map(str, maximums)))
print(' '.join(map(str, minimums)))

# If any level has two or more nodes, they are incomparable and no linear order exists.
# Otherwise, the linear order is obvious: it is stored in `ranged_nodes`.
is_linear_order = all(len(same_level_nodes) == 1 for same_level_nodes in minimum_levels + maximum_levels)
print(int(is_linear_order))

# Compute the maximum_level and minimum_level for each node for convenience.
maximum_level = {}
for i, same_level_nodes in enumerate(maximum_levels):
    for node in same_level_nodes:
        maximum_level[node] = i

minimum_level = {}
for i, same_level_nodes in enumerate(minimum_levels):
    for node in same_level_nodes:
        minimum_level[node] = i

# If the nodes of the relation are more than one level apart, the relation is excessive.
for x, y in relations:
    if maximum_level[y] + 1 == maximum_level[x] or minimum_level[y] - 1 == minimum_level[x]:
        print(x, y)
