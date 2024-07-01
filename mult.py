import sys
import os


class Transition:
    def __init__(self, from_state, to_state=None, guards=None, updates=None):
        if updates is None:
            updates = []
        if guards is None:
            guards = []
        self.from_state = from_state
        self.to_state = to_state
        self.guards = guards
        self.updates = updates


class TransitionSystem:
    def __init__(self, states, initial_state, pre_condition, cut_points, transitions):
        self.states = states
        self.initial_state = initial_state
        self.transitions = transitions
        self.cut_points = cut_points
        self.target_set = None
        self.pre_condition=pre_condition


class AutomataTransition:
    def __init__(self, from_state, to_state=None, guards=None, if_lines=None, if_not_lines=None):
        if if_not_lines is None:
            if_not_lines = []
        if if_lines is None:
            if_lines = []
        if guards is None:
            guards = []
        self.from_state = from_state
        self.to_state = to_state
        self.guards = guards
        self.if_lines = if_lines
        self.if_not_lines = if_not_lines


class BuchiAutomata:
    def __init__(self, states, target_states, initial_state, transitions):
        self.states = states
        self.target_states = target_states
        self.initial_state = initial_state
        self.transitions = transitions


def has_subset_transition(tra, tras):
    for transition in tras:
        if transition.from_state == tra.from_state and transition.to_state == tra.to_state and transition is not tra and set(transition.guards).issubset(set(tra.guards)) and set(transition.updates) == set(tra.updates):
            return True
    return False


def check_repetitive_transitions(tras):
    tmp = []
    for i in range(len(tras)):
        for j in range(i + 1, len(tras)):
            t1 = tras[i]
            t2 = tras[j]
            if t1.from_state == t2.from_state and t1.to_state == t2.to_state and set(t1.guards) == set(t2.guards) and set(t1.updates) == set(t2.updates):
                tmp.append(t2)
    for tau in tmp:
        if tau in tras:
            tras.remove(tau)


def multiply_ts_buchi(transition_system, buchi_automata):
    target_states = set()
    cut_points = set()
    initial_state = str(int(transition_system.initial_state) * 1000 + int(buchi_automata.initial_state))
    edges_from = {}

    new_transitions = []
    for transition in transition_system.transitions:
        for automata_transition in buchi_automata.transitions:
            # print(automata_transition.if_lines)
            # print(automata_transition.if_not_lines)
            if automata_transition.if_lines != [] and transition.from_state not in automata_transition.if_lines:
                continue
            if automata_transition.if_not_lines != [] and transition.from_state in automata_transition.if_not_lines:
                continue
            new_transition = Transition(str(int(transition.from_state) * 1000 + int(automata_transition.from_state)),
                                        str(int(transition.to_state) * 1000 + int(automata_transition.to_state)),
                                        transition.guards + automata_transition.guards,
                                        transition.updates)
            if transition.from_state in transition_system.cut_points:
                cut_points.add(new_transition.from_state)
            if transition.to_state in transition_system.cut_points:
                cut_points.add(new_transition.to_state)
            new_transitions.append(new_transition)
            if new_transition.from_state not in edges_from:
                edges_from[new_transition.from_state] = []
            edges_from[new_transition.from_state].append(new_transition.to_state)
            if automata_transition.from_state in buchi_automata.target_states:
                target_states.add(new_transition.from_state)
            if automata_transition.to_state in buchi_automata.target_states:
                target_states.add(new_transition.to_state)

    # print(edges_from['1001001'])
    # print(initial_state)
    reachable = set()
    reachable_cut_points = set()
    q = [initial_state]
    while q:
        tmp = q.pop()
        if tmp in edges_from:
            for e in edges_from[tmp]:
                if e not in reachable:
                    q.append(e)
        reachable.add(tmp)
        if tmp in cut_points:
            reachable_cut_points.add(tmp)

    check_repetitive_transitions(new_transitions)

    final_transitions = []
    for transition in new_transitions:
        if transition.from_state in reachable and not has_subset_transition(transition, new_transitions):
            final_transitions.append(transition)

    final_targets = []
    for ts in target_states:
        if ts in reachable:
            final_targets.append(ts)

    transition_s = TransitionSystem(list(reachable), initial_state, transition_system.pre_condition, list(reachable_cut_points), final_transitions)
    transition_s.target_set = final_targets
    return transition_s


def multiply_ts_ts(ts1, ts2):
    cut_points = set()
    states = set()
    initial_state = str(int(ts1.initial_state) * 1000 + int(ts2.initial_state))

    new_transitions = []
    for transition in ts1.transitions:
        for state in ts2.states:
            new_transition = Transition(str(int(transition.from_state) * 1000 + int(state)),
                                        str(int(transition.to_state) * 1000 + int(state)),
                                        transition.guards, transition.updates)
            states.add(str(int(transition.from_state) * 1000 + int(state)))
            states.add(str(int(transition.to_state) * 1000 + int(state)))
            if transition.from_state in ts1.cut_points:
                cut_points.add(new_transition.from_state)
            if transition.to_state in ts1.cut_points:
                cut_points.add(new_transition.to_state)
            if state in ts2.cut_points:
                cut_points.add(state)
            new_transitions.append(new_transition)
    for transition in ts2.transitions:
        for state in ts1.states:
            new_transition = Transition(str(int(transition.from_state) + int(state) * 1000),
                                        str(int(transition.to_state) + int(state) * 1000),
                                        transition.guards, transition.updates)
            states.add(str(int(transition.from_state) + int(state) * 1000))
            states.add(str(int(transition.to_state) + int(state) * 1000))
            if transition.from_state in ts2.cut_points:
                cut_points.add(new_transition.from_state)
            if transition.to_state in ts2.cut_points:
                cut_points.add(new_transition.to_state)
            if state in ts1.cut_points:
                cut_points.add(state)
            new_transitions.append(new_transition)

    transition_s = TransitionSystem(list(states), initial_state, list(cut_points), new_transitions)

    return transition_s


def read_transition_system(address):
    f = open(address, "r")
    line = f.readline()
    start_state = ''
    states = set()
    cut_points = []
    transitions = []
    new_transition = None
    pre_condition = None
    while line:
        if line.isspace():
            line = f.readline()
            continue
        if line.startswith('START'):
            start_state = line[7:-2]
            states.add(start_state)
        elif line.startswith('PRE'):
            pre_condition=line[4:-2]
        elif line.startswith('CUTPOINT'):
            cut_points = line[9:-2].replace('{', '').replace('}', '').replace(' ', '').split(',')
        elif line.startswith('FROM'):
            states.add(line[6:-2])
            if new_transition is not None:
                transitions.append(new_transition)
            new_transition = Transition(line[6:-2])
        elif line.startswith('TO'):
            states.add(line[4:-2])
            new_transition.to_state = line[4:-2]
        elif line.startswith('assume'):
            new_transition.guards.append(line)
        else:
            new_transition.updates.append(line)
        line = f.readline()

    if new_transition is not None:
        transitions.append(new_transition)

    return TransitionSystem(list(states), start_state, pre_condition, cut_points, transitions)


def read_buchi_automata(address):
    f = open(address, "r")
    line = f.readline()
    start_state = ''
    buchi_target = []
    states = set()
    buchi_transitions = []
    new_transition = None
    while line:
        if line.isspace():
            line = f.readline()
            continue
        if line.startswith('START'):
            start_state = line[7:-2]
            if not str.isdigit(start_state):
                raise Exception("buchi bad syntax 1")
            states.add(start_state)
        elif line.startswith('BUCHI'):
            buchi_target = line[7:-2].split()
            for bt in buchi_target:
                if not str.isdigit(bt):
                    raise Exception("buchi bad syntax 2")
                states.add(bt)
        elif line.startswith('FROM'):
            if not str.isdigit(line[6:-2]):
                raise Exception("buchi bad syntax 3")
            states.add(line[6:-2])
            if new_transition is not None:
                buchi_transitions.append(new_transition)
            new_transition = AutomataTransition(line[6:-2])
        elif line.startswith('TO'):
            if not str.isdigit(line[4:-2]):
                raise Exception("buchi bad syntax 1")
            states.add(line[4:-2])
            new_transition.to_state = line[4:-2]
        elif line.startswith('assume_line'):
            new_transition.if_lines.append(line[12:-3])
        elif line.startswith('assume_not_line'):
            new_transition.if_not_lines.append(line[16:-3])
        elif line.startswith('assume'):
            new_transition.guards.append(line)
        else:
            print(line)
            raise Exception()
        line = f.readline()

    if new_transition is not None:
        buchi_transitions.append(new_transition)

    return BuchiAutomata(list(states), buchi_target, start_state, buchi_transitions)


def write_transition_system(transition_system, address):
    f = open(address, "w")
    f.write('START: ' + transition_system.initial_state + ';\n')
    if transition_system.target_set:
        tmp = ''
        for ts in transition_system.target_set:
            tmp += ts + ', '
        f.write('BUCHI: {' + tmp[:-2] + '};\n')
    tmp = ''
    for ts in transition_system.states:
        tmp += ts + ', '
    # f.write('CUTPOINT: {' + tmp[:-2] + '};\n\n')
    if transition_system.pre_condition is not None:
        f.write(f"PRE: {transition_system.pre_condition};\n")
    for transition in transition_system.transitions:
        f.write('\n')
        f.write('FROM: ' + transition.from_state + ';\n')
        if transition.guards:
            for g in transition.guards:
                f.write(g)
        if transition.updates:
            for u in transition.updates:
                f.write(u)
        f.write('TO: ' + transition.to_state + ';\n')

    f.close()


def produce_transition_system_times_buchi(ts_name, buchi_name,output_file):
    transition_system = read_transition_system(ts_name)
    buchi_automata = read_buchi_automata(buchi_name)
    multiply_result = multiply_ts_buchi(transition_system, buchi_automata)
    write_transition_system(multiply_result, output_file)


def produce_transition_system_times_transition_system(file_address, ts1_name, ts2_name):
    ts1 = read_transition_system(file_address + ts1_name + '.c.t2')
    ts2 = read_transition_system(file_address + ts2_name + '.c.t2')
    multiply_result = multiply_ts_ts(ts1, ts2)
    write_transition_system(multiply_result, file_address + ts1_name + '*' + ts2_name + '.c.t2')


name1, name2, output_file= sys.argv[1], sys.argv[2], sys.argv[3]
produce_transition_system_times_buchi(name1, name2,output_file)