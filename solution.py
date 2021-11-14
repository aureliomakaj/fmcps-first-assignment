import sys
from typing import final
import pynusmv
from pynusmv.dd import BDD, Inputs, State
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    fsm = get_model_bddFsm()
    bdd_spec = spec_to_bdd(fsm, spec)

    reach = [fsm.init]
    init = [fsm.init]
    execution = []
    intersection = []
    goOn = True
    lastState = None
    while len(init) > 0 & goOn:
        toAnalize = init.pop()
        if toAnalize.intersected(~bdd_spec):
            intersection = toAnalize.intersection(~bdd_spec)
            lastState = toAnalize
            """print("---")
            print_states(fsm.pick_all_states(intersection))
            print("---")
            print_states(fsm.pick_all_states(toAnalize))"""
            goOn = False
        else:
            next = fsm.post(toAnalize)
            if not inList(reach, next):
                init.append(next)
                reach.append(next)

    if not goOn :
        res = find_path(fsm, fsm.pick_one_state(intersection))
        i = 0
        for elem in res:
            print("----")
            if i % 2 == 0:
                print_states(fsm.pick_all_states(elem))
            else: 
                if(elem.is_false()):
                    print("{}")
                else:
                    print_states(fsm.pick_all_inputs(elem))
            i += 1

    return goOn, execution

def find_path(bddFsm: BddFsm, final_state: State) :
    inputs = bddFsm.pick_all_inputs(final_state)
    pre = bddFsm.pre(final_state)
    print("---")
    print_states(bddFsm.pick_all_states(bddFsm.pre(pre)))
    """hasInputVariables = len(bddFsm.bddEnc.inputsVars) > 0
    found = False
    paths = [[bddFsm.init]]
    inspected = [bddFsm.init]
    while not found:
        tmp = []
        for path in paths:
            bdd = path[-1]
            if bdd.equal(final_states):
                return path
                
            if hasInputVariables:
                inputs = bddFsm.pick_all_inputs(bdd)
                for input in inputs:
                    post = bddFsm.post(bdd, input)
                    if not inList(inspected, post):
                        inspected.append(post)
                        path.append(input)
                        path.append(post)
                        tmp.append(path)
            else:
                post = bddFsm.post(bdd)
                if not inList(inspected, post):
                    inspected.append(post)
                    path.append(BDD.false())
                    path.append(post)
                    tmp.append(path)
        paths = tmp
    return []"""

def spec_to_bdd(model: BddFsm, spec: Spec) -> BDD:
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

    
def open_model():
    """
        Read the filename passed in the args and load the SMV model associated
        with it. 
    """
    #Check the correct number of args
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load(filename)
    pynusmv.glob.compute_model()


def get_model_bddFsm() -> BddFsm :
    """
    Get the BDD-encoded finite-state machine representing the SMV model
    """
    return pynusmv.glob.prop_database().master.bddFsm


def print_states(states):
    for state in states:
        print(state.get_str_values())

def inList(bddList, bdd: BDD):
    return any(bdd.equal(elem) for elem in bddList)

if __name__ == "__main__":
    open_model()

    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            my_res, my_trace= check_explain_inv_spec(spec)
            ltlspec = pynusmv.prop.g(spec)
            res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
            if(res == my_res):
                print("Same result, that is ", res)
                if not res:
                    """print("My trace: ")
                    print_states(my_trace)"""
                    print("Other trace: ")
                    print(trace)
            else:
                print("Different result. My: ", my_res, " .... Correct: ", res)

            """if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)"""
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()

