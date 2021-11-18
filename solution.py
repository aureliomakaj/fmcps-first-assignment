import sys
import pynusmv
from pynusmv.dd import BDD
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
    #Get the Finite State Machine of the model
    fsm = get_model_bddFsm()
    #Get the BDD of our property
    bdd_spec = spec_to_bdd(fsm, spec)
    #Variable used to save the counter-example, if the property is not satisfied.
    trace = []

    #BDD representing all the states reached
    reach = fsm.init
    #BDD reprenting the current region
    next = fsm.init
    #We save the BDDs of the 'next' BDDs encountered in the searching
    execution = [next]
    #If the model satisfies the property or not
    satisfy = True
    """
        We iterate until there are no more states to look 
        and we haven't found a state that violates our property
    """
    while (not next.is_false()) & satisfy:
        """
            If the intersection of the states we are currently looking at and 
            the negation of the property is not empty, this means that we have found
            at least one state that violates our property. Our search finish here.
        """
        found = next.intersected(~bdd_spec)
        #If there are not violating states
        if satisfy: 
            #Update the current region with the next one, removing the ones we already visited
            next = fsm.post(next) - reach
            #Update the states we visited
            reach = reach + next
            #Save the BDD of the region
            execution.append(next)

    
    if not satisfy: 
        has_inputs = len(fsm.bddEnc.inputsVars) > 0
        last = fsm.pick_one_state(next.intersection(~bdd_spec))
        trace.append(last.get_str_values())
        next = last
        last = fsm.pre(last)
        i = len(execution) - 2
        while i >= 0:
            intersect = execution[i].intersection(last)
            if has_inputs:
                inputs = fsm.get_inputs_between_states(intersect, next)
                trace.insert(0, fsm.pick_one_inputs(inputs).get_str_values())
            else:
                trace.insert(0, {})
            trace.insert(0, fsm.pick_one_state(intersect).get_str_values())
            next = last
            last = fsm.pre(intersect)
            i -= 1


    return satisfy, tuple(trace)


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
                    print("My trace: ")
                    print(my_trace)
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

