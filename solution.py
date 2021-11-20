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
    counter_example = []

    #Variable used to save the BDD representing all the states reached
    reach = fsm.init
    #Variable used to save the BDD reprenting the current region
    next = fsm.init
    #We save the BDDs of post operations. This will be used for the counter-example, if it is needed
    execution = [next]
    #Variable used to tell if the model satisfies the property or not
    satisfy = True
    """
        We iterate until there are no more new states to look 
        or we have found a state that violates our property
    """
    while (not next.is_false()) & satisfy:
        """
            If the intersection of the states we are currently looking at with 
            the negation of the property is not empty, this means that we have found
            at least one state that violates our property. Our search finish here.
        """
        satisfy = next.intersected(~bdd_spec) == False
        #If there are no violating states
        if satisfy: 
            #Update the current region with the next one, removing the ones we already visited
            next = fsm.post(next) - reach
            #Update BDD that represents the states we visited
            reach = reach + next
            #Append the BDD of the region in the least
            execution.append(next)

    #If the property is not satisfied, find a counter-example
    if not satisfy: 
        counter_example = find_counter_example(fsm, bdd_spec, next, execution)

    return tuple([satisfy, None if satisfy else tuple(counter_example)])


def find_counter_example(fsm: BddFsm, bdd_spec: BDD, last_bdd: BDD, execution: list) -> list:
    """
        Given the FSM of the model, the BDD of the property, the region
        where the property is not satisfied, that is where the negation of the property
        is satisfied, and a list of all the post operations, compute the counter-example. 
    """
    #Store the counter-example
    counter_example = []
    """
        Check if the model has inputs. The functions that works on inputs give an error
        if the model hasn't input variables.
    """
    has_inputs = len(fsm.bddEnc.inputsVars) > 0
    #We pick a state that doesn't satisfy the property
    last = fsm.pick_one_state(last_bdd.intersection(~bdd_spec))
    #We add to our counter_example
    counter_example.append(last.get_str_values())
    #Is the current BDD
    next = last
    #Last is the BDD of the pre operation
    last = fsm.pre(next)
    #We start from the second to last position, given that we already have choose a state for the last position
    i = len(execution) - 2
    
    #While we have not intersected all the BDD of the post-operations
    while i >= 0:
        intersect = execution[i].intersection(last)
        state = fsm.pick_one_state(intersect)
        if has_inputs:
            #Get the possible inputs from the current state and the next one
            #and insert it in the counter_example
            inputs = fsm.get_inputs_between_states(state, next)
            counter_example.insert(0, fsm.pick_one_inputs(inputs).get_str_values())
        else:
            counter_example.insert(0, {})
        #Insert the current state
        counter_example.insert(0, state.get_str_values())
        #Update the next state with the current one
        next = state
        #Find the states that goes into current state
        last = fsm.pre(next)
        i -= 1

    return counter_example

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

if __name__ == "__main__":
    open_model()

    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, counter_example = check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(counter_example)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()

