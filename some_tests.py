import sys
import pynusmv

from pynusmv.prop import Prop

global file

def printBdd(bdd):
    pynusmv.glob.bdd_encoding().dump(bdd, file)

def my_func(prop: Prop):
    bdd = pynusmv.mc.eval_ctl_spec(prop.bddFsm, prop)
    init = prop.bddFsm
    #printBdd(bdd)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    file = open('other_file.txt', 'w')
    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load(filename)
    pynusmv.glob.compute_model()

    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            my_func(prop)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")
    #pynusmv.glob.bdd_encoding().dump(pynusmv.glob.bdd_encoding().inputsMask, file)
    #for prop in pynusmv.glob.prop_database():
    
    file.close()
    pynusmv.init.deinit_nusmv()
