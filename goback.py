import pynusmv
import sys
import pprint

def spec_to_bdd(model, spec):
    """Return the set of states of `model` satisfying `spec`, as a BDD.

    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def research(fsm, bddspec):
    reach = fsm.init
    new = fsm.init
    sequence = []
    while fsm.count_states(new) > 0:
        notResp = new - bddspec
        if fsm.count_states(notResp) > 0:
            return fsm.pick_one_state_random(notResp), sequence
        sequence.append(new)
        new = fsm.post(new) - reach
        reach = reach + new
    return None, sequence

def compute_path(fsm, parent, current):
    inp_set = fsm.get_inputs_between_states(parent, current)
    inp = fsm.pick_one_inputs(inp_set)
    return parent, inp

def go_back(fsm, node, sequence):
    current = node
    init = fsm.init
    path = current,
    it = 1
    while (current * init).is_false():
        # intersection between the "back" set in the sequence and the
        # pre-image of the current considered state, this way we can
        # obtain all the nodes that are reachable and whose post image
        # is the current node
        parent_region = sequence[-it] & fsm.pre(current)
        # pick one from this set
        parent = fsm.pick_one_state(parent_region)
        path = compute_path(fsm, parent, current) + path
        current = parent
        it += 1
    return path

def check_explain_inv_spec(spec):
    """Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model
    satisfies `spec` or not. Return also an explanation for why the
    model does not satisfy `spec``, if it is the case, or `None`
    otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either
    `None` if the first element is `True``, or an execution of the SMV
    model violating `spec` otherwise.

    The execution is a tuple of alternating states and inputs,
    starting and ennding with a state. States and inputs are
    represented by dictionaries where keys are state and inputs
    variable of the loaded SMV model, and values are their value.

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(fsm, spec)
    node, reachable = research(fsm, bddspec) #ricerca per vedere se rispetta
    #funzione che costruisce l'albero e controllo su res
    if node is not None:
        path = go_back(fsm, node, reachable) # returns tuple of nodes
        str_path = ()
        for element in path:
            str_path = str_path + (element.get_str_values(), )
        return False, str_path
    else:
        return True, None

if len(sys.argv) != 2:
    print("Usage: ", sys.argv[0], " filename.smv")
    sys.exit(1)

# init 
pynusmv.init.init_nusmv()
filename = sys.argv[1]
# load file
pynusmv.glob.load_from_file(filename)
# compute model, goes to state of the library
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
# check all the property in the library status, if one is $invtype,
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    # then
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
