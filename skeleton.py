
MAX_CONSTANTS = 10

# Constant term declaration
PROPOSITION = ["p", "q", "r", "s"]
NEGATED_PROPOSITION = [f"~{p}" for p in PROPOSITION]
BINARY_CONNECTIVE = ["=>", "\\/", "/\\"]
VARIABLES = ["x", "y", "z", "w"]
PREDICATES = ["P", "Q", "R", "S"]
ATOMS = [f"{p}({v1},{v2})" for p in PREDICATES for v1 in VARIABLES for v2 in VARIABLES]
NEGATED_ATOMS = [f"~{a}" for a in ATOMS]

# Syntax for logical parsing
PROPOSITIONAL_LOGIC = PROPOSITION + BINARY_CONNECTIVE + ["~", "(", ")"]
FIRST_ORDER_LOGIC = (
    VARIABLES + PREDICATES + BINARY_CONNECTIVE + ["~", "(", ")", " ", ",", "E", "A"]
)

# Logical formula cases for tableau classification
ALPHA = ["/\\", "~~", "~\\/", "~=>"]
BETA = ["\\/", "~/\\", "=>"]
DELTA = ["E", "~A"]
GAMMA = ["A", "~E"]

CONSTANTS = [chr(x) for x in range(ord("a"), ord("j") + 1)] # Constants for substitution

PICKED = [] # Tracks the constants used for substitution

# Exception classes
class NotAFormula(Exception):
    pass


class TooManyConstants(Exception):
    pass


class AllClosedTermsPicked(Exception):
    pass

# Function to determine first-order logic formulas
def first_order(fmla):
    if fmla == "":
        return False
    
    i = 0
    length = len(fmla)

    while i < length:
        if fmla[i] in FIRST_ORDER_LOGIC:
            i += 1
        elif i + 1 < length and fmla[i:i + 2] in BINARY_CONNECTIVE:
            # If a two-character binary connective is found, move the index by 2
            i += 2
        else:
            return False
    
    try:
        if parse(fmla) == 0:
            return False
        else:
            return True
    except NotAFormula:
        return False


# Function to determine propositional logic formulas
def prop_formula(fmla):
    if fmla == "":
        return False

    i = 0
    length = len(fmla)

    while i < length:
        if fmla[i] in PROPOSITIONAL_LOGIC:
            i += 1
        elif i + 1 < length and fmla[i:i + 2] in BINARY_CONNECTIVE:
            # If a two-character binary connective is found, move the index by 2
            i += 2
        else:
            return False
    
    try:
        if parse(fmla) == 0:
            return False
        else:
            return True
    except NotAFormula:
        return False


# Function to determine the main binary connective in a formula
def main_connective(fmla):
    parenthesis_scope = []
    length = len(fmla)

    count = 0
    while count < length:
        char = fmla[count]

        # Check for binary connectives with two characters
        if count + 1 < length:
            two_char_connective = fmla[count:count + 2]
            if two_char_connective in BINARY_CONNECTIVE and len(parenthesis_scope) == 1:
                return count

        # Handle parentheses to determine the scope level
        if char == "(":
            parenthesis_scope.append("a")
        elif char == ")":
            try:
                parenthesis_scope.pop()
            except IndexError:
                raise NotAFormula

        # Move to the next character
        count += 1

    # If no main connective is found, raise NotAFormula exception
    raise NotAFormula


# Return the LHS of a binary connective formula
def lhs(fmla):
    index = main_connective(fmla)
    return fmla[1:index]  # LHS starts right after the '(' and ends at the main connective

# Return the main connective of a formula
def con(fmla):
    index = main_connective(fmla)
    connective_length = 2  # The length of each binary connective is 2 characters
    return fmla[index:index + connective_length]


# Return the RHS of a binary connective formula
def rhs(fmla):
    index = main_connective(fmla)
    connective_length = 2  # Binary connectives are two characters long
    return fmla[index + connective_length: len(fmla) - 1]  # RHS starts after the connective and ends before ')'

# Parses a formula and returns the type of formula
def parse(fmla):
    if fmla in PROPOSITION:  # Return "A proposition" if formula is a proposition.
        return 6

    elif (
        fmla in NEGATED_PROPOSITION
    ):  # Return "Negated propositional formula" if formula is a negated proposition.
        return 7

    elif fmla in ATOMS:  # Return "an atom" if the formula is an atom.
        return 1

    elif (
        fmla[0] == "E" and fmla[1] in VARIABLES
    ):  # Return "an existentially quantified formula" if whatever follows after "Ex" is a first order formula,
        # else return "not a formula".]
        if first_order(fmla[2:]):
            return 4
        else:
            return 0
    elif (
        fmla[0] == "A" and fmla[1] in VARIABLES
    ):  # Return "an universally quantified formula" if whatever follows after "Ax" is a first order formula,
        # else return "not a formula".
        if first_order(fmla[2:]):
            return 3
        else:
            return 0

    elif (
        fmla[0] == "~"
    ):  # Return "a negation of a first order logic formula" if whatever follows after "~" is a first order formula,
        # return "a negation of a propositional formula" if whatever follows after "~" is a propositional formula.
        if first_order(fmla[1:]):
            return 2
        if prop_formula(fmla[1:]):
            return 7
        else:
            return 0

    # Handling binary connective formulas (e.g., "( ... connective ... )")
    elif fmla[0] == "(" and fmla[-1] == ")":
        try:
            index = main_connective(fmla)
        except NotAFormula:
            return 0


        # Check if both sides are valid first-order or propositional formulas
        if first_order(lhs(fmla)) and first_order(rhs(fmla)):
            return 5  # Binary connective first-order formula

        elif prop_formula(lhs(fmla)) and prop_formula(rhs(fmla)):
            return 8  # Binary connective propositional formula

        else:
            return 0  # Not a valid formula

    # If no valid parsing case matches
    else:
        return 0  # Not a valid formula
     
    
# Check if theory is fully expanded i.e. all elements are literals
def expanded(theory, literal_count=0):
    adjust_theory(theory) # Normalize the theory
    for count, element in enumerate(theory):
        try:
            tableau_case(element)
            for char in ["E", "A"]:
                if char in element:
                    continue
        except NotAFormula:
            literal_count += 1
        if count + 1 == len(theory):
            return True if literal_count == len(theory) else False

# Check for contradictions (e.g. formula and its negation) in a tableau 
def contradictory(tableau):
    for count, element in enumerate(tableau):
        if element[0] != "~":
            if f"~{element}" in tableau[count + 1 : len(tableau)]:
                return True
        if element[0] == "~":
            if element[1:] in tableau[count + 1 : len(tableau)]:
                return True
    return False


# You may choose to represent a theory as a set or a list
def theory(fmla):  # initialise a theory with a single formula in it
    theory = [fmla]
    return theory

# Select a non-literal element from the theory
def pick_non_literal(theory):
    theory = adjust_theory(theory)
    for element in theory:
        try:
            tableau_case(element)
            return element
        except NotAFormula:
            continue

# Flatten a list of terms and return the closed terms
def closed_terms(tableau):
    tableau_sum = list_sum(list_sum(tableau))
    closed_terms = []
    for char in tableau_sum:
        if char in VARIABLES + CONSTANTS:
            closed_terms.append(char)
    return list(set(closed_terms))

# Apply alpha formula rules for conjuctive formulas
def alpha(phi, theory, case):
    if case == "/\\":
        theory.insert(0, lhs(phi))
        theory.insert(0, rhs(phi))
    elif case == "~=>":
        theory.insert(0, lhs(phi)[1:])
        theory.insert(0, f"~{rhs(phi)}")
    elif case == "~~":
        theory.insert(0, phi[2:])
    elif case == "~\\/":
        theory.insert(0, f"~{lhs(phi)[1:]}")
        theory.insert(0, f"~{rhs(phi)}")
    return theory

# Apply beta formula rules for disjunctive formulas
def beta(phi, theory):
    theory.insert(0, phi)
    return theory

# Apply delta formula rules for existential quantifiers
def delta(phi, theory, constant, bound_var):
    for count, char in enumerate(phi):
        if char == bound_var:
            phi = phi[:count] + constant + phi[count + 1 :]
    theory.insert(0, phi)
    return theory

# Apply gamma formula rules for universal quantifiers
def gamma(phi, theory, bound_var, closed_terms):
    for i in CONSTANTS + closed_terms:
        new_phi = phi
        for count, char in enumerate(phi):
            if char == bound_var:
                new_phi = new_phi[:count] + i + new_phi[count + 1 :]
        theory.insert(0, new_phi)
    return theory

# Classify formulas into tableau cases
def tableau_case(phi):
    if phi[0] == "~" and phi[1] == "~":
        return "~~"
    if phi[0] == "E":
        return "E"
    if phi[0] == "~" and phi[1] == "A":
        return "~A"
    if phi[0] == "A":
        return "A"
    if phi[0] == "~" and phi[1] == "E":
        return "~E"
    if phi[0] == "~":
        return f"~{con(phi)}"
    else:
        return con(phi)

# Flatten a list of lists
def list_sum(_list):
    sum_list = []
    for count, char in enumerate(_list):
        sum_list += _list[count]
    return sum_list

# Adjust the theory for consistent variable names
def adjust_theory(theory):
    for element in theory:
        adjust(element)
    return theory

# Function to replace the constants with generic variable names
def adjust(phi):
    for count, char in enumerate(phi):
        if char in CONSTANTS:
            phi = phi[:count] + "x" + phi[count + 1 :]
    return phi

# Extracts the left-hand side and right-hand side of a formula together
def lhs_rhs(phi, case):
    if case == "\\/":
        _lhs = lhs(phi)
        _rhs = rhs(phi)
    if case == "=>":
        _lhs = f"~{lhs(phi)}"
        _rhs = rhs(phi)
    if case == "~/\\":
        _lhs = f"~{lhs(phi)[1:]}"
        _rhs = f"~{rhs(phi)}"
    return _lhs, _rhs

# Add theory to the tableau if not contradictory
def add_theory(theory, tableau):
    if theory not in tableau and not contradictory(theory):
        tableau.insert(0, theory)


# check for satisfiability of a tableau
def sat(tableau):
    global PICKED
    if not prop_formula(tableau[0][0]) and not first_order(tableau[0][0]):
        return 0 # Invalid tableau
    while len(tableau) != 0:
        terms = closed_terms(tableau)
        theory = tableau.pop(0)
        if expanded(theory) and not contradictory(theory):
            PICKED = [] # Reset the PICKED constants
            return 1 # Satisfiable
        else:
            theory_copy = theory.copy()
            phi = pick_non_literal(theory_copy)
            try:
                case = tableau_case(phi)
            except NotAFormula:
                adjusted_phi = adjust(phi)
                case = tableau_case(adjusted_phi)
            theory.remove(phi)

            if case in ALPHA:
                theory = alpha(phi, theory, case)
                add_theory(theory, tableau)

            if case in BETA:
                _lhs, _rhs = lhs_rhs(phi, case)

                theory_1 = beta(_lhs, theory.copy())
                theory_2 = beta(_rhs, theory.copy())

                add_theory(theory_1, tableau)
                add_theory(theory_2, tableau)

            if case in DELTA:
                try:
                    constant = CONSTANTS[len(PICKED)]
                    PICKED.append(CONSTANTS[len(PICKED)])
                except IndexError:
                    PICKED = []
                    return 2 # Constant limit reached

                if case == "E":
                    theory = delta(phi[2:], theory, constant, phi[1])
                if case == "~A":
                    theory = delta(f"~{phi[3: len(phi)]}", theory, constant, phi[2])
                add_theory(theory, tableau)
            if case in GAMMA:
                if case == "A":
                    theory = gamma(phi[2:], theory, phi[1], terms)
                if case == "~E":
                    theory = gamma(f"~{phi[3 : len(phi)]}", theory, phi[2], terms)

                add_theory(theory, tableau)
    PICKED = [] # Reset PICKED
    return 0 # Unsatisfiable









#------------------------------------------------------------------------------------------------------------------------------:
#                   DO NOT MODIFY THE CODE BELOW. MODIFICATION OF THE CODE BELOW WILL RESULT IN A MARK OF 0!                   :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
